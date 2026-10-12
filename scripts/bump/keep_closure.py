"""keep_closure.py — the declarations a bundle must keep because the TEXT of a kept declaration names them.

`BundleKeep.lean` computes what to keep from the elaborated terms of the passed theorems. A name that is written in a proof but does not end up in its term is invisible to that
closure: an argument of `simp only [foo]` / `simpa only [foo] using …` that the simplifier never needed, a lemma named in `rw`/`exact` that a later tactic made redundant, a name in a
`calc` or `have` that was inlined. The pruner then cuts `foo` from the module that declares it (nothing passed needs it), the module that names it still says `foo`, and the tree's
build stops at 'Unknown identifier `foo`' (2026-10-11: openai-math `PerfectMatching/Face.lean` named `polytope_eq_constraints`, cut from `PerfectMatching/Polytope.lean`; navier
`MeanPathLpBlocks.lean` named `pathLpOperator_apply`, cut from `TimeLpLinearity.lean`; each cost a recut of about an hour and a half). The bump compiles the unpruned files, so it never sees it.

`close(modules, sidecars, keep_blocks, skip)` adds those declarations to `keep_blocks` (in place) and repeats on what it added, until nothing new is named. A token matches a declaration
of the library when it equals the declaration's full name, or when its last component equals the declaration's last component and that component is a distinctive name (8+ characters
with an underscore or an inner capital, declared at most three times in the library): over-keeping a declaration is harmless, a missing one stops the build. A declaration that contains `sorry` is
never kept (the tree refuses it): the module that names it is returned in `unresolved`, to be left out. The same for a declaration that FAILED in the factory's own build (`failed`: the blocks
Lean reported an error in): it has no `sorry` in its text, Lean closes it with one, and the tree would stop at the same line (2026-10-11: six of the seven modules of openai-math part 7
that the merge queue rejected were this, each already in the factory's own error log at the same line).
"""

from __future__ import annotations

import json
import re
from collections import defaultdict

from adapters import code_mask

TOKEN = re.compile(r"[^\W\d][\w.'!?]*")
AUTO = re.compile(r"^(?:_|match_\d|proof_\d|eq_\d|eq_def$|induct$|inj$|injEq$|sizeOf_spec$|casesOn$|recOn$|rec$|noConfusion)")
SORRY = re.compile(r"\bsorry\b")
INSTANCE_BLOCK = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|scoped|local|public)\s+)*instance\b", re.M)


PRIVATE_NAME = re.compile(r"^_private\.(?:.+?)\.\d+\.(.+)$")


def field_notation(tok: str) -> bool:
    """`alg.predictorStep_wide`, `φ₁.tensorMul`: a distinctive name behind a local variable (lower case, Greek or a single capital such as `L`; never `_root_` or a namespace such as `Finset`)."""
    first, _, rest = tok.partition(".")
    return bool(rest) and first != "_root_" and (not first[:1].isupper() or len(first) == 1) and distinctive(tok.rsplit(".", 1)[-1])


def distinctive(last: str) -> bool:
    return len(last) >= 8 and ("_" in last or any(c.isupper() for c in last[1:]))


def visible_name(name: str) -> str | None:
    """The name a proof writes for a constant Lean reports as `name` (a private declaration is `_private.<Module>.<n>.<name>`); None for the compiler's own."""
    m = PRIVATE_NAME.match(name)
    if m:
        name = m.group(1)
    last = name.rsplit(".", 1)[-1]
    return None if any(c.startswith("_") for c in name.split(".")) or AUTO.match(last) else name


NAMESPACE_CMD = re.compile(r"^namespace\s+(\S+)")
SECTION_CMD = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:public\s+|noncomputable\s+|private\s+)*section\b")
END_CMD = re.compile(r"^end\b")
OPEN_CMD = re.compile(r"^(?:open|export)\s+(?:scoped\s+)?(?P<rest>.*?)(?:\s+in)?\s*$")


def open_names(rest: str) -> list[str]:
    """The namespaces an `open` command names (`open A B (x y) hiding z in` -> A, B)."""
    out = []
    for w in rest.split():
        if w.startswith("(") or w in ("hiding", "renaming", "in"):
            break
        out.append(w)
    return out


def code_lines(module) -> list[str]:
    """The lines of the module with comments and strings blanked: an `end` or `namespace` inside a block comment is no command (CodeRabbit on #34: a commented `end` popped a real section)."""
    text = "\n".join(module.lines)
    return "".join(c if k or c == "\n" else " " for c, k in zip(text, code_mask(text))).split("\n")


def walk_code(code: list[str]):
    """Yields (line number, the code of that line, the namespace in force before it, the namespaces opened before it) for every line. Only commands in column 0 change the context:
    `namespace`, `section`, `end`, `open`."""
    stack: list[tuple[list[str], set[str]]] = [([], set())]  # the file's own level: an `open` there lasts to the end of the file
    for i, line in enumerate(code, 1):
        yield i, line, ".".join(p for parts, _ in stack for p in parts), {o for _, os_ in stack for o in os_}
        if not line or line[0].isspace():
            continue
        m = NAMESPACE_CMD.match(line)
        if m:
            stack.append((m.group(1).split("."), set()))
        elif SECTION_CMD.match(line):
            stack.append(([], set()))
        elif END_CMD.match(line):
            if len(stack) > 1:
                stack.pop()
        else:
            m = OPEN_CMD.match(line)
            if m and not line.rstrip().endswith(" in"):
                stack[-1][1].update(open_names(m.group("rest")))


def block_contexts(module) -> dict[tuple[int, int], tuple[str, tuple[str, ...]]]:
    """For each block of the module: the namespace in force at its first line ('A.B', or '') and the namespaces opened there (and by an `open … in` inside the block)."""
    starts = {b[0]: b for b in module.blocks}
    code = code_lines(module)
    out: dict[tuple[int, int], tuple[str, tuple[str, ...]]] = {}
    for i, _, ns, opens in walk_code(code):
        if i in starts:
            b = starts[i]
            for ln in code[b[0] - 1 : b[1]]:  # an `open X in` that leads the declaration
                m = OPEN_CMD.match(ln)
                if m and ln.rstrip().endswith(" in"):
                    opens |= set(open_names(m.group("rest")))
            out[b] = (ns, tuple(sorted(opens)))
    return out


EXPORT_CMD = re.compile(r"^export\s+(?P<ns>[\w.']+)\s*\((?P<names>[^)]*)\)")


def glue_tail(line: str) -> str:
    """The part of a glue line that REFERS to declarations rather than binding names: after the closing bracket of `attribute [fun_prop] …`, after the `=>` of a notation (`infixl:90 "⨀₂" => mdp₂!`),
    after the `:=` of an `alias`. A `variable (k : ℕ)` binds `k`: it names no declaration, whatever `Ns.k` exists. Empty when there is no such part."""
    code = line.strip()
    if code.startswith(("attribute", "local attribute", "scoped attribute")) and "]" in code:
        return code[code.index("]") + 1 :]
    if "=>" in code:
        return code.split("=>", 1)[1]
    if code.startswith("alias") and ":=" in code:
        return code.split(":=", 1)[1]
    if m := EXPORT_CMD.match(code):  # `export Foo (bar baz)` makes `Foo.bar`, `Foo.baz` visible: they are what the command refers to
        return " ".join(f"{m.group('ns')}.{x}" for x in m.group("names").split())
    return ""


GLUE_SKIP = re.compile(r"^\s*(?:import|namespace|section|end|open|universe)\b|^\s*(?:@\[[^\]]*\]\s*)*(?:public\s+|noncomputable\s+|private\s+)*section\b")


BINDER_GROUP = re.compile(r"[\(\{\[⦃]\s*((?:[^\s:()\[\]{}⦃⦄]+\s+)*[^\s:()\[\]{}⦃⦄]+)\s*:")


def without_binders(line: str) -> str:
    """A `variable` line with the names it BINDS blanked: `variable {k : ℕ} (h : k = 1)` binds `k` and `h`; their uses are not references to a declaration `Ns.k` either."""
    code = line.strip()
    if not code.startswith(("variable", "local variable")):
        return line
    names = {n for m in BINDER_GROUP.finditer(code) for n in m.group(1).split()}
    return re.sub(r"(?<![\w.'])(?:" + "|".join(map(re.escape, sorted(names, key=len, reverse=True))) + r")(?![\w'])", " ", line) if names else line


def glue_units(module) -> list[tuple[str, str, tuple[str, ...]]]:
    """(code, namespace, opens) for every line outside all blocks that is not a structure command: the glue that stays in the pruned file whatever is kept (an `attribute [fun_prop] foo`, a
    `variable (x : Foo)`, a local notation). Comments and strings are blanked, so prose naming a declaration names nothing."""
    inside = {n for s, e in module.blocks for n in range(s, e + 1)}
    return [(line, ns, tuple(sorted(opens))) for i, line, ns, opens in walk_code(code_lines(module)) if i not in inside and line.strip() and not GLUE_SKIP.match(line)]


def namespace_candidates(tok: str, ns: str, opens: tuple[str, ...]) -> list[list[str]]:
    """The full names `tok` can mean at a place in namespace `ns` with `opens`, most specific first (Lean's order): each inner list is one priority level."""
    levels: list[list[str]] = []
    parts = ns.split(".") if ns else []
    for k in range(len(parts), 0, -1):
        levels.append([".".join(parts[:k]) + "." + tok])
    levels.append([tok])
    levels.append([o + "." + tok for o in opens] + [".".join(parts[:k]) + "." + o + "." + tok for o in opens for k in range(len(parts), 0, -1)])
    return levels


def aux_only_ranges(kept, source_of) -> dict[str, set[tuple[int, int]]]:
    """module -> the declaration ranges that are in the keep set ONLY because of compiler-made constants (`Foo._proof_1`, `match_1`, `eq_1`…) that map onto them. Lean extracts closed
    sub-proofs of a declaration as `_proof_N` constants and a later theorem may reuse one: its term then names `Foo._proof_1`, and the pruner mapped that onto the whole of `Foo`. The
    theorem's own text proves the sub-goal again, so nothing needs `Foo` itself (openai-math `differenceLaw_fresh`, 2026-10-11: Gate 2 had rejected it, and it was shipped)."""
    flags: dict[tuple[str, tuple[int, int]], list[bool]] = defaultdict(list)
    for mod, const in kept:
        r = source_of(mod, const)
        if r:
            flags[(mod, tuple(r))].append(visible_name(const) is None)
    out: dict[str, set[tuple[int, int]]] = defaultdict(set)
    for (mod, r), fl in flags.items():
        if all(fl):
            out[mod].add(r)
    return out


def parse_graph(log: str) -> tuple[dict[tuple[str, str], set[tuple[str, str]]] | None, set[tuple[str, str]] | None]:
    """(graph, tainted) from the `BUNDLE_GRAPH` lines of the keep logs (BundleKeep.lean prints one per shard): graph[(module, constant)] = the constants that one uses, among the library
    constants the keep step did NOT keep; tainted = those that stand on `sorryAx`. (None, None) when the log has no such line (a shard run from before the graph existed): the
    closure then works as it always did."""
    graph: dict[tuple[str, str], set[tuple[str, str]]] = defaultdict(set)
    tainted: set[tuple[str, str]] = set()
    found = False
    for m in re.finditer(r"BUNDLE_GRAPH (\{.*?\}) BUNDLE_END", log, re.S):
        found = True
        j = json.loads(re.sub(r"\s*\n\s*", "", m.group(1)))
        nodes = [(mod, c) for mod, c in j["nodes"]]
        for i, deps in j["edges"]:
            graph[nodes[i]].update(nodes[d] for d in deps)
        tainted.update(nodes[i] for i in j["tainted"])
    return (dict(graph), tainted) if found else (None, None)


def close(
    modules,
    sidecars: dict,
    keep_blocks: dict[str, set],
    skip: set[str] = frozenset(),
    failed: dict[str, set[tuple[int, int]]] | None = None,
    aux_only: dict[str, set[tuple[int, int]]] | None = None,
    failed_seeds: list[tuple[str, tuple[int, int]]] | None = None,
    fatal: dict[str, set[tuple[int, int]]] | None = None,
    graph: dict[tuple[str, str], set[tuple[str, str]]] | None = None,
    tainted: set[tuple[str, str]] | None = None,
    stats: dict | None = None,
    drop_tainted: bool = False,
) -> tuple[int, dict[str, set[str]]]:
    """Returns (how many declarations were added, {module: names it uses that cannot be kept}). `failed`: module -> the blocks that had an error in the build.

    `graph`/`tainted` (parse_graph): what the TERM of a kept declaration uses. A declaration kept because a kept text names it has no term in the keep step, so a lemma or an instance
    its proof uses without any text naming it was never kept (the closure above is of text, and a name is invisible to it when no one writes it: lean-pool `PDL`, tauceti `Quasicoherent`).
    With the graph, every block that is kept, by the keep step or by text, brings what its constants use, and that is followed to the end. `stats["followed"]` counts the blocks the graph added.

    `tainted` (constants that stand on `sorryAx` IN THE LIBRARY'S OWN BUILD) is reported by default (`stats["text_kept_tainted"]`: the blocks added by text or by the graph that are tainted) and acts
    only with `drop_tainted`: then such a block is not kept for a text that names it, like one that failed in the build. It is off by default because the library's build is not the tree's:
    on btc-verified the rule dropped one module and, through its importers, 67 of 101 theorems, some of which the tree's newer Mathlib may well build; the tree's own build (tree_verify.py)
    is the judge of that."""
    failed = failed or {}
    aux_only = aux_only or {}
    fatal = fatal or {}
    by_full: dict[str, list[tuple[str, tuple[int, int], tuple[int, int]]]] = defaultdict(list)
    by_last: dict[str, list[tuple[str, tuple[int, int], tuple[int, int]]]] = defaultdict(list)
    block_range: dict[tuple[str, tuple[int, int]], tuple[int, int]] = {}  # the range Lean reported for a block: a block without one cannot ship
    for mod, names in sidecars.items():
        if mod not in modules:
            continue
        for name, (s, e) in names.items():
            vis = visible_name(name)
            blk = modules[mod].block_of(s)
            if vis is None or blk is None:
                continue
            by_full[vis].append((mod, blk, (s, e)))
            block_range.setdefault((mod, blk), (s, e))
            last = vis.rsplit(".", 1)[-1]
            if distinctive(last):
                by_last[last].append((mod, blk, (s, e)))

    def locate(mod: str, const: str):
        """(module, block, range) of the declaration of `const`, or of the declaration it was made for (`foo.proof_1`, `foo.match_1`: the longest prefix Lean has a range for)."""
        names = sidecars.get(mod)
        if not names or mod not in modules:
            return None
        parts = const.split(".")
        while parts:
            r = names.get(".".join(parts))
            if r:
                blk = modules[mod].block_of(r[0])
                return (mod, blk, (r[0], r[1])) if blk else None
            parts.pop()
        return None

    graph_edges: dict[tuple[str, tuple[int, int]], dict[tuple[str, tuple[int, int]], tuple[int, int]]] = defaultdict(dict)
    tainted_blocks: set[tuple[str, tuple[int, int]]] = set()
    for node, deps in (graph or {}).items():
        src = locate(*node)
        if src is None:
            continue
        for d in deps:
            dst = locate(*d)
            if dst is not None and dst[:2] != src[:2]:
                graph_edges[src[:2]][dst[:2]] = dst[2]
    for node in tainted or ():
        if (src := locate(*node)) is not None:
            tainted_blocks.add(src[:2])
    contexts: dict[str, dict[tuple[int, int], tuple[str, tuple[str, ...]]]] = {}
    kept: set[tuple[str, tuple[int, int]]] = set()
    unresolved: dict[str, set[str]] = defaultdict(set)
    for mod, rs in keep_blocks.items():
        for blk in modules[mod].kept_blocks(rs) if mod in modules else ():
            if blk in fatal.get(mod, ()):
                # the parser stopped inside this block in the factory's own build (a theorem can still pass Gate 2: Lean elaborates the text up to the stop): the same text stops it in the tree,
                # so the module cannot ship (lean-pool Exercise113, 2026-10-11: a cleanup step had deleted a closing bracket)
                unresolved[mod].add(f"<block at line {blk[0]} does not parse>")
                continue
            if blk in failed.get(mod, ()):
                ranges_in = {r for r in rs if blk[0] <= r[0] <= blk[1]}
                if ranges_in and ranges_in <= aux_only.get(mod, set()):
                    # only a compiler-made sub-proof of this failed declaration was needed (see aux_only_ranges): the theorem that reused it proves the sub-goal in its own text
                    rs -= ranges_in
                    continue
                # a block the build failed in IS needed by the term of something that passed. It stays (parts 1-7 of openai-math shipped such blocks and merged: dropping every module that has one
                # would lose about a tenth of the library), but it is accounted for: the caller reports it, so a rejection in the queue can be traced to it
                if failed_seeds is not None:
                    failed_seeds.append((mod, blk))
            kept.add((mod, blk))
    work = list(kept)
    added = 0

    def resolve(tok: str, context, glue: bool = False):
        """(the declarations `tok` can name, whether by its full name as written or as its namespace and `open`s read it). In glue (`infixl:90 "⨀₂" => mdp₂!`, `alias foo := bar'!`) a name
        of any length is read by the namespace it is written in: nothing there is a local variable, and the last-component guess below still needs a distinctive one. A QUALIFIED name
        (`FiniteContext.weakening` inside `namespace LO.Entailment`) is read that way at any length too: lean-pool `HilbertStyle/Context`, 2026-10-12, where `weakening` is one plain word."""
        last = tok.rsplit(".", 1)[-1]
        if glue:
            # glue is read the way Lean reads it: the innermost namespace first, the root last (`foo` inside `namespace Toy` is `Toy.foo` even when a root `foo` exists)
            ns, opens = context()
            for level in namespace_candidates(tok, ns, opens):
                hit = [c for name in level for c in by_full.get(name, ())]
                if hit:
                    return hit, True
        cands = list(by_full.get(tok, ()))
        exact = bool(cands)
        if not cands and (glue or distinctive(last) or "." in tok):
            # the name as the file's own namespace and `open`s read it: `pointsFunctor_map` inside `namespace HopfAlgebra` is `HopfAlgebra.pointsFunctor_map`, however many
            # declarations in the library end in that name (tauceti, 2026-10-11: a name that ends 4 times is out of reach of the last-component guess, and the module that wrote it
            # short lost the lemma)
            ns, opens = context()
            for level in namespace_candidates(tok, ns, opens):
                hit = [c for name in level for c in by_full.get(name, ())]
                if hit:
                    return hit, True
        if not cands and distinctive(last) and 0 < len(by_last.get(last, ())) <= 3:
            cands = list(by_last[last])
        return cands, exact

    def block_context_of(mod: str, blk: tuple[int, int]):
        def context():
            if mod not in contexts:
                contexts[mod] = block_contexts(modules[mod]) if mod in modules else {}
            return contexts[mod].get(blk, ("", ()))

        return context

    usable_memo: dict[tuple[str, tuple[int, int]], bool] = {}

    def usable(m2: str, b2: tuple[int, int]) -> bool:
        key = (m2, b2)
        if key not in usable_memo:
            usable_memo[key] = b2 not in failed.get(m2, ()) and not (drop_tainted and key in tainted_blocks) and not SORRY.search("\n".join(modules[m2].lines[b2[0] - 1 : b2[1]]))
        return usable_memo[key]

    bad_last_memo: dict[str, set[str]] = {}

    def bad_last(m2: str) -> set[str]:
        """The last components of the declarations of `m2` that cannot be kept (failed in the build, or sorry)."""
        if m2 not in bad_last_memo:
            bad_last_memo[m2] = {name.rsplit(".", 1)[-1] for name, (s, _) in sidecars.get(m2, {}).items() if (blk := modules[m2].block_of(s)) and not usable(m2, blk)}
        return bad_last_memo[m2]

    def block_tokens(mm: str, bb: tuple[int, int]) -> set[str]:
        return {t.rstrip(".") for t in TOKEN.findall("\n".join(modules[mm].lines[bb[0] - 1 : bb[1]]))}

    def clean_to_drag(m2: str, ib: tuple[int, int]) -> bool:
        """Whether keeping the optional block `ib` can only pull in declarations that are safe to keep: everything its text names, by the closure's own resolution, transitively, is usable,
        and lives in a module with no declaration that failed or has sorry. Such a module is not safe: an instance can lean on a failed declaration without naming it (`inferInstanceAs`
        finds another instance, which writes `qM.tensor`, a name by its last component only that the closure cannot resolve: tauceti `Quasicoherent/Monoidal`, 2026-10-12)."""
        seen: set[tuple[str, tuple[int, int]]] = set()
        stack = [(m2, ib)]
        while stack:
            mm, bb = stack.pop()
            if (mm, bb) in seen or (mm, bb) in kept:
                continue
            seen.add((mm, bb))
            if len(seen) > 300 or not usable(mm, bb) or bad_last(mm):
                return False
            context = block_context_of(mm, bb)
            stack.extend((c2, cb) for tok in block_tokens(mm, bb) for c2, cb, _ in resolve(tok, context)[0])
        return True

    def drag_instances(m2: str, b2: tuple[int, int]) -> None:
        """A declaration kept because a kept TEXT names it has no elaborated term in the keep step, so the instances its proof resolves silently are not in the keep set (tauceti
        `AlbertAlgebra.finrank_traceZero` names `Octonion.finrank_eq_eight`, whose proof needs the module's anonymous `Module.Free` instance: 'failed to synthesize' in the tree,
        2026-10-12). The instances of its module that come before it are kept with it, unless keeping one would pull in something that cannot be kept (`clean_to_drag`): an instance nobody
        asked for is not worth a module."""
        nonlocal added
        for ib in modules[m2].blocks:
            if ib[0] >= b2[0] or (m2, ib) in kept or (m2, ib) not in block_range or not usable(m2, ib):
                continue
            if not INSTANCE_BLOCK.search("\n".join(modules[m2].lines[ib[0] - 1 : ib[1]])) or not clean_to_drag(m2, ib):
                continue
            kept.add((m2, ib))
            keep_blocks[m2].add(block_range[(m2, ib)])
            work.append((m2, ib))
            added += 1

    def visit(mod: str, text: str, context, glue: bool = False) -> None:
        """Keep what `text` (a block of `mod`, or one line of its glue) names; `context()` is the (namespace, opens) the text is written in."""
        nonlocal added
        for tok in set(TOKEN.findall(text)):
            tok = tok.rstrip(".")
            if field_notation(tok) and tok.rsplit(".", 1)[-1] in bad_last(mod):
                # field notation on a local naming a declaration of THIS file that failed or has sorry: the tree stops at the same name (lean-pool `GeneratedConvergence`), however many
                # declarations elsewhere end in it (the capped last-component guess below would find none)
                unresolved[mod].add(tok)
            cands, exact = resolve(tok, context, glue)
            for m2, b2, r2 in cands:
                if (m2, b2) in kept:
                    continue
                if b2 in failed.get(m2, ()):
                    # a declaration that failed in the build is never kept. The module that names it by its full name cannot go to the tree; a match by last component alone is a guess
                    # (a local name, a field, another declaration with the same ending): it keeps nothing and does not drop the naming module, unless the declaration is in the naming
                    # module itself and its name is distinctive: field notation on a type declared in the same file (`x.predictorStep_wide`), lean-pool `GeneratedConvergence`, 2026-10-12
                    if exact:
                        unresolved[mod].add(tok)
                    continue
                if (drop_tainted and (m2, b2) in tainted_blocks) or SORRY.search("\n".join(modules[m2].lines[b2[0] - 1 : b2[1]])):
                    unresolved[mod].add(tok)  # sorry in the text, or (drop_tainted) a declaration that stands on one
                    continue
                kept.add((m2, b2))
                text_added.add((m2, b2))
                keep_blocks[m2].add(r2)
                work.append((m2, b2))
                added += 1
                drag_instances(m2, b2)

    followed = 0
    text_added: set[tuple[str, tuple[int, int]]] = set()  # blocks added by text or by the graph (not the keep step's own)

    def follow(mod: str, blk: tuple[int, int]) -> None:
        """What the terms of the constants declared in this kept block use, and nothing in the TEXT names (an instance found by unification, a lemma `simp` used). The block ships whole,
        so every constant it declares is elaborated in the tree, whether or not the keep step kept that constant."""
        nonlocal added, followed
        for (m2, b2), r2 in graph_edges.get((mod, blk), {}).items():
            if (m2, b2) in kept:
                continue
            if not usable(m2, b2):
                unresolved[mod].add(f"<a declaration in {m2} at line {b2[0]}, which the term of a kept declaration uses, cannot be kept>")
                continue
            kept.add((m2, b2))
            text_added.add((m2, b2))
            keep_blocks[m2].add(r2)
            work.append((m2, b2))
            added += 1
            followed += 1

    glue_read: set[str] = set()
    while work:
        mod, blk = work.pop()
        if mod in skip:
            continue
        if mod in modules and mod not in glue_read:
            # the glue of a module that ships stays in its pruned file whatever is kept (`attribute [fun_prop] measurable_polarRows`), so what it names is kept too (openai-math
            # `ProjectionMoments/BallMoments`, 2026-10-12: the lemma was cut from the module that declares it, and the tree stopped at 'Unknown constant')
            glue_read.add(mod)
            for line, ns, opens in glue_units(modules[mod]):
                ctx = lambda ns=ns, opens=opens: (ns, opens)  # noqa: E731
                if tail := glue_tail(line):
                    visit(mod, tail, ctx, glue=True)  # only what the command refers to; the rest of the line is attribute names, notation binders, keywords
                else:
                    visit(mod, without_binders(line), ctx)

        visit(mod, "\n".join(modules[mod].lines[blk[0] - 1 : blk[1]]), block_context_of(mod, blk))
        follow(mod, blk)
    if stats is not None:
        stats.update(
            followed=followed,
            graph_nodes=len(graph or ()),
            graph_edges=sum(len(v) for v in (graph or {}).values()),
            tainted=len(tainted or ()),
            text_kept_tainted=sorted(f"{m}:{b[0]}" for m, b in text_added if (m, b) in tainted_blocks),
        )
    return added, unresolved
