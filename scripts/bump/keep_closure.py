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

import re
from collections import defaultdict

TOKEN = re.compile(r"[^\W\d][\w.'!?]*")
AUTO = re.compile(r"^(?:_|match_\d|proof_\d|eq_\d|eq_def$|induct$|inj$|injEq$|sizeOf_spec$|casesOn$|recOn$|rec$|noConfusion)")
SORRY = re.compile(r"\bsorry\b")


PRIVATE_NAME = re.compile(r"^_private\.(?:.+?)\.\d+\.(.+)$")


def distinctive(last: str) -> bool:
    return len(last) >= 8 and ("_" in last or any(c.isupper() for c in last[1:]))


def visible_name(name: str) -> str | None:
    """The name a proof writes for a constant Lean reports as `name` (a private declaration is `_private.<Module>.<n>.<name>`); None for the compiler's own."""
    m = PRIVATE_NAME.match(name)
    if m:
        name = m.group(1)
    last = name.rsplit(".", 1)[-1]
    return None if any(c.startswith("_") for c in name.split(".")) or AUTO.match(last) else name


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


def close(
    modules,
    sidecars: dict,
    keep_blocks: dict[str, set],
    skip: set[str] = frozenset(),
    failed: dict[str, set[tuple[int, int]]] | None = None,
    aux_only: dict[str, set[tuple[int, int]]] | None = None,
    failed_seeds: list[tuple[str, tuple[int, int]]] | None = None,
) -> tuple[int, dict[str, set[str]]]:
    """Returns (how many declarations were added, {module: names it uses that cannot be kept}). `failed`: module -> the blocks that had an error in the build."""
    failed = failed or {}
    aux_only = aux_only or {}
    by_full: dict[str, list[tuple[str, tuple[int, int], tuple[int, int]]]] = defaultdict(list)
    by_last: dict[str, list[tuple[str, tuple[int, int], tuple[int, int]]]] = defaultdict(list)
    for mod, names in sidecars.items():
        if mod not in modules:
            continue
        for name, (s, e) in names.items():
            vis = visible_name(name)
            blk = modules[mod].block_of(s)
            if vis is None or blk is None:
                continue
            by_full[vis].append((mod, blk, (s, e)))
            last = vis.rsplit(".", 1)[-1]
            if distinctive(last):
                by_last[last].append((mod, blk, (s, e)))
    kept: set[tuple[str, tuple[int, int]]] = set()
    unresolved: dict[str, set[str]] = defaultdict(set)
    for mod, rs in keep_blocks.items():
        for blk in modules[mod].kept_blocks(rs) if mod in modules else ():
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
    while work:
        mod, blk = work.pop()
        if mod in skip:
            continue
        text = "\n".join(modules[mod].lines[blk[0] - 1 : blk[1]])
        for tok in set(TOKEN.findall(text)):
            tok = tok.rstrip(".")
            cands = list(by_full.get(tok, ()))
            exact = bool(cands)
            last = tok.rsplit(".", 1)[-1]
            if not cands and distinctive(last) and 0 < len(by_last.get(last, ())) <= 3:
                cands = list(by_last[last])
            for m2, b2, r2 in cands:
                if (m2, b2) in kept:
                    continue
                if b2 in failed.get(m2, ()):
                    # a declaration that failed in the build is never kept. The module that names it by its full name cannot go to the tree; a match by last component alone is a guess
                    # (a local name, a field, another declaration with the same ending): it keeps nothing and does not drop the naming module
                    if exact:
                        unresolved[mod].add(tok)
                    continue
                if SORRY.search("\n".join(modules[m2].lines[b2[0] - 1 : b2[1]])):
                    unresolved[mod].add(tok)
                    continue
                kept.add((m2, b2))
                keep_blocks[m2].add(r2)
                work.append((m2, b2))
                added += 1
    return added, unresolved
