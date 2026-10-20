#!/usr/bin/env python3
"""tree_dups.py — a library's copy of a module the tree already has: the copy is not shipped, and what imports it imports the tree's module, when the two are provably the same.

A library can carry its own copy of another library's file (lean-pool pools 216 projects, and many vendor PFR, AddCombi, Mathlib files...). The tree already has that file, and it cannot hold two
declarations of one name, so the copy cannot go in. Until now the copy was dropped and so was everything that imports it (lean-pool: ~900 modules holding up ~20k theorems). This step keeps what
imports the copy, when it can show that nothing they stand on changes.

THE QUESTION THIS STEP ANSWERS, and nothing else: may a module that imports the library's copy M import the tree's module I instead, and still be the same module (the same statements, about the same
definitions)? It does not decide whether anything is true (Lean's kernel does, in the tree's build), and it does not look at proofs.

Where it runs: `tree_verify.py` has built the draft in the tree; the draft still holds M and its importers. This step, in order (the workflow runs the Lean programs between the commands):

  tree_dups.py candidates  find the copies: the new modules that built and share a name with a module of the tree (`ModuleClashes.lean`), the tree modules they share it with, and every new module
                           that imports a copy, directly or not. Writes the module lists the fingerprint program reads.
  (ModuleFingerprint.lean)  the fingerprints of the copies and their importers (BEFORE), and of the tree modules (PARTNERS)
  tree_dups.py plan        decide, per copy. SAME: every declaration of M is a declaration of the tree's module(s) with the same fingerprint (type, value and everything below them). Then M leaves the tree
                           checkout, and each module that imports it has the import line replaced by the tree's module(s) (`apply_alias_text`); `new.json` and `targets.txt` follow.
                           NOT SAME (or no verdict): nothing changes for M; it stays a clash, and the clash scan refuses it with what imports it, as before this step existed.
  (lake build)             the modules that import a copy are built again, now on the tree's module.
  tree_dups.py after-list  which of them built (a module that does not, or imports one that does not, is refused)
  (ModuleFingerprint.lean)  their fingerprints AFTER
  tree_dups.py after-verdict  a module whose declarations are not exactly what they were before (a name missing or added, a kind or a fingerprint changed) is refused with what imports it.

What the outcome of each decision lets you say (the claim, its assumptions, and what it does not claim):

  ALIASED (SAME, and every importer AFTER = BEFORE): in the tree's environment, each importer's declarations are the same, term for term below the seed, as when the copy was there; so the theorems
  it ships say what the library's text says, about the definitions the library's text has. Assumes: the fingerprint is a 128-bit structural hash (a collision is ~2^-128 and nobody controls the
  inputs), and the importer is the library's own text (the library build and Gate 2 judged it against the copy, in the library's environment: that step is unchanged and is not repeated here).
  Does NOT claim: that the proofs are the same (not read; the tree's build checks them), that the copy's own theorems are shipped (they are the tree's already: the ledger says so), or anything
  about registrations (instances, simp lemmas, notation) that no declaration of the importers shows.

  REFUSED (an importer whose declarations changed or that no longer builds): nothing is claimed about it, and it is not shipped, with what imports it. This is a statement that it was not shown to be the same.

  NOT SAME / NO VERDICT: nothing is claimed; the module goes the way it went before this step.

  FORKED IDENTICAL (`--fork-identical`, off unless asked): a copy that IS the tree's module cannot be aliased when a file that would import the tree's module is a file of Lean's `module` system and the
  tree's module is not (Lean: "cannot import non-`module` X from `module`": lean-pool's Navier importers, 2026-10-20). Rather than leave that copy and everything above it out, the copy is forked like one that
  differs. What ships is then a second copy of declarations the tree already has, under another name: the theorems of such a copy are DUPLICATES of the tree's, and the report counts them apart.

  FORKED (NOT SAME, with a complete fingerprint; the copy and what imports it are not `prelude` files and declare nothing outside the namespace): the copy is not the tree's module, so it cannot be aliased, and it declares names the tree has, so it cannot be
  shipped as it is. It and every module that imports it are wrapped in a namespace of their own (`<Library>Fork`: a `namespace` line after the header imports, left open to the end of the file; `apply_fork_text`),
  so that their declarations are `<Library>Fork.Foo`. The tree builds them so, and the program fingerprints each AFTER with the namespace left off (FP_STRIP): a module whose declarations are not
  exactly what they were BEFORE, in the library's own build, is refused with what imports it, like an importer of an aliased copy. Claims: each declaration of a forked module is, term for term below the
  seed, the declaration the library has (so the theorems say what the library says, about the definitions the library has), under the name `<Library>Fork.<name>`. Assumes what ALIASED assumes. Does NOT claim:
  that the forked module is anything like the tree's module of that name (it is another version, and both are in the tree), that proofs are the same, or anything about registrations (instances, simp lemmas)
  the wrap carries along: a forked copy's global instances and attributes are on its own types and names.

The result is written as `dups.json` (per mode); `bundle.py compose --tree-dups` makes the same edits to the bundle that ships (`apply_alias_text`), and `tree_verify.py check` then proves, byte for byte,
that every module that ships is a module the tree's build accepted.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import bundle_layers as bl  # noqa: E402
import lean_names  # noqa: E402
import bundle_rehead as rehead  # noqa: E402
import tolerant_build as tb  # noqa: E402
import tree_verify as tv  # noqa: E402

FP_LINE = re.compile(r"^FP\t(?P<mod>[^\t\n]+)\t(?P<name>[^\t\n]+)\t(?P<kind>[^\t\n]+)\t(?P<hash>[0-9a-f]{32})$", re.M)
FP_END = re.compile(r"^FPEND\t(?P<mod>[^\t\n]+)\t(?P<n>\d+)$", re.M)
FP_ERR = re.compile(r"^FPERR\t(?P<mod>[^\t\n]+)\t(?P<msg>[^\n]*)$", re.M)
MODULE_LINE = re.compile(r"^\s*module\s*(?:--.*)?$")
PRELUDE = re.compile(r"^\s*prelude\s*(?:--.*)?$")
# `public section`, `@[expose] public section`, `noncomputable section`: lean_names.names reads only a plain `section` as one (an `end` would pop the wrong scope)
SECTION_OPENER = re.compile(r"^([ \t]*)(?:@\[[^\]\n]*\][ \t]*)*(?:(?:public|private|meta|noncomputable)[ \t]+)+section\b", re.M)
IMPORT_RE = re.compile(r"^(\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?)(" + tb.MODNAME + r")(.*)$")
COMPONENT = re.compile(r"[^\W\d][\w']*")
# What Lean names itself while it elaborates a declaration: the matcher, the numbered proof and equation lemmas. Their numbers depend on the order the declarations were elaborated in, not on what is
# stated. A copy that differs from the tree's module only in these has the same statements: anything that mentions one of them in a type or a value (a definition that matches) takes its NAME into its
# fingerprint, so that one still differs. They are left out of the comparison of the copy's own declarations, never out of a fingerprint.
AUX = re.compile(r"^(?:match_\d+(?:_\d+)*|proof_\d+|eq_\d+|eq_def|eq_unfold|congr_simp)$")

class Fp(dict):
    """module (plain) -> declaration -> (kind, 32 hex digits), for the modules that were fingerprinted completely; `errors`: module -> why it was not (the program's message)."""

    errors: dict[str, str]

    def __init__(self, *a, **k):
        super().__init__(*a, **k)
        self.errors = {}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def quoted(module: str) -> str:
    """A module name as Lean writes it in an import (`Tengoku.Lib.A-B` -> `Tengoku.Lib.«A-B»`). Names that are already quoted are left as they are."""
    if "«" in module:
        return module
    return ".".join(c if COMPONENT.fullmatch(c) else f"«{c}»" for c in module.split("."))


def read_lines(path: str | Path) -> list[str]:
    p = Path(path)
    return [ln.strip() for ln in p.read_text().split("\n") if ln.strip()] if p.is_file() else []


def parse_fp(text: str) -> Fp:
    """The fingerprints of one or several ModuleFingerprint.lean runs (their outputs may be joined). A module counts only when its `FPEND` line is there AND its count is the number of `FP` lines read for it:
    a run that was killed, or a module the program could not import (`FPERR`), leaves that module out, and a module that was never fingerprinted must not pass as the same (the callers read its absence
    as 'no verdict' before the swap and as a refusal after it)."""
    rows: dict[str, dict[str, tuple[str, str]]] = defaultdict(dict)
    for m in FP_LINE.finditer(text):
        rows[tv.plain(m.group("mod"))][m.group("name")] = (m.group("kind"), m.group("hash"))
    out = Fp()
    for e in FP_END.finditer(text):
        mod = tv.plain(e.group("mod"))
        if int(e.group("n")) == len(rows.get(mod, {})):
            out[mod] = rows.get(mod, {})
        else:
            out.errors[mod] = f"its fingerprint is incomplete ({e.group('n')} declarations announced, {len(rows.get(mod, {}))} read)"
    for e in FP_ERR.finditer(text):
        out.errors[tv.plain(e.group("mod"))] = e.group("msg")[:300]
    return out


def parse_fp_file(path: str) -> Fp | None:
    """The fingerprints in a file, or None when the file is missing (the step did not run). Whatever is in the file is read module by module (`parse_fp`)."""
    p = Path(path)
    return parse_fp(p.read_text(errors="replace")) if p.is_file() else None


def clash_pairs(text: str, new_plain: set[str]) -> tuple[dict[str, set[str]], set[str]]:
    """(new module -> the tree modules it shares a name with, the new modules that share one with another NEW module too). Like the clash check itself, a run with no `clashes:` line did not
    finish and one whose count does not match its lines was cut short: both are refused. Names are the ones the program printed (guillemets where Lean writes them)."""
    done = tv.CLASH_DONE.search(text)
    if done is None:
        sys.exit("the clash check has no ending (it crashed or was killed): nothing is known about name clashes; refusing to guess")
    lines = list(tv.CLASH_LINE.finditer(text))
    if int(done.group("pairs")) != len(lines):
        sys.exit(f"the clash check says {done.group('pairs')} pair(s) and lists {len(lines)}: its output is incomplete; refusing to guess")
    partners: dict[str, set[str]] = defaultdict(set)
    both_new: set[str] = set()
    for ln in lines:
        a, b = ln.group("mod"), ln.group("other")
        a_new, b_new = tv.plain(a) in new_plain, tv.plain(b) in new_plain
        if a_new and b_new:
            both_new |= {tv.plain(a), tv.plain(b)}
        elif a_new:
            partners[tv.plain(a)].add(b)
        elif b_new:
            partners[tv.plain(b)].add(a)
    return partners, both_new


def decide(module: str, partners: list[str], before: Fp, partner_fp: Fp) -> tuple[list[str] | None, str]:
    """(the tree modules to import instead of `module`, "") when every declaration of `module` is a declaration of those modules with the same fingerprint; (None, why) when that cannot be shown.
    `module` and the partners are plain names. A module with no fingerprinted declaration is no verdict: an empty comparison would call anything the same. Lean's own auxiliary declarations (AUX) are not
    compared one by one: whatever states something in terms of one has its name in its fingerprint."""
    if module not in before:
        return None, "it was not fingerprinted" + (f" ({getattr(before, 'errors', {}).get(module, 'the run did not reach it')})")
    decls = {n: v for n, v in before[module].items() if not AUX.match(n.rsplit(".", 1)[-1])}
    if not decls:
        return None, "no declaration of it was fingerprinted"
    owners: dict[str, list[tuple[str, tuple[str, str]]]] = defaultdict(list)
    for p in partners:
        for name, v in partner_fp.get(tv.plain(p), {}).items():
            owners[name].append((p, v))
    unread = [p for p in partners if tv.plain(p) not in partner_fp]
    used: set[str] = set()
    for name, v in sorted(decls.items()):
        cands = owners.get(name)
        if not cands:
            # a tree module that was not fingerprinted may be the one that declares it: say so, so that the reason is not read as "the tree does not have it"
            return None, f"`{name}` is not declared by the tree's module(s)" + (f" that were fingerprinted ({unread[0]}: {getattr(partner_fp, 'errors', {}).get(tv.plain(unread[0]), 'the run did not reach it')})" if unread else "")
        same = sorted(p for p, pv in cands if pv == v)
        if not same:
            return None, f"`{name}` is not the same as the tree's (its type, or something it stands on, differs)"
        used.add(same[0])
    return sorted(used), ""


def apply_alias_text(text: str, aliases: dict[str, list[str]]) -> str:
    """The text with each header import of a module of `aliases` (plain name -> the tree's modules) replaced by imports of those modules, and a second copy of an import line dropped (the same
    rule as `bundle.once`). Only the header is read: a docstring that starts a line with the word `import` is prose. This is the one edit, made here on the checkout and by `bundle.py compose` on the
    bundle that ships, so that the bytes agree."""
    if not aliases:
        return text
    lines = text.split("\n")
    end, code = rehead.header_end(lines)  # code[i]: line i is code, not a line of a block comment
    out: list[str] = []
    seen: set[str] = set()
    changed = False
    for i, ln in enumerate(lines):
        m = IMPORT_RE.match(ln) if i < end and code[i] else None
        if m is None:
            out.append(ln)
            continue
        targets = aliases.get(tv.plain(m.group(2)))
        new = [ln] if targets is None else [f"{m.group(1)}{quoted(t)}{m.group(3)}" for t in targets]
        changed |= targets is not None
        for nl in new:
            if nl.strip() in seen:
                changed = True
                continue
            seen.add(nl.strip())
            out.append(nl)
    return "\n".join(out) if changed else text


def apply_fork_text(text: str, namespace: str) -> str | None:
    """The text with `namespace X` on its own line after the last import of the header (at the top of a file that imports nothing). Nothing closes it: Lean closes the scopes a file leaves open at its end,
    and nearly every file of the module system leaves `public section` open (4,049 of lean-pool's 4,131), where an `end X` would be an error. None for a file that cannot be wrapped: one with `prelude`.
    Files of Lean's `module` system are wrapped like any other (their `module` line and imports stay above the namespace). This is the one edit that makes a forked copy, made here on the checkout and by
    `bundle.py compose` on the bundle that ships (after `apply_alias_text`, in both places), so that the bytes agree."""
    lines = text.split("\n")
    end, code = rehead.header_end(lines)
    last = module_line = None
    for i in range(min(end, len(code))):
        if not code[i]:
            continue
        if PRELUDE.match(lines[i]):
            return None
        if MODULE_LINE.match(lines[i]):
            module_line = i
        if IMPORT_RE.match(lines[i]):
            last = i
    at = last + 1 if last is not None else module_line + 1 if module_line is not None else 0  # the `module` line comes first in a file of the module system, then its imports
    body = lines[:at] + ([""] if at else []) + [f"namespace {namespace}"] + lines[at:]
    return "\n".join(body) if text.endswith("\n") or not text else "\n".join(body) + "\n"


def wrap_escapes(text: str, namespace: str) -> list[str]:
    """The names a module declares outside `namespace` once it is wrapped in it: a `theorem _root_.foo` stays `foo` (CodeRabbit on emissary#73). Such a module is not forked: its declaration would still
    be the clashing one, and the theorem would be recorded under a name (`<namespace>.foo`) the shipped module does not declare. A `_root_.` in a type, a value, a comment or a string is not a declaration
    (lean_names.names reads code only)."""
    wrapped = apply_fork_text(text, namespace)
    if wrapped is None:
        return []
    return sorted(n for n in lean_names.names(SECTION_OPENER.sub(r"\1section", wrapped)) if not n.startswith(namespace + "."))


def is_module_system(text: str) -> bool:
    """The file is one of Lean's module system: a `module` line in its header."""
    lines = text.split("\n")
    end, code = rehead.header_end(lines)
    return any(code[i] and MODULE_LINE.match(lines[i]) for i in range(min(end, len(code))))


def alias_blocked(targets: list[str], members: set[str], texts: dict[str, str], tree: Path) -> bool:
    """True when the copy cannot be aliased: a file that would import the tree's module(s) (the copy and everything that imports it) is a file of the module system, and one of the tree's modules is
    not. Lean refuses that import. A tree module that has no file is not a module of the module system (it cannot be imported at all: the caller has filtered those)."""
    if not any(is_module_system(texts.get(w, "")) for w in members):
        return False
    for t in targets:
        f = (tree / Path(*tv.plain(t).split("."))).with_suffix(".lean")
        if not f.is_file() or not is_module_system(f.read_text(encoding="utf-8", errors="replace")):
            return True
    return False


def purge_build(tree: Path, rel: str) -> None:
    """The compiled files of a module that leaves the checkout (a stale olean must not be read by anything that imports the tree)."""
    stem = Path(rel).with_suffix("")
    for root in (".lake/build/lib/lean", ".lake/build/ir"):
        d = (tree / root / stem).parent
        if d.is_dir():
            for f in d.glob(stem.name + ".*"):
                f.unlink()


def new_graph(files: dict[str, bytes], mods: dict[str, dict]) -> dict[str, list[str]]:
    """module -> the new modules it imports, from the bundle's files (the draft)."""
    return {m: [d for d in deps if d in mods] for m, deps in bl.import_graph(files, {m: s["path"] for m, s in mods.items()}).items()}


def importers_of(root: str, graph: dict[str, list[str]]) -> set[str]:
    return tv.dependents({root}, graph)


def has_source(tree: Path, module: str) -> bool:
    """The module is a file of the tree's sources (`Tengoku.A.B` is `Tengoku/A/B.lean`). ModuleClashes reads every compiled file of the cache, and the cache keeps the compiled file of a module that moved
    (2026-10-19: `Tengoku.Std.CodeAction.Deprecated` next to `Tengoku.Seed.Std.CodeAction.Deprecated`): importing such a module is an import of a file that is not in the tree."""
    return (tree / Path(*tv.plain(module).split("."))).with_suffix(".lean").is_file()


def cmd_candidates(a: argparse.Namespace) -> None:
    new = json.loads(Path(a.new).read_text())
    ns, mods = new["ns"], new["modules"]
    out = Path(a.out)
    built = {tv.plain(m) for m in read_lines(a.built)}
    keyed = {tv.plain(m): m for m in mods}
    partners, both_new = clash_pairs(Path(a.clashes).read_text(errors="replace"), set(keyed))
    graph = new_graph(bl.read_bundle(Path(a.bundle)), mods)
    cands: dict[str, dict] = {}
    skipped: dict[str, str] = {}
    for plain_m, ps in sorted(partners.items()):
        m = keyed[plain_m]
        ps = {p for p in ps if has_source(Path(a.tree), p)}
        if not ps:
            skipped[m] = "the module it shares a name with has no source in the tree (a stale compiled file)"
        elif plain_m in both_new:
            skipped[m] = "it also shares a name with another new module of the bundle"
        elif plain_m not in built:
            skipped[m] = "it did not build in the tree"
        else:
            imps = sorted(x for x in importers_of(m, graph) if tv.plain(x) in built)
            cands[m] = {"partners": sorted(ps), "importers": imps}
    before = sorted({tv.plain(m) for m in cands} | {tv.plain(x) for c in cands.values() for x in c["importers"]})
    whole = sorted({tv.plain(p) for c in cands.values() for p in c["partners"]})
    out.mkdir(parents=True, exist_ok=True)
    (out / "dups-before.txt").write_text("".join(m + "\n" for m in before))
    (out / "dups-partners.txt").write_text("".join(m + "\n" for m in whole))
    (out / "dups-candidates.json").write_text(json.dumps({"ns": ns, "candidates": cands, "skipped": skipped}, indent=1) + "\n")
    # the verdict until `plan` says otherwise: nothing is aliased (a step that does not run, or has no time, leaves exactly this)
    (out / "dups.json").write_text(json.dumps({"ns": ns, "mode": a.mode, "aliases": {}, "not_same": {}, "refused": {}}, indent=1) + "\n")
    (out / "dups-failures.txt").write_text("")
    print(f"{len(cands)} copy(ies) of a tree module among the new modules, {len(before) - len(cands)} module(s) import one; {len(skipped)} skipped")
    for m, why in list(skipped.items())[:10]:
        print(f"  skipped: {tv.library_module(m, ns)}: {why}")


def fork_namespace(ns: str) -> str:
    """The namespace a library's forked copies are wrapped in: `LeanPool` -> `LeanPoolFork`."""
    return f"{ns}Fork"


def choose_forks(not_same: dict[str, str], cand: dict, before: Fp, aliased_plain: set[str], texts: dict[str, str], ns: str) -> tuple[dict[str, str], set[str], dict[str, str]]:
    """(the copies that are forked: copy -> why it is not the tree's, the modules to wrap: the forked copies and every module that imports one, and the copies that stay `not_same` -> why).
    A copy is forked when its fingerprint is complete (`before`: a copy that was not fingerprinted gives no verdict, and no verdict is never a yes) and it and everything that imports it can be wrapped
    (`apply_fork_text`). An identical copy that imports a forked one is not wrapped: it leaves the bundle."""
    forks = {m: why for m, why in not_same.items() if tv.plain(m) in before}
    kept_not_same = {m: why for m, why in not_same.items() if m not in forks}
    namespace = fork_namespace(ns)

    def problem(plain_module: str) -> str:
        text = texts.get(plain_module, "")
        if apply_fork_text(text, namespace) is None:
            return f"{plain_module} cannot be wrapped in a namespace (`prelude`)"
        if escapes := wrap_escapes(text, namespace):
            return f"{plain_module} declares {', '.join(f'`{n}`' for n in escapes[:3])} outside the namespace (`_root_`)"
        return ""

    while True:
        members = {m: ({tv.plain(m)} | {tv.plain(x) for x in cand[m]["importers"]}) - aliased_plain for m in forks}
        wrap = set().union(*members.values()) if members else set()
        bad = {m: why for m in forks if (why := next((pr for w in sorted(members[m]) if (pr := problem(w))), ""))}
        if not bad:
            return forks, wrap, kept_not_same
        for m, why in bad.items():  # a module of the fork cannot be wrapped faithfully: the copy goes the way it went before this step
            kept_not_same[m] = forks.pop(m) + "; not forked: " + why


def cmd_plan(a: argparse.Namespace) -> None:
    cand = json.loads(Path(a.candidates).read_text())
    if not cand["candidates"]:
        print("no copy of a tree module: nothing to decide")
        return
    before, partner_fp = parse_fp_file(a.fp_before), parse_fp_file(a.fp_partners)
    if before is None or partner_fp is None:
        print("no verdict: a fingerprint run did not finish, so nothing is aliased and the copies go the way they went before this step")
        return
    new = json.loads(Path(a.new).read_text())
    ns, mods = new["ns"], new["modules"]
    tree, out = Path(a.tree), Path(a.out)
    aliases: dict[str, list[str]] = {}
    not_same: dict[str, str] = {}
    for m, info in sorted(cand["candidates"].items()):
        targets, why = decide(tv.plain(m), info["partners"], before, partner_fp)
        if targets is None:
            not_same[m] = why
        else:
            aliases[m] = targets
    texts = {tv.plain(x): (tree / spec["path"]).read_text(encoding="utf-8") for x, spec in mods.items() if (tree / spec["path"]).is_file()}
    identical: dict[str, str] = {}
    if a.fork and a.fork_identical:
        for m in sorted(aliases):
            members = {tv.plain(m)} | {tv.plain(x) for x in cand["candidates"][m]["importers"]}
            if alias_blocked(aliases[m], members, texts, tree):
                identical[m] = "identical to " + ", ".join(aliases.pop(m)) + ", which a file of the module system cannot import (the tree's module is not one)"
        not_same.update(identical)
    plain_aliases = {tv.plain(m): ts for m, ts in aliases.items()}
    forks, wrap, not_same = choose_forks(not_same, cand["candidates"], before, set(plain_aliases), texts, ns) if a.fork else ({}, set(), not_same)
    fork_ns = fork_namespace(ns)
    edited: list[str] = []
    for x, spec in sorted(mods.items()):
        f = tree / spec["path"]
        if x in aliases or not f.is_file():
            continue
        text = f.read_text(encoding="utf-8")
        edited_text = apply_alias_text(text, plain_aliases) if any(tv.plain(i) in plain_aliases for i in tb.header_imports(text)) else text
        if tv.plain(x) in wrap:
            edited_text = apply_fork_text(edited_text, fork_ns) or edited_text  # choose_forks has seen that every module of `wrap` can be wrapped
        if edited_text != text:
            f.write_text(edited_text, encoding="utf-8")
            spec["sha256"] = sha256(edited_text.encode("utf-8"))
            edited.append(x)
    for m in aliases:
        (tree / mods[m]["path"]).unlink(missing_ok=True)
        purge_build(tree, mods[m]["path"])
        del mods[m]
    (out / "new.json").write_text(json.dumps(new, indent=1) + "\n")
    (out / "targets.txt").write_text("".join(m + "\n" for m in sorted(mods)))
    keyed = {tv.plain(m): m for m in mods}
    result = {"ns": ns, "mode": a.mode, "aliases": {tv.library_module(m, ns): ts for m, ts in aliases.items()},
              "not_same": {tv.library_module(m, ns): why for m, why in not_same.items()}, "refused": {},
              "forks": {tv.library_module(m, ns): why for m, why in forks.items()},
              "forks_identical": sorted(tv.library_module(m, ns) for m in forks if m in identical),
              "forked": sorted(tv.library_module(keyed[w], ns) for w in wrap if w in keyed), "fork_namespace": fork_ns if forks else ""}
    (out / "dups.json").write_text(json.dumps(result, indent=1) + "\n")
    importers = sorted({tv.plain(x) for m in aliases for x in cand["candidates"][m]["importers"]} - {tv.plain(m) for m in aliases})
    (out / "dups-importers.txt").write_text("".join(m + "\n" for m in importers))
    print(f"{len(aliases)} copy(ies) are the same as the tree's module(s) and leave the bundle; {len(forks)} are forked into {fork_ns} ({len(result['forks_identical'])} of them identical to the tree's, shipped again) with {len(result['forked']) - len(forks)} module(s) that import them; "
          f"{len(not_same)} are not shown to be the same; {len(edited)} module(s) edited")
    for m, why in list(not_same.items())[:10]:
        print(f"  not the same: {tv.library_module(m, ns)}: {why}")


def alive_after(a: argparse.Namespace) -> tuple[dict, dict, set[str], set[str]]:
    """(dups.json, new.json, the importers, the importers that did not build in the second build or import one that did not)"""
    dups = json.loads(Path(a.dups).read_text())
    new = json.loads(Path(a.new).read_text())
    ns, mods = new["ns"], new["modules"]
    cand = json.loads(Path(a.candidates).read_text())
    keyed = {tv.library_module(m, ns): m for m in cand["candidates"]}
    # what has to be shown to be exactly what it was: what imports an aliased copy (the copy itself is gone), and every module that was wrapped (the forked copies and what imports them)
    importers = {tv.plain(x) for lib in dups["aliases"] for x in cand["candidates"][keyed[lib]]["importers"]} - {tv.plain(keyed[lib]) for lib in dups["aliases"]}
    by_lib = {tv.library_module(m, ns): m for m in mods}
    importers |= {tv.plain(by_lib[w]) for w in dups.get("forked", []) if w in by_lib}
    log = Path(a.log2).read_text(errors="replace")
    failing = tv.failures_from_log(log, ns) & set(mods)
    graph: dict[str, list[str]] = {}
    for x, spec in mods.items():
        f = Path(a.tree) / spec["path"]
        graph[x] = [d for d in tb.header_imports(f.read_text(encoding="utf-8")) if d in mods] if f.is_file() else []
    gone = {tv.plain(m) for m in failing | tv.dependents(failing, graph)}
    if mods and not tv.FINISHED.search(log):
        # the build was killed or ran out of time: what has no `Built` line was not reached, and a module that was not built on the tree's module is not shown to be anything
        gone |= importers - {tv.plain(m.group("mod")) for m in tv.BUILT.finditer(log)}
    return dups, new, importers, importers & gone


def cmd_after_list(a: argparse.Namespace) -> None:
    dups, new, importers, gone = alive_after(a)
    alive = sorted(importers - gone)
    Path(a.out).mkdir(parents=True, exist_ok=True)
    (Path(a.out) / "dups-after.txt").write_text("".join(m + "\n" for m in alive))
    print(f"{len(alive)} of {len(importers)} importing module(s) built on the tree's module")


def cmd_after_verdict(a: argparse.Namespace) -> None:
    dups, new, importers, gone = alive_after(a)
    ns, mods = new["ns"], new["modules"]
    before, after = parse_fp_file(a.fp_before), parse_fp_file(a.fp_after)
    keyed = {tv.plain(m): m for m in mods}
    refused: dict[str, str] = {}
    for x in sorted(importers):
        if x not in keyed:
            continue
        if x in gone:
            refused[keyed[x]] = "it does not build on the tree's module, was not reached by the build, or imports a module that does not"
            continue
        b, f = (before.get(x) if before is not None else None), (after.get(x) if after is not None else None)
        if b is None or f is None:  # the checkout was already changed: what cannot be compared is not shown to be the same
            why = (getattr(after, "errors", {}) if f is None and after is not None else getattr(before, "errors", {})).get(x, "a fingerprint run did not reach it")
            refused[keyed[x]] = f"its fingerprints could not be compared ({why})"
            continue
        for name in sorted(set(b) | set(f)):
            if b.get(name) != f.get(name):
                refused[keyed[x]] = f"`{name}` is " + ("missing" if name not in f else "new" if name not in b else "not the same") + " on the tree's module"
                break
    dups["refused"] = {tv.library_module(m, ns): why for m, why in refused.items()}
    Path(a.dups).write_text(json.dumps(dups, indent=1) + "\n")
    Path(a.out).mkdir(parents=True, exist_ok=True)
    (Path(a.out) / "dups-failures.txt").write_text("".join(f"{m}\t{why}\n" for m, why in refused.items()))
    print(f"{len(importers) - len(refused)} of {len(importers)} importing module(s) are exactly what they were; {len(refused)} refused")
    for m, why in list(refused.items())[:10]:
        print(f"  refused: {tv.library_module(m, ns)}: {why}")


def cmd_merge(a: argparse.Namespace) -> None:
    modes: dict[str, dict] = {}
    ns = None
    for f in a.files:
        d = json.loads(Path(f).read_text())
        ns = d["ns"]
        if d["mode"] in modes:
            sys.exit(f"two files for the mode {d['mode']}")
        modes[d["mode"]] = {k: d[k] for k in ("aliases", "not_same", "refused")}
        modes[d["mode"]].update({k: d.get(k, v) for k, v in (("forks", {}), ("forked", []), ("fork_namespace", ""), ("forks_identical", []))})
    Path(a.out).write_text(json.dumps({"ns": ns, "modes": modes}, indent=1) + "\n")
    print(f"{sum(len(m['aliases']) for m in modes.values())} aliased in {sorted(modes)}")


def load_for_compose(path: str) -> dict[str, dict[str, list[str]]]:
    """mode -> {library module -> the tree modules}, from the merged file `--tree-dups` names. An unreadable or malformed file is an error: it would silently ship the importers as they were built."""
    d = json.loads(Path(path).read_text())
    if not isinstance(d, dict) or not isinstance(d.get("modes"), dict):
        sys.exit(f"{path}: not a merged dups file")
    out: dict[str, dict[str, list[str]]] = {}
    for mode, spec in d["modes"].items():
        al = spec.get("aliases")
        if not isinstance(al, dict) or not all(isinstance(k, str) and isinstance(v, list) and all(isinstance(x, str) for x in v) for k, v in al.items()):
            sys.exit(f"{path}: the aliases of {mode} are not a map from a module to a list of modules")
        out[mode] = al
    return out


def load_forks_for_compose(path: str) -> dict[str, tuple[str, set[str]]]:
    """mode -> (the namespace, the library modules that were wrapped in it), from the merged file `--tree-dups` names. A verdict from before forks existed has none: nothing is wrapped."""
    d = json.loads(Path(path).read_text())
    if not isinstance(d, dict) or not isinstance(d.get("modes"), dict):
        sys.exit(f"{path}: not a merged dups file")
    out: dict[str, tuple[str, set[str]]] = {}
    for mode, spec in d["modes"].items():
        forked, namespace = spec.get("forked", []), spec.get("fork_namespace", "")
        if not isinstance(forked, list) or not all(isinstance(x, str) for x in forked) or not isinstance(namespace, str) or (forked and not namespace):
            sys.exit(f"{path}: the forked modules of {mode} are not a list of modules with a namespace")
        out[mode] = (namespace, {tv.plain(x) for x in forked})
    return out


def load_identical_forks_for_compose(path: str) -> dict[str, set[str]]:
    """mode -> the library modules that were forked although they are the tree's own (their theorems are duplicates). A verdict from before this existed has none."""
    d = json.loads(Path(path).read_text())
    if not isinstance(d, dict) or not isinstance(d.get("modes"), dict):
        sys.exit(f"{path}: not a merged dups file")
    out: dict[str, set[str]] = {}
    for mode, spec in d["modes"].items():
        mods = spec.get("forks_identical", [])
        if not isinstance(mods, list) or not all(isinstance(x, str) for x in mods):
            sys.exit(f"{path}: the identical forks of {mode} are not a list of modules")
        out[mode] = {tv.plain(x) for x in mods}
    return out


def main(argv: list[str] | None = None) -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("candidates")
    c.add_argument("--clashes", required=True, help="the output of ModuleClashes.lean on the modules that built")
    c.add_argument("--new", required=True)
    c.add_argument("--built", required=True, help="out/built.txt: the new modules that built")
    c.add_argument("--bundle", required=True)
    c.add_argument("--tree", required=True, help="the checkout: a tree module that has no source file in it is not a module to import")
    c.add_argument("--out", required=True)
    c.add_argument("--mode", required=True)
    c.set_defaults(fn=cmd_candidates)
    p = sub.add_parser("plan")
    for k in ("--candidates", "--fp-before", "--fp-partners", "--new", "--tree", "--out", "--mode"):
        p.add_argument(k, required=True)
    p.add_argument("--fork", action="store_true", help="a copy that is not the tree's module (complete fingerprint) is wrapped in <Library>Fork with what imports it, instead of staying a clash")
    p.add_argument("--fork-identical", action="store_true", help="with --fork: a copy that IS the tree's module is forked too when a file of the module system would have to import a module of the tree that is not one (its theorems are duplicates)")
    p.set_defaults(fn=cmd_plan)
    for name, fn in (("after-list", cmd_after_list), ("after-verdict", cmd_after_verdict)):
        q = sub.add_parser(name)
        for k in ("--candidates", "--dups", "--new", "--tree", "--log2", "--out"):
            q.add_argument(k, required=True)
        if name == "after-verdict":
            q.add_argument("--fp-before", required=True)
            q.add_argument("--fp-after", required=True)
        q.set_defaults(fn=fn)
    m = sub.add_parser("merge")
    m.add_argument("--out", required=True)
    m.add_argument("files", nargs="+")
    m.set_defaults(fn=cmd_merge)
    a = ap.parse_args(argv)
    a.fn(a)


if __name__ == "__main__":
    main()
