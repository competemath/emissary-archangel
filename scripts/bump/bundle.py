#!/usr/bin/env python3
"""bundle.py — the intake bundle of a bumped library: only what passed, as ready-to-build Lean modules for the tree.

Per-record staging puts each theorem's whole context into a record (33 KB each on average: 600 MB per 17.6k records, ~4 GB for the
registered corpus), which cannot live in a repository. A bundle holds each module ONCE:

  Tengoku/<Library>/<source path>.lean   the library's modules cut down to what the passed theorems are made of PLUS every definition,
                                         structure, class and instance that stands on nothing failed (glue names them: `variable [C F]`, a
                                         notation), with the theorems those need; all glue (namespaces, opens, variables, notations, macros).
                                         A theorem nothing needs and nothing passed is gone, as is any declaration that failed or stands on
                                         one that did, and the text of any block Lean reported an error in. Imports are mapped to the tree's module names.
  Tengoku/<Library>.lean                 imports all of them
  manifest.jsonl                         one line per passed theorem: name, statement, module, source, how it was verified
  report.json                            counts, and what was left out and why

The pruned sources (original layout and imports, umbrella Mathlib) are written to --src: the workflow builds THAT with the tolerant
builder and requires zero errors and no sorry, so what is shipped is exactly what was built.

  bundle.py lean    --lib DIR --passed passed.json --roots R,R --out bundle-deps.lean
  bundle.py compose --lib DIR --log bundle-deps.log --passed passed.json --meta setup.ci.json --key K --toolchain T --errors build.log
                    --gate2 gate2.log --out BUNDLE --src PRUNED_SRC
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import portfolio  # noqa: E402
import records  # noqa: E402
import autonames  # noqa: E402
import strip_attrs  # noqa: E402
import tolerant_build as tb  # noqa: E402

# the packages the tree was seeded from (tengoku scripts/seed.py PACKAGES). A bundle reaches all of them through the root `Tengoku`, which
# re-exports every seeded module: where the seed's own modules sit in the tree (Tengoku/Seed/ since tengoku's restructure) is not the
# bundle's business, and a header of `public import Tengoku` is right before and after that move.
SEED_PACKAGES = ("Mathlib", "Batteries", "Aesop", "Qq", "ProofWidgets", "Plausible", "LeanSearchClient", "ImportGraph", "Cli")
CORE = ("Init", "Std", "Lean", "Lake")
IMPORT_RE = re.compile(r"^(\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?)(" + tb.MODNAME + r")(.*)$")

LEAN = r'''
open Lean Elab Command Meta

def bkParse (s : String) : Name := (s.splitOn ".").foldl (fun n part => Name.mkStr n part) Name.anonymous

def bkModOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?

/-- Does the constant stand on `sorryAx`, directly or through a library constant? (a failed proof, or anything built on one) -/
partial def bkTainted (env : Environment) (isOwn : Name → Bool) (memo : IO.Ref (Std.HashMap Name Bool)) (c : Name) : IO Bool := do
  if let some b := (← memo.get)[c]? then return b
  memo.modify (·.insert c false)  -- in progress: a cycle does not taint itself
  let some ci := env.find? c | return false
  let used := ci.getUsedConstantsAsSet
  let mut t := used.contains ``sorryAx
  unless t do
    for u in used.toList do
      if isOwn u && (← bkTainted env isOwn memo u) then
        t := true
        break
  memo.modify (·.insert c t)
  return t

/-- Every library constant (module, name) that must stay: the closure of the types, values and proofs of the passed theorems AND of every
library constant that is not a theorem and stands on nothing failed (definitions, structures, classes, instances: glue such as `variable
[MyClass F]` or a notation names them without any theorem using them, so cutting one breaks what is left). Theorems stay only
where something that stays needs them, and clean simp lemmas (`simp` uses them without the proof term saying so). -/
elab "#bundle_keep " names:str " in " libs:str : command => do
  let libMods : NameSet := (libs.getString.splitOn ",").foldl (fun s x => if x == "" then s else s.insert (bkParse x)) {}
  let j ← liftTermElabM do
    let env ← getEnv
    let isOwn (c : Name) : Bool := match bkModOf env c with | some m => libMods.contains m | none => false
    let taint ← IO.mkRef (({} : Std.HashMap Name Bool))
    let mut seeds : List Name := ((names.getString.splitOn ",").filter (· != "")).map bkParse
    -- `simp` (and `dsimp`) use the simp lemmas of the environment; a `rfl` lemma leaves nothing of itself in the proof term, so
    -- the closure of the passed theorems never sees it, yet the proofs that `simp` closed with it do not close without it
    let simpNames : NameSet := (← getSimpTheorems).lemmaNames.fold (init := {}) fun s o =>
      match o with
      | .decl n _ _ => s.insert n
      | _ => s
    -- a theorem's own auxiliary definitions (`foo.match_1`, ...) are not seeds: their source range is the theorem's block, and
    -- a seed keeps the block: a failed theorem would come back through its matcher
    let isAuxOfTheorem (c : Name) : Bool := Id.run do
      let mut p := c.getPrefix
      while !p.isAnonymous do
        if (env.find? p).any (·.isTheorem) then return true
        p := p.getPrefix
      return false
    for m in libMods.toList do
      let some idx := env.getModuleIdx? m | continue
      for c in env.header.moduleData[idx.toNat]!.constNames do
        if let some ci := env.find? c then
          if ci.isTheorem then
            if simpNames.contains c && !(← bkTainted env isOwn taint c) then seeds := c :: seeds
          else if !isAuxOfTheorem c && !(← bkTainted env isOwn taint c) then seeds := c :: seeds
    let mut seen : NameSet := {}
    let mut stack : List Name := seeds
    let mut consts : Array Json := #[]
    while !stack.isEmpty do
      match stack with
      | [] => pure ()
      | c :: rest =>
        stack := rest
        if seen.contains c then continue
        seen := seen.insert c
        if let some ci := env.find? c then
          for u in ci.getUsedConstantsAsSet.toList do
            if isOwn u && !seen.contains u then stack := u :: stack
          if let some m := bkModOf env c then
            consts := consts.push (Json.arr #[toJson m.toString, toJson c.toString])
    return Json.arr consts
  logInfo m!"BUNDLE_KEEP {j.compress} BUNDLE_END"
'''


def pascal(library: str) -> str:
    return "".join(p[:1].upper() + p[1:] for p in re.split(r"[-_ ]+", library) if p)


def built_modules(lib: Path, roots: list[str]) -> list[str]:
    base = lib / ".lake" / "build" / "lib" / "lean"
    out = []
    for p in sorted(base.rglob("*.olean")):
        mod = ".".join(tb.esc(x) for x in p.relative_to(base).with_suffix("").parts)
        if any(mod == r or mod.startswith(r + ".") for r in roots):
            out.append(mod)
    return out


def uses_mathlib(lib: Path) -> bool:
    pat = re.compile(r"\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(?:Mathlib|Batteries|Aesop|Qq|ProofWidgets|Plausible)\b")
    return any(
        pat.match(ln)
        for f in lib.rglob("*.lean")
        if ".lake" not in f.parts and f.name not in ("gate2-check.lean", "records-deps.lean", "bundle-deps.lean")
        for ln in f.read_text(errors="replace").splitlines()[:80]
    )


def lean_file(a: argparse.Namespace) -> None:
    lib = Path(a.lib)
    roots = [r for r in a.roots.split(",") if r]
    passed = json.loads(Path(a.passed).read_text())
    mods = built_modules(lib, roots)
    names = [n for m in sorted(passed) for n in passed[m]]
    head = ["import Lean"] + (["import Mathlib"] if uses_mathlib(lib) else []) + [f"import {m}" for m in sorted(passed)] + [LEAN]
    head.append(f'#bundle_keep "{",".join(names)}" in "{",".join(mods)}"')
    Path(a.out).write_text("\n".join(head) + "\n")
    print(f"{len(names)} passed names in {len(passed)} modules; {len(mods)} library modules")


def map_import_line(line: str, key: str, own: set[str]) -> tuple[str, str | None]:
    """The line with its module renamed for the tree, and the module's kind: 'own' / 'tree' / 'core' / 'external'.
    A comment after the module name is dropped: tengoku's header check reads a line that is nothing but the import, and a line with a trailing
    comment is not taken for a header line (the `import` word then reaches the content lint, which refuses it)."""
    m = IMPORT_RE.match(line)
    if not m:
        return line, None
    mod = m.group(2)
    rest = re.sub(r"\s*--.*$", "", m.group(3))
    if mod in own:
        return f"{m.group(1)}Tengoku.{pascal(key)}.{mod}{rest}", "own"
    head = mod.split(".")[0]
    if head in SEED_PACKAGES:
        return f"{m.group(1).replace('import all', 'import')}Tengoku{rest}", "tree"
    if head in CORE:
        return f"{m.group(1)}{mod}{rest}", "core"
    return line, "external"


def once(lines: list[str]) -> list[str]:
    """The lines without a second copy of an import line: every seeded package now maps to the one root import."""
    seen, out = set(), []
    for ln in lines:
        if IMPORT_RE.match(ln):
            if ln.strip() in seen:
                continue
            seen.add(ln.strip())
        out.append(ln)
    return out


def to_tree(text: str, key: str, own: set[str], rel: Path) -> str:
    """A pruned library module as the tree writes it: imports mapped to the tree's (`once`), and the library's auto-generated instance names given the
    tree's suffix (autonames.py: the name Lean generates depends on the module's root, which changes when the file moves into Tengoku)."""
    mapped = once([map_import_line(ln, key, own)[0] for ln in text.split("\n")])
    return autonames.rewrite("\n".join(mapped) + "\n", autonames.root_of(rel))[0]


def compose(a: argparse.Namespace) -> None:
    lib, out, src = Path(a.lib), Path(a.out), Path(a.src)
    meta = json.loads(Path(a.meta).read_text())
    passed = json.loads(Path(a.passed).read_text())
    log = Path(a.log).read_text(errors="replace")
    kept = set()
    for m in re.finditer(r"BUNDLE_KEEP (\[.*?\]) BUNDLE_END", log, re.S):
        kept |= {(mod, c) for mod, c in json.loads(re.sub(r"\s*\n\s*", "", m.group(1)))}
    if passed and not kept:  # the Lean step failed (an empty bundle would look like a library with nothing to keep)
        sys.exit("bundle-deps.log has no BUNDLE_KEEP line although theorems passed:\n" + "\n".join(log.splitlines()[-15:]))
    sidecars = {}
    base = lib / ".lake" / "build" / "lib" / "lean"
    for f in base.rglob("*.olean.ranges.json"):
        mod = ".".join(tb.esc(x) for x in str(f.relative_to(base))[: -len(".olean.ranges.json")].split("/"))
        sidecars[mod] = {n: (s, e) for n, s, e in json.loads(f.read_text())}
    own = set(sidecars)

    def source_of(mod: str, const: str):
        names = sidecars.get(mod, {})
        parts = const.split(".")
        while parts:
            r = names.get(".".join(parts))
            if r:
                return tuple(r)
            parts.pop()
        return None

    keep_blocks: dict[str, set] = defaultdict(set)
    for mod, c in kept:
        r = source_of(mod, c)
        if r:
            keep_blocks[mod].add(r)
    # lines Lean reported an error on: the text of a declaration that never made it into the environment has no range, so it looks like glue
    err_lines: dict[str, set[int]] = defaultdict(set)
    for ln in Path(a.errors).read_text(errors="replace").splitlines():
        m = portfolio.ERROR.match(ln)
        if m:
            err_lines[m.group(1)].add(int(m.group(2)))
    modules: dict[str, records.Module] = {}
    glue_error: set[str] = set()
    for mod in own:
        parts = tb.split_mod(mod)
        path = lib.joinpath(*parts[:-1], parts[-1] + ".lean")
        if not path.exists():
            continue
        m = records.Module(lib, mod, list(sidecars[mod].values()))
        rel = str(path.relative_to(lib))
        if err_lines.get(rel):
            for s, e in portfolio.blocks(m.lines):
                text = "\n".join(m.lines[s - 1 : e])
                if any(s <= L <= e for L in err_lines[rel]) and records.DECL.match(text.lstrip()) and (s, e) not in m.blocks:
                    m.blocks.append((s, e))
            m.blocks.sort()
        modules[mod] = m
        # an error outside every declaration block (a `variable`, a notation) cannot be cut out: the module cannot be shipped
        if err_lines.get(rel) and any(not any(bs <= L <= be for bs, be in m.blocks) for L in err_lines[rel]):
            glue_error.add(mod)
    imports = {mod: [d for d in tb.header_imports("\n".join(m.lines)) if d in own] for mod, m in modules.items()}
    external = {}
    for mod, m in modules.items():
        bad = []
        for name in tb.header_imports("\n".join(m.lines)):  # the header only: a docstring line that starts with the word "import" is prose, not an import
            _, kind = map_import_line(f"import {name}", a.key, own)
            if kind == "external":
                bad.append(name)
        if bad:
            external[mod] = bad
    # a module that imports a package the tree does not have cannot be built there, nor can what imports it
    base_dropped: dict[str, str] = {m: "imports " + ", ".join(b) for m, b in external.items()}
    base_dropped.update({m: "an error outside any declaration (glue)" for m in glue_error})
    # modules the merge queue's build of the tree could not compile (a name Mathlib has and the tree does not: a deprecated alias...): left out with what imports them
    for m in (a.drop_modules or "").split(","):
        if m.strip() in modules:
            base_dropped[m.strip()] = "did not build on the tree"
    sys.setrecursionlimit(100000)
    # the pruned text of every module that could be needed (what the passed theorems are made of, and what that imports)
    reach: set[str] = set()

    def reach_from(mod: str) -> None:
        if mod in reach or mod not in modules:
            return
        reach.add(mod)
        for d in imports[mod]:
            reach_from(d)

    for mod in keep_blocks:
        reach_from(mod)
    pruned = {mod: modules[mod].text(keep_blocks.get(mod, set()), strip_imports=False) for mod in reach}
    # attributes the tree's allow-list refuses are left out of the declarations that stay (strip_attrs.py): they never change what a declaration
    # says, and a proof that relied on one is found by the verification build
    stripped_attrs: Counter = Counter()
    for mod in list(pruned):
        pruned[mod], c = strip_attrs.strip_attributes(pruned[mod])
        stripped_attrs.update(c)
        pruned[mod], n_traces = strip_attrs.strip_portfolio_traces(pruned[mod])
        if n_traces:
            stripped_attrs["portfolio trace"] += n_traces
    # The tree compiles what it takes under its content lint (an allow-list of known-inert commands, attributes and options). The
    # copy here is tengoku's (scripts/bump/lint); the header is the bundle's own business (imports are mapped, `module` is the
    # module system), so it is not linted. `proposed` is the same lint with notation commands allowed (notation, infix, prefix,
    # postfix, notation3, scoped/local): they elaborate a term like any other and cannot run code of the library's, and
    # without them most libraries' statements do not read. Both bundles are cut; which one the tree takes is a policy decision.
    sys.path.insert(0, str(HERE / "lint"))
    import allowlist  # noqa: E402

    allowed = set(json.loads((HERE / "lint" / "allowed-options.json").read_text())["allowed"])
    notation_ok = re.compile(r"`(?:notation3?|infix[lr]?|prefix|postfix|scoped|local)`")
    header = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s|^\s*(?:module|prelude)\s*$")
    lint: dict[str, list[str]] = {}
    for mod, text in pruned.items():
        body = "\n".join(("" if header.match(ln) else ln) for ln in text.split("\n"))
        lint[mod] = allowlist.violations(body, allowed)
    repo = meta["repo"].rstrip("/").removesuffix(".git")
    via = passed_via(a.gate2)
    summary = {}
    for mode in ("strict", "proposed"):
        viol = {m: [v for v in vs if mode == "strict" or not notation_ok.search(v)] for m, vs in lint.items()}
        dropped = dict(base_dropped)
        dropped.update({m: "lint: " + "; ".join(vs[:3]) for m, vs in viol.items() if vs and m not in dropped})
        changed = True
        while changed:
            changed = False
            for mod, ds in imports.items():
                if mod not in dropped and any(d in dropped for d in ds):
                    dropped[mod] = "imports a module that cannot go to the tree"
                    changed = True
        needed: set[str] = set()

        def need(mod: str) -> None:
            if mod in needed or mod not in pruned or mod in dropped:
                return
            needed.add(mod)
            for d in imports[mod]:
                need(d)

        for mod in keep_blocks:
            need(mod)
        manifest, left_out = [], defaultdict(int)
        for mod, names in passed.items():
            if mod not in needed:
                left_out[dropped.get(mod, "module not in the bundle")] += len(names)
                continue
            m = modules[mod]
            for n in names:
                r = source_of(mod, n)
                if not r:
                    left_out["no source range"] += 1
                    continue
                text = "\n".join(m.lines[r[0] - 1 : r[1]])
                text = re.sub(r"^\s*/--.*?-/\s*", "", text, count=1, flags=re.S)
                lines_ = text.split("\n")
                while lines_ and records.IN_PREFIX.match(lines_[0]):  # `open Foo in` above the declaration belongs to the module, not the statement
                    lines_.pop(0)
                text = "\n".join(lines_)
                he = portfolio.statement_end(text, 0)
                stmt = (text[:he] if he > 0 else text.split(":=")[0]).strip()
                rel = str(m.path.relative_to(lib))
                manifest.append({"name": n, "statement": stmt, "module": f"Tengoku.{pascal(a.key)}.{mod}", "source_path": rel, "library": a.key,
                                 "source_url": f"{repo}/blob/{meta['commit']}/{rel}", "toolchain": a.toolchain, "via": via.get(n, "")})
        out_dir = out if mode == "strict" else Path(str(out) + "-proposed")
        src_dir = src if mode == "strict" else Path(str(src) + "-proposed")
        tree_root = out_dir / "Tengoku" / pascal(a.key)
        for d in (tree_root, src_dir):
            d.mkdir(parents=True, exist_ok=True)
        for mod in sorted(needed):
            rel = modules[mod].path.relative_to(lib)
            (src_dir / rel).parent.mkdir(parents=True, exist_ok=True)
            (src_dir / rel).write_text(pruned[mod] + "\n")
            (tree_root / rel).parent.mkdir(parents=True, exist_ok=True)
            (tree_root / rel).write_text(to_tree(pruned[mod], a.key, own, rel))
        (out_dir / "Tengoku" / f"{pascal(a.key)}.lean").write_text("".join(f"import Tengoku.{pascal(a.key)}.{m}\n" for m in sorted(needed)))
        # tengoku's generator rewrites Tengoku/All.lean from the libraries that have a Deps.lean: an empty one (a comment) keeps this library in it
        (tree_root / "Deps.lean").write_text(f"-- {pascal(a.key)}: a factory bundle (data/intake/{a.key}). This file only marks the library for Tengoku/All.lean.\n")
        (out_dir / "manifest.jsonl").write_text("".join(json.dumps(r, ensure_ascii=False) + "\n" for r in manifest))
        # what each rule costs: the passed theorems of a module whose lint failed, and of every module that imports it
        importers: dict[str, set[str]] = defaultdict(set)
        for mod_, ds in imports.items():
            for d in ds:
                importers[d].add(mod_)

        def with_importers(root: str) -> set[str]:
            seen_, stack = set(), [root]
            while stack:
                x = stack.pop()
                if x not in seen_:
                    seen_.add(x)
                    stack.extend(importers[x])
            return seen_

        classes: dict[str, int] = defaultdict(int)
        for m_, vs in viol.items():
            if vs:
                affected = sum(len(passed.get(x, [])) for x in with_importers(m_))
                for v in {x[:70] for x in vs}:
                    classes[v] += affected
        report = {"library": a.key, "lint_mode": mode, "modules_in_bundle": len(needed), "modules_dropped": len(dropped), "dropped": dict(list(dropped.items())[:50]), "dropped_truncated": len(dropped) > 50,
                  "theorems": len(manifest), "passed_total": sum(len(v) for v in passed.values()), "left_out": dict(left_out), "kept_constants": len(kept), "stripped_attributes": dict(stripped_attrs.most_common(15)),
                  "lint_cost": dict(sorted(classes.items(), key=lambda x: -x[1])[:15])}
        (out_dir / "report.json").write_text(json.dumps(report, indent=1))
        summary[mode] = {k: v for k, v in report.items() if k not in ("dropped", "lint_cost", "left_out")}
    print(json.dumps(summary))


def refine(a: argparse.Namespace) -> None:
    """After a verification build that was not clean: leave out the modules that did not build (and every module that imports one),
    from both bundles and their pruned sources. What was not built in the tree's environment is not shipped; the next build must be clean."""
    rep = json.loads(Path(a.report).read_text())
    log = Path(a.log).read_text(errors="replace")
    def to_mod(f: str) -> str:
        return ".".join(tb.esc(x) for x in f.removeprefix("./")[: -len(".lean")].split("/"))

    bad = {m for m, s in rep["status"].items() if s["state"] != "clean"}
    bad |= {to_mod(f) for f in re.findall(r"^error: (\S+?\.lean)\b", log, re.M)}
    bad |= {to_mod(f) for f in re.findall(r"^warning: (\S+?\.lean):\d+:\d+: declaration uses .sorry.", log, re.M)}
    key = pascal(a.key)
    summary = {}
    for mode, out_dir, src_dir in (("strict", Path(a.out), Path(a.src)), ("proposed", Path(str(a.out) + "-proposed"), Path(str(a.src) + "-proposed"))):
        tree_root = out_dir / "Tengoku" / key
        if not tree_root.is_dir():
            continue
        mods = {to_mod(str(f.relative_to(src_dir))) for f in src_dir.rglob("*.lean")} if src_dir.is_dir() else set()
        imports = {m: [d for d in tb.header_imports((src_dir / Path(*tb.split_mod(m)).with_suffix(".lean")).read_text()) if d in mods] for m in mods}
        gone = {m for m in mods if m in bad}
        changed = True
        while changed:
            changed = False
            for m, ds in imports.items():
                if m not in gone and any(d in gone for d in ds):
                    gone.add(m)
                    changed = True
        for m in gone:
            rel = Path(*tb.split_mod(m)).with_suffix(".lean")
            for root in (src_dir, tree_root):
                (root / rel).unlink(missing_ok=True)
        keep = sorted(mods - gone)
        (out_dir / "Tengoku" / f"{key}.lean").write_text("".join(f"import Tengoku.{key}.{m}\n" for m in keep))
        rows = [json.loads(ln) for ln in (out_dir / "manifest.jsonl").read_text().splitlines() if ln.strip()]
        kept_rows = [r for r in rows if r["module"].removeprefix(f"Tengoku.{key}.") not in gone]
        (out_dir / "manifest.jsonl").write_text("".join(json.dumps(r, ensure_ascii=False) + "\n" for r in kept_rows))
        report = json.loads((out_dir / "report.json").read_text())
        cut = len(rows) - len(kept_rows)
        report["modules_in_bundle"] = len(keep)
        report["theorems"] = len(kept_rows)
        report["verification_dropped"] = {**report.get("verification_dropped", {}), **{m: ("did not build in the verification build" if m in bad else "imports a module that did not build") for m in sorted(gone)}}
        report["left_out"] = {**report.get("left_out", {}), "verification build: module did not build, or imports one": report.get("left_out", {}).get("verification build: module did not build, or imports one", 0) + cut}
        (out_dir / "report.json").write_text(json.dumps(report, indent=1))
        summary[mode] = {"modules": len(keep), "theorems": len(kept_rows), "dropped_modules": len(gone), "dropped_theorems": cut}
    print(json.dumps(summary))
    if not any(s["modules"] for s in summary.values()):
        sys.exit("nothing is left of the bundle after the verification build")


def passed_via(gate2_log: str) -> dict[str, str]:
    p = Path(gate2_log) if gate2_log else None
    if p is None or not p.is_file():
        return {}
    return {m.group(1): m.group(3) for m in re.finditer(r"GATE2B_PASS old=(\S+) new=(\S+) via=(\w+)", p.read_text(errors="replace")) if m.group(1) == m.group(2)}


def check(a: argparse.Namespace) -> None:
    """The verification build of the pruned sources: every module clean, nothing left on sorry."""
    rep = json.loads(Path(a.report).read_text())
    log = Path(a.log).read_text(errors="replace")
    bad = {m: s["state"] for m, s in rep["status"].items() if s["state"] != "clean"}
    sorries = re.findall(r"^warning: (\S+:\d+):\d+: declaration uses .sorry.", log, re.M)
    errors = re.findall(r"^error: .*", log, re.M)
    out = {"modules": rep["modules"], "not_clean": bad, "sorry_warnings": len(sorries), "errors": len(errors)}
    print(json.dumps({k: (v if k != "not_clean" else dict(list(v.items())[:10])) for k, v in out.items()}))
    Path(a.out).write_text(json.dumps(out, indent=1))
    if bad or sorries or errors:
        print("the pruned sources do not build clean:", errors[:5], sorries[:5])
        sys.exit(1)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    k = sub.add_parser("check")
    for f in ("report", "log", "out"):
        k.add_argument(f"--{f}", required=True)
    l = sub.add_parser("lean")
    for f in ("lib", "passed", "roots", "out"):
        l.add_argument(f"--{f}", required=True)
    c = sub.add_parser("compose")
    for f in ("lib", "log", "passed", "meta", "key", "toolchain", "errors", "out", "src"):
        c.add_argument(f"--{f}", required=True)
    c.add_argument("--gate2", default="")
    c.add_argument("--drop-modules", default="", help="comma list of modules to leave out (with their importers): those that did not build on the tree")
    r = sub.add_parser("refine")
    for f in ("report", "log", "key", "out", "src"):
        r.add_argument(f"--{f}", required=True)
    args = ap.parse_args()
    {"lean": lean_file, "compose": compose, "check": check, "refine": refine}[args.cmd](args)
