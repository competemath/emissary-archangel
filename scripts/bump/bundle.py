#!/usr/bin/env python3
"""bundle.py — the intake bundle of a bumped library: only what passed, as ready-to-build Lean modules for the tree.

Per-record staging puts each theorem's whole context into a record (33 KB each on average: 600 MB per 17.6k records, ~4 GB for the
registered corpus), which cannot live in a repository. A bundle holds each module ONCE:

  Tengoku/<Library>/<source path>.lean   the library's modules cut down to what the passed theorems are made of: every declaration
                                         in the closure of the passed set (types, values and proofs, from the compiled environment),
                                         all glue (namespaces, opens, variables, notations, macros), nothing else. A declaration that
                                         failed, uses sorry, was not checked, or nothing passed depends on is gone, as is the text of
                                         any block Lean reported an error in. Imports are mapped to the tree's module names.
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
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import portfolio  # noqa: E402
import records  # noqa: E402
import tolerant_build as tb  # noqa: E402

# the tree's names for the packages it was seeded from (tengoku scripts/seed.py PACKAGES)
TREE = {
    "Mathlib": "Tengoku",
    "Batteries": "Tengoku.Std",
    "Aesop": "Tengoku.Tactic.Aesop",
    "Qq": "Tengoku.Meta.Qq",
    "ProofWidgets": "Tengoku.Widgets",
    "Plausible": "Tengoku.Testing.Random",
    "LeanSearchClient": "Tengoku.Search.LeanSearchClient",
    "ImportGraph": "Tengoku.Meta.ImportGraph",
    "Cli": "Tengoku.Meta.Cli",
}
CORE = ("Init", "Std", "Lean", "Lake")
IMPORT_RE = re.compile(r"^(\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?)(" + tb.MODNAME + r")(.*)$")

LEAN = r'''
open Lean Elab Command Meta

def bkParse (s : String) : Name := (s.splitOn ".").foldl (fun n part => Name.mkStr n part) Name.anonymous

def bkModOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?

/-- Every library constant (module, name) in the closure of the types, values and proofs of ALL the names: what must stay. -/
elab "#bundle_keep " names:str " in " libs:str : command => do
  let libMods : NameSet := (libs.getString.splitOn ",").foldl (fun s x => if x == "" then s else s.insert (bkParse x)) {}
  let j ← liftTermElabM do
    let env ← getEnv
    let isOwn (c : Name) : Bool := match bkModOf env c with | some m => libMods.contains m | none => false
    let mut seen : NameSet := {}
    let mut stack : List Name := ((names.getString.splitOn ",").filter (· != "")).map bkParse
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
    """The line with its module renamed for the tree, and the module's kind: 'own' / 'tree' / 'core' / 'external'."""
    m = IMPORT_RE.match(line)
    if not m:
        return line, None
    mod = m.group(2)
    if mod in own:
        return f"{m.group(1)}Tengoku.{pascal(key)}.{mod}{m.group(3)}", "own"
    head = mod.split(".")[0]
    if head in TREE:
        return f"{m.group(1)}{TREE[head]}{mod[len(head):]}{m.group(3)}", "tree"
    if head in CORE:
        return line, "core"
    return line, "external"


def compose(a: argparse.Namespace) -> None:
    lib, out, src = Path(a.lib), Path(a.out), Path(a.src)
    meta = json.loads(Path(a.meta).read_text())
    passed = json.loads(Path(a.passed).read_text())
    log = Path(a.log).read_text(errors="replace")
    kept = set()
    for m in re.finditer(r"BUNDLE_KEEP (\[.*?\]) BUNDLE_END", log, re.S):
        kept |= {(mod, c) for mod, c in json.loads(re.sub(r"\s*\n\s*", "", m.group(1)))}
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
    imports = {mod: [d for d in tb.header_imports("\n".join(m.lines)) if d in own] for mod, m in modules.items()}
    external = {}
    for mod, m in modules.items():
        bad = []
        for ln in m.lines[:200]:
            _, kind = map_import_line(ln, a.key, own)
            if kind == "external":
                bad.append(IMPORT_RE.match(ln).group(2))
        if bad:
            external[mod] = bad
    # a module that imports a package the tree does not have cannot be built there, nor can what imports it
    dropped: dict[str, str] = {m: "imports " + ", ".join(b) for m, b in external.items()}
    changed = True
    while changed:
        changed = False
        for mod, ds in imports.items():
            if mod not in dropped and any(d in dropped for d in ds):
                dropped[mod] = "imports a module that cannot go to the tree"
                changed = True
    needed: set[str] = set()

    def need(mod: str) -> None:
        if mod in needed or mod not in modules or mod in dropped:
            return
        needed.add(mod)
        for d in imports[mod]:
            need(d)

    sys.setrecursionlimit(100000)
    for mod in keep_blocks:
        need(mod)
    # a module the tree cannot hold takes its theorems with it
    manifest, left_out = [], defaultdict(int)
    repo = meta["repo"].rstrip("/").removesuffix(".git")
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
            he = portfolio.header_end(text, 0)
            stmt = (text[:he] if he > 0 else text.split(":=")[0]).strip()
            rel = str(modules[mod].path.relative_to(lib))
            manifest.append({"name": n, "statement": stmt, "module": f"Tengoku.{pascal(a.key)}.{mod}", "source_path": rel, "library": a.key,
                             "source_url": f"{repo}/blob/{meta['commit']}/{rel}", "toolchain": a.toolchain, "via": passed_via(a.gate2).get(n, "")})
    tree_root = out / "Tengoku" / pascal(a.key)
    for d in (tree_root, src):
        d.mkdir(parents=True, exist_ok=True)
    for mod in sorted(needed):
        m = modules[mod]
        pruned = m.text(keep_blocks.get(mod, set()), strip_imports=False)
        rel = m.path.relative_to(lib)
        (src / rel).parent.mkdir(parents=True, exist_ok=True)
        (src / rel).write_text(pruned + "\n")
        mapped = [map_import_line(ln, a.key, own)[0] for ln in pruned.split("\n")]
        (tree_root / rel).parent.mkdir(parents=True, exist_ok=True)
        (tree_root / rel).write_text("\n".join(mapped) + "\n")
    (out / "Tengoku" / f"{pascal(a.key)}.lean").write_text("".join(f"import Tengoku.{pascal(a.key)}.{m}\n" for m in sorted(needed)))
    (out / "manifest.jsonl").write_text("".join(json.dumps(r, ensure_ascii=False) + "\n" for r in manifest))
    report = {"library": a.key, "modules_in_bundle": len(needed), "modules_dropped": len(dropped), "dropped": dict(list(dropped.items())[:50]),
              "theorems": len(manifest), "passed_total": sum(len(v) for v in passed.values()), "left_out": dict(left_out),
              "kept_constants": len(kept)}
    (out / "report.json").write_text(json.dumps(report, indent=1))
    print(json.dumps({k: v for k, v in report.items() if k != "dropped"}))


def passed_via(gate2_log: str) -> dict[str, str]:
    p = Path(gate2_log)
    if not p.exists():
        return {}
    return {m.group(1): m.group(3) for m in re.finditer(r"GATE2B_PASS old=(\S+) new=(\S+) via=(\w+)", p.read_text(errors="replace")) if m.group(1) == m.group(2)}


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    l = sub.add_parser("lean")
    for f in ("lib", "passed", "roots", "out"):
        l.add_argument(f"--{f}", required=True)
    c = sub.add_parser("compose")
    for f in ("lib", "log", "passed", "meta", "key", "toolchain", "errors", "out", "src"):
        c.add_argument(f"--{f}", required=True)
    c.add_argument("--gate2", default="")
    args = ap.parse_args()
    lean_file(args) if args.cmd == "lean" else compose(args)
