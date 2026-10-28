#!/usr/bin/env python3
"""vendor_deps.py — bring the code a library imports from the OTHER Lake packages it requires into the library, so that it is built, checked and shipped with it.

  vendor_deps.py --lib LIB --roots A,B [--out vendored.json] [--print-roots]

Why. A library can `require` another Lake package (stafford38-formal requires algebraic-analysis; 84 of the 148 registered libraries require something besides Mathlib, mostly documentation tools, but
albert-frame-triple-invariants, derived-alg-geo-lean, epsilon-sml, quadratic-number-fields and stafford38-formal import real code). The factory builds a library with its own driver
(tolerant_build.py) and `lake update` only DOWNLOADS the packages: nothing builds them, so every `import AlgebraicAnalysis.X` was a "bad import" (2026-10-28, stafford38-formal: 20 of
the 34 modules that failed of their own accord, and 365 of 436 modules taken out with them). The tree has no cross-library imports either (tree_verify.py), so the dependency cannot be
"imported from the tree" in the end: what the library uses of it has to ship with the library, as lean-pool ships its vendored AddCombi.

What it does. From the library's own modules it follows the imports; an import that is a module of a required package (and not Lean, Mathlib or one of the packages the tree is seeded
from) is copied into LIB at its module path, and so are the imports of that module, and so on. Only the modules reached are copied. The roots of the copies (`AlgebraicAnalysis`) are
printed, to be added to the roots of the build.

What it will not do (each is a recorded reason, never a guess):
  * copy a package whose licence it cannot read as one of the permissive ones (Apache-2.0, MIT, BSD-2/3, CC0, Unlicense): an unlicensed or copyleft package is `refused`, and what imports it stays unresolved;
  * overwrite a file the library already has with a different one (`conflict`), or choose between two packages that both have a module of the same name (`ambiguous`);
  * copy anything that is not reached from the library.
The copies are the package's files at the revision the library's lake-manifest.json pins, byte for byte; the report says package, url, revision, licence and module for each, so that the intake
pull request can say what it carries and under which licence.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import tolerant_build as tb  # noqa: E402

# Modules the tree is seeded with or that ship with Lean: never vendored (their top-level name).
SEEDED = {"Init", "Std", "Lean", "Lake", "Mathlib", "Batteries", "Aesop", "Qq", "ProofWidgets", "Plausible", "LeanSearchClient", "ImportGraph", "Cli"}

PERMISSIVE = ("Apache-2.0", "MIT", "BSD-2-Clause", "BSD-3-Clause", "CC0-1.0", "Unlicense")
_LICENCE_FILES = ("LICENSE", "LICENSE.md", "LICENSE.txt", "LICENCE", "COPYING", "COPYING.md", "UNLICENSE")
# Phrases that identify a licence text. Order matters: the first match wins and the copyleft ones come first, so that a file that mentions two is read as the stricter.
_SIGNATURES = (
    ("GPL", re.compile(r"GNU (?:AFFERO |LESSER )?GENERAL PUBLIC LICENSE", re.I)),
    ("MPL", re.compile(r"Mozilla Public License", re.I)),
    ("Apache-2.0", re.compile(r"Apache License[\s,]+Version 2\.0", re.I)),
    ("MIT", re.compile(r"Permission is hereby granted, free of charge", re.I)),
    ("BSD-3-Clause", re.compile(r"Redistributions in binary form must reproduce.*?Neither the name", re.I | re.S)),
    ("BSD-2-Clause", re.compile(r"Redistributions in binary form must reproduce", re.I)),
    ("CC0-1.0", re.compile(r"CC0 1\.0 Universal|Creative Commons Zero", re.I)),
    ("Unlicense", re.compile(r"This is free and unencumbered software released into the public domain", re.I)),
)


def read_licence(pkg_dir: Path) -> str | None:
    """The SPDX name of the package's licence, or None when there is no licence file or it is not one of the known texts."""
    for name in _LICENCE_FILES:
        f = pkg_dir / name
        if f.is_file():
            text = f.read_text(errors="replace")
            for spdx, rx in _SIGNATURES:
                if rx.search(text):
                    return spdx
            return None
    return None


def package_src_dirs(pkg_dir: Path) -> list[Path]:
    """Where a package keeps its modules: every `srcDir` its lakefile names (a package with several `lean_lib` targets can have several), else its root."""
    dirs: list[Path] = []
    for name in ("lakefile.toml", "lakefile.lean"):
        f = pkg_dir / name
        if f.is_file():
            for m in re.finditer(r'srcDir\s*(?:=|:=)\s*"([^"]+)"', f.read_text(errors="replace")):
                d = pkg_dir / m.group(1)
                if d not in dirs:
                    dirs.append(d)
    return dirs or [pkg_dir]


def index_package(pkg_dir: Path) -> dict[str, Path]:
    """module name -> file, for the package's own sources (not its dependencies' packages, tests, or build output)."""
    out: dict[str, Path] = {}
    for src in package_src_dirs(pkg_dir):
        if not src.is_dir():
            continue
        for p in sorted(src.rglob("*.lean")):
            rel = p.relative_to(src)
            parts = rel.with_suffix("").parts
            if any(x in (".lake", "lake-packages", ".git") for x in parts) or (len(parts) == 1 and parts[0].lower().startswith("lakefile")):
                continue
            out.setdefault(".".join(tb.esc(x) for x in parts), p)
    return out


def own_modules(lib: Path, roots: list[str]) -> dict[str, Path]:
    return tb.module_files(lib, roots)


def vendor(lib: Path, roots: list[str], *, permissive: tuple[str, ...] = PERMISSIVE) -> dict:
    manifest_path = lib / "lake-manifest.json"
    report: dict = {"vendored": [], "packages": {}, "unresolved": [], "conflicts": [], "ambiguous": [], "refused": [], "roots": [], "copied": 0}
    if not manifest_path.is_file():
        return report
    manifest = json.loads(manifest_path.read_text())
    packages_dir = lib / manifest.get("packagesDir", ".lake/packages")
    pkgs: dict[str, dict] = {}
    for p in manifest.get("packages", []):
        name = p.get("name") or str(p.get("url", "")).rsplit("/", 1)[-1].removesuffix(".git")
        d = packages_dir / name
        if d.is_dir():
            pkgs[name] = {"dir": d, "url": p.get("url", ""), "rev": p.get("rev", ""), "index": index_package(d)}

    # What an earlier run copied is the factory's to manage, not the library's: the roots may have grown to include the copies, the repair rounds may have edited them, and the
    # dependency or the library's imports may have changed since. The marker (LIB/.vendored.json) says which files are ours.
    marker = lib / ".vendored.json"
    earlier: dict[str, dict] = {}
    if marker.is_file():
        earlier = {v["module"]: v for v in json.loads(marker.read_text()).get("vendored", [])}
    own = {m: f for m, f in own_modules(lib, roots).items() if m not in earlier}
    seen_own = set(own)
    queue = [m for m in own.values()]
    vendored: dict[str, tuple[str, Path]] = {}  # module -> (package, source file)
    unresolved: set[str] = set()
    refused: dict[str, str] = {}
    licence_of: dict[str, str | None] = {}

    def top(mod: str) -> str:
        return tb.split_mod(mod)[0]

    while queue:
        f = queue.pop()
        for dep in tb.header_imports(f.read_text(errors="replace")):
            if top(dep) in SEEDED or dep in seen_own or dep in vendored:
                continue
            owners = [n for n, p in pkgs.items() if dep in p["index"]]
            if not owners:
                unresolved.add(dep)
                continue
            if len(owners) > 1:
                report["ambiguous"].append({"module": dep, "packages": sorted(owners)})
                continue
            name = owners[0]
            if name not in licence_of:
                licence_of[name] = read_licence(pkgs[name]["dir"])
            if licence_of[name] not in permissive:
                refused[name] = f"licence {licence_of[name] or 'not found or not recognised'}"
                unresolved.add(dep)
                continue
            src = pkgs[name]["index"][dep]
            vendored[dep] = (name, src)
            queue.append(src)

    for mod, (name, src) in sorted(vendored.items()):
        dst = lib / Path(*tb.split_mod(mod)).with_suffix(".lean")
        data = src.read_bytes()
        ours = mod in earlier and earlier[mod].get("package") == name
        same_pin = ours and earlier[mod].get("rev") == pkgs[name]["rev"]
        if dst.exists() and dst.read_bytes() != data:
            if not ours:
                report["conflicts"].append({"module": mod, "package": name, "path": str(dst.relative_to(lib))})
                continue
            if same_pin:  # ours, at the same revision, edited since (a repair round): left as it is
                report["vendored"].append({"module": mod, "package": name, "rev": pkgs[name]["rev"], "path": str(dst.relative_to(lib))})
                continue
            # ours, and the package moved on: the new revision replaces it
        if not dst.exists() or dst.read_bytes() != data:
            dst.parent.mkdir(parents=True, exist_ok=True)
            dst.write_bytes(data)
            report["copied"] += 1
        report["vendored"].append({"module": mod, "package": name, "rev": pkgs[name]["rev"], "path": str(dst.relative_to(lib))})
    # a file we copied earlier that nothing reaches any more (the library or the dependency changed) is removed: it must not stay buildable
    reached = {m for m in vendored}
    for mod, v in earlier.items():
        if mod not in reached:
            stale = lib / v["path"]
            if stale.is_file():
                stale.unlink()
                report.setdefault("removed", []).append(mod)
    done = {v["module"] for v in report["vendored"]}
    # a module that was not copied (a conflict) leaves what imports it unresolved; say so
    report["unresolved"] = sorted(unresolved | {m for m in vendored if m not in done})
    for name in sorted({v["package"] for v in report["vendored"]} | set(refused)):
        report["packages"][name] = {
            "url": pkgs[name]["url"],
            "rev": pkgs[name]["rev"],
            "licence": licence_of.get(name),
            "modules": sum(1 for v in report["vendored"] if v["package"] == name),
            **({"refused": refused[name]} if name in refused else {}),
        }
    report["refused"] = [{"package": n, "reason": r} for n, r in sorted(refused.items())]
    report["roots"] = sorted({top(v["module"]) for v in report["vendored"]} - set(roots) - {top(m) for m in own})
    if report["vendored"] or marker.is_file():
        marker.write_text(json.dumps({"vendored": sorted(report["vendored"], key=lambda v: v["module"])}, indent=1))
    return report


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--lib", required=True)
    ap.add_argument("--roots", required=True, help="comma list")
    ap.add_argument("--out")
    ap.add_argument("--print-roots", action="store_true", help="print the roots of the library with the roots of the copies, as a comma list, and nothing else")
    a = ap.parse_args()
    roots = [r for r in a.roots.split(",") if r]
    rep = vendor(Path(a.lib), roots)
    if a.out:
        Path(a.out).write_text(json.dumps(rep, indent=1))
    if a.print_roots:
        print(",".join(roots + rep["roots"]))
    print(
        f"vendored {len(rep['vendored'])} modules of {len(rep['packages'])} packages ({rep['copied']} files written); unresolved {len(rep['unresolved'])}, "
        f"refused {len(rep['refused'])}, conflicts {len(rep['conflicts'])}, ambiguous {len(rep['ambiguous'])}",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
