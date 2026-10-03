#!/usr/bin/env python3
"""bundle_cut.py — leave modules out of a finished bundle (with every module of the bundle that imports one), without a rebuild.

The merge queue's build of the tree names modules that do not compile there (a name Mathlib has now, a name another library of the tree
declares): `drop` lists them, as the library's own module names (no `Tengoku.<Library>.` prefix). A single-job bump has its bundle already
composed, so this works on the bundle's files: the modules (and their importers) are deleted, the library's root file, the manifest and the
report follow. Sharded runs cut at compose (`bundle.py compose --drop-modules`); this is the same cut for the others.

  bundle_cut.py --bundle DIR --key K --drop A.B,C   (DIR and DIR-proposed are both cut)
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import scope_rewrite as sr  # noqa: E402
import tolerant_build as tb  # noqa: E402


def pascal(library: str) -> str:
    import re

    return "".join(p[:1].upper() + p[1:] for p in re.split(r"[-_ ]+", library) if p)


def cut_dir(out_dir: Path, key: str, drop: set[str]) -> dict | None:
    ns = pascal(key)
    tree_root = out_dir / "Tengoku" / ns
    if not tree_root.is_dir():
        return None
    pre = f"Tengoku.{ns}."
    files = {f.relative_to(tree_root).with_suffix("").parts: f for f in tree_root.rglob("*.lean") if f.name != "Deps.lean" and not f.is_symlink()}
    names = {".".join(tb.esc(x) for x in parts): f for parts, f in files.items()}
    imports = {m: [d.removeprefix(pre) for d in tb.header_imports(f.read_text()) if d.startswith(pre) and d.removeprefix(pre) in names] for m, f in names.items()}
    gone = {m for m in drop if m in names}
    changed = True
    while changed:
        changed = False
        for m, ds in imports.items():
            if m not in gone and any(d in gone for d in ds):
                gone.add(m)
                changed = True
    for m in gone:
        names[m].unlink()
    keep = sorted(set(names) - gone)
    (out_dir / "Tengoku" / f"{ns}.lean").write_text("".join(f"import {pre}{m}\n" for m in keep))
    rows = [json.loads(ln) for ln in (out_dir / "manifest.jsonl").read_text().splitlines() if ln.strip()]
    kept = [r for r in rows if r["module"].removeprefix(pre) not in gone]
    (out_dir / "manifest.jsonl").write_text("".join(json.dumps(r, ensure_ascii=False) + "\n" for r in kept))
    rep = json.loads((out_dir / "report.json").read_text())
    cutn = len(rows) - len(kept)
    rep["modules_in_bundle"] = len(keep)
    rep["theorems"] = len(kept)
    rep["queue_dropped"] = {m: ("did not build on the tree" if m in drop else "imports a module that did not build on the tree") for m in sorted(gone)}
    rep["left_out"] = {**rep.get("left_out", {}), "the tree's build: module did not build, or imports one": cutn}
    (out_dir / "report.json").write_text(json.dumps(rep, indent=1))
    return {"modules": len(keep), "theorems": len(kept), "dropped_modules": len(gone), "dropped_theorems": cutn, "not_in_bundle": sorted(drop - set(names))}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--bundle", required=True)
    ap.add_argument("--key", required=True)
    ap.add_argument("--drop", required=True)
    a = ap.parse_args()
    drop = {m.strip() for m in a.drop.split(",") if m.strip()}
    bad = [m for m in drop if sr.parts_of(m) is None]
    if bad:
        sys.exit(f"not module names: {bad}")
    out = {}
    for d in (Path(a.bundle), Path(a.bundle + "-proposed")):
        r = cut_dir(d, a.key, drop)
        if r:
            out[d.name] = r
    if not any(r["modules"] for r in out.values()):
        sys.exit("nothing is left of the bundle")
    print(json.dumps(out))


if __name__ == "__main__":
    main()
