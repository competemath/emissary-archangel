#!/usr/bin/env python3
"""make_raze.py — the files of a raze PR (tengoku docs/pr-classes.md, section 8), from a plan of deficient_tree.py.

  make_raze.py --tree TENGOKU_CHECKOUT --lib KEY --plan plan.json --id ID

Edits the checkout's working tree and nothing else (the branch, the commit and the PR are the caller's):
  - deletes the `Tengoku/<Ns>/….lean` file of every module of the plan's `raze`;
  - removes exactly their `import` lines from the umbrella `Tengoku/<Ns>.lean`, and exactly the lines of their records from `data/intake/<key>/manifest.jsonl`;
  - writes the marker `data/raze/<ID>.json` (library, modules, reason).
tengoku's `scripts/ci/raze_check.py` judges the result the same way the gate will: the caller runs it on the commit before pushing.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


def module_path(mod: str) -> str:
    """The inverse of the module name: `Tengoku.Lib.«A-B»` is `Tengoku/Lib/A-B.lean` (a dot inside guillemets is part of the component)."""
    return "/".join(m.group(0).strip("«»") for m in re.finditer(r"«[^»]*»|[^.]+", mod)) + ".lean"


def describe(plan: dict) -> str:
    deficient = plan["deficient"]
    fixable = [m for m in plan["raze"] if m in deficient]
    return (
        f"{len(fixable)} merged module(s) lack declarations that the corrected compose keeps (the first pruner cut names that proofs of other modules still use), "
        f"{len(plan['raze']) - len(fixable)} module(s) import them. A from-tree recut brings all {len(plan['raze'])} back from the corrected bundle."
    )


def make(tree: Path, lib: str, plan: dict, rid: str, reason: str = "") -> dict:
    ns = "".join(p[:1].upper() + p[1:] for p in lib.replace("_", "-").split("-") if p)
    razed = set(plan["raze"])
    if not razed:
        raise SystemExit("the plan razes nothing")
    for mod in sorted(razed):
        f = tree / module_path(mod)
        if not f.is_file():
            raise SystemExit(f"{f}: not a file of the tree: the plan was made against another tree")
        f.unlink()
    umbrella = tree / "Tengoku" / f"{ns}.lean"
    kept = [ln for ln in umbrella.read_text(encoding="utf-8").split("\n") if not (ln.startswith("import ") and ln[len("import ") :].strip() in razed)]
    umbrella.write_text("\n".join(kept), encoding="utf-8")
    manifest = tree / "data" / "intake" / lib / "manifest.jsonl"
    lines = manifest.read_text(encoding="utf-8").split("\n")

    def module_of(ln: str) -> str | None:
        try:
            return json.loads(ln).get("module")
        except Exception:
            return None

    out = [ln for ln in lines if ln.strip() == "" or module_of(ln) not in razed]
    manifest.write_text("\n".join(out), encoding="utf-8")
    marker = tree / "data" / "raze" / f"{rid}.json"
    marker.parent.mkdir(parents=True, exist_ok=True)
    marker.write_text(json.dumps({"library": lib, "modules": sorted(razed), "reason": reason or describe(plan)}, indent=1) + "\n", encoding="utf-8")
    return {"modules": len(razed), "manifest_lines_removed": len(lines) - len(out)}


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--tree", required=True)
    ap.add_argument("--lib", required=True)
    ap.add_argument("--plan", required=True)
    ap.add_argument("--id", required=True, help="the marker's file name: data/raze/<id>.json")
    ap.add_argument("--reason", default="")
    a = ap.parse_args(argv)
    r = make(Path(a.tree), a.lib, json.loads(Path(a.plan).read_text()), a.id, a.reason)
    print(f"razed {r['modules']} module(s) of {a.lib}; {r['manifest_lines_removed']} manifest line(s) removed; marker data/raze/{a.id}.json")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
