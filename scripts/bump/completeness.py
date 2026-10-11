#!/usr/bin/env python3
"""completeness.py — where every theorem of a library is, and why: nothing is missing without a reason.

  completeness.py --artifact BUMP_ARTIFACT_DIR --tree TENGOKU_CHECKOUT --lib KEY [--mode proposed] [--json out.json]

BUMP_ARTIFACT_DIR is a downloaded `bump-<key>` artifact of a bump run (bundle-<mode>/{manifest.jsonl,report.json}, bundle-<mode>.ledger.json, logs/gate2-results.json); the tree is a checkout of
tengoku with data/intake/<key>/manifest.jsonl. The chain, each hop with its count:

  checked            what Gate 2 looked at (gate2-results.json)
  verified           what passed: the theorems the factory stands behind
  shipped            verified theorems that are in the bundle (manifest.jsonl)
  left out           verified theorems that are not, by reason (ledger.json: module -> reason, names)
  in the tree        the tree's manifest
  pending            shipped, not in the tree yet (parts that did not merge yet)
  tree only          in the tree, not in this bundle (merged by an older compose; this one leaves them out)

Two things are checked and fail the run: (1) the identity verified = shipped + left out (compose enforces it too: it refuses to write a bundle that breaks it) and (2) every verified
theorem is shipped or in the ledger with a reason. `pending` and `tree only` are reported, not failed: they are the work in flight and what a raze/recut will settle.
"""

from __future__ import annotations

import argparse
import collections
import json
import sys
from pathlib import Path


def names_of(manifest: Path) -> set[str]:
    out: set[str] = set()
    if manifest.exists():
        for ln in manifest.read_text(encoding="utf-8").splitlines():
            if ln.strip():
                out.add(json.loads(ln)["name"])
    return out


def coarse(reason: str) -> str:
    """The reason without its names (`declares a record the tree already has: X, Y` -> `declares a record the tree already has`)."""
    return reason.split(":")[0][:90]


def account(artifact: Path, tree: Path, lib: str, mode: str) -> dict:
    bdir = artifact / ("bundle" if mode == "strict" else f"bundle-{mode}")
    shipped = names_of(bdir / "manifest.jsonl")
    report = json.loads((bdir / "report.json").read_text())
    ledger_path = artifact / (bdir.name + ".ledger.json")
    if not ledger_path.exists():
        ledger_path = bdir / "ledger.json"  # artifacts of before 2026-10-11 18:00 UTC
    ledger = json.loads(ledger_path.read_text()) if ledger_path.exists() else None
    # a ledger that says nothing was left out has `"left_out": {}`: present, and not the same as a missing key (an empty dict is falsy: `or` used to read the report instead)
    left_out = ledger["left_out"] if ledger is not None and "left_out" in ledger else report.get("left_out", {})
    verified = report["passed_total"]
    gate2 = artifact / "logs" / "gate2-results.json"
    g2 = json.loads(gate2.read_text()) if gate2.exists() else {}
    in_tree = names_of(tree / "data" / "intake" / lib / "manifest.jsonl")
    by_reason: dict[str, int] = collections.Counter()
    for reason, n in left_out.items():
        by_reason[coarse(reason)] += n
    problems = []
    if verified != len(shipped) + sum(left_out.values()):
        problems.append(f"verified {verified} != shipped {len(shipped)} + left out {sum(left_out.values())}")
    if ledger is not None:
        # the ledger is a second record of the same numbers: it must agree with the report and the manifest, not just with itself
        if ledger.get("verified") != verified:
            problems.append(f"the ledger says {ledger.get('verified')} verified theorems, the report {verified}")
        if ledger.get("shipped") != len(shipped):
            problems.append(f"the ledger says {ledger.get('shipped')} shipped theorems, the manifest has {len(shipped)}")
        ledger_left = sum(ledger.get("left_out", {}).values())
        if "left_out" in report and ledger_left != sum(report["left_out"].values()):
            problems.append(f"the ledger left out {ledger_left} theorems, the report {sum(report['left_out'].values())}")
        listed = sum(m["names"] for m in ledger["modules"].values())
        extra = sum(n for r, n in left_out.items() if r == "no source range")
        if listed + extra != sum(left_out.values()):
            problems.append(f"the ledger lists {listed} theorems (+{extra} without a source range) but {sum(left_out.values())} were left out")
    return {
        "library": lib,
        "mode": mode,
        "checked": g2.get("checked"),
        "gate2": {k: g2.get(k) for k in ("pass", "pass_equal", "pass_entails", "fail_reasons")},
        "verified": verified,
        "shipped": len(shipped),
        "left_out": dict(by_reason.most_common()),
        "in_tree": len(in_tree),
        "pending": len(shipped - in_tree),
        "tree_only": len(in_tree - shipped),
        "problems": problems,
        "ledger_file": ledger is not None,
    }


def render(r: dict) -> str:
    out = [f"{r['library']} ({r['mode']}): checked {r['checked']}, verified {r['verified']}"]
    g = r["gate2"].get("fail_reasons") or {}
    if g:
        out.append("  gate 2 did not pass: " + ", ".join(f"{k} {v}" for k, v in sorted(g.items(), key=lambda kv: -kv[1])))
    out.append(f"  shipped in the bundle {r['shipped']}; left out {sum(r['left_out'].values())}:")
    out += [f"    {n:>7}  {why}" for why, n in r["left_out"].items()]
    out.append(f"  in the tree {r['in_tree']}; pending (shipped, not merged) {r['pending']}; tree only (merged earlier, not in this bundle) {r['tree_only']}")
    out.append("  UNACCOUNTED: none" if not r["problems"] else "  UNACCOUNTED: " + "; ".join(r["problems"]))
    if not r["ledger_file"]:
        out.append("  (no ledger.json in this artifact: left-out reasons come from the report, per module detail needs a compose of today)")
    return "\n".join(out)


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--artifact", required=True)
    ap.add_argument("--tree", required=True)
    ap.add_argument("--lib", required=True)
    ap.add_argument("--mode", default="proposed", choices=["strict", "proposed", "wide"])
    ap.add_argument("--json", default="")
    a = ap.parse_args(argv)
    r = account(Path(a.artifact), Path(a.tree), a.lib, a.mode)
    print(render(r))
    if a.json:
        Path(a.json).write_text(json.dumps(r, indent=1) + "\n")
    return 1 if r["problems"] else 0


if __name__ == "__main__":
    sys.exit(main())
