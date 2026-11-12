#!/usr/bin/env python3
"""REGATE: which shards of a build-once run judge again (bump-waves.yml regate-plan): regate_plan.py --repo R --key K --run ID [--fill A,B] --library-from DIR --work DIR.

A lane job builds, then judges its targets in what is left of its 345 minutes; a long build leaves Gate 2 too little time, and the targets it reaches no verdict on are
listed in the shard's gate2-killed.json. flt-anthropic's job 43 (run 43146942669, 12 Nov 2026) built for 3 h 02 min and left 114 of its target modules unjudged. The bundle
cuts such a module with everything that imports it, so those theorems could never ship. Each shard whose own targets include a killed module is judged again on its own
build (bump-shard.yml regate); every other shard is left as it is.

The shard packs are read as the bundle reads them (fill_from.py): this run first, then the runs it resumes, newest first, a shard taken from the newest run that has it,
each run checked to be the lane's own run of the same library. Prints `shards=[...]` (the shards to judge again) and `from=RUN,...` (where their packs are) for $GITHUB_OUTPUT.
"""

from __future__ import annotations

import argparse
import contextlib
import json
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import fill_from as ff  # noqa: E402
import lane_reuse  # noqa: E402

MAX_REGATE = 64  # shards judged again in one run: more means the plan's budget is wrong, not that Gate 2 was unlucky


def to_regate(plan: dict, shards: Path, key: str) -> tuple[list[int], dict[int, int]]:
    """(the shards to judge again, {shard: its targets without a verdict}): a shard whose pack lists one of its own targets as killed"""
    out: list[int] = []
    counts: dict[int, int] = {}
    for s in plan["shards"]:
        n, targets = s["shard"], set(s.get("targets", []))
        if not targets:
            continue
        art = shards / f"shard-{key}-{n}"
        kf = next((c for c in (art / "emissary" / "gate2-killed.json", art / "shard-pack" / "gate2-killed.json") if c.is_file()), None)
        if kf is None:
            continue  # no pack (the job died, or kept none): nothing to judge again, and the bundle's `complete` says so
        killed = json.loads(kf.read_text())
        if not isinstance(killed, list) or not all(isinstance(x, str) for x in killed):
            sys.exit(f"{kf}: gate2-killed.json is not a list of module names")
        mine = targets & set(killed)
        if mine:
            out.append(n)
            counts[n] = len(mine)
    return sorted(out), counts


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", required=True)
    ap.add_argument("--key", required=True)
    ap.add_argument("--run", required=True, help="this run")
    ap.add_argument("--fill", default="", help="the runs this run resumes, newest first (lane_reuse.py fill)")
    ap.add_argument("--library-from", required=True, help="this run's checkout of this repository: the runs must have built its library")
    ap.add_argument("--work", required=True)
    a = ap.parse_args()
    runs = ff.runs_of(",".join([a.run] + ([a.fill] if a.fill else [])))
    work = Path(a.work)
    plan_dir = work / "plan"
    ff.gh(["run", "download", a.run, "-R", a.repo, "-n", f"plan-{a.key}", "-D", str(plan_dir)])
    plan = json.loads((plan_dir / "plan.json").read_text())
    base = Path(a.library_from)
    here = lane_reuse.library_identity(json.loads((base / "data" / "exports" / a.key / "setup.ci.json").read_text()), json.loads((base / "sources.json").read_text()), a.key)
    with contextlib.redirect_stdout(sys.stderr):  # stdout is $GITHUB_OUTPUT: only the two lines below may reach it (the fill prints its progress)
        filled = ff.fill_from(a.repo, a.key, runs, work / "shards", work / "fill", None, library=here)
    shards, counts = to_regate(plan, work / "shards", a.key)
    if len(shards) > MAX_REGATE:
        sys.exit(f"regate: {len(shards)} shards left targets without a verdict, more than {MAX_REGATE}: the plan's budget is wrong, not Gate 2's luck")
    print(f"regate: {len(shards)} shard(s) to judge again ({sum(counts.values())} targets): {counts}; packs read from {filled}", file=sys.stderr)
    print("shards=" + json.dumps(shards))
    print("from=" + ",".join(runs))


if __name__ == "__main__":
    main()
