#!/usr/bin/env python3
"""A build-once that goes on from an earlier run of itself: lane_reuse.py --plan plan.json --jobs jobs.json --artifacts names.json --key KEY (bump-waves.yml reuse_from).

flt-anthropic's lane (run 42678283150, 11 Nov 2026) lost job 62 at its time limit inside the build: its 420 modules have no pack, and 42 of the 55 jobs after it build on
them, so the rest of that run could only build around a hole. A new run on fixed code must not start again from wave 0 (two days of builds): it takes the earlier run's
plan, keeps every job that finished there, and runs the others.

Two questions per job of the earlier run:
  - is its PACK good: its pack step succeeded (the pack is made right after the build, before Gate 2; a job stopped later, in Gate 2, still handed on a whole
    build: flt-anthropic's jobs 43, 53 and 65), the pack is there (wave-KEY-N), and every pack it restored from is good. Job 62 was stopped inside its build:
    no pack, and every pack built on it is bad. A job of the new run restores a good pack from the earlier run (the reused jobs built on exactly that pack);
    any other from its own run.
  - is the JOB reused: it succeeded (a job stopped at its time limit uploads its packs too, so an artifact proves nothing), its pack is good and its shard
    pack (shard-KEY-N, for the bundle) is there.
Every job that is not reused runs, in its wave: one stopped in Gate 2 is judged again, one whose pack is bad is built again on the new packs.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from plan_waves import MAX_WAVES  # noqa: E402

JOB = re.compile(r"^w(\d+) \((\d+)\) / shard$")


def succeeded(jobs: list[dict]) -> set[int]:
    """the shards whose job finished with success (the jobs API: name `wN (S) / shard`, conclusion)"""
    return {int(m.group(2)) for j in jobs if (m := JOB.match(j.get("name", ""))) and j.get("conclusion") == "success"}


def packed(jobs: list[dict]) -> set[int]:
    """the shards whose pack step succeeded (`pack_step`: the conclusion of the step "This job's work, for the jobs after it"), or whose job succeeded"""
    return {int(m.group(2)) for j in jobs if (m := JOB.match(j.get("name", ""))) and (j.get("conclusion") == "success" or j.get("pack_step") == "success")}


def good_packs(plan: dict, packed_ok: set[int], artifacts: set[str], key: str) -> set[int]:
    """the shards whose pack the new run restores from the earlier run: packed, there, and built only on good packs (wave order: a job's sources come first)"""
    good: set[int] = set()
    for s in sorted(plan["shards"], key=lambda x: (x["wave"], x["shard"])):
        n = s["shard"]
        if n in packed_ok and f"wave-{key}-{n}" in artifacts and all(r in good for r in s.get("restore", [])):
            good.add(n)
    return good


def reusable(plan: dict, ok: set[int], good: set[int], artifacts: set[str], key: str) -> set[int]:
    """the jobs the new run does not run: succeeded, a good pack, and their shard pack for the bundle"""
    return {s["shard"] for s in plan["shards"] if s["shard"] in ok and s["shard"] in good and f"shard-{key}-{s['shard']}" in artifacts}


def outputs(plan: dict, keep: set[int], good: set[int], max_waves: int = MAX_WAVES) -> dict[str, str]:
    """w0 ... w31 -> the shards that run in that wave (reused ones left out); `packs` -> the shards whose pack comes from the earlier run, comma list"""
    if plan["waves"] > max_waves:
        raise ValueError(f"the plan has {plan['waves']} waves and the workflow runs {max_waves}")
    by_wave: dict[int, list[int]] = {}
    for s in plan["shards"]:
        if s["shard"] not in keep:
            by_wave.setdefault(s["wave"], []).append(s["shard"])
    out = {f"w{w}": json.dumps(sorted(by_wave.get(w, []))) for w in range(max_waves)}
    out["packs"] = ",".join(str(n) for n in sorted(good))
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--plan", required=True)
    ap.add_argument("--jobs", required=True, help="the earlier run's jobs (gh api .../runs/ID/jobs, the `jobs` objects, one JSON list)")
    ap.add_argument("--artifacts", required=True, help="the earlier run's artifacts that are not expired (a JSON list of names)")
    ap.add_argument("--key", required=True)
    a = ap.parse_args()
    plan = json.loads(Path(a.plan).read_text())
    jobs, artifacts = json.loads(Path(a.jobs).read_text()), set(json.loads(Path(a.artifacts).read_text()))
    good = good_packs(plan, packed(jobs), artifacts, a.key)
    keep = reusable(plan, succeeded(jobs), good, artifacts, a.key)
    out = outputs(plan, keep, good)
    run = [n for s in plan["shards"] if (n := s["shard"]) not in keep]
    print(f"reused from the earlier run: {len(keep)} of {len(plan['shards'])} jobs; run here: {len(run)} ({run[:20]})", file=sys.stderr)
    for k, v in out.items():
        print(f"{k}={v}")


if __name__ == "__main__":
    main()
