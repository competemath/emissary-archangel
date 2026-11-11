#!/usr/bin/env python3
"""RESUME: the shards a recut did not build come from earlier runs (bump-sharded.yml fill_from): fill_from.py --repo R --key K --runs A[,B,...] --shards DIR --work DIR [--plan-new DIR].

`--runs` is the run the resumed lane resumed, then the run that one resumed, and so on (bump-waves.yml passes lane_reuse.py's `fill`), newest first. flt-anthropic, 11 Nov
2026: the resume 43075875630 of 42678283150 kept 63 jobs whose shard packs are in 42678283150, ran 48 of its own, and lost job 43 to a GitHub outage; the bundle of its
resume must read all three runs. A shard already in --shards (built by the run being cut, or by a newer run of the chain) is never replaced by an older copy.

With --plan-new (compose): every run of the chain planned the same shards and built them with the same settings, or the step refuses (--unrecorded vouches for a run
from before plan/inputs.json, as fill_unrecorded did for one run).
"""

from __future__ import annotations

import argparse
import filecmp
import re
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import shard_pack  # noqa: E402

RUN = re.compile(r"^[1-9][0-9]{0,14}$")
MAX_RUNS = 8  # lane_reuse.MAX_CHAIN


def runs_of(text: str) -> list[str]:
    runs = [r for r in text.split(",") if r]
    if not runs or len(runs) > MAX_RUNS or len(set(runs)) != len(runs) or not all(RUN.match(r) for r in runs):
        raise ValueError(f"fill_from is 1 to {MAX_RUNS} distinct run ids, newest first, not {text!r}")
    return runs


def shard_names(names: list[str], key: str) -> list[str]:
    """the shard artifacts of the key (shard-KEY-N): never a wave pack, a plan, or another key's shard"""
    pat = re.compile(rf"^shard-{re.escape(key)}-[0-9]{{1,4}}$")
    return sorted({n for n in names if pat.match(n)}, key=lambda n: int(n.rsplit("-", 1)[1]))


def gh(args: list[str], runner=subprocess.run, sleep=time.sleep, tries: int = 4, wait: int = 30) -> str:
    """a gh call, tried again: the API answered 502 to large job and artifact listings for an hour on 11 Nov 2026"""
    for attempt in range(1, tries + 1):
        r = runner(["gh", *args], capture_output=True, text=True, check=False)
        if r.returncode == 0:
            return r.stdout
        if attempt < tries:
            sleep(attempt * wait)
    raise RuntimeError(f"gh {' '.join(args[:3])} failed {tries} times: {(r.stderr or '')[-300:]}")


def same_plan(old: Path, new: Path, unrecorded: bool, run: str) -> None:
    if not filecmp.cmp(old / "plan.json", new / "plan.json", shallow=False):
        sys.exit(f"the plan of run {run} differs from this run's, so its shards are not these shards (same shards, library commit?)")
    if (old / "inputs.json").exists():
        if not (new / "inputs.json").exists() or not filecmp.cmp(old / "inputs.json", new / "inputs.json", shallow=False):
            sys.exit(f"run {run} was built with other settings (mathlib, toolchain, imports, tengoku_ref, swap_gb, build_timeout_min) than this run")
    elif not unrecorded:
        sys.exit(f"run {run} recorded no settings (it predates plan/inputs.json): pass fill_unrecorded=true to vouch that they are the same")


def fill_from(repo: str, key: str, runs: list[str], shards: Path, work: Path, plan_new: Path | None = None, unrecorded: bool = False, runner=subprocess.run, sleep=time.sleep) -> dict[str, int]:
    """{run: shards filled in from it}, newest run first"""
    shards.mkdir(parents=True, exist_ok=True)
    filled: dict[str, int] = {}
    for run in runs:
        d = work / run
        if plan_new is not None:
            gh(["run", "download", run, "-R", repo, "-n", f"plan-{key}", "-D", str(d / "plan")], runner, sleep)
            same_plan(d / "plan", plan_new, unrecorded, run)
        listing = gh(["api", "--paginate", f"repos/{repo}/actions/runs/{run}/artifacts?per_page=100", "--jq", ".artifacts[] | select(.expired | not) | .name"], runner, sleep)
        for name in shard_names(listing.split(), key):
            if (shards / name).exists():  # built by the run being cut or by a newer run of the chain: never replaced
                continue
            gh(["run", "download", run, "-R", repo, "-n", name, "-D", str(d / "shards" / name)], runner, sleep)
        before = {p.name for p in shards.iterdir()}
        shard_pack.fill(argparse.Namespace(shards=str(shards), fill=str(d / "shards")))
        filled[run] = len({p.name for p in shards.iterdir()} - before)
    return filled


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", required=True)
    ap.add_argument("--key", required=True)
    ap.add_argument("--runs", required=True, help="fill_from: comma list of run ids, newest first")
    ap.add_argument("--shards", required=True)
    ap.add_argument("--work", required=True)
    ap.add_argument("--plan-new", default="", help="this run's plan directory: every run of the chain must have planned the same shards with the same settings")
    ap.add_argument("--unrecorded", default="false")
    a = ap.parse_args()
    try:
        runs = runs_of(a.runs)
    except ValueError as e:
        sys.exit(str(e))
    filled = fill_from(a.repo, a.key, runs, Path(a.shards), Path(a.work), Path(a.plan_new) if a.plan_new else None, a.unrecorded == "true")
    print("filled in: " + ", ".join(f"{n} shard(s) from run {r}" for r, n in filled.items()))


if __name__ == "__main__":
    main()
