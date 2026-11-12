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


FROM_TREE_LINE = re.compile(r"^\S+Z\s+FROM_TREE: (true|false)\s*$", re.M)
REUSE_FROM_LINE = re.compile(r"^\S+Z\s+REUSE_FROM: ?(\S*)\s*$", re.M)
MAX_CHAIN = 8  # runs: a resume of a resume of ... (each one days of builds); more is a loop or a mistake


def earlier_of(lane: dict | None, plan_log: str) -> str:
    """the run an earlier run itself resumed (its reuse_from), "" for a run that started from wave 0. Its plan's lane.json says (written since resumes of resumes),
    or its plan job's log, where the value shows in a step's environment (flt-anthropic's resume 43075875630 of 42678283150, 11 Nov 2026). Two values refuse."""
    if lane and "reuse_from" in lane:
        return str(lane["reuse_from"] or "")
    seen = set(REUSE_FROM_LINE.findall(plan_log))
    if len(seen) > 1:
        raise ValueError(f"the plan log shows more than one reuse_from: {sorted(seen)}")
    return seen.pop() if seen else ""


def library_identity(setup: dict, sources: dict, key: str) -> dict:
    """What a run built: the library's repo, commit and roots (data/exports/KEY/setup.ci.json, trial-library-build.py meta) and its subdir (sources.json). A resume
    reuses packs and shard packs of earlier runs only if they built this same library (hacktron, #178: the plan and the settings can match across two commits);
    the export hashes, timings and archive of the record may change between runs (a setup re-run republishes them) and are not the library."""
    src = (sources.get("sources") or {}).get(key) or {}
    return {"repo": setup.get("repo"), "commit": setup.get("commit"), "roots": setup.get("roots"), "subdir": src.get("subdir") or ""}


def chain_view(plan: dict, chain: list[tuple[str, list[dict], set[str]]], key: str) -> tuple[set[int], dict[int, str], set[int]]:
    """A resume of a resume (flt-anthropic, 11 Nov 2026: the resume 43075875630 of 42678283150 lost job 43's uploads in a GitHub outage, and the 63 jobs it kept live in
    42678283150). `chain`: (run, jobs, artifacts), the run this one resumes first, then the run that one resumed, and so on.

    A job's state is the one of the newest run in which it ran (a kept job has no job in the run that kept it). A pack is taken from the OLDEST run in which it is good,
    as every run does (a job of a resume restores a good pack of the run it resumes, and built on that one): packed there, there, and built only on good packs.
    Returns (the jobs that succeeded, {shard: the run of its good pack}, the jobs whose shard pack is in the run they last ran in)."""
    ok: set[int] = set()
    shard_pack: set[int] = set()
    last: dict[int, str] = {}
    for run, jobs, arts in chain:  # newest first: the first run with a job of a shard is where it last ran
        for j in jobs:
            m = JOB.match(j.get("name", ""))
            if not m or int(m.group(2)) in last:
                continue
            n = int(m.group(2))
            last[n] = run
            if j.get("conclusion") == "success":
                ok.add(n)
            if f"shard-{key}-{n}" in arts:
                shard_pack.add(n)
    source: dict[int, str] = {}
    for run, jobs, arts in reversed(chain):  # oldest first
        packed_here = packed(jobs)
        for s in sorted(plan["shards"], key=lambda x: (x["wave"], x["shard"])):
            n = s["shard"]
            if n not in source and n in packed_here and f"wave-{key}-{n}" in arts and all(r in source for r in s.get("restore", [])):
                source[n] = run
    return ok, source, shard_pack


def earlier_from_tree(lane: dict | None, plan_log: str) -> str | None:
    """the earlier run's from_tree: its plan's lane.json (written since this change), or the value its plan job's log shows in a step's environment (a run from before
    it, like flt-anthropic's 42678283150); None when neither says. A resume with another from_tree would number its parts from 001 instead of after the tree's last
    part, or the reverse (cubic, #174)."""
    if lane and lane.get("from_tree") in ("true", "false"):
        return lane["from_tree"]
    seen = set(FROM_TREE_LINE.findall(plan_log))
    return seen.pop() if len(seen) == 1 else None


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


def chain_outputs(plan: dict, keep: set[int], source: dict[int, str], runs: list[str], max_waves: int = MAX_WAVES) -> dict[str, str]:
    """outputs() for a chain: `packs` names each good pack's run (`N@RUN`, wave_pack.py run_of), `fill` the runs whose shard packs fill in the bundle, newest first"""
    out = outputs(plan, keep, set(source), max_waves)
    out["packs"] = ",".join(f"{n}@{source[n]}" for n in sorted(source))
    out["fill"] = ",".join(runs)
    return out


def main() -> None:
    if sys.argv[1:2] == ["library"]:  # lane_reuse.py library --setup setup.ci.json --sources sources.json --key K: the identity, canonical JSON (bump-waves.yml compares)
        e = argparse.ArgumentParser()
        e.add_argument("cmd")
        e.add_argument("--setup", required=True)
        e.add_argument("--sources", required=True)
        e.add_argument("--key", required=True)
        b = e.parse_args()
        ident = library_identity(json.loads(Path(b.setup).read_text()), json.loads(Path(b.sources).read_text()), b.key)
        if not ident["repo"] or not ident["commit"]:
            sys.exit(f"{b.setup}: no repo or commit")
        print(json.dumps(ident, sort_keys=True))
        return
    if sys.argv[1:2] == ["earlier"]:  # lane_reuse.py earlier --plan-log LOG [--lane lane.json]: the run an earlier run resumed, "" for none (bump-waves.yml walks the chain)
        e = argparse.ArgumentParser()
        e.add_argument("cmd")
        e.add_argument("--plan-log", required=True)
        e.add_argument("--lane", default="")
        b = e.parse_args()
        lane = json.loads(Path(b.lane).read_text()) if b.lane and Path(b.lane).exists() else None
        log = Path(b.plan_log).read_text(errors="replace") if Path(b.plan_log).exists() else ""
        if not (lane and "reuse_from" in lane) and not log.strip():
            # neither says: an unfetched log must not read as "this run started from wave 0", which would cut the chain and rebuild what its older runs kept (cubic, #178)
            sys.exit(f"{b.plan_log}: the plan log is empty or missing and lane.json does not say what the run resumed")
        try:
            print(earlier_of(lane, log))
        except ValueError as err:
            sys.exit(str(err))
        return
    ap = argparse.ArgumentParser()
    ap.add_argument("--plan", required=True)
    ap.add_argument("--jobs", default="", help="the earlier run's jobs (gh api .../runs/ID/jobs, the `jobs` objects, one JSON list)")
    ap.add_argument("--artifacts", default="", help="the earlier run's artifacts that are not expired (a JSON list of names)")
    ap.add_argument("--key", required=True)
    ap.add_argument("--from-tree", required=True, help="this run's from_tree: it must be the earlier run's")
    ap.add_argument("--lane", default="", help="the earlier run's plan/lane.json, when it has one")
    ap.add_argument("--plan-log", default="", help="the earlier run's plan job log, for a run from before lane.json")
    ap.add_argument("--chain", default="", help="the earlier runs, newest first (comma list): the run this one resumes, the run that one resumed, ... (bump-waves.yml)")
    ap.add_argument("--reuse-dir", default="", help="with --chain: RUN/jobs.json and RUN/artifacts.json of every run of the chain")
    a = ap.parse_args()
    lane = json.loads(Path(a.lane).read_text()) if a.lane and Path(a.lane).exists() else None
    was = earlier_from_tree(lane, Path(a.plan_log).read_text(errors="replace") if a.plan_log and Path(a.plan_log).exists() else "")
    if was is None:
        sys.exit("the earlier run's from_tree is not known (no plan/lane.json, and its plan log shows none or two values)")
    if was != a.from_tree:
        sys.exit(f"the earlier run ran with from_tree={was} and this one with from_tree={a.from_tree}: its parts would be numbered differently")
    plan = json.loads(Path(a.plan).read_text())
    if a.chain:
        runs = [r for r in a.chain.split(",") if r]
        if not runs or len(runs) > MAX_CHAIN or len(set(runs)) != len(runs) or not all(re.fullmatch(r"[1-9][0-9]{0,14}", r) for r in runs):
            sys.exit(f"--chain is 1 to {MAX_CHAIN} distinct run ids, newest first, not {a.chain!r}")
        base = Path(a.reuse_dir)
        ok, source, shard_pack = chain_view(plan, [(r, json.loads((base / r / "jobs.json").read_text()), set(json.loads((base / r / "artifacts.json").read_text()))) for r in runs], a.key)
        keep = {n for n in ok if n in source and n in shard_pack}
        out = chain_outputs(plan, keep, source, runs)
    else:
        if not a.jobs or not a.artifacts:
            sys.exit("--jobs and --artifacts, or --chain and --reuse-dir")
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
