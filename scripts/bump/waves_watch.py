#!/usr/bin/env python3
"""A bump-waves run whose build chain is dead is cancelled and resumed: waves_watch.py [--dry-run] (waves-watch.yml).

13 Nov 2026, run 43237206258 (flt-anthropic, 111 jobs): job 93 of wave 15 lost its runner at 19:14 after 54 minutes (no log, no failed step). Every later job restores the packs of the earlier jobs
(a build-once chain), so every job of waves 16 and 17 failed within 9 to 20 minutes at that step ("the pack of shard 93 could not be fetched in 4 tries") and the run went on until a person read the job
results at 23:44 and resumed it by hand (`reuse_from`, from_tree true: 94 of 111 jobs reused, 17 run). The same shape as the outage of 12 Nov. This is that recovery, made automatic.

The rule (doomed): a shard job failed (not cancelled), and shard jobs of at least two LATER waves failed at the restore step ("The work of the earlier jobs"): two jobs of one wave could be a transient fetch failure. Later waves only start when their predecessors
have finished, so the jobs still running when the rule fires cannot be lost work, and the first failure of a wave with other jobs still running (shard 93 at 19:14, with 92 and 94 running for four more
hours) never fires it: waiting for the wave is what spares them. The run is cancelled, and when it has ended a new run is dispatched with reuse_from the cancelled run, from_tree and the settings the
plan artifact recorded (inputs.json, lane.json), so that the plan step's own checks pass. A chain of more than MAX_CHAIN runs is left to a person (the same job failing again is not a runner lost), and so
is any run this cannot read.
It reads and cancels and dispatches; it runs no library's code. LANE_ENABLED (the intake lane's kill switch) stops it.
GitHub's scheduler did not fire the 20-minute cron once in the 46 minutes after the merge (14 Nov 2026), so the watcher does not wait for it: with --wait-minutes N it looks again every LOOK_SECONDS (five minutes)
for as long as a bump-waves run is in progress (up to N minutes), and then dispatches itself once more if one still is, so that a run is watched from the moment it is requested (waves-watch.yml
runs on the `requested` event of bump-waves) to its end, by a job that does not depend on the scheduler. The cost is one runner while a run lives."""

import argparse
import json
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path

REPO = "competemath/emissary-archangel"
WORKFLOW = "bump-waves.yml"
SHARD = re.compile(r"^w(\d+) \((\d+)\) / shard$")
RESTORE_STEP = "The work of the earlier jobs"
LATER_FAILURES = 2  # later WAVES with a job that failed at the restore step before a run counts as dead
MAX_RESUMES = 2  # runs resumed by one look: each may wait 10 minutes for its cancel, and the job's cap must cover them (cubic on #195)
MAX_CHAIN = 4  # runs of one chain (the first, and what this resumed); the workflow itself stops at 8
POLL_SECONDS = 15  # between two looks of ended(): a cancel
LOOK_SECONDS = 300  # between two looks at the runs while one is in progress (--wait-minutes)
ENDED_WITHIN_SECONDS = 600
SETTINGS = ("mathlib", "toolchain", "imports", "tengoku_ref", "swap_gb", "build_timeout_min")  # what inputs.json records and the plan step compares
SAFE = re.compile(r"^[A-Za-z0-9._/:+=-]*$")  # a value that can only be a setting: no space, no quote, no `$`, no `;`
KEY = re.compile(r"^[a-z0-9][a-z0-9-]*$")


class ReadFailure(RuntimeError):
    """A read of GitHub failed (a 502, a timeout, an answer that is not JSON): the only kind of failure a later look may tolerate. A cancel, a dispatch and a refusal are never this (cubic on #197)."""


def read(fn, *args):
    try:
        return fn(*args)
    except (subprocess.CalledProcessError, json.JSONDecodeError, KeyError, TypeError, OSError) as e:
        raise ReadFailure(f"{getattr(fn, '__name__', 'read')}: {type(e).__name__}: {e}") from e


class WatchError(RuntimeError):
    """Something this cannot read or may not do: left to a person (the job fails visibly)."""


def shard_jobs(jobs: list[dict]) -> list[dict]:
    out = []
    for j in jobs:
        m = SHARD.match(str(j.get("name", "")))
        if m:
            out.append({"wave": int(m.group(1)), "shard": int(m.group(2)), "conclusion": j.get("conclusion"), "steps": list(j.get("failed_steps") or [])})
    return out


def doomed(jobs: list[dict]) -> dict | None:
    """None, or why the run is dead: the shard jobs that failed and the jobs of later waves that failed at the restore step."""
    shards = shard_jobs(jobs)
    roots = [s for s in shards if s["conclusion"] == "failure"]
    if not roots:
        return None
    first = min(s["wave"] for s in roots)
    later = [s for s in roots if s["wave"] > first and any(x.startswith(RESTORE_STEP) for x in s["steps"])]
    if len({s["wave"] for s in later}) < LATER_FAILURES:  # distinct waves: two jobs of one wave failing to restore may be a transient (cubic on #195)
        return None
    return {"failed": sorted(s["shard"] for s in roots if s["wave"] == first), "wave": first, "later": sorted(s["shard"] for s in later)}


def dispatch_args(key: str, run: int, inputs: dict, lane: dict) -> list[str]:
    """`gh workflow run` for the resume: the cancelled run, the settings its plan recorded, from_tree as its lane says. A value that is not a plain setting is refused."""
    if not KEY.fullmatch(key):
        raise WatchError(f"not a source key: {key!r}")
    missing = [k for k in SETTINGS if k not in inputs] + (["from_tree"] if "from_tree" not in lane else [])
    if missing:  # before anything is cancelled: the resume's own plan step would stop on a settings mismatch (cubic on #195)
        raise WatchError(f"the plan recorded no {', '.join(missing)}: not resumed")
    values = {k: str(inputs[k]) for k in SETTINGS}
    values["from_tree"] = str(lane["from_tree"])
    for k, v in values.items():
        if not SAFE.fullmatch(v):
            raise WatchError(f"{k} is not a plain setting: {v!r}")
    if values["from_tree"] not in ("true", "false"):
        raise WatchError(f"from_tree is true or false, not {values['from_tree']!r}")
    args = ["gh", "workflow", "run", WORKFLOW, "-R", REPO, "--ref", "main", "-f", f"key={key}", "-f", f"reuse_from={int(run)}", "-f", f"from_tree={values['from_tree']}"]
    for k in SETTINGS:
        if values[k]:
            args += ["-f", f"{k}={values[k]}"]
    return args


def chain_length(first_lane: dict, lanes) -> int:
    """Runs of the chain a run belongs to: itself and every run its lane (plan/lane.json: reuse_from) leads back to; `lanes(run)` reads another run's lane (None when it has none)."""
    n, lane, seen = 1, first_lane, set()
    while lane and lane.get("reuse_from"):
        run = str(lane["reuse_from"])
        if run in seen or n > 2 * MAX_CHAIN:
            return 10**6  # a loop: never resumed
        seen.add(run)
        n += 1
        lane = lanes(run)
    return n


def gh(*args: str) -> str:
    return subprocess.run(["gh", *args], check=True, capture_output=True, text=True).stdout


def pages(path: str) -> list[dict]:
    out, page = [], 1
    while True:
        text = gh("api", f"{path}{'&' if '?' in path else '?'}per_page=60&page={page}")
        got = json.loads(text).get("jobs", [])
        out += got
        if len(got) < 60:
            return out
        page += 1


def jobs_of(run: int) -> list[dict]:
    return [
        {"name": j["name"], "status": j["status"], "conclusion": j["conclusion"], "failed_steps": [s["name"] for s in j.get("steps", []) if s.get("conclusion") == "failure"]}
        for j in pages(f"repos/{REPO}/actions/runs/{int(run)}/jobs")
    ]


def plan_files(run: int, key: str) -> tuple[dict, dict]:
    """inputs.json and lane.json of a run's plan artifact ({} for a file it has not)."""
    with tempfile.TemporaryDirectory() as d:
        subprocess.run(["gh", "run", "download", str(int(run)), "-R", REPO, "-n", f"plan-{key}", "-D", d], check=True, capture_output=True, text=True)
        read = lambda n: json.loads((Path(d) / n).read_text(encoding="utf-8")) if (Path(d) / n).exists() else {}  # noqa: E731
        return read("inputs.json"), read("lane.json")


def running() -> list[dict]:
    """Every bump-waves run of main that has not ended: in progress, and queued (a run that was just requested is queued: the watch of it must not end before it starts; cubic on #197)."""
    out, seen = [], set()
    for status in ("in_progress", "queued"):
        page = 1
        while True:
            text = gh("api", f"repos/{REPO}/actions/workflows/{WORKFLOW}/runs?status={status}&branch=main&event=workflow_dispatch&per_page=100&page={page}")
            got = json.loads(text).get("workflow_runs", [])
            for r in got:
                if int(r["id"]) not in seen:
                    seen.add(int(r["id"]))
                    out.append({"id": int(r["id"]), "title": str(r.get("display_title", "")), "status": status})
            if len(got) < 100:
                break
            page += 1
    return out


def key_of(title: str) -> str:
    m = re.match(r"^bump-waves ([a-z0-9][a-z0-9-]*)$", title)
    if not m:
        raise WatchError(f"no source key in the run's title {title!r}")
    return m.group(1)


def ended(run: int, sleep=time.sleep, clock=time.time) -> bool:
    deadline = clock() + ENDED_WITHIN_SECONDS
    while clock() < deadline:
        if json.loads(gh("api", f"repos/{REPO}/actions/runs/{int(run)}"))["status"] == "completed":
            return True
        sleep(POLL_SECONDS)
    return False


def look(dry: bool) -> tuple[int, int]:
    """One look at every run in progress: dead ones are cancelled and resumed (unless dry). (runs in progress at the start of the look, runs resumed)"""
    resumed = 0
    runs = read(running)
    for r in runs:
        if resumed >= MAX_RESUMES:  # per look: the next look is five minutes away
            print("the rest is left to the next look")
            break
        if r.get("status") == "queued":
            print(f"run {r['id']} ({r['title']}): queued, not started")
            continue
        d = doomed(read(jobs_of, r["id"]))
        if not d:
            print(f"run {r['id']} ({r['title']}): alive")
            continue
        print(f"run {r['id']} ({r['title']}): dead: shard(s) {d['failed']} of wave {d['wave']} failed and shards {d['later']} of later waves could not restore their packs")
        key = key_of(r["title"])
        inputs, lane = read(plan_files, r["id"], key)
        n = chain_length(lane, lambda run: read(plan_files, int(run), key)[1])
        if n > MAX_CHAIN:
            print(f"run {r['id']}: the chain has {n} runs (more than {MAX_CHAIN}): left to a person")
            continue
        args = dispatch_args(key, r["id"], inputs, lane)
        if dry:
            print("dry run: would cancel the run and dispatch: " + " ".join(args[3:]))
            continue
        subprocess.run(["gh", "run", "cancel", str(r["id"]), "-R", REPO], check=True)
        if not ended(r["id"]):
            raise WatchError(f"run {r['id']} did not end within {ENDED_WITHIN_SECONDS} seconds of its cancel: no resume dispatched")
        subprocess.run(args, check=True)  # never retried: a second dispatch would be a second resume
        resumed += 1
        print(f"run {r['id']} cancelled; resume dispatched: " + " ".join(args[3:]))
    return len(runs), resumed


def main(argv: list[str] | None = None, sleep=time.sleep, clock=time.time) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--wait-minutes", type=int, default=0, help="while a bump-waves run is in progress, look again every five minutes for this long, then dispatch this workflow once more")
    a = ap.parse_args(argv)
    deadline = clock() + 60 * a.wait_minutes
    total, first = 0, True
    while True:
        try:
            alive, resumed = look(a.dry_run)
        except ReadFailure as e:  # a failed READ of GitHub must not end the watch of a run; a cancel, a dispatch or a refusal always does (cubic on #197); the first look and the last failing are real failures
            if first or clock() + LOOK_SECONDS > deadline:
                raise
            print(f"this look failed ({type(e).__name__}: {e}); the next is in {LOOK_SECONDS // 60} minutes")
            alive, resumed = 1, 0
        first = False
        total += resumed
        if a.dry_run or not alive:
            break
        if clock() + LOOK_SECONDS > deadline:
            if a.wait_minutes:
                # a run is still in progress at the end of this job's time: the watch goes on in a new job (never retried: a second dispatch would only queue a second watcher)
                subprocess.run(["gh", "workflow", "run", "waves-watch.yml", "-R", REPO, "--ref", "main", "-f", "dry_run=false"], check=True)
                print("a run is still in progress: the watch goes on in a new job")
            break
        sleep(LOOK_SECONDS)
    print(f"{total} resumed")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except WatchError as e:
        print(f"::error::{e}")
        sys.exit(1)
