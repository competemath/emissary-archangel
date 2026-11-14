#!/usr/bin/env python3
"""A bump-waves run whose build chain is dead is cancelled and resumed: waves_watch.py [--dry-run] (waves-watch.yml).

13 Nov 2026, run 43237206258 (flt-anthropic, 111 jobs): job 93 of wave 15 lost its runner at 19:14 after 54 minutes (no log, no failed step). Every later job restores the packs of the earlier jobs
(a build-once chain), so every job of waves 16 and 17 failed within 9 to 20 minutes at that step ("the pack of shard 93 could not be fetched in 4 tries") and the run went on until a person read the job
results at 23:44 and resumed it by hand (`reuse_from`, from_tree true: 94 of 111 jobs reused, 17 run). The same shape as the outage of 12 Nov. This is that recovery, made automatic.

The rule (doomed): a shard job failed (not cancelled), and at least two shard jobs of LATER waves failed at the restore step ("The work of the earlier jobs"). Later waves only start when their predecessors
have finished, so the jobs still running when the rule fires cannot be lost work, and the first failure of a wave with other jobs still running (shard 93 at 19:14, with 92 and 94 running for four more
hours) never fires it: waiting for the wave is what spares them. The run is cancelled, and when it has ended a new run is dispatched with reuse_from the cancelled run, from_tree and the settings the
plan artifact recorded (inputs.json, lane.json), so that the plan step's own checks pass. A chain of more than MAX_CHAIN runs is left to a person (the same job failing again is not a runner lost), and so
is any run this cannot read.
It reads and cancels and dispatches; it runs no library's code. LANE_ENABLED (the intake lane's kill switch) stops it."""

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
LATER_FAILURES = 2  # jobs of later waves that failed at the restore step before a run counts as dead
MAX_CHAIN = 4  # runs of one chain (the first, and what this resumed); the workflow itself stops at 8
POLL_SECONDS = 15
ENDED_WITHIN_SECONDS = 600
SETTINGS = ("mathlib", "toolchain", "imports", "tengoku_ref", "swap_gb", "build_timeout_min")  # what inputs.json records and the plan step compares
SAFE = re.compile(r"^[A-Za-z0-9._/:+=-]*$")  # a value that can only be a setting: no space, no quote, no `$`, no `;`
KEY = re.compile(r"^[a-z0-9][a-z0-9-]*$")


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
    if len(later) < LATER_FAILURES:
        return None
    return {"failed": sorted(s["shard"] for s in roots if s["wave"] == first), "wave": first, "later": sorted(s["shard"] for s in later)}


def dispatch_args(key: str, run: int, inputs: dict, lane: dict) -> list[str]:
    """`gh workflow run` for the resume: the cancelled run, the settings its plan recorded, from_tree as its lane says. A value that is not a plain setting is refused."""
    if not KEY.match(key):
        raise WatchError(f"not a source key: {key!r}")
    values = {k: str(inputs.get(k, "")) for k in SETTINGS}
    values["from_tree"] = str(lane.get("from_tree", ""))
    for k, v in values.items():
        if not SAFE.match(v):
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


def running(dry: bool = False) -> list[dict]:
    text = gh("api", f"repos/{REPO}/actions/workflows/{WORKFLOW}/runs?status=in_progress&branch=main&event=workflow_dispatch&per_page=20")
    return [{"id": int(r["id"]), "title": str(r.get("display_title", ""))} for r in json.loads(text).get("workflow_runs", [])]


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


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args(argv)
    resumed = 0
    for r in running():
        d = doomed(jobs_of(r["id"]))
        if not d:
            print(f"run {r['id']} ({r['title']}): alive")
            continue
        print(f"run {r['id']} ({r['title']}): dead: shard(s) {d['failed']} of wave {d['wave']} failed and shards {d['later']} of later waves could not restore their packs")
        key = key_of(r["title"])
        inputs, lane = plan_files(r["id"], key)
        n = chain_length(lane, lambda run: plan_files(int(run), key)[1])
        if n > MAX_CHAIN:
            print(f"run {r['id']}: the chain has {n} runs (more than {MAX_CHAIN}): left to a person")
            continue
        args = dispatch_args(key, r["id"], inputs, lane)
        if a.dry_run:
            print("dry run: would cancel the run and dispatch: " + " ".join(args[3:]))
            continue
        subprocess.run(["gh", "run", "cancel", str(r["id"]), "-R", REPO], check=True)
        if not ended(r["id"]):
            raise WatchError(f"run {r['id']} did not end within {ENDED_WITHIN_SECONDS} seconds of its cancel: no resume dispatched")
        subprocess.run(args, check=True)  # never retried: a second dispatch would be a second resume
        resumed += 1
        print(f"run {r['id']} cancelled; resume dispatched: " + " ".join(args[3:]))
    print(f"{resumed} resumed")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except WatchError as e:
        print(f"::error::{e}")
        sys.exit(1)
