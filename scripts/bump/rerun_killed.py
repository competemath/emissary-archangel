#!/usr/bin/env python3
"""A bump whose shard was killed for memory starts itself again with swap, once: rerun_killed.py REPOSITORY RUN_ID

The real case: leanbridge (8 Nov 2026), shard 6 of 7 was killed at 33 minutes (exit 137, the runner shut down) and compose stopped as designed. It was started again by hand. A resume of the one
shard cannot work: swap and the build limit change what a shard can build and judge, so compose refuses to mix shards built with and without them (plan_inputs.py). The whole plan runs again,
with the same inputs and the settings of the big-memory lane.

Only a killed shard counts: exit 137, the runner's shutdown message, a failed job with no failed step (the runner was lost), or GitHub's own note on the job that its runner lost
communication. EtingofRepresentationTheory (bump-sharded run 43292037870, shard 2, 12 Nov 2026): the runner went silent 9 minutes into the build without swap, GitHub marked the build step
failed, stored no log (BlobNotFound) and left one annotation, "The hosted runner lost communication with the server": by log and steps alone it read as a build that fails, and nothing was
started. Any other failed shard (the library does not build, an outage) is a failure that swap does not cure, and nothing is started. The workflow runs this only for a run with no `heavy` setting and no resume, so the run this starts can never start another.
"""

import json
import os
import subprocess
import sys
import time

SWAP = "swap_gb=48;build_timeout_min=170"
RESUME_INPUTS = ("only_shards", "fill_from", "fill_unrecorded", "recut_from")


LOST = ("lost communication with the server", "received a shutdown signal")  # GitHub's annotations on a job whose runner died under it


def killed(job: dict, log: str, notes: str = "") -> bool:
    """`notes`: the job's annotations (GitHub writes them even when it stores no log)"""
    if "exit code 137" in log or "received a shutdown signal" in log:
        return True
    if any(m in notes for m in LOST):
        return True
    return not any(s.get("conclusion") == "failure" for s in job.get("steps", []))


def decide(jobs: list[tuple[dict, str]]) -> tuple[bool, str]:
    """(start it again?, why). `jobs`: every job of the run with its log, and optionally its annotations: (job, log) or (job, log, notes)."""
    jobs = [(t[0], t[1], t[2] if len(t) > 2 else "") for t in jobs]
    failed = [(j, log, notes) for j, log, notes in jobs if j.get("name", "").startswith("shard") and j.get("conclusion") == "failure"]
    if not failed:
        return False, "no shard failed"
    other = [j["name"] for j, log, notes in failed if not killed(j, log, notes)]
    if other:
        return False, f"{len(other)} of {len(failed)} failed shards were not killed for memory ({', '.join(other[:5])}): swap does not cure that"
    return True, f"{len(failed)} shard(s) killed: {', '.join(j['name'] for j, _, _ in failed[:5])}"


def payload(inputs: dict) -> dict:
    """The same inputs, the swap settings, and no resume: the shards that did finish were built without swap, so none of them can be filled in."""
    out = {k: ("" if v is None else str(v).lower() if isinstance(v, bool) else str(v)) for k, v in inputs.items()}
    for k in RESUME_INPUTS:
        out.pop(k, None)  # left out: each has the workflow's own default
    out["heavy"] = SWAP
    return out


def gh(args: list[str], stdin: str | None = None, must: bool = False, timeout: int = 120) -> str:
    """The output of `gh`; empty if it failed or ran out of time (a lost runner has no log), or RuntimeError if `must`. A call that times out is a failed call, never a
    crash of the script (cubic, #184)."""
    try:
        r = subprocess.run(["gh", *args], input=stdin, capture_output=True, text=True, timeout=timeout, check=False)
    except subprocess.TimeoutExpired:
        if must:
            raise RuntimeError(f"gh took more than {timeout} s")
        return ""
    if must and r.returncode != 0:
        raise RuntimeError(r.stderr.strip()[-300:] or f"gh exited with {r.returncode}")
    return r.stdout if r.returncode == 0 else ""



LOG_TRIES, LOG_WAIT = 6, 30
LOG_DEADLINE = 240  # seconds for all of the log reading, calls and waits together: the job has 10 minutes, and each call may take up to 2


def job_logs(api, repo: str, job_ids: list[int], sleep=time.sleep, clock=time.monotonic) -> dict[int, str]:
    """The logs of these jobs, waiting for the ones not stored yet: GitHub stores a log some time after its job ends. aintlib (9 Nov 2026): this job asked 3 seconds after shard 16's runner was
    shut down, got no log, read no shutdown and started nothing; the same log was there minutes later. One wait per round for all of them, and one deadline over every call and wait, so that the
    job always reaches its decision in time. Empty at the end: a runner lost before it wrote one, or no time left to read it."""
    logs = {i: "" for i in job_ids}
    end = clock() + LOG_DEADLINE
    for attempt in range(1, LOG_TRIES + 1):
        for i in [i for i, text in logs.items() if not text]:
            if clock() >= end:
                return logs
            logs[i] = api(["api", f"repos/{repo}/actions/jobs/{i}/logs"])
        if all(logs.values()) or attempt == LOG_TRIES or clock() + LOG_WAIT >= end:
            break
        sleep(LOG_WAIT)
    return logs


NOTES_DEADLINE, NOTES_CALL = 90, 30  # seconds for all annotation reads, and for one: with the logs' 240 (+120 for a last slow call) the job stays inside its 10 minutes


def annotations(api, repo: str, job_id: int) -> str:
    """the messages GitHub attached to a job (its check run), every page of them (cubic, #184: GitHub pages them 30 at a time by default): there even when the job's log is
    not. One message per line; empty if they cannot be read."""
    return api(["api", f"repos/{repo}/check-runs/{job_id}/annotations", "--method", "GET", "-F", "per_page=100", "--paginate", "--jq", ".[].message"]) or ""


def gh_notes(args: list[str]) -> str:
    return gh(args, timeout=NOTES_CALL)


def job_notes(api, repo: str, job_ids: list[int], clock=time.monotonic) -> dict[int, str]:
    """the annotations of these jobs, inside one deadline (cubic, #184): a job not reached in time has none, and none is never a kill"""
    notes: dict[int, str] = {}
    end = clock() + NOTES_DEADLINE
    for i in job_ids:
        if clock() >= end:
            break
        notes[i] = annotations(api, repo, i)
    return notes


def run(repo: str, run_id: str, inputs: dict, api=gh, sleep=time.sleep, clock=time.monotonic, notes_api=None) -> int:
    notes_api = notes_api or (gh_notes if api is gh else api)  # the real gh reads annotations with a short timeout; a test's fake answers both
    jobs, page = [], 1
    while True:
        batch = json.loads(api(["api", f"repos/{repo}/actions/runs/{run_id}/jobs?per_page=100&page={page}"]) or "{}").get("jobs", [])
        jobs += batch
        if len(batch) < 100:
            break
        page += 1
    if not jobs:
        print("::error::the jobs of this run could not be read", file=sys.stderr)
        return 1
    failed = [j for j in jobs if j.get("name", "").startswith("shard") and j.get("conclusion") == "failure"]
    logs = job_logs(api, repo, [j["id"] for j in failed], sleep, clock)
    notes = job_notes(notes_api, repo, [j["id"] for j in failed], clock)
    go, why = decide([(j, logs.get(j["id"], ""), notes.get(j["id"], "")) for j in jobs])
    if not go:
        print(f"not started again: {why}")
        return 0
    body = json.dumps({"ref": "main", "inputs": payload(inputs)})
    try:  # one try: a dispatch reported as failed may still have been accepted, and a second one would run the whole plan twice
        api(["api", "--method", "POST", f"repos/{repo}/actions/workflows/bump-sharded.yml/dispatches", "--input", "-"], stdin=body, must=True)
    except RuntimeError as e:  # a rerun that was never started must not read as started
        print(f"::error::{why}, and the run could not be started: {e}", file=sys.stderr)
        return 1
    print(f"::notice::{why}: the whole plan runs again with {SWAP}")
    return 0


if __name__ == "__main__":
    sys.exit(run(sys.argv[1], sys.argv[2], json.loads(os.environ["INPUTS"])))
