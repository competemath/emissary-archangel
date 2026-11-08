#!/usr/bin/env python3
"""A bump whose shard was killed for memory starts itself again with swap, once: rerun_killed.py REPOSITORY RUN_ID

The real case: leanbridge (8 Nov 2026), shard 6 of 7 was killed at 33 minutes (exit 137, the runner shut down) and compose stopped as designed. It was started again by hand. A resume of the one
shard cannot work: swap and the build limit change what a shard can build and judge, so compose refuses to mix shards built with and without them (plan_inputs.py). The whole plan runs again,
with the same inputs and the settings of the big-memory lane.

Only a killed shard counts: exit 137, the runner's shutdown message, or a failed job with no failed step (the runner was lost). Any other failed shard (the library does not build, an outage) is
a failure that swap does not cure, and nothing is started. The workflow runs this only for a run with no `heavy` setting and no resume, so the run this starts can never start another.
"""

import json
import os
import subprocess
import sys
import time

SWAP = "swap_gb=48;build_timeout_min=170"
RESUME_INPUTS = ("only_shards", "fill_from", "fill_unrecorded", "recut_from")


def killed(job: dict, log: str) -> bool:
    if "exit code 137" in log or "received a shutdown signal" in log:
        return True
    return not any(s.get("conclusion") == "failure" for s in job.get("steps", []))


def decide(jobs: list[tuple[dict, str]]) -> tuple[bool, str]:
    """(start it again?, why). `jobs`: every job of the run with its log."""
    failed = [(j, log) for j, log in jobs if j.get("name", "").startswith("shard") and j.get("conclusion") == "failure"]
    if not failed:
        return False, "no shard failed"
    other = [j["name"] for j, log in failed if not killed(j, log)]
    if other:
        return False, f"{len(other)} of {len(failed)} failed shards were not killed for memory ({', '.join(other[:5])}): swap does not cure that"
    return True, f"{len(failed)} shard(s) killed: {', '.join(j['name'] for j, _ in failed[:5])}"


def payload(inputs: dict) -> dict:
    """The same inputs, the swap settings, and no resume: the shards that did finish were built without swap, so none of them can be filled in."""
    out = {k: ("" if v is None else str(v).lower() if isinstance(v, bool) else str(v)) for k, v in inputs.items()}
    for k in RESUME_INPUTS:
        out.pop(k, None)  # left out: each has the workflow's own default
    out["heavy"] = SWAP
    return out


def gh(args: list[str], stdin: str | None = None, must: bool = False) -> str:
    """The output of `gh`; empty if it failed (a lost runner has no log), or RuntimeError if `must`."""
    r = subprocess.run(["gh", *args], input=stdin, capture_output=True, text=True, timeout=120, check=False)
    if must and r.returncode != 0:
        raise RuntimeError(r.stderr.strip()[-300:] or f"gh exited with {r.returncode}")
    return r.stdout if r.returncode == 0 else ""


TRIES = 3
WAIT_S = 20


def run(repo: str, run_id: str, inputs: dict, api=gh, sleep=time.sleep) -> int:
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
    logs = {j["id"]: api(["api", f"repos/{repo}/actions/jobs/{j['id']}/logs"]) for j in failed}
    go, why = decide([(j, logs.get(j["id"], "")) for j in jobs])
    if not go:
        print(f"not started again: {why}")
        return 0
    body = json.dumps({"ref": "main", "inputs": payload(inputs)})
    for attempt in range(1, TRIES + 1):
        try:
            api(["api", "--method", "POST", f"repos/{repo}/actions/workflows/bump-sharded.yml/dispatches", "--input", "-"], stdin=body, must=True)
        except RuntimeError as e:  # a rerun that was never started must not read as started
            print(f"could not start the run (try {attempt} of {TRIES}): {e}")
            if attempt == TRIES:
                print(f"::error::{why}, and the run could not be started: {e}", file=sys.stderr)
                return 1
            sleep(WAIT_S)
            continue
        print(f"::notice::{why}: the whole plan runs again with {SWAP}")
        return 0
    return 1


if __name__ == "__main__":
    sys.exit(run(sys.argv[1], sys.argv[2], json.loads(os.environ["INPUTS"])))
