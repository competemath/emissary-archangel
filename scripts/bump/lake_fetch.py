#!/usr/bin/env python3
"""lake_fetch.py — `lake update`, then `lake exe cache get`, in a library's directory: each try under a time limit, tried again when it fails or hangs, all of it within one budget.

evm-asm (2026-11-07): of 38 bump shards, one failed in this step with "mathlib: failed to fetch cache" and one hung in it for 5 h 43 min until the job's limit cancelled it;
the compose that needed both died, and the bump with it. The step had neither a limit nor a retry (the toolchain download before it already had retries, for the same reason).

  lake_fetch.py DIR [--tries N] [--minutes M] [--budget-minutes B] [--pause S]

Each try gets at most M minutes (default 20) and each command N tries (default 4), S seconds apart times the try number (default 20); everything together, pauses included,
fits in B minutes (default 60): the shard job has 345 minutes and the build and Gate 2 come after this step. A try that runs out of time is killed with its whole process group
(lake starts children; killing lake alone leaves them running). A command's output goes to a file, and only its last lines are printed. Exit 0 when both succeeded, 1 otherwise,
with a GitHub error line naming the command.
"""

from __future__ import annotations

import argparse
import math
import os
import signal
import subprocess
import sys
import tempfile
import time


def run(cmd: list[str], cwd: str, seconds: float) -> tuple[int | None, str]:
    """(exit code, the last lines of the output); the code is None when the command ran out of time (it and its children are killed). The output goes to a file, not memory."""
    with tempfile.TemporaryFile("w+", encoding="utf-8", errors="replace") as log:
        p = subprocess.Popen(cmd, cwd=cwd, stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
        try:
            code: int | None = p.wait(timeout=seconds)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(p.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            p.wait()
            code = None
        log.seek(0, os.SEEK_END)
        log.seek(max(0, log.tell() - 4096))
        tail = log.read().strip().splitlines()[-3:]
    return code, "\n".join(tail)


def fetch(directory: str, tries: int, minutes: float, pause: float, budget_minutes: float) -> bool:
    deadline = time.monotonic() + budget_minutes * 60
    for cmd in (["lake", "update"], ["lake", "exe", "cache", "get"]):
        name = " ".join(cmd)
        for attempt in range(1, tries + 1):
            left = deadline - time.monotonic()
            if left <= 0:
                print(f"::error::{name}: the {budget_minutes:g}-minute budget of this step is spent")
                return False
            code, tail = run(cmd, directory, min(minutes * 60, left))
            if code == 0:
                if tail:
                    print(tail)
                break
            why = "ran out of time" if code is None else f"exited {code}"
            print(f"::warning::{name} {why} (try {attempt} of {tries})" + (f": {tail}" if tail else ""))
            if attempt == tries:
                print(f"::error::{name} did not succeed in {tries} tries")
                return False
            time.sleep(min(pause * attempt, max(0.0, deadline - time.monotonic())))
    return True


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("dir")
    ap.add_argument("--tries", type=int, default=4)
    ap.add_argument("--minutes", type=float, default=20)
    ap.add_argument("--budget-minutes", type=float, default=60)
    ap.add_argument("--pause", type=float, default=20)
    a = ap.parse_args()
    finite = all(math.isfinite(v) for v in (a.minutes, a.budget_minutes, a.pause))
    if not finite or a.tries < 1 or not a.minutes > 0 or not a.budget_minutes > 0 or a.pause < 0:
        sys.exit("lake_fetch.py: --tries at least 1, --minutes and --budget-minutes above 0, --pause not negative, all finite numbers")
    sys.exit(0 if fetch(a.dir, a.tries, a.minutes, a.pause, a.budget_minutes) else 1)
