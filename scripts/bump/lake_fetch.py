#!/usr/bin/env python3
"""lake_fetch.py — `lake update`, then `lake exe cache get`, in a library's directory: each under a time limit and tried again when it fails or hangs.

evm-asm (2026-11-07): of 38 bump shards, one failed in this step with "mathlib: failed to fetch cache" and one hung in it for 5 h 43 min until the job's limit cancelled it;
the compose that needed both died, and the bump with it. The step had neither a limit nor a retry (the toolchain download before it already had retries, for the same reason).

  lake_fetch.py DIR [--tries N] [--minutes M] [--pause S]

Each command gets at most M minutes (default 30) and N tries (default 4), S seconds apart times the try number (default 20). A try that runs out of time is killed with its whole
process group (lake starts children; killing lake alone leaves them running). The last lines of each command's output are printed. Exit 0 when both succeeded, 1 otherwise, with
a GitHub error line naming the command.
"""

from __future__ import annotations

import argparse
import os
import signal
import subprocess
import sys
import time


def run(cmd: list[str], cwd: str, seconds: float) -> tuple[int | None, str]:
    """(exit code, output); the code is None when the command ran out of time (it and its children are killed)"""
    p = subprocess.Popen(cmd, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, start_new_session=True)
    try:
        out, _ = p.communicate(timeout=seconds)
        return p.returncode, out
    except subprocess.TimeoutExpired:
        try:
            os.killpg(p.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        out, _ = p.communicate()
        return None, out or ""


def fetch(directory: str, tries: int, minutes: float, pause: float) -> bool:
    for cmd in (["lake", "update"], ["lake", "exe", "cache", "get"]):
        name = " ".join(cmd)
        for attempt in range(1, tries + 1):
            code, out = run(cmd, directory, minutes * 60)
            tail = "\n".join(out.strip().splitlines()[-3:])
            if code == 0:
                if tail:
                    print(tail)
                break
            why = f"ran out of {minutes:g} min" if code is None else f"exited {code}"
            print(f"::warning::{name} {why} (try {attempt} of {tries})" + (f": {tail}" if tail else ""))
            if attempt == tries:
                print(f"::error::{name} did not succeed in {tries} tries")
                return False
            time.sleep(pause * attempt)
    return True


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("dir")
    ap.add_argument("--tries", type=int, default=4)
    ap.add_argument("--minutes", type=float, default=30)
    ap.add_argument("--pause", type=float, default=20)
    a = ap.parse_args()
    if a.tries < 1 or not a.minutes > 0 or a.pause < 0:
        sys.exit("lake_fetch.py: --tries at least 1, --minutes above 0, --pause not negative")
    sys.exit(0 if fetch(a.dir, a.tries, a.minutes, a.pause) else 1)
