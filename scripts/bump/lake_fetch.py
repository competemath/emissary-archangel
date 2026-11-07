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
import json
import math
import os
import re
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path


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


UNREADABLE = re.compile(r"fatal: unable to read tree \(?([0-9a-f]{40})\)?")


def packages_dir(directory: str) -> Path:
    """Where Lake keeps the library's packages (lake-manifest.json `packagesDir`, `.lake/packages` by default)."""
    try:
        return Path(directory) / (json.loads((Path(directory) / "lake-manifest.json").read_text()).get("packagesDir") or ".lake/packages")
    except (OSError, ValueError):
        return Path(directory) / ".lake" / "packages"


def has_commit(clone: Path, rev: str) -> bool:
    return subprocess.run(["git", "-C", str(clone), "cat-file", "-e", f"{rev}^{{commit}}"], capture_output=True).returncode == 0


def repair_pins(directory: str, output: str, deadline: float | None = None) -> list[str]:
    """A dependency pinned to a commit that no branch of its repository holds: Lake's clone does not have it and git says "fatal: unable to read tree (<rev>)" (padic-l-functions
    pins LeanModularForms at 512911ce, 7 Nov 2026: its setup was repaired by scripts/pinned-deps.mjs, and its bump then failed here, four tries of `lake update` with the same line).
    GitHub serves a commit named by its hash: each clone of the library's packages that lacks the commit fetches it. Returns the packages that now have it (Lake runs again)."""
    revs = set(UNREADABLE.findall(output))
    fixed: list[str] = []
    root = packages_dir(directory)
    for rev in sorted(revs):
        for clone in sorted(p for p in root.glob("*") if (p / ".git").exists()):
            if has_commit(clone, rev):
                continue
            left = 600.0 if deadline is None else min(600.0, deadline - time.monotonic())
            if left <= 0:
                return fixed  # the step's budget is spent: no repair outruns it
            # through run(): a fetch that runs out of the time left is killed with its whole process group (its ssh/https transport child too), and is a failed repair
            # an absolute path: run() works in `directory`, and the workflows pass it relative (`lib`), so `lib/.lake/…` would be read as `lib/lib/.lake/…` (cubic on #156)
            code, _ = run(["git", "-C", str(clone.resolve()), "fetch", "--quiet", "origin", rev], directory, left)
            if code is None:
                continue
            if has_commit(clone, rev):
                print(f"dependency {clone.name}: commit {rev[:12]} is on no branch of its repository; fetched it by its hash")
                fixed.append(clone.name)
    return fixed


def fetch(directory: str, tries: int, minutes: float, pause: float, budget_minutes: float) -> bool:
    deadline = time.monotonic() + budget_minutes * 60
    repairs = 0  # at most 5 free repairs in the whole step, both commands together
    for cmd in (["lake", "update"], ["lake", "exe", "cache", "get"]):
        name = " ".join(cmd)
        attempt = 0
        while True:
            left = deadline - time.monotonic()
            if left <= 0:
                print(f"::error::{name}: the {budget_minutes:g}-minute budget of this step is spent")
                return False
            attempt += 1
            code, tail = run(cmd, directory, min(minutes * 60, left))
            if code == 0:
                if tail:
                    print(tail)
                break
            why = "ran out of time" if code is None else f"exited {code}"
            print(f"::warning::{name} {why} (try {attempt} of {tries})" + (f": {tail}" if tail else ""))
            # a pinned commit Lake's clone lacks is fetched by its hash, and that try does not count: the next one runs at once (at most 5 such repairs)
            if code is not None and repairs < 5 and repair_pins(directory, tail, deadline):
                repairs += 1
                attempt -= 1
                continue
            if attempt >= tries:
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
