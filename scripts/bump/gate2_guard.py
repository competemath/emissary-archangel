#!/usr/bin/env python3
"""gate2_guard.py — run one command and kill it, cleanly, when it grows past a memory limit or a time limit.

Why: Gate 2 (gate2_batch.py) checks the declarations of a shard in one Lean process, and that process can grow until the runner's kernel kills it (`Killed`)
or the whole runner VM goes ("The runner has received a shutdown signal"): navier-stokes-euler lost a shard to it four times on 2026-10-10, three of them
shards of only 38 to 249 modules. A process we kill ourselves, while the runner is still healthy, leaves a log and lets the caller split the work and go on.

  run_guarded(cmd, cwd, env, log, timeout_s, rss_limit_kb) -> Result(kind, returncode, peak_kb, seconds)
  kind: ok (it ended on its own, with any exit code: Lean exits non-zero when a declaration has an error), memory, timeout, signal (something else killed it)
"""

from __future__ import annotations

import os
import signal
import subprocess
import time
from dataclasses import dataclass
from pathlib import Path

DEFAULT_LIMIT_KB = 6 * 1024 * 1024
RUNNER_SHARE = 0.80  # of the machine's memory: what is left is the runner agent, the shell and the kernel's own needs


@dataclass
class Result:
    kind: str
    returncode: int
    peak_kb: int
    seconds: float


def mem_limit_kb(share: float = RUNNER_SHARE) -> int:
    """`share` of the machine's memory (Linux /proc/meminfo); a fixed 6 GB where there is none."""
    try:
        for ln in Path("/proc/meminfo").read_text().splitlines():
            if ln.startswith("MemTotal:"):
                return int(int(ln.split()[1]) * share)
    except OSError:
        pass
    return DEFAULT_LIMIT_KB


def rss_kb(group_leader: int) -> int:
    """Resident memory of the process group the command leads (the command and what it started), in KB."""
    out = subprocess.run(["ps", "-o", "rss=", "-g", str(group_leader)], capture_output=True, text=True).stdout
    return sum(int(x) for x in out.split() if x.isdigit())


def run_guarded(cmd: list[str], cwd: str | Path, env: dict[str, str], log: str | Path, timeout_s: float, rss_limit_kb: int, poll_s: float = 1.0) -> Result:
    start, peak, kind = time.monotonic(), 0, "ok"
    with open(log, "wb") as f:
        p = subprocess.Popen(cmd, cwd=cwd, env=env, stdout=f, stderr=subprocess.STDOUT, start_new_session=True)  # its own group: the kill takes the whole tree
        while p.poll() is None:
            peak = max(peak, rss := rss_kb(p.pid))
            if rss > rss_limit_kb:
                kind = "memory"
            elif time.monotonic() - start > timeout_s:
                kind = "timeout"
            if kind != "ok":
                try:
                    os.killpg(p.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                break
            time.sleep(poll_s)
        p.wait()
    if kind == "ok" and p.returncode < 0:
        kind = "signal"  # the kernel's OOM killer, or anything else, got there first
    return Result(kind, p.returncode, peak, round(time.monotonic() - start, 1))
