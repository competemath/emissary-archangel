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
# how often the memory of the command is read. Lean can grow by gigabytes in a second; what it grows between two reads is how far it can pass the limit, and the limit plus that has to stay below
# the machine (2026-10-20, Navier shard 3 at share 0.92 = 14.7 GB of 16: the runner went down, "received a shutdown signal", before a read a second apart could stop the process; shard 63 at the same share finished)
POLL_S = 0.2


@dataclass
class Result:
    kind: str
    returncode: int
    peak_kb: int
    seconds: float


def limit_from_meminfo(meminfo: str, share: float = RUNNER_SHARE, count_swap: bool = False) -> int | None:
    """`share` of the machine's memory, in KB, from the text of /proc/meminfo; with `count_swap` the swap counts as memory too (the job added it for modules that do not fit in the
    runner's RAM: Lean then lives on swap, and a limit on the resident part alone would kill it long before the machine is short). None when the text has no MemTotal."""
    fields = {}
    for ln in meminfo.splitlines():
        name, _, rest = ln.partition(":")
        if name in ("MemTotal", "SwapTotal") and rest.split():
            fields[name] = int(rest.split()[0])
    if "MemTotal" not in fields:
        return None
    return int((fields["MemTotal"] + (fields.get("SwapTotal", 0) if count_swap else 0)) * share)


def mem_limit_kb(share: float = RUNNER_SHARE, count_swap: bool = False) -> int:
    """`share` of the machine's memory (Linux /proc/meminfo), and of its swap with `count_swap`; a fixed 6 GB where there is none."""
    try:
        got = limit_from_meminfo(Path("/proc/meminfo").read_text(), share, count_swap)
        if got is not None:
            return got
    except OSError:
        pass
    return DEFAULT_LIMIT_KB


def footprint_from_status(status: str) -> int:
    """VmRSS + VmSwap, in KB, from the text of /proc/<pid>/status: what the process holds in RAM and what it has pushed out to swap."""
    kb = 0
    for ln in status.splitlines():
        name, _, rest = ln.partition(":")
        if name in ("VmRSS", "VmSwap") and rest.split():
            kb += int(rest.split()[0])
    return kb


def rss_kb(group_leader: int, count_swap: bool = False) -> int:
    """Resident memory of the process group the command leads (the command and what it started), in KB; with `count_swap` what it has in swap too."""
    out = subprocess.run(["ps", "-o", "pid=,rss=", "-g", str(group_leader)], capture_output=True, text=True).stdout
    total = 0
    for ln in out.splitlines():
        parts = ln.split()
        if len(parts) != 2 or not all(x.isdigit() for x in parts):
            continue
        if count_swap:
            try:
                total += footprint_from_status(Path(f"/proc/{parts[0]}/status").read_text())
                continue
            except OSError:
                pass  # it ended between the two reads, or this is not Linux: the resident size ps gave is what there is
        total += int(parts[1])
    return total


def run_guarded(cmd: list[str], cwd: str | Path, env: dict[str, str], log: str | Path, timeout_s: float, rss_limit_kb: int, poll_s: float = POLL_S, count_swap: bool = False) -> Result:
    start, peak, kind = time.monotonic(), 0, "ok"
    with open(log, "wb") as f:
        p = subprocess.Popen(cmd, cwd=cwd, env=env, stdout=f, stderr=subprocess.STDOUT, start_new_session=True)  # its own group: the kill takes the whole tree
        while p.poll() is None:
            peak = max(peak, rss := rss_kb(p.pid, count_swap))
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
