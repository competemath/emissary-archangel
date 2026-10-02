#!/usr/bin/env python3
"""orchestrate.py — run the bump over many libraries in the cloud, as fast as the runners allow, with nobody watching.

Each library is dispatched as `bump-library.yml` (one runner) or `bump-sharded.yml` (a plan, N shards in parallel, a merge) by
its size. GitHub runs 20 jobs of a repository at once, so a dispatch waits until the jobs it will use fit: a big library first
(it decides the finish time), small ones in the slots it leaves. The orchestrator is itself a job and may not outlive six
hours: it hands what it has not dispatched to a fresh copy of itself before that. State is only what the runs already say
(in-flight runs are found by their run-name), so a restart or a copy loses nothing.

  orchestrate.py --keys "a b c" [--capacity 20] [--skip "x y"] [--deadline-min 330] [--dispatch-self]
"""

from __future__ import annotations

import argparse
import json
import math
import subprocess
import sys
import time
from pathlib import Path

REPO = ""
SMALL = "bump-library.yml"
BIG = "bump-sharded.yml"


def gh(*args: str, check: bool = True) -> str:
    r = subprocess.run(["gh", *args], capture_output=True, text=True)
    if check and r.returncode:
        raise RuntimeError(f"gh {' '.join(args)}: {r.stderr.strip()[:300]}")
    return r.stdout.strip()


def size_of(key: str) -> tuple[int, int]:
    """(modules, lines) of the library's setup: how big a job it is."""
    p = Path(f"data/exports/{key}/setup.ci.json")
    d = json.loads(p.read_text()) if p.exists() else {}
    modules = int(d.get("modules", 0) or 0)
    return modules, int(d.get("lines", 0) or modules * 450)


def jobs_needed(key: str) -> tuple[str, int]:
    modules, lines = size_of(key)
    if modules >= 350 or lines >= 200_000:
        return BIG, min(8, max(2, math.ceil(lines / 200_000))) + 2  # bump-sharded runs 8 shards at once (its `parallel` input)
    return SMALL, 1


def in_flight() -> dict[str, int]:
    """key -> jobs reserved by its runs that have not finished."""
    out: dict[str, int] = {}
    for wf in (SMALL, BIG):
        for status in ("in_progress", "queued", "waiting", "pending"):
            rows = json.loads(gh("run", "list", "-R", REPO, "--workflow", wf, "--status", status, "--limit", "100", "--json", "displayTitle") or "[]")
            for r in rows:
                parts = r["displayTitle"].split()
                if len(parts) == 2 and parts[0] in ("bump", "bump-sharded"):
                    out[parts[1]] = jobs_needed(parts[1])[1]
    return out


def main() -> None:
    global REPO
    ap = argparse.ArgumentParser()
    ap.add_argument("--keys", required=True)
    ap.add_argument("--repo", required=True)
    ap.add_argument("--capacity", type=int, default=14)  # the repository has 20 runners; tengoku CI needs some
    ap.add_argument("--skip", default="")
    ap.add_argument("--deadline-min", type=int, default=330)
    ap.add_argument("--dispatch-self", action="store_true")
    a = ap.parse_args()
    REPO = a.repo
    start = time.time()
    keys = [k for k in a.keys.split() if k and k not in a.skip.split()]
    keys.sort(key=lambda k: -size_of(k)[1])  # the biggest decides when everything is done
    pending = list(keys)
    flight = in_flight()
    print(f"{len(pending)} libraries to dispatch; {len(flight)} runs already in flight: {flight}", flush=True)
    while pending:
        if time.time() - start > a.deadline_min * 60:
            break
        flight = in_flight()
        used = sum(flight.values())
        for k in list(pending):
            if k in flight:
                pending.remove(k)  # already running (a previous copy dispatched it)
                continue
            wf, need = jobs_needed(k)
            if used + need <= a.capacity or (used == 0 and need > a.capacity):
                gh("workflow", "run", wf, "-R", REPO, "--ref", "main", "-f", f"key={k}")
                print(f"{time.strftime('%H:%M:%S')} dispatched {k} ({wf}, {need} jobs); {used + need}/{a.capacity} in use", flush=True)
                pending.remove(k)
                used += need
                time.sleep(8)  # the run appears in the listing
        if pending:
            time.sleep(120)
    if pending:
        print(f"deadline: handing {len(pending)} libraries to a fresh copy", flush=True)
        if a.dispatch_self:
            gh("workflow", "run", "bump-all.yml", "-R", REPO, "--ref", "main", "-f", f"keys={' '.join(pending)}", "-f", f"capacity={a.capacity}")
    else:
        print("every library has been dispatched", flush=True)


if __name__ == "__main__":
    main()
