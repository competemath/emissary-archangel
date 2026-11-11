#!/usr/bin/env python3
"""The opener again as soon as an intake pull request merges: intake_next.py --target competemath/tengoku (intake-next.yml).

A library in parts gets one part at a time: part N+1 opens when part N has merged (intake_open.py). The opener runs on a schedule that says every 10 minutes, but
GitHub ran it at 22:24, 00:21 and 02:04 and then not until 08:45 on 10-11 Nov 2026: aintlib's part 1 merged at 02:06 and part 2 waited six and a half hours for an
opener started by hand (run 42989534423). flt-anthropic's bundle will be cut into tens of parts, each waiting for the one before it.

This waits instead: it notes the lane's open pull requests (head branch intake/<key>-<run>[-part-NNN], intake_open.BRANCH), asks again every POLL seconds, and when
one of them is no longer open (merged, or closed by a person) it starts the opener, which opens whatever is now due, for every library. With nothing open it ends at
once. A wait that reaches its deadline starts itself again, so a pull request that takes longer than one job is still followed. It reads public pull requests and starts
two workflows of this repository: it opens, closes and merges nothing.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path
from typing import Callable

sys.path.insert(0, str(Path(__file__).resolve().parent))
from intake_open import BRANCH  # noqa: E402

POLL = 120  # seconds between looks: the queue takes ~40 minutes or more per part, so two minutes is nothing next to it
TRIES = 5  # a look that fails (an API hiccup) is tried again this many times before the wait gives up and leaves it to the schedule


def lane_open(rows: list[dict]) -> set[int]:
    """the numbers of the open pull requests of the intake lane, from `gh pr list --state open --json number,headRefName`"""
    return {r["number"] for r in rows if BRANCH.match(r.get("headRefName", ""))}


def wait(fetch: Callable[[], list[dict]], sleep: Callable[[float], None], clock: Callable[[], float], deadline_s: float, poll: float = POLL) -> tuple[str, list[int]]:
    """("none", []) when nothing of the lane is open; ("changed", the numbers no longer open) when one merged or closed; ("deadline", the numbers still open) when the
    time ran out first; ("blind", []) when GitHub could not be read TRIES times in a row (the schedule is left to it)."""
    end = clock() + deadline_s

    def look() -> set[int] | None:
        for _ in range(TRIES):
            try:
                return lane_open(fetch())
            except Exception:  # noqa: BLE001 - any failure to read is a failure to read: wait and try again
                if clock() + poll >= end:
                    return None
                sleep(poll)
        return None

    first = look()
    if first is None:
        return "blind", []
    if not first:
        return "none", []
    while clock() + poll < end:
        sleep(poll)
        now = look()
        if now is None:
            return "blind", []
        gone = first - now
        if gone:
            return "changed", sorted(gone)
    return "deadline", sorted(first)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--target", default="competemath/tengoku")
    ap.add_argument("--repo", default="competemath/emissary-archangel", help="this repository: where the opener and this wait run")
    ap.add_argument("--deadline-min", type=float, default=330)
    a = ap.parse_args()

    def fetch() -> list[dict]:
        out = subprocess.run(["gh", "pr", "list", "-R", a.target, "--state", "open", "-L", "500", "--json", "number,headRefName"], check=True, capture_output=True, text=True, timeout=120)
        return json.loads(out.stdout)

    what, prs = wait(fetch, time.sleep, time.monotonic, a.deadline_min * 60)
    if what == "changed":
        print(f"no longer open: {', '.join(f'#{n}' for n in prs)}: the opener is started")
        subprocess.run(["gh", "workflow", "run", "intake-open.yml", "-R", a.repo, "--ref", "main", "-f", f"target={a.target}", "-f", "dry_run=false"], check=True)
    elif what == "deadline":
        print(f"still open after {a.deadline_min:g} minutes: {', '.join(f'#{n}' for n in prs)}: this wait is started again")
        subprocess.run(["gh", "workflow", "run", "intake-next.yml", "-R", a.repo, "--ref", "main"], check=True)
    elif what == "blind":
        print("::warning::the target's pull requests could not be read: the opener's schedule takes over")
    else:
        print("nothing of the intake lane is open: nothing to wait for")
    return 0


if __name__ == "__main__":
    sys.exit(main())
