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
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable

sys.path.insert(0, str(Path(__file__).resolve().parent))
from intake_open import BRANCH  # noqa: E402

POLL = 120  # seconds between looks: the queue takes ~40 minutes or more per part, so two minutes is nothing next to it
TRIES = 5  # a look that fails (an API hiccup) is tried again this many times before the wait gives up and leaves it to the schedule


def lane(rows: list[dict]) -> list[dict]:
    return [r for r in rows if BRANCH.match(r.get("headRefName", ""))]


def lane_open(rows: list[dict]) -> set[int]:
    """the numbers of the open pull requests of the intake lane, from `gh pr list --state all --json number,headRefName,state,closedAt`"""
    return {r["number"] for r in lane(rows) if r.get("state", "OPEN") == "OPEN"}


def closed_since(rows: list[dict], since: datetime | None) -> list[int]:
    """the lane's pull requests merged or closed at or after `since` (the start of the opener run that started this wait): a part that merged between that run's look and this
    wait's first look is no longer open when the wait starts, and the change would be missed (cubic, #172)"""
    if since is None:
        return []
    return sorted(r["number"] for r in lane(rows) if r.get("state") in ("MERGED", "CLOSED") and r.get("closedAt") and parse_time(r["closedAt"]) >= since)


def parse_time(s: str) -> datetime:
    t = datetime.fromisoformat(s.replace("Z", "+00:00"))
    if t.tzinfo is None:
        raise ValueError(f"a time without a zone: {s}")
    return t


def wait(fetch: Callable[[], list[dict]], sleep: Callable[[float], None], clock: Callable[[], float], deadline_s: float, poll: float = POLL,
         since: datetime | None = None) -> tuple[str, list[int]]:
    """("changed", the numbers no longer open) when a lane pull request merged or closed since `since` or during the wait; ("none", []) when nothing of the lane is open and
    nothing closed since `since`; ("deadline", the numbers still open) when the time ran out first; ("blind", []) when GitHub could not be read TRIES times in a row (the
    schedule is left to it)."""
    end = clock() + deadline_s

    def look() -> list[dict] | None:
        for _ in range(TRIES):
            try:
                return fetch()
            except Exception:  # noqa: BLE001 - any failure to read is a failure to read: wait and try again
                if clock() + poll >= end:
                    return None
                sleep(poll)
        return None

    rows = look()
    if rows is None:
        return "blind", []
    already = closed_since(rows, since)
    if already:
        return "changed", already
    first = lane_open(rows)
    if not first:
        return "none", []
    while clock() < end:
        sleep(min(poll, end - clock()))  # the last look comes at the deadline itself, not up to a poll before it (cubic, #172)
        rows = look()
        if rows is None:
            return "blind", []
        gone = first - lane_open(rows)
        if gone:
            return "changed", sorted(gone)
    return "deadline", sorted(first)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--target", default="competemath/tengoku")
    ap.add_argument("--repo", default="competemath/emissary-archangel", help="this repository: where the opener and this wait run")
    ap.add_argument("--deadline-min", type=float, default=330)
    ap.add_argument("--since", default="", help="when the opener run that started this wait began (ISO 8601 with a zone): a part merged after it counts as a change")
    a = ap.parse_args()
    since = parse_time(a.since) if a.since else None

    def fetch() -> list[dict]:
        # open ones, and the recently closed ones for `since`: the newest 200 pull requests of every state (the lane opens at most LANE_MAX_OPEN at once)
        out = subprocess.run(["gh", "pr", "list", "-R", a.target, "--state", "all", "-L", "200", "--json", "number,headRefName,state,closedAt"], check=True, capture_output=True, text=True, timeout=120)
        return json.loads(out.stdout)

    what, prs = wait(fetch, time.sleep, time.monotonic, a.deadline_min * 60, since=since)
    if what == "changed":
        print(f"no longer open: {', '.join(f'#{n}' for n in prs)}: the opener is started")
        # `automatic=true`: the opener runs only while the lane is switched on (LANE_ENABLED), as its schedule does; a person's dispatch is not held by the switch (cubic, #172)
        subprocess.run(["gh", "workflow", "run", "intake-open.yml", "-R", a.repo, "--ref", "main", "-f", f"target={a.target}", "-f", "dry_run=false", "-f", "automatic=true"], check=True)
    elif what == "deadline":
        now = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
        print(f"still open after {a.deadline_min:g} minutes: {', '.join(f'#{n}' for n in prs)}: this wait is started again")
        subprocess.run(["gh", "workflow", "run", "intake-next.yml", "-R", a.repo, "--ref", "main", "-f", f"since={now}"], check=True)
    elif what == "blind":
        print("::warning::the target's pull requests could not be read: the opener's schedule takes over")
    else:
        print("nothing of the intake lane is open: nothing to wait for")
    return 0


if __name__ == "__main__":
    sys.exit(main())
