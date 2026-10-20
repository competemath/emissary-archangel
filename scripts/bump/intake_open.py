#!/usr/bin/env python3
"""intake_open.py — open the next intake / extend PRs of the factory's finished bundles. Runs in GitHub Actions (intake-open.yml), as the intake App.

  intake_open.py [--target competemath/tengoku] [--max-open 80] [--daily-cap 400] [--per-tick 12] [--pace 90] [--keys "a b"] [--auto-merge] [--dry-run]

State is what GitHub says and nothing else: the factory's successful bump runs (bundles are kept 3 days) and the PR branches `intake/<key>-<run>[-part-NNN]` of the target.
For every library with a finished bundle:
  * one open PR per library at a time;
  * part 1 opens when the library has no PR that merged; part N+1 opens when part N is merged (`Depends-On`), from the SAME run (a later run needs a recut from the tree);
  * a library whose last part merged, a library that arrived as one unparted bundle, a library that is in the tree without an intake (seeded, hand-made), and a PR closed without merging for this run are left alone;
  * a bundle with no verified theorem is refused by open_intake_pr.py and costs nothing but the attempt.
How many it opens in one tick is the smallest of: room under --max-open open PRs, what is left of --daily-cap for the last 24 hours (counted from the App's own PRs), --per-tick.
The pace between two PRs is --pace seconds (GitHub flagged a bot account that opened 38 in minutes). `--auto-merge` arms the merge queue on EXTEND parts; `--auto-merge-first` on a first part too (the user's call, 2026-10-10: automate it all; a first part adds a line to
Tengoku/All.lean, which CODEOWNERS no longer owns, and the gates decide who may edit it). Whether the lane is on at all is the workflow's switch (the repository variable LANE_ENABLED).
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time
from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from open_intake_pr import pascal  # noqa: E402

FACTORY = "competemath/emissary-archangel"
TARGET = "competemath/tengoku"
BRANCH = re.compile(r"^intake/(?P<key>.+)-(?P<run>\d{9,})(?:-part-(?P<part>\d+))?$")
RUN_TITLE = re.compile(r"^bump(?:-sharded)? (?P<key>\S+?)(?P<tree> \(from tree\))?$")  # a recut that continues after what the tree has says so in its title (bump-sharded.yml, bump-library.yml)
OF_TOTAL = re.compile(r"part (\d+) of (\d+)")
KEEP = timedelta(hours=72)  # the factory's artifacts are kept 3 days


@dataclass(frozen=True)
class Pr:
    number: int
    state: str  # OPEN | CLOSED | MERGED
    key: str
    run: int
    part: int
    title: str
    parted: bool = True  # the branch has `-part-NNN`: the library was cut into parts; an older bundle is a single `intake/<key>-<run>`


def parse_prs(rows: list[dict]) -> dict[str, list[Pr]]:
    """The intake PRs of the target by library, from `gh pr list --json number,state,headRefName,title`."""
    out: dict[str, list[Pr]] = {}
    for r in rows:
        m = BRANCH.match(r["headRefName"])
        if m:
            out.setdefault(m["key"], []).append(Pr(r["number"], r["state"], m["key"], int(m["run"]), int(m["part"] or 1), r.get("title", ""), bool(m["part"])))
    return out


def newest_bundles(rows: list[dict], now: datetime) -> dict[str, tuple[int, str, bool]]:
    """key -> (run id, created, from_tree) of the newest successful bump run of each library whose artifacts are still kept; `rows` are `gh run list --json databaseId,displayTitle,conclusion,createdAt`.
    from_tree: the run is a recut whose parts continue after the parts the tree already has."""
    best: dict[str, tuple[int, str, bool]] = {}
    for r in rows:
        m = RUN_TITLE.match(r["displayTitle"])
        if not m or r["conclusion"] != "success":
            continue
        if now - datetime.fromisoformat(r["createdAt"].replace("Z", "+00:00")) > KEEP:
            continue
        if m["key"] not in best or r["createdAt"] > best[m["key"]][1]:
            best[m["key"]] = (r["databaseId"], r["createdAt"], bool(m["tree"]))
    return best


def last_part_merged(merged: list[Pr]) -> bool:
    t = OF_TOTAL.search(merged[-1].title)
    return bool(t) and int(t.group(1)) >= int(t.group(2))


def parts_still_owed(mine: list[Pr]) -> bool:
    """the last merged part's title says 'part N of M' with N < M: parts are expected, a missing archive is then a failure"""
    merged = sorted((p for p in mine if p.state == "MERGED"), key=lambda p: p.part)
    t = OF_TOTAL.search(merged[-1].title) if merged else None
    return bool(t) and int(t.group(1)) < int(t.group(2))


def decide(mine: list[Pr], run: int | None, unmanaged_in_tree: bool, from_tree: bool = False, tree_last: int | None = None) -> tuple[str, str | dict]:
    """("open", {part, run, depends_on}) or ("skip", why) for one library. `from_tree`: the newest run is a recut cut from the tree, so its parts start at the next number and replace the old run's.
    `tree_last`: the highest part number the tree itself has (data/intake/<key>/parts/NNN.json). A recut is numbered from the tree, not from the pull requests: after a raze the old
    pull requests carry numbers the tree has forgotten (navier-stokes-euler, 2026-10-20: part 5 of an old run merged, the tree restarted at 001/002, the recut cut part 003 and the opener
    asked for part 6: 'the run has no part 6')."""
    if any(p.state == "OPEN" for p in mine):
        return "skip", "a pull request of this library is open"
    merged = sorted((p for p in mine if p.state == "MERGED"), key=lambda p: p.part)
    # the merged part says 'part N of N' for the run it came from. A recut cut from the tree after it (`from_tree`, a newer run) has parts after N (lean-pool, 2026-10-19: part 14 of 14 merged, and the
    # dups recut cut part 15): they are not behind the library's end. The run that has no such part is still found out when the part is opened ('the run has no part N: every part of it is in the tree').
    if merged and last_part_merged(merged) and not (from_tree and merged[-1].run != run):
        return "skip", "every part is in the tree"
    if merged and not merged[-1].parted and not OF_TOTAL.search(merged[-1].title):
        return "skip", "the library arrived as one bundle, not in parts: nothing follows it"  # leaninfotheory: 'part 2' of a run that has no part archives, every 10 minutes
    if run is None:
        return "skip", "no finished bundle"
    if not merged and unmanaged_in_tree:
        return "skip", "in the tree without an intake"
    nxt = merged[-1].part + 1 if merged else 1
    depends = f"#{merged[-1].number}" if merged else None
    if from_tree and tree_last is not None and merged:
        nxt = tree_last + 1
        depends = f"#{max(merged, key=lambda p: p.number).number}"  # the newest merged part: the tree's last
    if merged and merged[-1].run != run and not from_tree:
        return "skip", f"part {nxt} would come from run {run}, but part {merged[-1].part} merged from run {merged[-1].run}: needs a recut from the tree"
    if any(p.state == "CLOSED" and p.run == run and p.part == nxt for p in mine):
        return "skip", "closed without merging for this run: a person decides, or a newer run comes"
    return "open", {"part": nxt, "run": run, "depends_on": depends}


def budget(open_now: int, opened_24h: int, max_open: int, daily_cap: int, per_tick: int) -> int:
    return max(0, min(max_open - open_now, daily_cap - opened_24h, per_tick))


class Gh:
    """The calls that touch GitHub, in one place so a test can replace them."""

    def __init__(self, target: str, factory: str, author: str):
        self.target, self.factory, self.author = target, factory, author

    @staticmethod
    def run(*a: str) -> subprocess.CompletedProcess:
        return subprocess.run(["gh", *a], capture_output=True, text=True)

    def json(self, *a: str):
        r = self.run(*a)
        if r.returncode:
            raise RuntimeError(f"gh {' '.join(a)}: {r.stderr.strip()[:300]}")
        return json.loads(r.stdout)

    def prs(self) -> list[dict]:
        return self.json("pr", "list", "-R", self.target, "--state", "all", "--limit", "2000", "--json", "number,state,headRefName,title")

    def runs(self) -> list[dict]:
        rows: list[dict] = []
        for wf in ("bump-library.yml", "bump-sharded.yml"):
            rows += self.json("run", "list", "-R", self.factory, "--workflow", wf, "--status", "success", "--limit", "200", "--json", "databaseId,displayTitle,conclusion,createdAt")
        return rows

    def opened_since(self, since: datetime) -> int:
        q = f"author:{self.author} created:>={since.strftime('%Y-%m-%dT%H:%M:%SZ')}"
        return len(self.json("pr", "list", "-R", self.target, "--state", "all", "--search", q, "--limit", "1000", "--json", "number"))

    def exists(self, path: str) -> bool:
        r = self.run("api", f"repos/{self.target}/contents/{path}?ref=main", "--silent")
        if r.returncode == 0:
            return True
        if "404" in r.stderr:
            return False
        raise RuntimeError(f"gh api contents/{path}: {r.stderr.strip()[:300]}")

    def tree_last_part(self, key: str) -> int | None:
        """The highest part number in the tree's data/intake/<key>/parts, or None when there is none (a library that came in one bundle, or is not there)."""
        r = self.run("api", f"repos/{self.target}/contents/data/intake/{key}/parts?ref=main", "--jq", "[.[].name]")
        if r.returncode:
            if "404" in r.stderr:
                return None
            raise RuntimeError(f"gh api contents/data/intake/{key}/parts: {r.stderr.strip()[:300]}")
        nums = [int(m.group(1)) for n in json.loads(r.stdout or "[]") if (m := re.fullmatch(r"(\d+)\.json", n))]
        return max(nums) if nums else None

    def unmanaged_in_tree(self, key: str) -> bool:
        return self.exists(f"Tengoku/{pascal(key)}") and not self.exists(f"data/intake/{key}/manifest.jsonl")


def open_pr(target: str, key: str, act: dict, auto_merge: bool, auto_first: bool = False) -> subprocess.CompletedProcess:
    cmd = [sys.executable, str(Path(__file__).with_name("open_intake_pr.py")), "--key", key, "--run", str(act["run"]), "--repo", target, "--mode", "proposed", "--part", str(act["part"])]
    if act["depends_on"]:
        cmd += ["--depends-on", act["depends_on"]]
    env = None
    if auto_merge and (act["depends_on"] or auto_first):  # a first part only when the lane says so: LANE_AUTOMERGE_FIRST
        cmd += ["--auto-merge"]
        if auto_first:
            env = {**os.environ, "LANE_AUTOMERGE_FIRST": "true"}
    return subprocess.run(cmd, capture_output=True, text=True, env=env)


def tick(a: argparse.Namespace, gh: Gh, opener=open_pr, sleep=time.sleep, now: datetime | None = None) -> dict:
    now = now or datetime.now(timezone.utc)
    by_key = parse_prs(gh.prs())
    open_now = sum(1 for ps in by_key.values() for p in ps if p.state == "OPEN")
    room = budget(open_now, gh.opened_since(now - timedelta(hours=24)), a.max_open, a.daily_cap, a.per_tick)
    print(f"open intake/extend PRs: {open_now}; this tick opens at most {room} (max-open {a.max_open}, daily cap {a.daily_cap}, per tick {a.per_tick})")
    bundles = newest_bundles(gh.runs(), now)
    wanted = set(a.keys.split()) if a.keys else None
    opened, skipped, failed = [], {}, []
    for key, (run, _, from_tree) in sorted(bundles.items(), key=lambda kv: kv[1][1]):  # oldest bundle first: they expire first
        if wanted is not None and key not in wanted:
            continue
        if len(opened) >= room:
            break
        mine = by_key.get(key, [])
        unmanaged = not mine and gh.unmanaged_in_tree(key)
        verdict, what = decide(mine, run, unmanaged, from_tree, gh.tree_last_part(key) if from_tree else None)
        if verdict == "skip":
            skipped[key] = str(what)
            continue
        assert isinstance(what, dict)
        line = f"{key} part {what['part']} from run {what['run']}" + (f" (after {what['depends_on']})" if what["depends_on"] else "")
        if a.dry_run:
            print("DRY", line)
            opened.append(key)
            continue
        r = opener(a.target, key, what, a.auto_merge, a.auto_merge_first)
        tail = (r.stdout.strip().splitlines() or [""])[-1]
        if r.returncode == 0:
            print("opened", line, "->", tail)
            opened.append(key)
            if len(opened) < room:
                sleep(a.pace)
        elif "EMPTY BUNDLE" in r.stderr:
            skipped[key] = "no verified theorem in the bundle"
        elif what["depends_on"] and "has no archive" in r.stderr and not parts_still_owed(mine):
            # a recut from the tree names no total ('part 13', not 'part 13 of 14'): after its last part there is no archive for the next number. That is the end of the library, not a failure
            # (2026-10-18: lean-pool 'part 14' of a run that had only part 13 failed every run of this workflow for a day)
            skipped[key] = f"the run has no part {what['part']}: every part of it is in the tree"
        else:
            print("FAILED", line, "::", (r.stderr.strip().splitlines() or ["?"])[-1][:300])
            failed.append(key)
    return {"opened": opened, "skipped": skipped, "failed": failed}


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--target", default=TARGET)
    ap.add_argument("--factory", default=FACTORY)
    ap.add_argument("--author", default="app/tengoku-intake", help="the App's login in a search: the daily cap counts its PRs")
    ap.add_argument("--max-open", type=int, default=80)
    ap.add_argument("--daily-cap", type=int, default=400)
    ap.add_argument("--per-tick", type=int, default=12)
    ap.add_argument("--pace", type=int, default=90)
    ap.add_argument("--keys", default="")
    ap.add_argument("--auto-merge", action="store_true")
    ap.add_argument("--auto-merge-first", action="store_true", help="also arm auto-merge on a library's FIRST part (LANE_AUTOMERGE_FIRST; needs Tengoku/All.lean unowned in CODEOWNERS)")
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args(argv)
    res = tick(a, Gh(a.target, a.factory, a.author))
    print(json.dumps(res, indent=1))
    return 1 if res["failed"] else 0


if __name__ == "__main__":
    sys.exit(main())
