#!/usr/bin/env python3
"""A library newly registered in sources.json gets its setup: setup_pickup.py [--dry-run] (setup-pickup.yml, twice an hour and when sources.json changes on main). Until now a person started
setup-auto.yml by hand for every registered library (batch 6, 13 Nov 2026: four dispatches, each with the tree branch that held its records).

One library per run, the one registered first, so that runners stay free; its bump follows by itself (setup-sharded.yml and setup-libraries.yml start bump-pickup.yml when they finish). A library is
picked up once: any setup started after it was registered (setup-auto.yml unless it was a dry run, or setup-sharded.yml), finished or not, counts, so a setup that failed is looked at by a person and
never started again by this. Left alone: a library registered before FIRST_REGISTER (23 registered in September were left unset up on purpose or set up by other means), one registered more than
WINDOW_DAYS ago (its runs can no longer be read in full), one that already has a setup record, and one whose tentative records are neither on the tree's main nor in exactly one open `records:` pull
request from a branch of the tree repository itself (a fork's branch is never used). Nothing starts unless bump_pickup.NEED_FREE of the org's 20 runners are free.
Registered means the line `    "<key>": {` was added to sources.json by a commit; its time is the first such commit's."""

import argparse
import json
import re
import subprocess
import time
from pathlib import Path

import bump_pickup as bp
from tree_records import BRANCH, holds, main_files, setup_holds, records_prs, records_ref, tentative_files  # noqa: F401 (the tests use them through this module)

ENTRY = re.compile(r'^\+    "([a-z0-9][a-z0-9-]*)": \{$')
FIRST_REGISTER = 1794528000  # 2026-11-13 00:00 UTC
WINDOW_DAYS = 14
SETUP_TITLE = re.compile(r"^setup-(auto|sharded) ([a-z0-9][a-z0-9-]*) \((.*)\)$")
DRY_MARK = ", dry run"  # setup-auto.yml's run-name ends its parenthesis with this for a dry run


def registered(log: str) -> dict[str, int]:
    """key -> when its entry was first added, from `git log -p --reverse --format==%ct -- sources.json` (oldest first)"""
    out: dict[str, int] = {}
    when = 0
    for line in log.splitlines():
        if line.startswith("="):
            when = int(line[1:].split("\t", 1)[0])
        elif m := ENTRY.match(line):
            out.setdefault(m.group(1), when)
    return out


def _epoch(iso: str) -> int:
    return bp._epoch(iso)


def attempts(runs: list[dict]) -> dict[str, int]:
    """key -> when its newest real setup started, from the runs of setup-auto.yml and setup-sharded.yml"""
    out: dict[str, int] = {}
    for r in runs:
        m = SETUP_TITLE.match(r["displayTitle"])
        if not m or (m.group(1) == "auto" and m.group(3).endswith(DRY_MARK)):
            continue
        out[m.group(2)] = max(out.get(m.group(2), 0), _epoch(r["createdAt"]))
    return out


def window_start(now: int) -> int:
    return max(FIRST_REGISTER, now - WINDOW_DAYS * 86400)


def pending(reg: dict[str, int], sources: dict, set_up: set[str], tried: dict[str, int], since: int) -> list[str]:
    """registered in the window, still in sources.json, no setup record, no setup since it was registered: oldest first"""
    keys = [k for k, w in reg.items() if w >= since and k in sources and k not in set_up and tried.get(k, 0) < w]
    return sorted(keys, key=lambda k: (reg[k], k))


def decide(keys: list[str], refs: dict[str, tuple[str | None, str]], free: int) -> tuple[str | None, str | None, list[str]]:
    """(the library to set up or None, its tengoku_ref, why each other one is left)"""
    notes, ready = [], []
    for k in keys:
        ref, why = refs[k]
        if ref is None:
            notes.append(f"{k}: {why}")
        else:
            ready.append((k, ref))
    if ready and free < bp.NEED_FREE:
        notes.append(f"{len(ready)} ready, {free} runners free of the {bp.NEED_FREE} needed: next run")
        return None, None, notes
    if not ready:
        return None, None, notes
    return ready[0][0], ready[0][1], notes + [f"{k}: waits for the next run" for k, _ in ready[1:]]


def dispatch_args(key: str, ref: str, repo: str) -> list[str]:
    if ref and not BRANCH.match(ref):
        raise ValueError(f"not a branch name: {ref!r}")
    return ["gh", "workflow", "run", "setup-auto.yml", "-R", repo, "--ref", "main", "-f", f"key={key}", "-f", f"tengoku_ref={ref}"]


def setup_runs(repo: str, since: int, gh=bp._lines) -> list[dict]:
    """every run of the two setup workflows since `since`; a list so long that some may be missing stops the pickup instead of starting a setup twice"""
    day = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(since))
    runs: list[dict] = []
    for wf in ("setup-auto.yml", "setup-sharded.yml"):
        got = gh("api", "--paginate", f"repos/{repo}/actions/workflows/{wf}/runs?per_page=100&created=>={day}", "--jq", ".workflow_runs[] | {displayTitle: .display_title, createdAt: .created_at}")
        if len(got) >= bp.LIST_LIMIT:
            raise RuntimeError(f"{wf}: {len(got)} runs since {day}: the list may be cut short")
        runs += got
    return runs


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default="competemath/emissary-archangel")
    ap.add_argument("--tree", default="competemath/tengoku")
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args()
    log = subprocess.run(["git", "log", "-p", "--reverse", "--format==%ct", "--", "sources.json"], check=True, capture_output=True, text=True).stdout
    sources = json.loads(Path("sources.json").read_text(encoding="utf-8"))["sources"]
    reg = registered(log)
    since = window_start(int(time.time()))
    set_up = {k for k in sources if (Path("data/exports") / k / "setup.ci.json").exists()}
    keys = pending(reg, sources, set_up, attempts(setup_runs(a.repo, since)), since)
    refs: dict[str, tuple[str | None, str]] = {}
    if keys:
        prs = records_prs(a.tree)
        for k in keys:
            refs[k] = records_ref(k, sources[k], main_files(a.tree, k, sources[k]), prs, a.tree, rule=setup_holds)
    free = max(0, bp.RUNNERS - bp.runners_in_use()) if keys else 0
    key, ref, notes = decide(keys, refs, free)
    for n in notes:
        print(n)
    print(f"{len(keys)} registered and not set up; setup: {key or 'none'}" + (f" (tengoku_ref={ref or 'main'})" if key else ""))
    if key and not a.dry_run:
        subprocess.run(dispatch_args(key, ref or "", a.repo), check=True)


if __name__ == "__main__":
    main()
