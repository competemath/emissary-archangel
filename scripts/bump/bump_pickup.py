#!/usr/bin/env python3
"""A library whose setup has finished gets its bump: bump_pickup.py [--dry-run] (the hourly bump-pickup.yml). Until now a person started every bump by hand after the setup.

One library per run, the smallest first, so that runners stay free. A setup is picked up once: any bump started after it, finished or not, counts as its bump, so a bump that failed is looked at by a
person and never started again by this. Left alone: a library with a part open on the tree (a new cut would renumber the parts, 13 Oct 2026, tengoku #546), one that exported nothing, one too big for a
plain bump (flt-anthropic has its build-once lane), and every setup from before this existed. Nothing starts unless NEED_FREE of the org's 20 runners are free, and those free runners set `parallel`.
Only a commit the setup jobs write counts as a setup, so a change across the setup records can never start a bump."""

import argparse
import json
import re
import subprocess
from datetime import datetime
from pathlib import Path

SETUP_COMMIT = re.compile(r"^exports: ([A-Za-z0-9_.-]+) \((?:sharded )?runner\)$")
FIRST_SETUP = 1794211200  # 2026-11-09 08:00 UTC: older setups were bumped by hand, or left unbumped on purpose
RUNNERS, NEED_FREE, MAX_MODULES = 20, 10, 10000
REPOS = ("competemath/tengoku", "competemath/emissary-archangel", "competemath/emissary-sandbox", "competemath/tengoku-sandbox")
BUMP = {"shards": "0", "max_targets": "400", "parts": "300", "imports": "faithful", "verify": "true", "verify_partial": "true", "verify_modes": "proposed"}


def setups(log: str) -> dict[str, int]:
    """library -> when its newest setup was published, from `git log --format=@%ct%x09%s --name-only -- 'data/exports/*/setup.ci.json'` (newest first)."""
    out: dict[str, int] = {}
    key, when = None, 0
    for line in log.splitlines():
        if line.startswith("@"):
            stamp, _, subject = line[1:].partition("\t")
            m = SETUP_COMMIT.match(subject)
            key, when = (m.group(1), int(stamp)) if m else (None, 0)
        elif key and line == f"data/exports/{key}/setup.ci.json":
            out.setdefault(key, when)
    return out


def _epoch(iso: str) -> int:
    return int(datetime.fromisoformat(iso.replace("Z", "+00:00")).timestamp())


def last_bumps(runs: list[dict]) -> dict[str, int]:
    """library -> when its newest bump started, from the runs of bump-sharded.yml, whatever became of them"""
    out: dict[str, int] = {}
    for r in runs:
        words = r["displayTitle"].split()
        if len(words) >= 2 and words[0] == "bump-sharded":
            out[words[1]] = max(out.get(words[1], 0), _epoch(r["createdAt"]))
    return out


def open_parts(titles: list[str]) -> set[str]:
    return {m.group(1) for t in titles if (m := re.match(r"^(?:intake|extend): (\S+) part ", t))}


def parallel_for(free: int) -> int:
    """half of what is free above four kept for the tree's own CI, three to six shards at once"""
    return min(6, max(3, (free - 4) // 2))


def decide(published: dict[str, int], records: dict[str, dict], bumps: dict[str, int], parts: set[str], free: int) -> tuple[str | None, list[str]]:
    """(the library to bump or None, why each other one is left)"""
    notes, ready = [], []
    for key, when in sorted(published.items()):
        rec = records.get(key)
        if when < FIRST_SETUP:
            continue
        if bumps.get(key, 0) >= when:
            continue
        if not rec:
            notes.append(f"{key}: no setup record")
        elif rec["exported"] < 1:
            notes.append(f"{key}: exported nothing")
        elif rec["modules"] > MAX_MODULES:
            notes.append(f"{key}: {rec['modules']} modules, too big for a plain bump")
        elif key in parts:
            notes.append(f"{key}: a part is open on the tree")
        else:
            ready.append((rec["modules"], key))
    if ready and free < NEED_FREE:
        notes.append(f"{len(ready)} ready, {free} runners free of the {NEED_FREE} needed: next hour")
        return None, notes
    ready.sort()
    return (ready[0][1] if ready else None), notes + [f"{k}: waits for the next run" for _, k in ready[1:]]


def dispatch_args(key: str, free: int, repo: str) -> list[str]:
    args = ["gh", "workflow", "run", "bump-sharded.yml", "-R", repo, "--ref", "main", "-f", f"key={key}", "-f", f"parallel={parallel_for(free)}"]
    for k, v in BUMP.items():
        args += ["-f", f"{k}={v}"]
    return args


def _gh(*args: str):
    return json.loads(subprocess.run(["gh", *args], check=True, capture_output=True, text=True).stdout)


def runners_in_use() -> int:
    used = 0
    for repo in REPOS:
        for status in ("in_progress", "queued"):
            for run in _gh("api", f"repos/{repo}/actions/runs?status={status}&per_page=100")["workflow_runs"]:
                jobs = _gh("api", f"repos/{repo}/actions/runs/{run['id']}/jobs?per_page=100")["jobs"]
                used += sum(j["status"] in ("in_progress", "queued") for j in jobs)
    return used


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default="competemath/emissary-archangel")
    ap.add_argument("--tree", default="competemath/tengoku")
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args()
    log = subprocess.run(["git", "log", "--format=@%ct%x09%s", "--name-only", "--", "data/exports/*/setup.ci.json"], check=True, capture_output=True, text=True).stdout
    published = setups(log)
    records = {}
    for key in published:
        p = Path("data/exports") / key / "setup.ci.json"
        if p.exists():
            r = json.loads(p.read_text(encoding="utf-8"))
            records[key] = {"exported": int(r.get("exported") or 0), "modules": len(r["modules"]) if isinstance(r.get("modules"), list) else int(r.get("modules") or 0)}
    runs = _gh("run", "list", "-R", a.repo, "-w", "bump-sharded.yml", "-L", "1000", "--json", "displayTitle,createdAt")
    titles = [p["title"] for p in _gh("pr", "list", "-R", a.tree, "--state", "open", "-L", "200", "--json", "title")]
    free = max(0, RUNNERS - runners_in_use())
    key, notes = decide(published, records, last_bumps(runs), open_parts(titles), free)
    for n in notes:
        print(n)
    print(f"{free} runners free; bump: {key or 'none'}")
    if key and not a.dry_run:
        subprocess.run(dispatch_args(key, free, a.repo), check=True)


if __name__ == "__main__":
    main()
