#!/usr/bin/env python3
"""A library whose setup has finished gets its bump: bump_pickup.py [--dry-run] (the hourly bump-pickup.yml). Until now a person started every bump by hand after the setup.

One library per run, the smallest first, so that runners stay free. A setup is picked up once: any bump started after it, finished or not, counts as its bump, so a bump that failed is looked at by a
person and never started again by this. Left alone: a library with a part open on the tree (a new cut would renumber the parts, 13 Oct 2026, tengoku #546), one that exported nothing, one too big for a
plain bump (flt-anthropic has its build-once lane), and every setup from before this existed. Nothing starts unless NEED_FREE of the org's 20 runners are free, and those free runners set `parallel`.
Only a commit the setup jobs write counts as a setup, so a change across the setup records can never start a bump.
The bump reads the library's records from where the tree holds them (tree_records.py): main, or the branch of its open records pull request; a library whose records are neither is left
(rankamplificationtotient, 13 Nov 2026: its bump read main before its records were merged, found none and failed)."""

import argparse
import json
import os
import re
import subprocess
import time
from datetime import UTC, datetime
from pathlib import Path

SETUP_COMMIT = re.compile(r"^exports: ([A-Za-z0-9_.-]+) \((?:sharded )?runner\)$")
FIRST_SETUP = 1794211200  # 2026-11-09 08:00 UTC: older setups were bumped by hand, or left unbumped on purpose
RUNNERS, NEED_FREE, MAX_MODULES = 20, 10, 10000
WINDOW_DAYS = 14  # a setup waits this long at most: the runs that say whether it was bumped can then always be read in full
LIST_LIMIT = 1000  # the most runs GitHub lists for a date range: a list that long may have lost some, and a run it lost could be a setup's bump
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
        if len(words) >= 2 and words[0] in ("bump", "bump-sharded"):  # bump-library.yml and bump-sharded.yml
            out[words[1]] = max(out.get(words[1], 0), _epoch(r["createdAt"]))
    return out


def open_parts(titles: list[str]) -> set[str]:
    return {m.group(1) for t in titles if (m := re.match(r"^(?:intake|extend): (\S+) part ", t))}


def parallel_for(free: int) -> int:
    """half of what is free above four kept for the tree's own CI, three to six shards at once"""
    return min(6, max(3, (free - 4) // 2))


def window_start(now: int) -> int:
    return max(FIRST_SETUP, now - WINDOW_DAYS * 86400)


def classify(
    published: dict[str, int], records: dict[str, dict], bumps: dict[str, int], parts: set[str], since: int = FIRST_SETUP, refs: dict[str, tuple[str | None, str]] | None = None
) -> tuple[list[str], list[tuple[int, str]]]:
    """(why each library is left, the ready ones as (modules, key)); `refs` (tree_records.records_ref of each, when given): a library whose records the tree holds nowhere to trust is left"""
    notes, ready = [], []
    for key, when in sorted(published.items()):
        rec = records.get(key)
        if when < since:
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
        elif refs is not None and refs.get(key, (None, "records not looked for"))[0] is None:
            notes.append(f"{key}: {refs.get(key, (None, 'records not looked for'))[1]}")
        else:
            ready.append((rec["modules"], key))
    return notes, ready


def waits_for_runners(key: str | None, ready: int, free: int) -> bool:
    """Nothing started although a library is ready, and the runners are the only reason (decide starts the first with NEED_FREE free): worth looking again soon, from the numbers and not from the words of the notes."""
    return key is None and ready > 0 and free < NEED_FREE


def decide(
    published: dict[str, int], records: dict[str, dict], bumps: dict[str, int], parts: set[str], free: int, since: int = FIRST_SETUP, refs: dict[str, tuple[str | None, str]] | None = None
) -> tuple[str | None, list[str]]:
    """(the library to bump or None, why each other one is left)"""
    notes, ready = classify(published, records, bumps, parts, since, refs)
    if ready and free < NEED_FREE:
        notes.append(f"{len(ready)} ready, {free} runners free of the {NEED_FREE} needed: next hour")
        return None, notes
    ready.sort()
    return (ready[0][1] if ready else None), notes + [f"{k}: waits for the next run" for _, k in ready[1:]]


def dispatch_args(key: str, free: int, repo: str, ref: str = "") -> list[str]:
    """the standard bump; `ref`: the tree branch that holds the library's records when they are not on main"""
    args = ["gh", "workflow", "run", "bump-sharded.yml", "-R", repo, "--ref", "main", "-f", f"key={key}", "-f", f"parallel={parallel_for(free)}"]
    for k, v in BUMP.items():
        args += ["-f", f"{k}={v}"]
    if ref:
        import tree_records as tr

        if not tr.BRANCH.match(ref):
            raise ValueError(f"not a branch name: {ref!r}")
        args += ["-f", f"tengoku_ref={ref}"]
    return args


def _lines(*args: str) -> list:
    """gh, one JSON value per line of its answer (--paginate --jq writes a line per item, whatever the number of pages)"""
    out = subprocess.run(["gh", *args], check=True, capture_output=True, text=True).stdout
    return [json.loads(ln) for ln in out.splitlines() if ln.strip()]


def runners_in_use(gh=_lines, skip_run: str | None = None, skip_repo: str | None = None) -> int:
    """Jobs running or queued in the org's repositories, not counting the run that is asking (a pickup's own job holds a runner it does not
    take from anyone else: counted, it made 10 free look like 9 and the pickup waited for 11; 13 Nov 2026). The asking run is GITHUB_RUN_ID of
    GITHUB_REPOSITORY: a run id is unique only within its repository (cubic on #192), so a run of another repository with the same number still counts."""
    skip = str(os.environ.get("GITHUB_RUN_ID", "") if skip_run is None else skip_run)
    skip_repo = os.environ.get("GITHUB_REPOSITORY", "") if skip_repo is None else skip_repo
    used = 0
    for repo in REPOS:
        for status in ("in_progress", "queued"):
            for run in gh("api", "--paginate", f"repos/{repo}/actions/runs?status={status}&per_page=100", "--jq", ".workflow_runs[].id"):
                if skip and str(run) == skip and (not skip_repo or repo == skip_repo):
                    continue
                used += sum(gh("api", "--paginate", f"repos/{repo}/actions/runs/{run}/jobs?per_page=100", "--jq", '[.jobs[] | select(.status == "in_progress" or .status == "queued")] | length'))
    return used


def bump_runs(repo: str, since: int, gh=_lines) -> list[dict]:
    """every run of the two bump workflows since `since`; a list so long that some may be missing stops the pickup instead of starting a bump twice"""
    day = datetime.fromtimestamp(since, UTC).strftime("%Y-%m-%dT%H:%M:%SZ")
    runs: list[dict] = []
    for wf in ("bump-sharded.yml", "bump-library.yml"):
        got = gh("api", "--paginate", f"repos/{repo}/actions/workflows/{wf}/runs?per_page=100&created=>={day}", "--jq", ".workflow_runs[] | {displayTitle: .display_title, createdAt: .created_at}")
        if len(got) >= LIST_LIMIT:
            raise RuntimeError(f"{wf}: {len(got)} runs since {day}: the list may be cut short")
        runs += got
    return runs


def open_titles(tree: str, gh=_lines) -> list[str]:
    got = gh("pr", "list", "-R", tree, "--state", "open", "-L", str(LIST_LIMIT), "--json", "title", "--jq", ".[].title | @json")
    if len(got) >= LIST_LIMIT:
        raise RuntimeError(f"{tree}: {len(got)} open pull requests: the list may be cut short")
    return got


POLL_SECONDS = 300  # how often a waiting pickup looks at the runners again (setup_pickup.py has the same)


def once(a, log=print) -> tuple[str | None, bool]:
    """One look: the library whose bump starts now (started unless a dry run), and whether only the runners hold a ready library back."""
    text = subprocess.run(["git", "log", "--format=@%ct%x09%s", "--name-only", "--", "data/exports/*/setup.ci.json"], check=True, capture_output=True, text=True).stdout
    published = setups(text)
    records = {}
    for key in published:
        p = Path("data/exports") / key / "setup.ci.json"
        if p.exists():
            r = json.loads(p.read_text(encoding="utf-8"))
            records[key] = {"exported": int(r.get("exported") or 0), "modules": len(r["modules"]) if isinstance(r.get("modules"), list) else int(r.get("modules") or 0)}
    since = window_start(int(time.time()))
    runs = bump_runs(a.repo, since)
    bumps = last_bumps(runs)
    free = max(0, RUNNERS - runners_in_use())
    import tree_records as tr

    waiting = [k for k, w in published.items() if w >= since and bumps.get(k, 0) < w]
    refs: dict[str, tuple[str | None, str]] = {}
    if waiting:
        sources = json.loads(Path("sources.json").read_text(encoding="utf-8"))["sources"]
        prs = tr.records_prs(a.tree)
        for k in waiting:
            if k not in sources:
                refs[k] = (None, "no longer in sources.json")
                continue
            refs[k] = tr.records_ref(k, sources[k], tr.main_files(a.tree, k, sources[k]), prs, a.tree)
    parts = open_parts(open_titles(a.tree))
    key, notes = decide(published, records, bumps, parts, free, since, refs)
    for n in notes:
        log(n)
    ref = refs[key][0] if key else ""
    log(f"{free} runners free; bump: {key or 'none'}" + (f" (tengoku_ref={ref or 'main'})" if key else ""))
    if key and not a.dry_run:
        subprocess.run(dispatch_args(key, free, a.repo, ref or ""), check=True)
    ready = len(classify(published, records, bumps, parts, since, refs)[1])
    return key, waits_for_runners(key, ready, free)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default="competemath/emissary-archangel")
    ap.add_argument("--tree", default="competemath/tengoku")
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--wait-minutes", type=int, default=0, help="when only the runners hold a ready library back, look again every five minutes for this long")
    a = ap.parse_args()
    deadline = time.time() + 60 * a.wait_minutes
    first = True
    while True:
        try:
            key, waits = once(a)
        except Exception as e:  # noqa: BLE001 - a transient failure of gh at minute 30 must not end the wait; the first look failing is a real failure
            if first:
                raise
            print(f"this look failed ({type(e).__name__}: {e}); the next is in {POLL_SECONDS // 60} minutes")
            key, waits = None, True
        first = False
        if a.dry_run or not waits or time.time() + POLL_SECONDS > deadline:
            return
        time.sleep(POLL_SECONDS)


if __name__ == "__main__":
    main()
