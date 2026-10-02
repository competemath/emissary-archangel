#!/usr/bin/env python3
"""mine_moves.py OLD_REV NEW_REV [--out moves.json] — which Mathlib modules were moved, split or merged between two revisions.

Mathlib.lean lists every module of Mathlib, one `import` per line, so each commit that adds, removes, renames, splits or
merges a module changes that file by exactly the module names involved. Walking those commits (GitHub's commits API, no
clone) gives, per commit, the modules removed R and added A:
  |R| = 1, |A| = 1   a move (a rename)
  |R| = 1, |A| > 1   a split: the old module's content now lives in the A modules; importing all of A re-provides it
  |R| > 1, |A| = 1   a merge: the one new module provides all of R
  otherwise          a reshuffle: each removed module maps to the whole of A (a safe superset)
Chains compose (A moved in June, then again in July): the map is resolved to modules that exist at NEW_REV, and a
module that was removed outright (deleted, nothing added) maps to [].

The mapping only says where the CONTENT went. Importing the targets in place of the dead import changes what is in scope
(never less than before); whether any statement then elaborates differently is Gate 2's job, not this script's.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys

M = "leanprover-community/mathlib4"
IMPORT = re.compile(r"^([+-])(?:public )?import (Mathlib\.[\w.«»]+)\s*$")


def gh(path: str):
    r = subprocess.run(["gh", "api", path], capture_output=True, text=True)
    if r.returncode:
        sys.exit(f"gh api {path}: {r.stderr.strip()[:200]}")
    return json.loads(r.stdout)


def commit_info(rev: str) -> tuple[str, str]:
    c = gh(f"repos/{M}/commits/{rev}")
    return c["sha"], c["commit"]["committer"]["date"]


def mine(old_rev: str, new_rev: str) -> dict:
    old_sha, since = commit_info(old_rev)
    new_sha, until = commit_info(new_rev)
    shas: list[str] = []
    page = 1
    while True:
        batch = gh(f"repos/{M}/commits?path=Mathlib.lean&since={since}&until={until}&per_page=100&page={page}")
        if not batch:
            break
        shas += [c["sha"] for c in batch]
        page += 1
    events = []  # oldest first
    for sha in reversed(shas):
        c = gh(f"repos/{M}/commits/{sha}")
        for f in c.get("files", []):
            if f["filename"] != "Mathlib.lean":
                continue
            removed, added = [], []
            for line in (f.get("patch") or "").splitlines():
                m = IMPORT.match(line)
                if m:
                    (removed if m.group(1) == "-" else added).append(m.group(2))
            # a module whose line only moved within Mathlib.lean (re-sorting) is in both lists: neither added nor removed
            both = set(removed) & set(added)
            removed, added = [x for x in removed if x not in both], [x for x in added if x not in both]
            if removed or added:
                events.append({"sha": sha[:9], "parent": c["parents"][0]["sha"], "date": c["commit"]["committer"]["date"][:10], "removed": removed, "added": added})
    # compose, oldest first: the content of a removed module goes to what was added; later moves of those move it on
    moved: dict[str, list[str]] = {}
    for e in events:
        r, a = e["removed"], e["added"]
        if not r:
            continue
        # a module that was ADDED earlier in the window and removed now is not an old module: re-point what pointed at it
        for old, targets in list(moved.items()):
            if any(t in r for t in targets):
                moved[old] = sorted({t for t in targets if t not in r} | set(a))
        for x in r:
            if x not in moved and not any(x in t for t in moved.values()):
                moved[x] = sorted(a)
    exists_new = existing_modules(new_sha)
    # A module removed with nothing added in the same commit was usually a DEPRECATED STUB: Mathlib keeps a tiny file at
    # the old path for months, importing the new location, then deletes it ("delete deprecated modules"). What the
    # stub imported, read from the commit before its deletion, is where the content lives.
    removed_at = {}
    for e in events:
        for x in e["removed"]:
            removed_at.setdefault(x, e)
    stubs = 0
    for old, ts in list(moved.items()):
        if ts or old in exists_new:
            continue
        e = removed_at.get(old)
        if not e:
            continue
        path = old.replace(".", "/") + ".lean"
        r = subprocess.run(["gh", "api", f"repos/{M}/contents/{path}?ref={e['parent']}", "--jq", ".content"], capture_output=True, text=True)
        if r.returncode:
            continue
        import base64

        text = base64.b64decode(r.stdout.strip()).decode(errors="replace")
        targets = [m.group(1) for m in re.finditer(r"^(?:public )?import (Mathlib\.[\w.«»]+)", text, re.M) if "DeprecatedModule" not in m.group(1)]
        if targets and len(text.splitlines()) < 40:  # a stub: a header, imports and a deprecated_module line
            moved[old] = sorted(set(targets))
            stubs += 1
    # follow chains: a stub's target may itself have moved on
    for _ in range(5):
        for old, ts in moved.items():
            moved[old] = sorted({u for t in ts for u in (moved[t] if t in moved and t not in exists_new else [t])})
    resolved = {old: [t for t in ts if t in exists_new] for old, ts in moved.items() if old not in exists_new}
    return {"old": old_sha, "new": new_sha, "commits_changing_Mathlib.lean": len(events), "stubs_read": stubs, "moves": resolved}


def existing_modules(sha: str) -> set[str]:
    import base64

    c = gh(f"repos/{M}/contents/Mathlib.lean?ref={sha}")
    text = base64.b64decode(c["content"]).decode()
    return {m.group(1) for m in re.finditer(r"^(?:public )?import (Mathlib\.[\w.«»]+)", text, re.M)}


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("old_rev")
    ap.add_argument("new_rev")
    ap.add_argument("--out", default="moves.json")
    a = ap.parse_args()
    res = mine(a.old_rev, a.new_rev)
    json.dump(res, open(a.out, "w"), indent=1)
    n = res["moves"]
    print(f"{res['commits_changing_Mathlib.lean']} module-list commits, {len(n)} modules gone at {a.new_rev}: "
          f"{sum(1 for v in n.values() if len(v) == 1)} moved/merged, {sum(1 for v in n.values() if len(v) > 1)} split, {sum(1 for v in n.values() if not v)} removed outright")
