#!/usr/bin/env python3
"""Where the tree holds a library's tentative records, for a setup or a bump started by a pickup (setup_pickup.py, bump_pickup.py): on its main, or on the branch of one open `records:` pull request of
the tree repository (a fork's branch is never used, nor one of several, nor one holding only some of the files). Until a library's records pull request is merged, a setup or bump that reads main
finds no record (rankamplificationtotient, 13 Nov 2026: bump-pickup started its bump on main, it planned no shard and failed at compose)."""

import re
import subprocess

import bump_pickup as bp

BRANCH = re.compile(r"^[A-Za-z0-9._/-]+$")  # what setup-auto.yml accepts as tengoku_ref


def tentative_files(key: str, source: dict) -> list[str]:
    """the files setup-auto.yml reads from the tree, by the same rule"""
    return ["data/tentative/" + f for f in source.get("tentative", [key + ".jsonl"])]


def records_ref(files: list[str], on_main: bool, prs: list[dict], tree: str) -> tuple[str | None, str]:
    """(the tengoku_ref to set the library up with: '' for main, a branch, or None when there is none to trust, why)"""
    if on_main:
        return "", "records on the tree's main"
    holders = [p for p in prs if p["repo"] == tree and set(files) <= set(p["files"])]
    if len(holders) == 1:
        p = holders[0]
        if not BRANCH.match(p["branch"]):
            return None, f"#{p['number']}'s branch name is not one setup-auto accepts"
        return p["branch"], f"records in #{p['number']}"
    if not holders:
        return None, "records neither on the tree's main nor in an open records pull request of the tree repository"
    return None, "records in " + ", ".join(f"#{p['number']}" for p in holders) + ": which one is not guessed"


def on_main(tree: str, files: list[str], run=subprocess.run) -> bool:
    """every file is on the tree's main; a 404 is 'no', any other failure stops the pickup"""
    for f in files:
        r = run(["gh", "api", f"repos/{tree}/contents/{f}?ref=main", "--silent"], capture_output=True, text=True)
        if r.returncode == 0:
            continue
        if "HTTP 404" in r.stderr:
            return False
        raise RuntimeError(f"{tree}: {f}: {r.stderr.strip()}")
    return True


def records_prs(tree: str, gh=bp._lines) -> list[dict]:
    """the tree's open pull requests titled `records:` (what register_libraries.py opens), with their files"""
    prs = gh("api", "--paginate", f"repos/{tree}/pulls?state=open&per_page=100", "--jq", '.[] | select(.title | startswith("records:")) | {number, branch: .head.ref, repo: .head.repo.full_name}')
    for p in prs:
        p["files"] = gh("api", "--paginate", f"repos/{tree}/pulls/{p['number']}/files?per_page=100", "--jq", ".[].filename | @json")
    return prs
