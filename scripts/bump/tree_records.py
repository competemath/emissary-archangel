#!/usr/bin/env python3
"""Where the tree holds a library's tentative records, for a setup or a bump started by a pickup (setup_pickup.py, bump_pickup.py): on its main, or on the branch of one open `records:` pull request of
the tree repository (a fork's branch is never used, nor one of several, nor one holding only some of the files). Until a library's records pull request is merged, a setup or bump that reads main
finds no record (rankamplificationtotient, 13 Nov 2026: bump-pickup started its bump on main, it planned no shard and failed at compose)."""

import re
import subprocess

import bump_pickup as bp
import tentative_files as tf

BRANCH = re.compile(r"^[A-Za-z0-9._/-]+$")  # what setup-auto.yml accepts as tengoku_ref


def tentative_files(key: str, source: dict) -> list[str]:
    """the files sources.json lists for the library (<key>.jsonl when it lists none), as tentative_files.py names them"""
    return ["data/tentative/" + n for n in tf.names({"sources": {key: source}}, key)]


def directory(key: str) -> str:
    return f"data/tentative/{key}/"


def in_directory(key: str, path: str) -> bool:
    """a file the bump's glob data/tentative/<key>/*.jsonl reads"""
    d = directory(key)
    return path.startswith(d) and path.endswith(".jsonl") and "/" not in path[len(d) :]


def is_record_path(key: str, source: dict, path: str) -> bool:
    return path in tentative_files(key, source) or in_directory(key, path)


def holds(key: str, source: dict, present: set[str]) -> bool:
    """the records the bump reads (tentative_files.globs) are all there: every file sources.json lists that the directory does not cover, and at least one file to read.
    A library that lists nothing reads <key>.jsonl if it is there and the directory always (cubic on #187: records only in the directory are records)."""
    listed = tf.names({"sources": {key: source}}, key)
    dir_files = any(in_directory(key, f) for f in present)
    if "tentative" not in source:
        return f"data/tentative/{key}.jsonl" in present or dir_files
    need = [f"data/tentative/{n}" for n in listed if not tf.covered_by_directory(key, n)]
    return all(f in present for f in need) and (bool(need) or dir_files)


def setup_holds(key: str, source: dict, present: set[str]) -> bool:
    """what setup-auto.yml reads: the listed files only (its sparse checkout has no directory), every one of them"""
    return all(f in present for f in tentative_files(key, source))


def records_ref(key: str, source: dict, on_main: set[str], prs: list[dict], tree: str, rule=holds) -> tuple[str | None, str]:
    """(the tengoku_ref to set up or bump the library with: '' for main, a branch, or None when there is none to trust, why).
    `on_main`: the library's record paths that are on the tree's main; `rule`: what the reader needs (holds for a bump, setup_holds for a setup). Main first; else the one open records pull request of
    the tree repository (never a fork's) that touches the library's records, when its branch (main and its files) holds them all; two such pull requests are not chosen between."""
    if rule(key, source, on_main):
        return "", "records on the tree's main"
    touching = [p for p in prs if p["repo"] == tree and any(is_record_path(key, source, f) for f in p["files"])]
    if not touching:
        return None, "records neither on the tree's main nor in an open records pull request of the tree repository"
    if len(touching) > 1:
        return None, "records in " + ", ".join(f"#{p['number']}" for p in touching) + ": which one is not guessed"
    p = touching[0]
    if not rule(key, source, on_main | set(p["files"])):
        return None, f"#{p['number']} with main does not hold every record file sources.json lists"
    if not BRANCH.match(p["branch"]):
        return None, f"#{p['number']}'s branch name is not one setup-auto accepts"
    return p["branch"], f"records in #{p['number']}"


def main_files(tree: str, key: str, source: dict, run=subprocess.run) -> set[str]:
    """the library's record paths on the tree's main: each listed file, and the .jsonl files of its directory; a 404 is 'not there', any other failure stops the pickup"""

    def get(path: str) -> subprocess.CompletedProcess | None:
        r = run(["gh", "api", f"repos/{tree}/contents/{path}?ref=main", "--jq", "if type == \"array\" then .[].path else .path end"], capture_output=True, text=True)
        if r.returncode == 0:
            return r
        if "HTTP 404" in r.stderr:
            return None
        raise RuntimeError(f"{tree}: {path}: {r.stderr.strip()}")

    out: set[str] = set()
    for f in tentative_files(key, source):
        if get(f) is not None:
            out.add(f)
    r = get(directory(key).rstrip("/"))
    if r is not None:
        out |= {ln for ln in r.stdout.split() if in_directory(key, ln)}
    return out


def records_prs(tree: str, gh=bp._lines) -> list[dict]:
    """the tree's open pull requests titled `records:` (what register_libraries.py opens), with their files"""
    prs = gh("api", "--paginate", f"repos/{tree}/pulls?state=open&per_page=100", "--jq", '.[] | select(.title | startswith("records:")) | {number, branch: .head.ref, repo: .head.repo.full_name}')
    for p in prs:
        p["files"] = gh("api", "--paginate", f"repos/{tree}/pulls/{p['number']}/files?per_page=100", "--jq", ".[].filename | @json")
    return prs
