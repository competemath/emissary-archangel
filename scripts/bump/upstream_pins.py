#!/usr/bin/env python3
"""upstream_pins.py [--sources sources.json] [--md report.md] [--json report.json] — which registered libraries have a newer upstream than the commit sources.json pins.

REPORT ONLY: it reads sources.json and the upstream repositories' heads (`git ls-remote`), asks GitHub how far each pin is behind (`gh api compare`), writes a table, and changes nothing.
Why (2026-10-18): OpenAI pushed 283 new Lean files to openai/math two days after we registered it, and nothing noticed for ten days.

    upstream_pins.py --md pins.md --json pins.json
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

GITHUB = re.compile(r"^https://github\.com/([A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+?)(?:\.git)?/?$")
SHA = re.compile(r"^[0-9a-f]{40}$")


def registered(sources: dict) -> list[tuple[str, str, str]]:
    """(key, GitHub slug, pinned commit) of every source that names a GitHub repository and a full commit"""
    out = []
    for key, spec in sorted((sources.get("sources") or sources).items()):
        if not isinstance(spec, dict):
            continue
        m = GITHUB.match(str(spec.get("repo", "")))
        commit = str(spec.get("commit", ""))
        if m and SHA.match(commit):
            out.append((key, m.group(1), commit))
    return out


def head_of(slug: str, run=subprocess.run) -> str | None:
    """the commit HEAD points to upstream, or None when the repository cannot be read (moved, private, deleted)"""
    try:
        r = run(["git", "ls-remote", f"https://github.com/{slug}.git", "HEAD"], capture_output=True, text=True, timeout=120)
    except (subprocess.TimeoutExpired, OSError):  # one slow or missing repository must not cost the whole report
        return None
    line = (r.stdout or "").split("\n")[0].split()
    return line[0] if r.returncode == 0 and line and SHA.match(line[0]) else None


def compare(slug: str, pinned: str, head: str, run=subprocess.run) -> dict:
    """how far `pinned` is behind `head`: {ahead_by, files, last} or {diverged: True} when GitHub cannot compare them (a history rewrite)"""
    try:
        r = run(
            ["gh", "api", f"repos/{slug}/compare/{pinned}...{head}", "-q", "{ahead_by: .ahead_by, status: .status, files: (.files|length), last: .commits[-1].commit.committer.date}"],
            capture_output=True,
            text=True,
            timeout=120,
        )
    except (subprocess.TimeoutExpired, OSError):
        return {"unknown": True}
    if r.returncode != 0:
        return {"diverged": True}
    try:
        d = json.loads(r.stdout)
    except ValueError:
        return {"unknown": True}
    return {"ahead_by": d.get("ahead_by", 0), "files": d.get("files", 0), "last": (d.get("last") or "")[:10]}


def report(items: list[tuple[str, str, str]], heads=head_of, comparer=compare) -> list[dict]:
    rows = []
    for key, slug, pinned in items:
        head = heads(slug)
        if head is None:
            rows.append({"key": key, "slug": slug, "pinned": pinned, "head": None, "state": "unreadable"})
        elif head == pinned:
            continue
        else:
            rows.append({"key": key, "slug": slug, "pinned": pinned, "head": head, "state": "behind", **comparer(slug, pinned, head)})
    return sorted(rows, key=lambda r: (-(r.get("ahead_by") or 0), r["key"]))


def markdown(rows: list[dict], total: int) -> str:
    out = [f"{len(rows)} of {total} registered libraries have an upstream that moved, or cannot be read (report only; nothing was changed).", ""]
    if rows:
        out += ["| key | upstream | pinned | head | commits ahead | files | last upstream commit |", "|---|---|---|---|---|---|---|"]
        for r in rows:
            if r["state"] == "unreadable":
                out.append(f"| {r['key']} | {r['slug']} | `{r['pinned'][:10]}` | unreadable | | | |")
            elif r.get("unknown"):
                out.append(f"| {r['key']} | {r['slug']} | `{r['pinned'][:10]}` | `{r['head'][:10]}` | unknown (the comparison failed) | | |")
            elif r.get("diverged"):
                out.append(f"| {r['key']} | {r['slug']} | `{r['pinned'][:10]}` | `{r['head'][:10]}` | diverged (history rewritten?) | | |")
            else:
                out.append(f"| {r['key']} | {r['slug']} | `{r['pinned'][:10]}` | `{r['head'][:10]}` | {r['ahead_by']} | {r['files']} | {r['last']} |")
    return "\n".join(out) + "\n"


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--sources", default="sources.json")
    ap.add_argument("--md")
    ap.add_argument("--json")
    a = ap.parse_args(argv)
    items = registered(json.loads(Path(a.sources).read_text(encoding="utf-8")))
    rows = report(items)
    text = markdown(rows, len(items))
    print(text)
    if a.md:
        Path(a.md).write_text(text, encoding="utf-8")
    if a.json:
        Path(a.json).write_text(json.dumps(rows, indent=1), encoding="utf-8")
    return 0


if __name__ == "__main__":
    sys.exit(main())
