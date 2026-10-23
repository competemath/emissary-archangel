#!/usr/bin/env python3
"""run.py — the memory intake's commands, called by .github/workflows/memory-intake.yml (python3 -m scripts.memory_intake.run <command>).

  collect  GET the candidates (OIDC), compose each bundle, write out/<n>/composition.json (+ bundle.tar for the accepted) and out/events.json
  open     one PR per composition that has accepted theorems, as the studied App (GH_TOKEN = the App's token), and write out/opened.json
  post     POST the events and the opened PRs to competemath.com (OIDC), and mark the submitted theorems
  report   the current state of every studied PR, as the notices' `prs` (OIDC): what the site tells the account about its pull requests

The I/O is here and in githubapi.py; compose.py and events.py are pure. Nothing here runs a line of a pull request or of a candidate.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import urllib.error
import urllib.request
from pathlib import Path

from . import compose as C
from . import events as E
from . import githubapi as G

SITE = "https://competemath.com"
MAX_BUNDLES = 5  # per run: the cap on PRs a run opens


def http(method: str, url: str, token: str, body: dict | None = None) -> dict:
    req = urllib.request.Request(url, method=method, data=json.dumps(body).encode() if body is not None else None,
                                 headers={"Authorization": f"Bearer {token}", "Content-Type": "application/json", "User-Agent": "memory-intake"})
    try:
        with urllib.request.urlopen(req, timeout=60) as r:  # noqa: S310 - https to the site
            return json.loads(r.read() or b"{}")
    except urllib.error.HTTPError as e:
        raise SystemExit(f"{method} {url}: HTTP {e.code} {e.read()[:200]!r}") from e


def praiser_review(modules: dict, facts: dict) -> tuple[dict, set]:
    """praiser's text checks over the modules and its bar (`bar/0`) on each theorem. Needs PRAISER_PATH (a checkout of competemath/tengoku-praiser)."""
    sys.path.insert(0, os.environ["PRAISER_PATH"])
    from praiser import bar, reviewer  # noqa: E402

    res = reviewer.review(modules, checks=reviewer.TEXT_CHECKS)
    items = {eid: f["module"] for eid, f in facts.items()}
    verdicts = bar.decide(res.findings, items, {eid: {"stars": f["stars"], "cited_by": f["cited_by"]} for eid, f in facts.items()}, ran=set(res.ran))
    return {eid: v.as_dict() for eid, v in verdicts.items()}, set(res.ran)


def dump(comp: C.Composition) -> dict:
    return {
        "target": comp.target, "author": comp.author, "bundle": comp.bundle, "modules": comp.modules, "manifest_lines": comp.manifest_lines, "report": comp.report,
        "verdicts": [{"entry": v.entry, "verdict": v.verdict, "codes": v.codes, "merit": v.merit} for v in comp.verdicts],
    }


def load(d: dict) -> C.Composition:
    comp = C.Composition(d["target"], d["author"], bundle=d["bundle"], modules=d["modules"], manifest_lines=d["manifest_lines"], report=d["report"])
    comp.verdicts = [C.Verdict(v["entry"], v["verdict"], v["codes"], v["merit"]) for v in d["verdicts"]]
    return comp


def bundle_tar(comp: C.Composition, toolchain: str, canonical, out: str) -> str:
    """The archive the gate rebuilds from the PR (tengoku scripts/ci/studied_check.py): each module in its canonical form (tags out), the manifest's new lines and the report."""
    sys.path.insert(0, os.environ.get("BUNDLE_TAR_PATH", str(Path(__file__).resolve().parents[1] / "bump")))
    from bundle_tar import write_tar  # noqa: E402

    members = {p: canonical(t).encode("utf-8") for p, t in comp.modules.items()}
    members["manifest.jsonl"] = ("\n".join(C.fill_toolchain(comp.manifest_lines, toolchain)) + "\n").encode("utf-8")
    members["report.json"] = (json.dumps(comp.report, ensure_ascii=False) + "\n").encode("utf-8")
    return write_tar(members, out)


def cmd_collect(a: argparse.Namespace) -> int:
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    if a.candidates_file:
        data = json.loads(Path(a.candidates_file).read_text())
    else:
        data = http("GET", f"{a.site}/api/leak/memory/candidates?limit={MAX_BUNDLES}", os.environ["LEAK_OIDC_TOKEN"])
    sys.path.insert(0, a.tengoku_scripts)
    import isnad_tag  # noqa: E402

    toolchain = (Path(a.tengoku_root) / "lean-toolchain").read_text().strip()
    events, summary = [], []
    for n, b in enumerate((data.get("bundles") or [])[:MAX_BUNDLES]):
        try:
            comp = C.compose(b, praiser_review)
        except ValueError as e:
            summary.append({"n": n, "refused": str(e)})
            continue
        d = out / str(n)
        d.mkdir(exist_ok=True)
        (d / "composition.json").write_text(json.dumps(dump(comp), ensure_ascii=False))
        events += comp.events()
        row = {"n": n, "target": comp.target, "author": comp.author, "accepted": len(comp.accepted), "returned": sum(v.verdict == "return" for v in comp.verdicts),
               "rejected": sum(v.verdict == "reject" for v in comp.verdicts)}
        if comp.accepted:
            row["bundle"] = comp.bundle
            row["tar_sha256"] = bundle_tar(comp, toolchain, isnad_tag.canonical_text, str(d / "bundle.tar"))
        summary.append(row)
    (out / "events.json").write_text(json.dumps(events))
    (out / "summary.json").write_text(json.dumps(summary, indent=1))
    print(json.dumps(summary, indent=1))
    return 0


def cmd_open(a: argparse.Namespace) -> int:
    """Open one pull request per accepted bundle. A bundle that fails does not stop the others, and opened.json is rewritten after every success, so what was opened is
    posted (and marked, so it is not offered again) even when a later bundle failed; the exit code is 1 when any bundle failed."""
    out = Path(a.out)
    opened, failed = [], []
    for d in sorted(p for p in out.iterdir() if p.is_dir() and (p / "composition.json").exists()):
        comp = load(json.loads((d / "composition.json").read_text()))
        if not comp.accepted:
            continue
        try:
            pr = G.open_pr(G.gh_api, a.repo, a.base, comp, a.bot, a.email, a.dry_run)
        except G.ApiError as e:
            print(f"::error::bundle {d.name} ({comp.target}) was not opened: {e}")
            failed.append(d.name)
            continue
        print(f"{'would open' if a.dry_run else 'opened'} {pr.get('url') or pr['branch']}")
        opened.append({"username": comp.author, "target": comp.target, "number": pr["number"], "url": pr["url"], "bundle": comp.bundle,
                       "ids": [v.entry["id"] for v in comp.accepted], "names": [v.entry["name"] for v in comp.accepted]})
        (out / "opened.json").write_text(json.dumps(opened))
    (out / "opened.json").write_text(json.dumps(opened))
    return 1 if failed else 0


def cmd_post(a: argparse.Namespace) -> int:
    out = Path(a.out)
    token = os.environ["LEAK_OIDC_TOKEN"]
    events = json.loads((out / "events.json").read_text()) if (out / "events.json").exists() else []
    opened = json.loads((out / "opened.json").read_text()) if (out / "opened.json").exists() else []
    prs = [{"username": o["username"], "target": o["target"], "number": o["number"], "url": o["url"],
            "events": [{"kind": "submitted", "code": "pr.opened", "ids": o["ids"], "names": o["names"]}]} for o in opened if o["number"]]
    if events or prs:
        print(json.dumps(http("POST", f"{a.site}/api/leak/memory/intake-events", token, {"events": events[:300], "prs": prs})))
    marks = [{"username": o["username"], "target": o["target"], "ids": o["ids"], "bundle": o["bundle"]} for o in opened if o["number"]]
    if marks:
        print(json.dumps(http("POST", f"{a.site}/api/leak/memory/candidates", token, {"marks": marks})))
    return 0


def cmd_report(a: argparse.Namespace) -> int:
    prs = []
    for issue in G.open_studied_prs(G.gh_api, a.repo):
        pr, checks, reviews = G.pr_state(G.gh_api, a.repo, issue["number"])
        r = E.report_for(pr, checks, reviews)
        if r:
            prs.append(r)
    print(f"{len(prs)} studied pull request(s)")
    if a.dry_run:
        print(json.dumps(prs, indent=1))
        return 0
    if prs:
        print(json.dumps(http("POST", f"{a.site}/api/leak/memory/intake-events", os.environ["LEAK_OIDC_TOKEN"], {"prs": prs[:100]})))
    return 0


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(prog="memory_intake")
    sub = ap.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("collect")
    c.add_argument("--site", default=SITE)
    c.add_argument("--out", default="out")
    c.add_argument("--candidates-file")
    c.add_argument("--tengoku-root", required=True)
    c.add_argument("--tengoku-scripts", required=True)
    o = sub.add_parser("open")
    o.add_argument("--out", default="out")
    o.add_argument("--repo", required=True)
    o.add_argument("--base", required=True, help="the commit of the target repository's main the PR is made against")
    o.add_argument("--bot", required=True)
    o.add_argument("--email", required=True)
    o.add_argument("--dry-run", action="store_true")
    p = sub.add_parser("post")
    p.add_argument("--site", default=SITE)
    p.add_argument("--out", default="out")
    r = sub.add_parser("report")
    r.add_argument("--site", default=SITE)
    r.add_argument("--repo", required=True)
    r.add_argument("--dry-run", action="store_true")
    a = ap.parse_args(argv)
    return {"collect": cmd_collect, "open": cmd_open, "post": cmd_post, "report": cmd_report}[a.cmd](a)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
