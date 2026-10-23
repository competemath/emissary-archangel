"""Settle the studied pull requests a code owner has decided on: close them, and say what became of each theorem.

A bundle is one pull request, and its attestation covers all its theorems, so a theorem cannot be taken out of an open pull request. When a code owner has returned or rejected some of
them (decisions.py), the pull request is closed with a comment that says so, the theorems nobody decided on are freed on the site (`reviews`, `accepted`) and the next intake run bundles
them again, as a new pull request (githubapi.open_pr: the next round). The decided ones stay held: a rejected theorem is never offered again, a returned one only when its text changed.

Runs in the job that holds the App's token, only for pull requests the App itself opened (the author), and does nothing twice: the comment carries a marker, a closed pull request is left alone.
"""

from __future__ import annotations

import re

from . import decisions as D
from . import events as E
from . import githubapi as G

MAX_PRS = 100
SAFE = re.compile(r"[^\w.'!?]")


def tick(name: str) -> str:
    return "`" + SAFE.sub("_", str(name))[:80] + "`"


def close_text(mark: dict, decisions: list[D.Decision]) -> str:
    names = dict(zip(mark["ids"], mark["names"]))
    decided = {d.id for d in decisions}
    rest = [names.get(i, i[:8]) for i in mark["ids"] if i not in decided]
    lines = ["Closed by the intake: a code owner decided on theorems of this bundle (a bundle is attested as a whole, so a theorem cannot leave an open pull request)."]
    for verdict, words in (("return", "returned: the author may come back with a better one"), ("reject", "rejected: not shipped")):
        ds = [d for d in decisions if d.verdict == verdict]
        if ds:
            lines.append(f"- {words}: " + ", ".join(f"{tick(names.get(d.id, d.id[:8]))} ({d.code})" for d in ds))
    lines.append("- the others go into the next bundle, as a new pull request: " + (", ".join(tick(n) for n in rest) if rest else "none left"))
    return "\n".join(lines) + "\n\n" + G.SETTLED


def ignored_text(rows: list[D.Ignored]) -> str:
    lines = ["Decision lines the intake did not take (a decision is a plain line, not quoted and not in a code block: `studied: return|reject <first 8 characters of the id> <code> [text]`; "
             f"return codes: {' '.join(D.RETURN_CODES)}; reject codes: {' '.join(D.REJECT_CODES)}):"]
    lines += [f"- line {r.line}: {r.why}" for r in rows]
    return "\n".join(lines)


def settle(api: G.Api, repo: str, bot: str, dry_run: bool = False) -> tuple[list[dict], list[dict], list[str]]:
    """Returns (`prs`, `reviews`, a log) for the site: the closed pull requests' notices and what happens to their theorems."""
    owners = G.code_owners(api, repo)
    prs: list[dict] = []
    reviews: list[dict] = []
    log: list[str] = []
    if not owners:
        return prs, reviews, ["no code owner found in .github/CODEOWNERS on main: no decision counts"]
    for issue in G.open_studied_prs(api, repo, MAX_PRS):
        n = issue["number"]
        pr = api("GET", f"repos/{repo}/pulls/{n}")
        mark = E.parse_marker(pr.get("body"))  # type: ignore[union-attr]
        if mark is None or pr.get("state") != "open" or (pr.get("user") or {}).get("login") != bot:  # type: ignore[union-attr]
            continue  # not this App's, or already closed or merged: nothing to settle
        decisions, ignored = D.parse(G.pr_comments(api, repo, n), mark["ids"], owners)
        mine = [i for i in ignored if i.owner]
        for cid in sorted({i.comment_id for i in mine}):
            rows = [i for i in mine if i.comment_id == cid]
            log.append(f"PR #{n}: comment {cid}: {len(rows)} line(s) not taken")
            if not dry_run:
                G.comment_once(api, repo, n, f"<!-- studied-ignored:v1 {cid} -->", ignored_text(rows) + f"\n\n<!-- studied-ignored:v1 {cid} -->", bot)
        if not decisions:
            continue
        log.append(f"PR #{n}: {len(decisions)} decision(s): " + ", ".join(f"{d.verdict} {d.id[:8]} {d.code}" for d in decisions))
        if dry_run:
            log.append(f"PR #{n}: would close")
            continue
        G.comment_once(api, repo, n, G.SETTLED, close_text(mark, decisions), bot)
        G.close_pr(api, repo, n)
        closed = {**pr, "state": "closed"}
        rep = E.report_for(closed, [], [], decisions)
        if rep:
            prs.append(rep)
        rv = D.review_payload(mark, decisions, closed=True)
        if rv:
            reviews.append(rv)
        log.append(f"PR #{n}: closed")
    return prs, reviews, log
