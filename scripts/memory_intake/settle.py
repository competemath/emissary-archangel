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


def settle(api: G.Api, repo: str, bot: str, dry_run: bool = False) -> tuple[list[dict], list[dict], list[str], int]:
    """Returns (`prs`, `reviews`, a log, how many pull requests failed) for the site: the closed pull requests' notices and what happens to their theorems. A pull request whose
    calls fail is logged and skipped; the others go on (what was closed is reported by the next `report` anyway: it sees a closed pull request with decisions)."""
    owners = G.code_owners(api, repo)
    prs: list[dict] = []
    reviews: list[dict] = []
    log: list[str] = []
    failed = 0
    if not owners:
        return prs, reviews, ["no code owner found in .github/CODEOWNERS on main: no decision counts"], failed
    for issue in G.open_studied_prs(api, repo, MAX_PRS):
        n = issue["number"]
        try:
            one = settle_one(api, repo, bot, owners, n, dry_run, log)
        except G.ApiError as e:
            failed += 1
            log.append(f"::error::PR #{n} was not settled: {e}")
            continue
        if one:
            prs.append(one[0])
            if one[1]:
                reviews.append(one[1])
    return prs, reviews, log, failed


def settle_one(api: G.Api, repo: str, bot: str, owners: set[str], n: int, dry_run: bool, log: list[str]) -> tuple[dict, dict | None] | None:
    """One pull request: close it if a code owner decided on its theorems. Returns its report and review, or None when there is nothing to report."""
    pr = api("GET", f"repos/{repo}/pulls/{n}")
    mark = E.parse_marker(pr.get("body"))  # type: ignore[union-attr]
    if mark is None or pr.get("state") != "open" or (pr.get("user") or {}).get("login") != bot:  # type: ignore[union-attr]
        return None  # not this App's, or already closed or merged: nothing to settle
    decisions, ignored = D.parse(G.pr_comments(api, repo, n), mark["ids"], owners)
    mine = [i for i in ignored if i.owner]
    for cid in sorted({i.comment_id for i in mine}):
        rows = [i for i in mine if i.comment_id == cid]
        log.append(f"PR #{n}: comment {cid}: {len(rows)} line(s) not taken")
        if not dry_run:
            G.comment_once(api, repo, n, f"<!-- studied-ignored:v1 {cid} -->", ignored_text(rows) + f"\n\n<!-- studied-ignored:v1 {cid} -->", bot)
    if not decisions:
        return None
    log.append(f"PR #{n}: {len(decisions)} decision(s): " + ", ".join(f"{d.verdict} {d.id[:8]} {d.code}" for d in decisions))
    if dry_run:
        log.append(f"PR #{n}: would close")
        return None
    G.comment_once(api, repo, n, G.SETTLED, close_text(mark, decisions), bot)
    G.close_pr(api, repo, n)
    log.append(f"PR #{n}: closed")
    rep = E.report_for({**pr, "state": "closed"}, [], [], decisions)  # type: ignore[dict-item]
    return (rep, D.review_payload(mark, decisions, closed=True)) if rep else None
