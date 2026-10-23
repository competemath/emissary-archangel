"""A code owner's decisions on the theorems of a studied pull request, read from its comments.

Pure. The grammar is one line a person writes at the start of a line of a pull request comment (the same as the specialised reviewer's file in tengoku, `.gitar/review/studied.md`):

    studied: return <first 8 characters of the theorem id> <code> [free text]
    studied: reject <first 8 characters of the theorem id> <code> [free text]

    return  the author may come back with a better one      codes: merit duplicate general naming docs
    reject  not shipped, and this text is not to be sent again   codes: hygiene scope report

Only a comment of a code owner counts (the `*` line of tengoku's CODEOWNERS, and a GitHub association that says a person with write access); everything else is ignored: another account, a bot, the
pull request's author. A line that is quoted (`>`, or continuing a quote without a blank line), inside a code fence, inside an HTML comment or indented four spaces is not a decision: someone quoting a decision is not making one, and the
person who reads the comment must see the line as a line. A malformed line, an unknown code, a code that does not belong to the verdict, an id that is not one of the pull request's (or is the
prefix of two) is IGNORED and reported, never guessed. The latest decision of an id wins.
"""

from __future__ import annotations

import re
from dataclasses import dataclass

RETURN_CODES = ("merit", "duplicate", "general", "naming", "docs")
REJECT_CODES = ("hygiene", "scope", "report")
CODES = {"return": RETURN_CODES, "reject": REJECT_CODES}
# a GitHub comment's author_association for a person with write access to the repository
OWNER_ASSOCIATIONS = frozenset({"OWNER", "MEMBER", "COLLABORATOR"})
MAX_DETAIL = 300

LINE = re.compile(r"^ {0,3}studied:[ \t]+(return|reject)[ \t]+([0-9a-f]{8})[ \t]+([a-z]+)(?:[ \t]+(.*?))?[ \t]*$")
ATTEMPT = re.compile(r"^ {0,3}studied:", re.I)
FENCE = re.compile(r"^ {0,3}(`{3,}|~{3,})")
QUOTE = re.compile(r"^ {0,3}>")
HTML_COMMENT = re.compile(r"<!--.*?-->", re.S)
HANDLE = re.compile(r"^@[A-Za-z0-9][A-Za-z0-9-]{0,38}$")
CONTROL = re.compile(r"[\u0000-\u0008\u000b-\u001f\u007f​-‏‪-‮⁦-⁩]")


@dataclass(frozen=True)
class Decision:
    id: str  # the theorem's full id
    verdict: str  # return | reject
    code: str
    detail: str  # the owner's own words after the code: shown to the account, never to the driver
    comment_id: int
    author: str


@dataclass(frozen=True)
class Ignored:
    comment_id: int
    author: str
    owner: bool  # the author is a code owner (a non-owner's lines are noise and are never answered on the pull request)
    line: int  # 1-based, in the comment body
    why: str


def owners_from_codeowners(text: str) -> set[str]:
    """The account handles (lower case, no `@`) of the `*` line of a CODEOWNERS file; a team (`@org/team`) is not an account and is left out."""
    for raw in text.splitlines():
        parts = raw.split("#", 1)[0].split()
        if parts and parts[0] == "*":
            return {h[1:].lower() for h in parts[1:] if HANDLE.match(h)}
    return set()


def is_owner(comment: dict, owners: set[str]) -> bool:
    user = comment.get("user") or {}
    return (
        user.get("type") == "User"
        and str(user.get("login", "")).lower() in owners
        and comment.get("author_association") in OWNER_ASSOCIATIONS
    )


def visible_lines(body: str) -> list[tuple[int, str, bool]]:
    """The lines of a comment that a reader sees as ordinary text: not in an HTML comment, a code fence or a quote. (Line number, text, lazy), where `lazy` marks a line that Markdown
    still renders inside the quote above it (a quote goes on over lines without a `>` until a blank line)."""
    body = HTML_COMMENT.sub(lambda m: "\n" * m.group(0).count("\n"), body or "")
    out: list[tuple[int, str, bool]] = []
    fence: str | None = None
    quoted = False
    for n, line in enumerate(body.replace("\r\n", "\n").split("\n"), 1):
        m = FENCE.match(line)
        if fence is not None:
            if m and m.group(1)[0] == fence[0] and len(m.group(1)) >= len(fence) and line.strip() == m.group(1):
                fence = None
            continue
        if m:
            fence = m.group(1)
            quoted = False
            continue
        if QUOTE.match(line):
            quoted = True
            continue
        if not line.strip():
            quoted = False
        out.append((n, line, quoted))
    return out


def parse(comments: list[dict], ids: list[str], owners: set[str]) -> tuple[list[Decision], list[Ignored]]:
    """The decisions in `comments` (GitHub issue comments of the pull request) about `ids` (the full ids of its theorems), and the lines that were not taken.

    Latest comment wins; within one comment the later line wins."""
    latest: dict[str, Decision] = {}
    ignored: list[Ignored] = []
    for c in sorted(comments, key=lambda c: (str(c.get("created_at", "")), int(c.get("id") or 0))):
        cid, author = int(c.get("id") or 0), str((c.get("user") or {}).get("login", ""))
        owner = is_owner(c, owners)
        for n, line, lazy in visible_lines(str(c.get("body") or "")):
            if not ATTEMPT.match(line):
                continue
            if not owner:
                ignored.append(Ignored(cid, author, False, n, "the author is not a code owner"))
                continue
            if lazy:
                ignored.append(Ignored(cid, author, True, n, "this line is still inside the quote above it (leave a blank line after a quote)"))
                continue
            m = LINE.match(line)
            if not m:
                ignored.append(Ignored(cid, author, True, n, "not `studied: return|reject <id8> <code> [text]`"))
                continue
            verdict, id8, code, text = m.group(1), m.group(2), m.group(3), m.group(4) or ""
            if code not in CODES[verdict]:
                ignored.append(Ignored(cid, author, True, n, f"`{code}` is not a {verdict} code (use: {' '.join(CODES[verdict])})"))
                continue
            hit = [i for i in ids if i.startswith(id8)]
            if len(hit) != 1:
                ignored.append(Ignored(cid, author, True, n, f"`{id8}` is not the id of exactly one theorem of this pull request"))
                continue
            latest[hit[0]] = Decision(hit[0], verdict, code, " ".join(CONTROL.sub(" ", text).split())[:MAX_DETAIL], cid, author)
    return sorted(latest.values(), key=lambda d: (d.verdict, d.code, d.id)), ignored


def events_for(mark: dict, decisions: list[Decision]) -> list[dict]:
    """The notices the decisions are: one event per verdict and code, listing the theorems it is about. The words come from the site's catalogue by the code; the owner's own words are the detail."""
    names = dict(zip(mark["ids"], mark["names"]))
    by: dict[tuple[str, str], list[Decision]] = {}
    for d in decisions:
        by.setdefault((d.verdict, d.code), []).append(d)
    out = []
    for (verdict, code), ds in sorted(by.items()):
        detail = "; ".join(f"{names.get(d.id, d.id[:8])}: {d.detail}" for d in ds if d.detail)
        out.append(
            {
                "kind": "returned" if verdict == "return" else "rejected",
                "code": f"review.{verdict}.{code}",
                "ids": [d.id for d in ds][:50],
                "names": [names.get(d.id, d.id[:8]) for d in ds][:50],
                "detail": detail[:500],
            }
        )
    return out


def review_payload(mark: dict, decisions: list[Decision], closed: bool) -> dict | None:
    """What the site does to the kept theorems: hold the decided ones; once the pull request is closed, free the others (`accepted`) so the next bundle takes them. None: no decision."""
    if not decisions:
        return None
    decided = {d.id for d in decisions}
    return {
        "username": mark["account"],
        "target": mark["target"],
        "bundle": mark["bundle"],
        "returned": [{"id": d.id, "code": d.code} for d in decisions if d.verdict == "return"],
        "rejected": [{"id": d.id, "code": d.code} for d in decisions if d.verdict == "reject"],
        "accepted": [i for i in mark["ids"] if i not in decided] if closed else [],
    }
