"""What a studied pull request says about itself, as the notices of competemath.com: the body that names it, and the events derived from its state.

Pure. The pull request's body carries one machine-readable line (`<!-- studied:v1 {...} -->`: account, target, bundle, theorem ids and names), written by the job that opened it; the
reporter reads it back and turns the PR's state (open, merged, closed, its checks, its reviews) into the events `POST /api/leak/memory/intake-events` takes. Each report is the
CURRENT state of the PR: the site answers the notices a PR no longer has (competemath.com `docs/leak-notices.md`).
"""

from __future__ import annotations

import json
import re

from . import decisions as D

MARKER = re.compile(r"<!-- studied:v1 (\{.*?\}) -->", re.S)
# a check run's name -> the code the notices catalogue has words for
GATE_CODES = (
    (re.compile(r"born tagged|isnad|autotag", re.I), "gate.isnad"),
    (re.compile(r"studied|provenance|classify", re.I), "gate.studied"),
    (re.compile(r"build|queue|lake|axiom", re.I), "gate.build"),
    (re.compile(r"lint|allowlist|credits|dco|secret", re.I), "gate.lint"),
)
FAILED = {"failure", "timed_out", "action_required", "startup_failure"}


def marker(account: str, target: str, bundle: str, ids: list[str], names: list[str]) -> str:
    return "<!-- studied:v1 " + json.dumps({"account": account, "target": target, "bundle": bundle, "ids": ids, "names": names}, sort_keys=True) + " -->"


def pr_body(account: str, target: str, bundle: str, rows: list[dict], harness_n: int) -> str:
    """The text of the PR: what it is, and the marker."""
    lines = [f"- `{r['name']}` ({r['stars']} stars) · id `{str(r['id'])[:8]}`" for r in rows]
    return (
        f"Theorems that Leak runs proved on the target `{target}` and rated four stars or more, put forward by `{account}` and accepted by the intake's bar (`bar/0`): "
        "each one showed it is useful or general, and none broke a style, naming, documentation or duplicate rule.\n\n"
        + "\n".join(lines)
        + f"\n\nBundle `{bundle[:16]}`. The harness evidence of {harness_n} theorem(s) is in the report (`data/studied/{target}/bundles/`). "
        "Every module is built on the Tengoku tree by the autotag build (which also writes the isnad tags into this branch) and again by the merge queue before it can merge; "
        "approval is one code owner or two independent contributors with write access (docs/pr-classes.md, section 9).\n\n"
        "A code owner can send single theorems back with a comment line that starts with `studied: return <id> <code>` (codes: merit duplicate general naming docs: the author may come back "
        "with a better one) or `studied: reject <id> <code>` (hygiene scope report: not shipped). The intake then closes this pull request and bundles the other theorems again "
        "(`memory-intake/README.md` in competemath/emissary-archangel).\n\n"
        + marker(account, target, bundle, [r["id"] for r in rows], [r["name"] for r in rows])
        + "\n"
    )


def parse_marker(body: str | None) -> dict | None:
    m = MARKER.search(body or "")
    if not m:
        return None
    try:
        d = json.loads(m.group(1))
    except ValueError:
        return None
    ok = isinstance(d, dict) and all(isinstance(d.get(k), str) for k in ("account", "target", "bundle")) and isinstance(d.get("ids"), list) and isinstance(d.get("names"), list)
    return d if ok else None


def gate_code(check_name: str) -> str:
    for pat, code in GATE_CODES:
        if pat.search(check_name):
            return code
    return "gate.other"


def derive(pr: dict, checks: list[dict], reviews: list[dict], mark: dict, decisions: list[D.Decision] | tuple = ()) -> list[dict]:
    """The events of one PR now. `pr`: GitHub's pull request object; `checks`: check runs of its head; `reviews`: its reviews, oldest first; `decisions`: a code owner's per-theorem
    decisions (decisions.py). A closed pull request with decisions on some of its theorems was closed so that the others go on in the next bundle: its words are `review.superseded`
    (when every theorem was decided there is nothing to go on, and it is `pr.closed`); the decisions stay listed either way (they are the lasting verdicts)."""
    ids, names = mark["ids"][:50], mark["names"][:50]
    base = {"ids": ids, "names": names}
    if pr.get("merged_at") or pr.get("merged"):
        return [{"kind": "merged", "code": "pr.merged", **base}]
    decided = D.events_for(mark, list(decisions))
    if pr.get("state") == "closed":
        rest = [i for i in ids if i not in {i2 for e in decided for i2 in e["ids"]}]
        if decided and rest:
            by = dict(zip(mark["ids"], mark["names"]))
            return [{"kind": "closed", "code": "review.superseded", "ids": rest, "names": [by.get(i, i[:8]) for i in rest]}, *decided]
        return [{"kind": "closed", "code": "pr.closed", **base}, *decided]
    out = [{"kind": "submitted", "code": "pr.opened", **base}]
    seen: dict[str, dict] = {}
    for c in checks:
        if c.get("conclusion") in FAILED:
            code = gate_code(str(c.get("name", "")))
            detail = f"{c.get('name', '')}: {((c.get('output') or {}).get('title') or (c.get('output') or {}).get('summary') or c.get('conclusion') or '')}"
            if code not in seen:
                seen[code] = {"kind": "gate_failed", "code": code, "detail": detail[:500], **base}
    out += list(seen.values())
    last: dict[str, dict] = {}
    for r in reviews:  # the latest state of each reviewer: a later approval or dismissal answers an earlier request
        who = str((r.get("user") or {}).get("login") or "")
        if r.get("state") in ("CHANGES_REQUESTED", "APPROVED", "DISMISSED"):
            last[who] = r
    asked = [r for r in last.values() if r.get("state") == "CHANGES_REQUESTED"]
    if asked:
        out.append({"kind": "changes_requested", "code": "review.changes", "detail": str(asked[0].get("body") or "")[:500], **base})
    return out + decided


def report_for(pr: dict, checks: list[dict], reviews: list[dict], decisions: list[D.Decision] | tuple = ()) -> dict | None:
    """One entry of `prs` for the site, or None for a PR that is not a studied one (no marker)."""
    mark = parse_marker(pr.get("body"))
    if mark is None or not isinstance(pr.get("number"), int) or not str(pr.get("html_url", "")).startswith("https://github.com/"):
        return None
    return {"username": mark["account"], "target": mark["target"], "number": pr["number"], "url": pr["html_url"], "events": derive(pr, checks, reviews, mark, decisions)}
