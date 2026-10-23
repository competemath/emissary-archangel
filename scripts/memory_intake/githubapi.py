"""The studied lane's side of GitHub: the files of a PR, the PR itself (as the studied App, through the git data API: no clone), and the state of the PRs it opened.

Every function takes `api`, a function (method, path, body=None, raw=False) that talks to GitHub: `gh_api` below in the workflow, a fake in the tests.
"""

from __future__ import annotations

import base64
import json
import subprocess
from typing import Callable

from .compose import Composition, fill_toolchain, pascal
from .events import pr_body

Api = Callable[..., object]


class ApiError(RuntimeError):
    pass


def gh_api(method: str, path: str, body: dict | None = None, raw: bool = False) -> object:
    cmd = ["gh", "api", "-X", method, path] + (["-H", "Accept: application/vnd.github.raw"] if raw else []) + (["--input", "-"] if body is not None else [])
    r = subprocess.run(cmd, input=json.dumps(body) if body is not None else None, capture_output=True, text=not raw, check=False)
    if r.returncode != 0:
        err = r.stderr if not raw else r.stderr.decode("utf-8", "replace")
        if raw and "404" in err:
            return b""
        raise ApiError(f"gh api {method} {path}: {err[:300]}")
    return r.stdout if raw else (json.loads(r.stdout) if r.stdout.strip() else {})


def read(api: Api, repo: str, path: str, ref: str) -> str:
    raw = api("GET", f"repos/{repo}/contents/{path}?ref={ref}", raw=True)
    return raw.decode("utf-8") if isinstance(raw, bytes) else str(raw)


def pr_files(api: Api, repo: str, base: str, comp: Composition) -> dict[str, str]:
    """Every file the PR writes, as the studied gate wants them (docs/pr-classes.md section 9): the modules, the manifest appended, the report, the root file appended, and
    for the first bundle of a target the line in Tengoku/Studied.lean (and, for the very first of all, that file and the line in Tengoku/All.lean)."""
    t, ns = comp.target, pascal(comp.target)
    toolchain = read(api, repo, "lean-toolchain", base).strip()
    files = dict(comp.modules)
    manifest = f"data/studied/{t}/manifest.jsonl"
    old = read(api, repo, manifest, base)
    first = old == ""
    if old and not old.endswith("\n"):
        raise ApiError(f"{manifest} does not end with a newline")
    files[manifest] = old + "\n".join(fill_toolchain(comp.manifest_lines, toolchain)) + "\n"
    files[f"data/studied/{t}/bundles/{comp.bundle[:16]}.json"] = json.dumps(comp.report, ensure_ascii=False) + "\n"
    root = f"Tengoku/Studied/{ns}.lean"
    mods = [p[: -len(".lean")].replace("/", ".") for p in sorted(comp.modules)]
    files[root] = read(api, repo, root, base) + "".join(f"import {m}\n" for m in mods)
    if first:
        top = "Tengoku/Studied.lean"
        old_top = read(api, repo, top, base)
        files[top] = old_top + f"import Tengoku.Studied.{ns}\n"
        if old_top == "":
            all_ = read(api, repo, "Tengoku/All.lean", base)
            files["Tengoku/All.lean"] = all_ + ("" if all_.endswith("\n") else "\n") + "import Tengoku.Studied\n"
    return files


def branch_exists(api: Api, repo: str, branch: str) -> bool:
    try:
        api("GET", f"repos/{repo}/git/ref/heads/{branch}")
    except ApiError as e:
        if "404" in str(e) or "Not Found" in str(e):
            return False
        raise
    return True


def pr_of_branch(api: Api, repo: str, branch: str) -> dict | None:
    """The pull request (open, closed or merged) whose head is `branch`, or None."""
    rows = api("GET", f"repos/{repo}/pulls?head={repo.split('/')[0]}:{branch}&state=all&per_page=1")
    return rows[0] if isinstance(rows, list) and rows else None  # type: ignore[index]


def open_pr(api: Api, repo: str, base: str, comp: Composition, bot: str, email: str, dry_run: bool = False) -> dict:
    """One commit on a new branch off `base`, a PR from it, the label `studied`. Returns {"number", "url", "branch"} (dry run: what would be opened).
    Safe to run again after a run that stopped half way: the branch the bundle id names is the same, so an existing branch is reused (no second commit), an existing
    pull request is returned (open, closed or merged: a decision already made is not asked again), and the label is put on it either way."""
    files = pr_files(api, repo, base, comp)
    branch = f"studied/{comp.target}/{comp.bundle[:16]}"
    if dry_run:
        return {"number": 0, "url": "", "branch": branch, "files": sorted(files)}
    pr = None
    if branch_exists(api, repo, branch):
        pr = pr_of_branch(api, repo, branch)
    else:
        head = api("GET", f"repos/{repo}/git/commits/{base}")
        entries = []
        for path, text in sorted(files.items()):
            b = api("POST", f"repos/{repo}/git/blobs", {"content": base64.b64encode(text.encode("utf-8")).decode(), "encoding": "base64"})
            entries.append({"path": path, "mode": "100644", "type": "blob", "sha": b["sha"]})  # type: ignore[index]
        tree = api("POST", f"repos/{repo}/git/trees", {"base_tree": head["tree"]["sha"], "tree": entries})  # type: ignore[index]
        who = {"name": bot, "email": email}
        n = len(comp.accepted)
        msg = f"studied: {n} theorem{'s' if n != 1 else ''} for {comp.target} from {comp.author}\n\nSigned-off-by: {bot} <{email}>\n"
        commit = api("POST", f"repos/{repo}/git/commits", {"message": msg, "tree": tree["sha"], "parents": [base], "author": who, "committer": who})  # type: ignore[index]
        api("POST", f"repos/{repo}/git/refs", {"ref": f"refs/heads/{branch}", "sha": commit["sha"]})  # type: ignore[index]
    if pr is None:
        n = len(comp.accepted)
        rows = [{"id": v.entry["id"], "name": v.entry["name"], "stars": (v.entry.get("quality") or {}).get("s")} for v in comp.accepted]
        pr = api("POST", f"repos/{repo}/pulls", {
            "title": f"studied: {n} theorem{'s' if n != 1 else ''} for {comp.target} ({comp.author})", "head": branch, "base": "main",
            "body": pr_body(comp.author, comp.target, comp.bundle, rows, len(comp.report.get("harness", []))), "draft": False})
    api("POST", f"repos/{repo}/issues/{pr['number']}/labels", {"labels": ["studied"]})  # type: ignore[index]  # adding a label twice is a no-op
    return {"number": pr["number"], "url": pr["html_url"], "branch": branch}  # type: ignore[index]


def open_studied_prs(api: Api, repo: str, limit: int = 100) -> list[dict]:
    """The pull requests labelled `studied`, open and closed, newest first (the issues endpoint lists pull requests too)."""
    rows = api("GET", f"repos/{repo}/issues?labels=studied&state=all&per_page={min(limit, 100)}&sort=updated&direction=desc")
    return [r for r in rows if isinstance(r, dict) and "pull_request" in r]  # type: ignore[union-attr]


def pr_state(api: Api, repo: str, number: int) -> tuple[dict, list, list]:
    pr = api("GET", f"repos/{repo}/pulls/{number}")
    checks = api("GET", f"repos/{repo}/commits/{pr['head']['sha']}/check-runs?per_page=100")  # type: ignore[index]
    reviews = api("GET", f"repos/{repo}/pulls/{number}/reviews?per_page=100")
    return pr, checks.get("check_runs", []), reviews  # type: ignore[return-value,union-attr]
