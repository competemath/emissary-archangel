#!/usr/bin/env python3
"""Push the current commit to a branch of the remote only if the branch still holds what we last saw (compare and swap).

    GH_TOKEN=... python3 scripts/safe-push.py --repo . --remote-repo OWNER/NAME [--branch main] [--attempts 30]

What the `finish` job of translate.yml used to do was `git pull --rebase` and `git push` in a loop, retrying anything that failed.
This does the same work with the guarantee spelled out: fetch the branch, rebase our commits onto it, and push with an
expected-old-sha lease (warden.safegit.push_cas, i.e. --force-with-lease=<ref>:<sha>), so a push that lost a race to another
shard's commit is refused by the server and retried from a fresh fetch, and nothing is ever overwritten. Everything that can
be transient (a lost race, a failed fetch, a refusal by the remote) is retried up to --attempts, as before; a refusal by a local
hook is not, and an unconditional force cannot be expressed at all.

Exit status: 0 pushed (or nothing to push), 1 gave up, 2 bad input. The token is in the remote URL only for the git calls and
is removed from everything this script prints.
"""
from __future__ import annotations

import argparse
import os
import random
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from warden import safegit  # noqa: E402
from warden.secretscan import redact  # noqa: E402


def remote_url(repo: str, token: str) -> str:
    return "https://x-access-token:%s@github.com/%s.git" % (token, repo) if token else "https://github.com/%s.git" % repo


def attempt(repo_dir: str, url: str, branch: str, env=None):
    """One round. Returns (status, detail): pushed | nothing | retry | fatal."""
    fetched = safegit.run_git(repo_dir, ["fetch", "--quiet", url, "refs/heads/%s" % branch], env=env)
    if fetched.returncode != 0:
        return "retry", "fetch: " + fetched.stderr.strip()[:300]
    remote_sha = safegit.run_git(repo_dir, ["rev-parse", "FETCH_HEAD"], env=env).stdout.strip()
    safegit.check_oid(remote_sha, "fetched sha")
    ahead = safegit.run_git(repo_dir, ["rev-list", "--count", "%s..HEAD" % remote_sha], env=env)
    if ahead.returncode == 0 and ahead.stdout.strip() == "0":
        return "nothing", "already contained in the remote"
    rebased = safegit.run_git(repo_dir, ["rebase", "--quiet", remote_sha], env=env)
    if rebased.returncode != 0:
        safegit.run_git(repo_dir, ["rebase", "--abort"], env=env)
        return "retry", "rebase: " + (rebased.stderr or rebased.stdout).strip()[:300]
    new_sha = safegit.run_git(repo_dir, ["rev-parse", "HEAD"], env=env).stdout.strip()
    res = safegit.push_cas(repo_dir, url, "refs/heads/%s" % branch, new_sha, remote_sha, env=env)
    if res.ok:
        return "pushed", new_sha
    if res.reason == "hook_rejected":
        return "fatal", "%s: %s" % (res.reason, res.detail)
    return "retry", "%s: %s" % (res.reason, res.detail)


def main(argv=None, sleep=time.sleep, rng=random.random) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--repo", default=".", help="the local clone")
    ap.add_argument("--remote-repo", required=True, help="OWNER/NAME on GitHub")
    ap.add_argument("--branch", default="main")
    ap.add_argument("--attempts", type=int, default=30)
    ns = ap.parse_args(argv)
    token = os.environ.get("GH_TOKEN", "")
    if not ns.remote_repo.count("/") == 1 or not ns.branch or ns.branch.startswith("-"):
        print("safe-push: bad --remote-repo or --branch", file=sys.stderr)
        return 2
    url = remote_url(ns.remote_repo, token)
    last = ""
    for n in range(1, max(1, ns.attempts) + 1):
        status, detail = attempt(ns.repo, url, ns.branch)
        detail = redact(detail.replace(token, "***") if token else detail)
        if status == "pushed":
            print("safe-push: pushed %s to %s (attempt %d)" % (detail[:12], ns.branch, n))
            return 0
        if status == "nothing":
            print("safe-push: nothing to push (%s)" % detail)
            return 0
        last = detail
        if status == "fatal":
            print("safe-push: giving up: %s" % detail, file=sys.stderr)
            return 1
        print("safe-push: attempt %d did not land (%s); fetching again" % (n, detail[:120].replace("\n", " ")))
        sleep(5 + rng() * 15)
    print("safe-push: could not push after %d attempts: %s" % (ns.attempts, last), file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main())
