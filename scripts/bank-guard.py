#!/usr/bin/env python3
"""The checks scripts/bank-flush.mjs passes before it may push a branch and open a pull request into the tree.

    python3 scripts/bank-guard.py --title T --body-file F --branch B --base main --expect-target ID --file PATH [--file PATH ...]
        [--repo-dir TREE --base-rev origin/main --head-rev HEAD --policy scripts/agent-paths.json --class translator | --skip-scope]

Three independent checks; any failure is a refusal (exit 1) and bank-flush leaves the bank where it is:

1. warden.secretscan over every file the pull request will carry (the staged records), added line by line: a record that holds
   something shaped like a credential is never published. Findings are reported as file:line:kind, never the value.
2. warden.safegit.validate_pr over the title, body, base and head: exactly one v1 target marker whose ``target`` is the one
   bank-flush meant to write, a base branch from the allowlist, sane lengths, no control characters, and a secret scan of the
   title and body (a missing scanner counts as a failure).
3. warden.scope over the commit bank-flush made (git objects only): the change adds only paths the scope policy lists for the
   class (scripts/agent-paths.json: data/staging/<library>/<batch>.jsonl and nothing else), as mode 100644, with no deletion,
   no binary file and no more files or lines than a batch.

Exit status: 0 all clear, 1 refused, 2 bad input.
"""
from __future__ import annotations

import argparse
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from warden import safegit, scope, secretscan  # noqa: E402


def check_files(paths):
    """secretscan every file; returns a list of "file:line: kind" strings (the preview is left out on purpose)."""
    found = []
    for path in paths:
        with open(path, "rb") as fh:
            text = fh.read().decode("utf-8", errors="replace")
        for f in secretscan.scan(text, path):
            found.append("%s:%d: %s" % (path, f.line, f.kind))
    return found


def check_pr(title, body, *, branch, base, expect_target):
    check = safegit.validate_pr(title, body, base=base, head=branch, allowed_bases=[base], marker_required=True, require_scan=True)
    problems = list(check.problems)
    if check.marker is not None and check.marker.get("target") != expect_target:
        problems.append("target marker names %r, expected %r" % (check.marker.get("target"), expect_target))
    return problems


def check_scope(repo_dir, base_rev, head_rev, policy_path, actor_class):
    policy = scope.Policy.load(policy_path)
    result = scope.check(repo_dir, base_rev, head_rev, policy, actor_class)
    return ["%s %s %s" % (v.code, v.path or "-", v.detail) for v in result.violations]


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--title", required=True)
    ap.add_argument("--body-file", required=True)
    ap.add_argument("--branch", required=True)
    ap.add_argument("--base", default="main")
    ap.add_argument("--expect-target", required=True)
    ap.add_argument("--file", action="append", default=[], help="a file the pull request will carry (repeatable)")
    ap.add_argument("--repo-dir")
    ap.add_argument("--base-rev", default="origin/main")
    ap.add_argument("--head-rev", default="HEAD")
    ap.add_argument("--policy", default=os.path.join(HERE, "agent-paths.json"))
    ap.add_argument("--class", dest="actor_class", default="translator")
    ap.add_argument("--skip-scope", action="store_true", help="no commit exists yet (a dry run): do checks 1 and 2 only")
    ns = ap.parse_args(argv)
    if not ns.file:
        print("bank-guard: no --file: nothing to check is a refusal", file=sys.stderr)
        return 2
    if not ns.skip_scope and not ns.repo_dir:
        print("bank-guard: --repo-dir is required unless --skip-scope", file=sys.stderr)
        return 2
    try:
        with open(ns.body_file, "r", encoding="utf-8") as fh:
            body = fh.read()
        problems = []
        problems += ["secretscan " + p for p in check_files(ns.file)]
        problems += ["pull request " + p for p in check_pr(ns.title, body, branch=ns.branch, base=ns.base, expect_target=ns.expect_target)]
        if not ns.skip_scope:
            problems += ["scope " + p for p in check_scope(ns.repo_dir, ns.base_rev, ns.head_rev, ns.policy, ns.actor_class)]
    except (OSError, scope.PolicyError) as exc:
        print("bank-guard: %s" % exc, file=sys.stderr)
        return 2
    for p in problems:
        print("bank-guard: REFUSED: " + p)
    if not problems:
        print("bank-guard: ok (%d file(s), marker %s%s)" % (len(ns.file), ns.expect_target, "" if not ns.skip_scope else ", scope not checked"))
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
