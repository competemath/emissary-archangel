#!/usr/bin/env python3
"""Refresh the vendored copy of tengoku-warden from a checkout, and rewrite PIN.

    python3 scripts/warden/refresh.py /path/to/tengoku-warden [--check]

The files listed in VENDORED are copied byte for byte from <checkout>/warden/ into this directory, and PIN records the
checkout's commit and the sha256 of every copied file. scripts/agent-tests/test_warden_pin.py fails if a file here differs
from PIN, so a hand edit of a vendored file cannot go unnoticed: change tengoku-warden, then run this script.

The checkout must be a clean git work tree of competemath/tengoku-warden, so that the recorded commit really names the bytes.
With --check nothing is written; the exit status says whether this directory already matches the checkout.

This file is ours, not vendored, and is not listed in PIN.
"""
from __future__ import annotations

import argparse
import hashlib
import os
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
VENDORED = (
    "__init__", "__main__", "toolpolicy", "envscrub", "jail", "selftest", "egress", "secretscan", "sanitize", "caps",
    "safegit", "scope", "audit", "untrusted", "verdict",
)
REPO_URL = "https://github.com/competemath/tengoku-warden"
HEADER = (
    "# Vendored from competemath/tengoku-warden by scripts/warden/refresh.py. Do not edit the files listed here:\n"
    "# change tengoku-warden, then run `python3 scripts/warden/refresh.py <checkout>`.\n"
)


def sha256_of(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def git(checkout: str, *args: str) -> str:
    out = subprocess.run(["git", "-C", checkout] + list(args), check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    return out.stdout.decode("utf-8", "replace").strip()


def render_pin(commit: str, digests) -> str:
    lines = [HEADER.rstrip("\n"), "repo " + REPO_URL, "commit " + commit]
    lines += ["%s  %s" % (digest, name) for name, digest in digests]
    return "\n".join(lines) + "\n"


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("checkout", help="a clean work tree of competemath/tengoku-warden")
    ap.add_argument("--check", action="store_true", help="write nothing; exit 1 if this directory differs from the checkout")
    ns = ap.parse_args(argv)
    src = os.path.join(ns.checkout, "warden")
    if not os.path.isdir(src):
        print("refresh: %s has no warden/ directory" % ns.checkout, file=sys.stderr)
        return 2
    try:
        commit = git(ns.checkout, "rev-parse", "HEAD")
        dirty = git(ns.checkout, "status", "--porcelain", "--", "warden")
    except (OSError, subprocess.CalledProcessError) as exc:
        print("refresh: cannot read the checkout's git state: %s" % exc, file=sys.stderr)
        return 2
    if dirty:
        print("refresh: the checkout has uncommitted changes under warden/; the recorded commit would not name these bytes", file=sys.stderr)
        return 2
    digests = []
    differs = []
    for mod in VENDORED:
        name = mod + ".py"
        from_path = os.path.join(src, name)
        if not os.path.isfile(from_path):
            print("refresh: %s is missing from the checkout" % name, file=sys.stderr)
            return 2
        to_path = os.path.join(HERE, name)
        if not os.path.isfile(to_path) or sha256_of(to_path) != sha256_of(from_path):
            differs.append(name)
        if not ns.check:
            shutil.copyfile(from_path, to_path)
        digests.append((name, sha256_of(from_path)))
    pin = render_pin(commit, digests)
    pin_path = os.path.join(HERE, "PIN")
    pin_old = open(pin_path, "r", encoding="utf-8").read() if os.path.isfile(pin_path) else ""
    if ns.check:
        if differs or pin_old != pin:
            print("refresh: differs from %s: %s" % (commit[:12], ", ".join(differs) or "PIN only"))
            return 1
        print("refresh: matches %s" % commit[:12])
        return 0
    with open(pin_path, "w", encoding="utf-8") as fh:
        fh.write(pin)
    print("refresh: %s at %s (%d files%s)" % (REPO_URL, commit[:12], len(digests), ", changed: " + ", ".join(differs) if differs else ", unchanged"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
