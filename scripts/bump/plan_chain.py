#!/usr/bin/env python3
"""plan_chain.py OLD_MATHLIB_REV TARGET_TAG [--step N] — the Mathlib releases to bump a library through, oldest first.

Mathlib moves itself one release at a time: a breaking change leaves a `@[deprecated]` alias that says what replaced it,
and the alias is deleted about six months later. Lean's warning ("`old` has been deprecated, use `new` instead") is what
scripts/fix_deprecations.py rewrites call sites from, so the rewrite is only possible while the alias exists. A library
that jumps over 18 releases in one step meets every name deleted in the meantime as a bare "unknown identifier"; stepping
through intermediate releases (each at most `--step` minor versions after the last, default 3 = about three months) gives
the fixer each alias while it still exists.

Prints one `TAG TOOLCHAIN` per line (the target last); a library already within `step` minors of the target gets just the target.
"""

import argparse
import re
import subprocess
import sys

M = "leanprover-community/mathlib4"


def gh(path: str, jq: str) -> str:
    r = subprocess.run(["gh", "api", path, "--jq", jq], capture_output=True, text=True)
    if r.returncode:
        sys.exit(f"gh api {path}: {r.stderr.strip()[:200]}")
    return r.stdout.strip()


def minor_of(toolchain: str) -> int:
    m = re.search(r"v4\.(\d+)", toolchain)
    return int(m.group(1)) if m else 0


def raw(path: str, ref: str) -> str:
    r = subprocess.run(["bash", "-c", f"gh api 'repos/{M}/contents/{path}?ref={ref}' --jq .content | base64 -d"], capture_output=True, text=True)
    if r.returncode or not r.stdout.strip():
        sys.exit(f"cannot read {path} at {ref}")
    return r.stdout.strip()


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("old_rev")
    ap.add_argument("target_tag")
    ap.add_argument("--step", type=int, default=3)
    a = ap.parse_args()
    old = minor_of(raw("lean-toolchain", a.old_rev))
    target_tc = raw("lean-toolchain", a.target_tag)
    new = minor_of(target_tc)
    tags = gh(f"repos/{M}/tags?per_page=100", ".[].name")
    releases = {minor_of(t): t for t in tags.splitlines() if re.fullmatch(r"v4\.\d+\.0", t)}
    tags2 = gh(f"repos/{M}/tags?per_page=100&page=2", ".[].name")
    releases.update({minor_of(t): t for t in tags2.splitlines() if re.fullmatch(r"v4\.\d+\.0", t)})
    out, at = [], old
    while new - at > a.step:
        at += a.step
        tag = releases.get(at) or releases.get(at + 1) or releases.get(at - 1)
        if tag and tag != a.target_tag:
            out.append((tag, raw("lean-toolchain", tag)))
    out.append((a.target_tag, target_tc))
    for tag, tc in out:
        print(tag, tc)


if __name__ == "__main__":
    main()
