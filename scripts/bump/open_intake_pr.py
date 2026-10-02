#!/usr/bin/env python3
"""open_intake_pr.py — turn a finished factory run into an intake PR on tengoku (or its sandbox).

  open_intake_pr.py --key K --run RUN_ID --repo competemath/tengoku[-sandbox] [--mode strict|proposed] [--factory competemath/emissary-archangel] [--dry-run]

Downloads the run's artifact `bump-K`, checks the build attestation of the archive against the factory's workflows (the gate does it
again; refusing here saves a PR), unpacks the bundle into the tree's layout (Tengoku/<Library>/…, Tengoku/<Library>.lean,
data/intake/K/manifest.jsonl + report.json), adds the one import line to Tengoku/All.lean, commits it signed off and opens the PR. The
bundle is the archive's bytes: nothing is edited on the way (tengoku's scripts/ci/intake_check.py rebuilds the archive from the PR's files).
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path


def sh(*a: str, cwd: str | None = None, check: bool = True) -> str:
    r = subprocess.run(a, cwd=cwd, capture_output=True, text=True)
    if check and r.returncode:
        sys.exit(f"{' '.join(a)}: {(r.stdout + r.stderr)[-600:]}")
    return r.stdout.strip()


def pascal(s: str) -> str:
    return "".join(p[:1].upper() + p[1:] for p in re.split(r"[-_ ]+", s) if p)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--key", required=True)
    ap.add_argument("--run", required=True)
    ap.add_argument("--repo", required=True)
    ap.add_argument("--mode", default="strict", choices=["strict", "proposed"])
    ap.add_argument("--factory", default="competemath/emissary-archangel")
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args()
    work = Path(tempfile.mkdtemp())
    sh("gh", "run", "download", a.run, "-R", a.factory, "-n", f"bump-{a.key}", "-D", str(work / "art"))
    tar = next((work / "art").rglob(f"bundle-{a.key}-{a.mode}.tar"))
    ok = False
    for wf in ("bump-library", "bump-sharded"):
        r = subprocess.run(["gh", "attestation", "verify", str(tar), "--repo", a.factory, "--signer-workflow", f"{a.factory}/.github/workflows/{wf}.yml"], capture_output=True, text=True)
        ok = ok or r.returncode == 0
    if not ok:
        sys.exit(f"{tar.name}: no build attestation of {a.factory} matches it")
    stage = work / "bundle"
    with tarfile.open(tar) as tf:
        tf.extractall(stage, filter="data")
    report = json.loads((stage / "report.json").read_text())
    ns = pascal(a.key)
    repo = work / "repo"
    sh("git", "clone", "-q", "--filter=blob:none", "--no-checkout", f"https://github.com/{a.repo}", str(repo))
    sh("git", "sparse-checkout", "set", "--no-cone", "/Tengoku/All.lean", f"/Tengoku/{ns}.lean", f"/Tengoku/{ns}/", cwd=str(repo))
    sh("git", "checkout", "-q", "main", cwd=str(repo))
    if (repo / "Tengoku" / ns).exists() or (repo / "Tengoku" / f"{ns}.lean").exists():
        sys.exit(f"{a.repo} already has Tengoku/{ns}: a library is intaken once")
    branch = f"intake/{a.key}-{a.run}"
    sh("git", "checkout", "-q", "-b", branch, cwd=str(repo))
    for f in sorted(p for p in stage.rglob("*") if p.is_file()):
        rel = f.relative_to(stage)
        dst = repo / ("data/intake/%s/%s" % (a.key, rel) if str(rel) in ("manifest.jsonl", "report.json") else str(rel))
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.write_bytes(f.read_bytes())
    allp = repo / "Tengoku" / "All.lean"
    text = allp.read_text()
    allp.write_text(text + ("" if text.endswith("\n") else "\n") + f"import Tengoku.{ns}\n")
    n_files = sum(1 for _ in (repo / "Tengoku" / ns).rglob("*.lean"))
    msg = f"intake: {a.key} ({report['theorems']} verified theorems in {report['modules_in_bundle']} modules)"
    body = f"""A verified bundle of **{a.key}** from the translation factory ({a.factory}), run [{a.run}](https://github.com/{a.factory}/actions/runs/{a.run}).

- {report['theorems']} theorems of {report['passed_total']} the factory's batched Gate 2 passed, in {report['modules_in_bundle']} modules ({n_files} files); lint mode **{a.mode}**
- every theorem: its statement entails the original's (kernel-checked: identical, or a bridge `new → old`), no `sorry`, only the three standard axioms; the library definitions
  its statement is built on are definitionally equal to the originals; the pruned sources were built clean by the factory
- left out and why: {json.dumps(report.get('left_out', {}))}
- the archive of these files is attested: `gh attestation verify bundle.tar --repo {a.factory}` (the gate rebuilds the archive from this PR's files and checks it)

🤖 Generated with [Claude Code](https://claude.com/claude-code)
"""
    sh("git", "add", "-A", cwd=str(repo))
    sh("git", "commit", "-q", "-s", "-m", msg + "\n\nCo-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>", cwd=str(repo))
    print(f"branch {branch}: {msg}; {n_files} files")
    if a.dry_run:
        print(f"dry run: nothing pushed (the clone is {repo})")
        return
    sh("git", "push", "-q", "origin", branch, cwd=str(repo))
    print(sh("gh", "pr", "create", "-R", a.repo, "--base", "main", "--head", branch, "--title", msg, "--body", body))


if __name__ == "__main__":
    main()
