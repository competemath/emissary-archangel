#!/usr/bin/env python3
"""open_intake_pr.py — turn a finished factory run into an intake PR on tengoku (or its sandbox).

  open_intake_pr.py --key K --run RUN_ID --repo competemath/tengoku[-sandbox] [--mode strict|proposed] [--factory competemath/emissary-archangel] [--dry-run]
                    [--part N [--depends-on PR]]

Downloads the run's artifact `bump-K`, checks the build attestation of the archive against the factory's workflows (the gate does it
again; refusing here saves a PR), unpacks the bundle into the tree's layout (Tengoku/<Library>/…, Tengoku/<Library>.lean,
data/intake/K/manifest.jsonl + report.json), adds the one import line to Tengoku/All.lean, commits it signed off and opens the PR. The
bundle is the archive's bytes: nothing is edited on the way (tengoku's scripts/ci/intake_check.py rebuilds the archive from the PR's files).

A library cut into parts (the run was dispatched with `parts`, scripts/bump/bundle_layers.py) is sent part by part. `--part 1` is an ordinary intake PR with the first part's
archive. `--part N` (N > 1) is an EXTEND PR: the library is in the tree already, the part's modules are added, the root file is the part's (the imports so far), the
manifest is the tree's with the part's lines appended, the part's report is data/intake/K/parts/NNN.json, and Tengoku/All.lean is not touched; `--depends-on` names
the PR of the part before (`#N` or its URL; the description says `Depends-On: #N`, which the gate waits for). Parts must merge in order.
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


def place(stage: Path, repo: Path, key: str, ns: str, part: int | None) -> None:
    """Write the unpacked bundle (or part) `stage` into the checkout `repo` in the tree's layout. An extend part (N > 1) appends its manifest lines to the tree's and keeps
    its report under parts/; the first part and an unparted bundle are an intake: manifest and report as they are, and the library's one line in Tengoku/All.lean."""
    extend = part is not None and part > 1
    for f in sorted(p for p in stage.rglob("*") if p.is_file()):
        rel = str(f.relative_to(stage))
        if rel == "manifest.jsonl":
            dst = repo / f"data/intake/{key}/manifest.jsonl"
            data = (dst.read_bytes() if extend else b"") + f.read_bytes()
        elif rel == "report.json":
            dst = repo / (f"data/intake/{key}/parts/{part:03d}.json" if extend else f"data/intake/{key}/report.json")
            data = f.read_bytes()
        else:
            dst, data = repo / rel, f.read_bytes()
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.write_bytes(data)
    if not extend:
        allp = repo / "Tengoku" / "All.lean"
        text = allp.read_text()
        allp.write_text(text + ("" if text.endswith("\n") else "\n") + f"import Tengoku.{ns}\n")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--key", required=True)
    ap.add_argument("--run", required=True)
    ap.add_argument("--repo", required=True)
    ap.add_argument("--mode", default="strict", choices=["strict", "proposed"])
    ap.add_argument("--factory", default="competemath/emissary-archangel")
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--part", type=int, help="send this part of a library cut into parts (1 = the intake PR, later ones extend PRs)")
    ap.add_argument("--depends-on", help="extend PRs: the PR of the part before (`#N` or its URL), named in the description as `Depends-On: #N`")
    a = ap.parse_args()
    if a.part is not None and a.part < 1:
        sys.exit("--part counts from 1")
    if a.depends_on and not (a.part and a.part > 1):
        sys.exit("--depends-on belongs to an extend PR (--part N, N > 1)")
    if a.depends_on and not re.search(r"(?:^#|/pull/)(\d+)$", a.depends_on):
        sys.exit("--depends-on is `#N` or the URL of a pull request")
    extend = a.part is not None and a.part > 1
    suffix = "" if a.part is None else f"-part-{a.part:03d}"
    work = Path(tempfile.mkdtemp())
    sh("gh", "run", "download", a.run, "-R", a.factory, "-n", f"bump-{a.key}", "-D", str(work / "art"))
    tar = next((work / "art").rglob(f"bundle-{a.key}-{a.mode}{suffix}.tar"), None)
    if tar is None:
        sys.exit(f"run {a.run} has no archive bundle-{a.key}-{a.mode}{suffix}.tar (was it dispatched with `parts`?)")
    ok = False
    for wf in ("bump-library", "bump-sharded"):
        r = subprocess.run(
            ["gh", "attestation", "verify", str(tar), "--repo", a.factory, "--signer-workflow", f"{a.factory}/.github/workflows/{wf}.yml"],
            capture_output=True,
            text=True,
        )
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
    sh("git", "sparse-checkout", "set", "--no-cone", "/Tengoku/All.lean", f"/Tengoku/{ns}.lean", f"/Tengoku/{ns}/", f"/data/intake/{a.key}/", cwd=str(repo))
    sh("git", "checkout", "-q", "main", cwd=str(repo))
    in_tree = (repo / "Tengoku" / ns).exists() or (repo / "Tengoku" / f"{ns}.lean").exists()
    if extend and not (in_tree and (repo / "data" / "intake" / a.key / "manifest.jsonl").exists()):
        sys.exit(f"{a.repo} does not have {a.key} yet: part 1 (the intake PR) must be in before part {a.part}")
    if not extend and in_tree:
        sys.exit(f"{a.repo} already has Tengoku/{ns}: a library is intaken once")
    branch = f"intake/{a.key}-{a.run}{suffix}"
    sh("git", "checkout", "-q", "-b", branch, cwd=str(repo))
    place(stage, repo, a.key, ns, a.part)
    n_files = sum(1 for _ in (stage / "Tengoku" / ns).rglob("*.lean"))
    nparts = ""
    if a.part is not None:
        plan_file = next((work / "art").rglob(f"parts-{a.mode}.json"), None)
        nparts = f" of {len(json.loads(plan_file.read_text())['parts'])}" if plan_file else ""
    what = "extend" if extend else "intake"
    part_txt = "" if a.part is None else f" part {a.part}{nparts}"
    theorems, modules = report["theorems"], report.get("modules_in_bundle", report.get("modules"))
    msg = f"{what}: {a.key}{part_txt} ({theorems} verified theorems in {modules} modules)"
    depends = f"\nDepends-On: #{re.search(r'(\d+)$', a.depends_on).group(1)}\n" if a.depends_on else ""
    body = f"""{"The next part of" if extend else "A verified bundle of"} **{a.key}**{part_txt} from the translation factory ({a.factory}), run [{a.run}](https://github.com/{a.factory}/actions/runs/{a.run}).
{depends}
- {theorems} theorems{" of " + str(report["passed_total"]) + " the factory's batched Gate 2 passed" if "passed_total" in report else ""}, in {modules} modules ({n_files} files); lint mode **{a.mode}**
- every theorem: its statement entails the original's (kernel-checked: identical, or a bridge `new → old`), no `sorry`, only the three standard axioms; the library definitions
  its statement is built on are definitionally equal to the originals; the pruned sources were built clean by the factory
- left out and why: {json.dumps(report.get("left_out", {}))}
- the archive of these files is attested: `gh attestation verify bundle.tar --repo {a.factory}` (the gate rebuilds the archive from this PR's files and checks it)

🤖 Generated with [Claude Code](https://claude.com/claude-code)
"""
    sh("git", "add", "--sparse", "-A", cwd=str(repo))
    sh("git", "commit", "-q", "-s", "-m", msg + "\n\nCo-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>", cwd=str(repo))
    print(f"branch {branch}: {msg}; {n_files} files")
    if a.dry_run:
        print(f"dry run: nothing pushed (the clone is {repo})")
        return
    sh("git", "push", "-q", "origin", branch, cwd=str(repo))
    print(sh("gh", "pr", "create", "-R", a.repo, "--base", "main", "--head", branch, "--title", msg, "--body", body))


if __name__ == "__main__":
    main()
