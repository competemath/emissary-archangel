#!/usr/bin/env python3
"""open_intake_pr.py — turn a finished factory run into an intake PR on tengoku (or its sandbox).

  open_intake_pr.py --key K --run RUN_ID --repo competemath/tengoku[-sandbox] [--mode strict|proposed|wide] [--factory competemath/emissary-archangel] [--dry-run]
                    [--part N [--depends-on PR]] [--auto-merge]

Downloads the run's artifact `bump-K`, checks the build attestation of the archive against the factory's workflows (the gate does it
again; refusing here saves a PR), unpacks the bundle into the tree's layout (Tengoku/<Library>/…, Tengoku/<Library>.lean,
data/intake/K/manifest.jsonl + report.json), adds the one import line to Tengoku/All.lean, commits it signed off and opens the PR. The
bundle is the archive's bytes: nothing is edited on the way (tengoku's scripts/ci/intake_check.py rebuilds the archive from the PR's files).

A library cut into parts (the run was dispatched with `parts`, scripts/bump/bundle_layers.py) is sent part by part. `--part 1` is an ordinary intake PR with the first part's
archive. `--part N` (N > 1) is an EXTEND PR: the library is in the tree already, the part's modules are added, the root file is the part's (the imports so far), the
manifest is the tree's with the part's lines appended, the part's report is data/intake/K/parts/NNN.json, and Tengoku/All.lean is not touched; `--depends-on` names
the PR of the part before (`#N` or its URL; the description says `Depends-On: #N`, which the gate waits for). Parts must merge in order.

In GitHub Actions (intake-open.yml) the factory's own token reads the run and verifies the attestation, and the intake App's token (TENGOKU_TOKEN) does everything on the target
repository: the clone, the push and the pull request. The commit is then the App's, signed off as it (BOT_NAME, BOT_EMAIL). `--auto-merge` arms auto-merge (the merge queue) on the PR it
opened; the caller passes it only for an extend part, and only when the lane is switched on.
"""

from __future__ import annotations

import argparse
import base64
import json
import re
import os
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path


def parts_total(plan: dict) -> int:
    """How many parts the library has: the last part's number (a recut from the tree starts at 2, so counting the plan's parts would say one too few)."""
    return max(part["part"] for part in plan["parts"])


def refuse_empty(report: dict, name: str) -> None:
    """A bundle without a verified theorem is not an intake: tengoku collects theorems (2026-10-09: sphere-packing-ext, cslib and aisafety-atlas came out as 0 theorems in 1 or 2 modules)."""
    if not report.get("theorems"):
        sys.exit(f"EMPTY BUNDLE: no verified theorem in {name}, nothing to intake")


def sh(*a: str, cwd: str | None = None, check: bool = True, env: dict[str, str] | None = None) -> str:
    r = subprocess.run(a, cwd=cwd, capture_output=True, text=True, env=env)
    if check and r.returncode:
        sys.exit(f"{' '.join(a)}: {(r.stdout + r.stderr)[-600:]}")
    return r.stdout.strip()


def target_env(env: dict[str, str]) -> dict[str, str]:
    """The environment for git and gh on the TARGET repository: with TENGOKU_TOKEN, that token (and nothing in the arguments: git reads the header from its config environment);
    without it, whatever the caller is logged in as, as before."""
    token = env.get("TENGOKU_TOKEN")
    if not token:
        return dict(env)
    basic = base64.b64encode(f"x-access-token:{token}".encode()).decode()
    return {**env, "GH_TOKEN": token, "GIT_CONFIG_COUNT": "1", "GIT_CONFIG_KEY_0": "http.https://github.com/.extraheader", "GIT_CONFIG_VALUE_0": f"AUTHORIZATION: basic {basic}"}


def commit_identity(env: dict[str, str]) -> dict[str, str]:
    """The App's name and address for the commit (and so for its sign-off), when BOT_NAME and BOT_EMAIL are given; else git's own configuration."""
    name, email = env.get("BOT_NAME"), env.get("BOT_EMAIL")
    if not (name and email):
        return {}
    return {"GIT_AUTHOR_NAME": name, "GIT_AUTHOR_EMAIL": email, "GIT_COMMITTER_NAME": name, "GIT_COMMITTER_EMAIL": email}


def pascal(s: str) -> str:
    return "".join(p[:1].upper() + p[1:] for p in re.split(r"[-_ ]+", s) if p)


def with_import(text: str, line: str) -> str:
    """`text` (Tengoku/All.lean) with the import `line` added: before the first import that sorts after it, at the end when none does. Appending every library at the end
    made two intake PRs in the merge queue conflict on the last line (2026-10-08, #348); at its own place a library only conflicts with one that sorts into the same gap."""
    lines = text.split("\n")
    if line in lines:
        return text
    imports = [i for i, ln in enumerate(lines) if ln.startswith("import ")]
    at = next((i for i in imports if lines[i].lower() > line.lower()), None)
    if at is None:
        return text + ("" if text.endswith("\n") else "\n") + line + "\n"
    return "\n".join([*lines[:at], line, *lines[at:]])


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
        allp.write_text(with_import(allp.read_text(), f"import Tengoku.{ns}"))


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--key", required=True)
    ap.add_argument("--run", required=True)
    ap.add_argument("--repo", required=True)
    ap.add_argument("--mode", default="strict", choices=["strict", "proposed", "wide"])
    ap.add_argument("--factory", default="competemath/emissary-archangel")
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--part", type=int, help="send this part of a library cut into parts (1 = the intake PR, later ones extend PRs)")
    ap.add_argument("--depends-on", help="extend PRs: the PR of the part before (`#N` or its URL), named in the description as `Depends-On: #N`")
    ap.add_argument("--auto-merge", action="store_true", help="arm auto-merge (the merge queue) on the PR once it is open; the caller passes it for extend parts when the lane is on")
    a = ap.parse_args()
    if a.part is not None and a.part < 1:
        sys.exit("--part counts from 1")
    if a.auto_merge and not (a.part and a.part > 1):
        sys.exit("--auto-merge belongs to an extend PR (--part N, N > 1): a first part adds a line to an owned file and needs a person")
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
    refuse_empty(report, tar.name)
    ns = pascal(a.key)
    repo = work / "repo"
    tenv = target_env(dict(os.environ))
    sh("git", "clone", "-q", "--filter=blob:none", "--no-checkout", f"https://github.com/{a.repo}", str(repo), env=tenv)
    sh("git", "sparse-checkout", "set", "--no-cone", "/Tengoku/All.lean", f"/Tengoku/{ns}.lean", f"/Tengoku/{ns}/", f"/data/intake/{a.key}/", cwd=str(repo))
    sh("git", "checkout", "-q", "main", cwd=str(repo), env=tenv)
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
        nparts = f" of {parts_total(json.loads(plan_file.read_text()))}" if plan_file else ""
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
    sh("git", "commit", "-q", "-s", "-m", msg + "\n\nCo-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>", cwd=str(repo), env={**tenv, **commit_identity(dict(os.environ))})
    print(f"branch {branch}: {msg}; {n_files} files")
    if a.dry_run:
        print(f"dry run: nothing pushed (the clone is {repo})")
        return
    sh("git", "push", "-q", "origin", branch, cwd=str(repo), env=tenv)
    url = sh("gh", "pr", "create", "-R", a.repo, "--base", "main", "--head", branch, "--title", msg, "--body", body, env=tenv)
    print(url)
    if a.auto_merge:
        r = subprocess.run(["gh", "pr", "merge", url, "--auto", "--merge"], capture_output=True, text=True, env=tenv)
        print("auto-merge armed" if r.returncode == 0 else f"auto-merge NOT armed: {(r.stdout + r.stderr).strip()[-300:]}")


if __name__ == "__main__":
    main()
