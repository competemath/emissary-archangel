#!/usr/bin/env python3
"""RESUME: the shards a recut did not build come from earlier runs (bump-sharded.yml fill_from): fill_from.py --repo R --key K --runs A[,B,...] --shards DIR --work DIR [--plan-new DIR].

`--runs` is the run the resumed lane resumed, then the run that one resumed, and so on (bump-waves.yml passes lane_reuse.py's `fill`), newest first. flt-anthropic, 11 Nov
2026: the resume 43075875630 of 42678283150 kept 63 jobs whose shard packs are in 42678283150, ran 48 of its own, and lost job 43 to a GitHub outage; the bundle of its
resume must read all three runs. A shard already in --shards (built by the run being cut, or by a newer run of the chain) is never replaced by an older copy.

With --plan-new (compose): every run of the chain planned the same shards and built them with the same settings, or the step refuses (--unrecorded vouches for a run
from before plan/inputs.json, as fill_unrecorded did for one run).
"""

from __future__ import annotations

import argparse
import base64
import filecmp
import json
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lane_reuse  # noqa: E402
import shard_pack  # noqa: E402

RUN = re.compile(r"^[1-9][0-9]{0,14}$")
MAX_RUNS = 8  # lane_reuse.MAX_CHAIN
RUN_INFO = "{head_sha, path, display_title, head_branch, event, head_repo: .head_repository.full_name}"


def runs_of(text: str, most: int = MAX_RUNS) -> list[str]:
    runs = text.split(",")  # an empty field (`A,,B`) is a typo, never a run to skip (cubic, #178)
    if not text or len(runs) > most or len(set(runs)) != len(runs) or not all(RUN.match(r) for r in runs):
        raise ValueError(f"fill_from is 1 to {most} distinct run ids, newest first, not {text!r}")
    return runs


def shard_names(names: list[str], key: str) -> list[str]:
    """the shard artifacts of the key (shard-KEY-N): never a wave pack, a plan, or another key's shard"""
    pat = re.compile(rf"^shard-{re.escape(key)}-[0-9]{{1,4}}$")
    return sorted({n for n in names if pat.match(n)}, key=lambda n: int(n.rsplit("-", 1)[1]))


def pack_names(names: list[str], key: str) -> dict[str, str]:
    """{shard-KEY-N: the artifact that holds its pack in this run}: regate-KEY-N when the run judged the shard again (bump-shard.yml regate: the
    shard's pack with the new verdicts, under its own name so that a failed regate never touches the first pack; cubic, #180), else shard-KEY-N"""
    pat = re.compile(rf"^(shard|regate)-{re.escape(key)}-([0-9]{{1,4}})$")
    out: dict[str, str] = {}
    for n in names:
        m = pat.match(n)
        if m and (m.group(1) == "regate" or f"shard-{key}-{m.group(2)}" not in out):
            out[f"shard-{key}-{m.group(2)}"] = n
    return dict(sorted(out.items(), key=lambda kv: int(kv[0].rsplit("-", 1)[1])))


def gh(args: list[str], runner=subprocess.run, sleep=time.sleep, tries: int = 4, wait: int = 30) -> str:
    """a gh call, tried again: the API answered 502 to large job and artifact listings for an hour on 11 Nov 2026"""
    for attempt in range(1, tries + 1):
        r = runner(["gh", *args], capture_output=True, text=True, check=False)
        if r.returncode == 0:
            return r.stdout
        if attempt < tries:
            sleep(attempt * wait)
    raise RuntimeError(f"gh {' '.join(args[:3])} failed {tries} times: {(r.stderr or '')[-300:]}")


def same_plan(old: Path, new: Path, unrecorded: bool, run: str) -> None:
    if not filecmp.cmp(old / "plan.json", new / "plan.json", shallow=False):
        sys.exit(f"the plan of run {run} differs from this run's, so its shards are not these shards (same shards, library commit?)")
    if (old / "inputs.json").exists():
        if not (new / "inputs.json").exists() or not filecmp.cmp(old / "inputs.json", new / "inputs.json", shallow=False):
            sys.exit(f"run {run} was built with other settings (mathlib, toolchain, imports, tengoku_ref, swap_gb, build_timeout_min) than this run")
    elif not unrecorded:
        sys.exit(f"run {run} recorded no settings (it predates plan/inputs.json): pass fill_unrecorded=true to vouch that they are the same")


def library_of_run(repo: str, run: str, key: str, runner=subprocess.run, sleep=time.sleep) -> dict:
    """the library a run built, as its own commit of this repository recorded it (lane_reuse.library_identity)"""
    info = json.loads(gh(["api", f"repos/{repo}/actions/runs/{run}", "--jq", RUN_INFO], runner, sleep))
    why = lane_reuse.untrusted(info, repo, key)
    if why:
        sys.exit(f"run {run} may not hand its artifacts to this one: {why}")
    head = info["head_sha"]
    setup = json.loads(base64.b64decode(gh(["api", f"repos/{repo}/contents/data/exports/{key}/setup.ci.json?ref={head}", "--jq", ".content"], runner, sleep)))
    sources = json.loads(base64.b64decode(gh(["api", f"repos/{repo}/contents/sources.json?ref={head}", "--jq", ".content"], runner, sleep)))
    return lane_reuse.library_identity(setup, sources, key)


def promote(repo: str, key: str, run: str, shards: Path, work: Path, runner=subprocess.run, sleep=time.sleep) -> list[str]:
    """The run's regate packs in place of its shard packs in --shards (the run being cut: its shard packs are downloaded by name pattern, its regate
    packs here). A regate pack replaces the shard's only when it is a whole pack."""
    listing = gh(["api", "--paginate", f"repos/{repo}/actions/runs/{run}/artifacts?per_page=100", "--jq", ".artifacts[] | select(.expired | not) | .name"], runner, sleep)
    done = []
    for name, artifact in pack_names(listing.split(), key).items():
        if not artifact.startswith("regate-"):
            continue
        dest = work / artifact
        gh(["run", "download", run, "-R", repo, "-n", artifact, "-D", str(dest)], runner, sleep)
        if not shard_pack.has_pack(dest):
            sys.exit(f"{artifact} of run {run} holds no whole pack")
        if (shards / name).exists():
            shutil.rmtree(shards / name)
        shutil.move(str(dest), str(shards / name))
        done.append(name)
    return done


def check_library(repo: str, key: str, run: str, library: dict, runner=subprocess.run, sleep=time.sleep) -> None:
    then = library_of_run(repo, run, key, runner, sleep)
    if then != library:
        sys.exit(f"run {run} built another library ({json.dumps(then, sort_keys=True)}) than this run ({json.dumps(library, sort_keys=True)})")


def fill_from(repo: str, key: str, runs: list[str], shards: Path, work: Path, plan_new: Path | None = None, unrecorded: bool = False, runner=subprocess.run, sleep=time.sleep,
              library: dict | None = None) -> dict[str, int]:
    """{run: shards filled in from it}, newest run first. `library` (compose): this run's library; a run that built another one is refused (hacktron, #178)."""
    shards.mkdir(parents=True, exist_ok=True)
    filled: dict[str, int] = {}
    for run in runs:
        d = work / run
        if library is not None:
            check_library(repo, key, run, library, runner, sleep)
        if plan_new is not None:
            gh(["run", "download", run, "-R", repo, "-n", f"plan-{key}", "-D", str(d / "plan")], runner, sleep)
            same_plan(d / "plan", plan_new, unrecorded, run)
        listing = gh(["api", "--paginate", f"repos/{repo}/actions/runs/{run}/artifacts?per_page=100", "--jq", ".artifacts[] | select(.expired | not) | .name"], runner, sleep)
        for name, artifact in pack_names(listing.split(), key).items():
            if (shards / name).exists():  # built by the run being cut or by a newer run of the chain: never replaced
                continue
            gh(["run", "download", run, "-R", repo, "-n", artifact, "-D", str(d / "shards" / name)], runner, sleep)
        before = {p.name for p in shards.iterdir()}
        shard_pack.fill(argparse.Namespace(shards=str(shards), fill=str(d / "shards")))
        filled[run] = len({p.name for p in shards.iterdir()} - before)
    return filled


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", required=True)
    ap.add_argument("--key", required=True)
    ap.add_argument("--runs", default="", help="fill_from: comma list of run ids, newest first")
    ap.add_argument("--promote-from", default="", help="put this run's regate packs in place of its shard packs in --shards (the run being cut)")
    ap.add_argument("--check-library", default="", help="only check that this run (recut_from: its shards are in shards/ before any fill) built the library of --library-from")
    ap.add_argument("--shards", required=True)
    ap.add_argument("--work", required=True)
    ap.add_argument("--plan-new", default="", help="this run's plan directory: every run of the chain must have planned the same shards with the same settings")
    ap.add_argument("--unrecorded", default="false")
    ap.add_argument("--library-from", default="", help="this run's checkout of this repository: every run of the chain must have built the library its setup record names")
    a = ap.parse_args()
    if a.promote_from:
        if not RUN.match(a.promote_from):
            sys.exit("--promote-from is a run id")
        done = promote(a.repo, a.key, a.promote_from, Path(a.shards), Path(a.work))
        print(f"regate packs in place of {len(done)} shard pack(s): {', '.join(done)}")
        return
    if a.check_library:
        # a recut merges the shards of recut_from as they are, before any fill: they are checked here, or another commit's shards pass where a fill's would not (cubic, #178)
        if not RUN.match(a.check_library) or not a.library_from:
            sys.exit("--check-library is a run id, with --library-from")
        base = Path(a.library_from)
        here = lane_reuse.library_identity(json.loads((base / "data" / "exports" / a.key / "setup.ci.json").read_text()), json.loads((base / "sources.json").read_text()), a.key)
        check_library(a.repo, a.key, a.check_library, here)
        print(f"run {a.check_library} built this library")
        return
    try:
        runs = runs_of(a.runs)
    except ValueError as e:
        sys.exit(str(e))
    library = None
    if a.library_from:
        base = Path(a.library_from)
        library = lane_reuse.library_identity(json.loads((base / "data" / "exports" / a.key / "setup.ci.json").read_text()), json.loads((base / "sources.json").read_text()), a.key)
    filled = fill_from(a.repo, a.key, runs, Path(a.shards), Path(a.work), Path(a.plan_new) if a.plan_new else None, a.unrecorded == "true", library=library)
    print("filled in: " + ", ".join(f"{n} shard(s) from run {r}" for r, n in filled.items()))


if __name__ == "__main__":
    main()
