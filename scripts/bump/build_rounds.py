#!/usr/bin/env python3
"""build_rounds.py: a shard's build, then its repair rounds and portfolio rounds, inside the job's time (bump-shard.yml).

Every round edits sources (engine.py repair, portfolio.py apply) and rebuilds what the edits touch. Until 10 Nov 2026 the rounds
ran whatever the time: flt-anthropic's build-once job 28 (run 42678283150) built for 172 minutes, then its rounds took 163 more,
and the job ended 2 minutes inside its 345-minute limit. A job that runs out of time loses everything, and in a build-once also
the pack every later wave restores from.

Now every build gets the job's deadline (tolerant_build.py --deadline). A round that runs out of time is undone: before it starts,
the files it can change are saved (the job's own modules' sources and build outputs, their build-cache entries, the repair state),
and they are put back exactly, so the shard goes on with the last finished build, as if the round had never been tried. No guess
of how long a round takes is needed. A first build that runs out of time keeps what it built (modules it did not finish are left
unbuilt: no olean, no cache key) and no round is tried.

  build_rounds.py --lib DIR --roots R,R --modules build.txt [--own own.txt] --deadline EPOCH --timeout MIN --repair-rounds 4 --portfolio-rounds 3
Writes build-final.log, tb-final.json and rounds.json (what ran, what was undone) in the working directory.
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import tolerant_build as tb  # noqa: E402
from wave_pack import OUT  # noqa: E402

SUFFIXES = tb.SUFFIXES

OUT_OF_TIME = 3  # tolerant_build.py's exit when its deadline stopped it


class OutOfTime(Exception):
    """an edit (engine.py repair, portfolio.py apply) that the deadline stopped: the round is put back like one whose build ran out of time"""


def module_paths(lib: Path, roots: list[str], modules: list[str]) -> list[str]:
    """Every file a round can change for these modules, relative to the library: the source, everything Lean writes for it, its build-cache entry"""
    sources = tb.module_files(lib, roots, follow_imports=True)
    out: list[str] = []
    for m in modules:
        if m not in sources:
            raise SystemExit(f"pipeline error: {m} is in the module list but no source of it is found under {roots}: a round could edit it and it would not be put back")
        out.append(str(sources[m].relative_to(lib)))
        stem = OUT.joinpath(*tb.split_mod(m))
        out += [f"{stem}{s}" for s in SUFFIXES]
        out += [f".bump-cache/{m}.key", f".bump-cache/{m}.log.json"]
    return out


def linkable(rel: str) -> bool:
    """A build output: tolerant_build.py removes it before Lean writes a new one, so a hard link keeps the old content (a source or a cache entry is rewritten in place: copied)"""
    return rel.endswith(SUFFIXES) and rel.startswith(str(OUT) + "/")


def _keep(src: Path, dst: Path, rel: str) -> None:
    if linkable(rel):
        try:
            os.link(src, dst)
            return
        except OSError:  # another file system: a copy is as good, only slower
            pass
    shutil.copy2(src, dst)


def save(lib: Path, paths: list[str], extra: list[Path], into: Path) -> dict:
    """The files that exist now (build outputs by hard link, the rest copied), and the list of those that do not (a round may create them; putting back removes them).
    Hard links: a deep job's own build outputs are hundreds of MB and a shard's closure several GB, saved before each of up to 7 rounds."""
    if into.exists():
        shutil.rmtree(into)
    into.mkdir(parents=True)
    had: list[str] = []
    for rel in paths:
        f = lib / rel
        if f.exists():
            dst = into / "lib" / rel
            dst.parent.mkdir(parents=True, exist_ok=True)
            _keep(f, dst, rel)
            had.append(rel)
    kept_extra: list[str] = []
    for i, f in enumerate(extra):
        if f.exists():
            shutil.copy2(f, into / f"extra-{i}")
            kept_extra.append(str(f))
    manifest = {"paths": paths, "had": had, "extra": [str(f) for f in extra], "had_extra": kept_extra}
    (into / "manifest.json").write_text(json.dumps(manifest))
    return manifest


def put_back(lib: Path, into: Path) -> int:
    """The files exactly as save() found them: saved ones copied back, ones that did not exist removed. Returns how many files were restored or removed."""
    m = json.loads((into / "manifest.json").read_text())
    had, n = set(m["had"]), 0
    for rel in m["paths"]:
        f = lib / rel
        if rel in had:
            f.parent.mkdir(parents=True, exist_ok=True)
            if linkable(rel):
                f.unlink(missing_ok=True)
                _keep(into / "lib" / rel, f, rel)
            else:  # written back in place, through a symlink when it is one (a `srcdir` library links its sources): the link stays, the file it points to gets its text back
                shutil.copyfile(into / "lib" / rel, f)
            n += 1
        elif f.exists() or f.is_symlink():
            f.unlink()
            n += 1
    had_extra = set(m["had_extra"])
    for i, name in enumerate(m["extra"]):
        f = Path(name)
        if name in had_extra:
            shutil.copy2(into / f"extra-{i}", f)
        else:
            f.unlink(missing_ok=True)
    return n


def run_rounds(build, edit, snapshot, restore, repair_rounds: int, portfolio_rounds: int, clock=time.time, deadline: float = 0) -> dict:
    """The round loop. build(name) -> exit code (0, or OUT_OF_TIME); edit(kind, n, last) -> True when it changed a source; snapshot() before a round, restore() after one that ran out of time.
    Returns {"last": the name of the last finished build, "rounds": [...], "stopped": None | where the deadline stopped the work}."""
    log: list[dict] = []
    rc = build("s0")
    if rc not in (0, OUT_OF_TIME):
        raise SystemExit(f"tolerant_build failed with exit {rc} on the first build")
    if rc == OUT_OF_TIME:
        return {"last": "s0", "rounds": log, "stopped": "s0: the first build ran out of time; what it finished is kept, no round is tried"}
    last = "s0"
    for kind, count, prefix in (("repair", repair_rounds, "r"), ("portfolio", portfolio_rounds, "p")):
        for n in range(1, count + 1):
            if deadline and clock() >= deadline:
                return {"last": last, "rounds": log, "stopped": f"{kind} {n}: not started, the deadline has passed"}
            snapshot()
            t0 = clock()
            try:
                changed = edit(kind, n, last)
            except OutOfTime:
                restore()
                log.append({"round": f"{prefix}{n}", "changed": True, "undone": True, "minutes": round((clock() - t0) / 60, 1)})
                return {"last": last, "rounds": log, "stopped": f"{kind} {n}: its edit ran out of time and was undone; the shard keeps build {last}"}
            if not changed:
                log.append({"round": f"{prefix}{n}", "changed": False})
                break
            rc = build(f"{prefix}{n}")
            if rc not in (0, OUT_OF_TIME):
                raise SystemExit(f"tolerant_build failed with exit {rc} in round {prefix}{n}")
            if rc == OUT_OF_TIME:
                restore()
                log.append({"round": f"{prefix}{n}", "changed": True, "undone": True, "minutes": round((clock() - t0) / 60, 1)})
                return {"last": last, "rounds": log, "stopped": f"{kind} {n}: ran out of time and was undone; the shard keeps build {last}"}
            log.append({"round": f"{prefix}{n}", "changed": True, "minutes": round((clock() - t0) / 60, 1)})
            last = f"{prefix}{n}"
    return {"last": last, "rounds": log, "stopped": None}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--lib", required=True)
    ap.add_argument("--roots", required=True)
    ap.add_argument("--modules", required=True, help="build.txt")
    ap.add_argument("--own", default="", help="own.txt of a build-once job (only these are built, edited and saved)")
    ap.add_argument("--deadline", type=float, required=True, help="epoch seconds by which every build of this step is done")
    ap.add_argument("--timeout", required=True, help="minutes per module")
    ap.add_argument("--repair-rounds", type=int, default=4)
    ap.add_argument("--portfolio-rounds", type=int, default=3)
    ap.add_argument("--snapshot", default="../round-snapshot")
    a = ap.parse_args()
    lib = Path(a.lib)
    roots = [r for r in a.roots.split(",") if r]
    names = [ln.strip() for ln in Path(a.own or a.modules).read_text().splitlines() if ln.strip()]
    paths = module_paths(lib.resolve(), roots, names)
    extra = [Path("moves.json"), Path("state.json")]
    snap = Path(a.snapshot)
    Path("moves.json").write_text('{"moves":{}}')
    own = ["--own", a.own] if a.own else []
    py = sys.executable

    def build(name: str) -> int:
        cmd = [py, str(HERE / "tolerant_build.py"), "--lib", a.lib, "--roots", a.roots, "--modules", a.modules, "--log", f"build-{name}.log", "--report", f"tb-{name}.json",
               "--jobs", "4", "--cache", str(lib / ".bump-cache"), "--timeout", a.timeout, "--deadline", str(a.deadline), *own]
        return subprocess.run(cmd).returncode

    def bounded(cmd: list[str]) -> None:
        try:
            subprocess.run(cmd, check=True, timeout=max(1.0, a.deadline - time.time()))
        except subprocess.TimeoutExpired as e:
            raise OutOfTime from e

    def edit(kind: str, n: int, last: str) -> bool:
        if kind == "repair":
            bounded([py, str(HERE / "engine.py"), "repair", "--lib", a.lib, "--log", f"build-{last}.log", "--roots", a.roots, "--moves", "moves.json", "--state", "state.json",
                     "--round", str(n), "--out", f"repair-{n}.json", "--deprecations"])
            return bool(json.loads(Path(f"repair-{n}.json").read_text())["changed"])
        bounded([py, str(HERE / "portfolio.py"), "apply", "--lib", a.lib, "--log", f"build-{last}.log", "--out", f"portfolio-{n}.json"])
        d = json.loads(Path(f"portfolio-{n}.json").read_text())
        return d["theorems_rewritten"] + d.get("superfluous_tactics_deleted", 0) != 0

    res = run_rounds(build, edit, lambda: save(lib, paths, extra, snap), lambda: put_back(lib, snap), a.repair_rounds, a.portfolio_rounds, deadline=a.deadline)
    shutil.rmtree(snap, ignore_errors=True)
    shutil.copy(f"build-{res['last']}.log", "build-final.log")
    shutil.copy(f"tb-{res['last']}.json", "tb-final.json")
    Path("rounds.json").write_text(json.dumps(res, indent=1))
    d = json.loads(Path("tb-final.json").read_text())
    print(d["by_state"], d["seconds"], "s")
    if res["stopped"]:
        print(f"::warning::{res['stopped']}")


if __name__ == "__main__":
    main()
