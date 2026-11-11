#!/usr/bin/env python3
"""wave_pack.py: what one job of a build-once hands to the jobs after it (build_waves.py plans the jobs).

  wave_pack.py pack --lib DIR --roots R,R --modules own.txt --report tb.json --out DIR     this job's oleans, their cache entries and the sources it repaired, with a manifest
  wave_pack.py restore --lib DIR --packs DIR --modules closure.txt        the files of exactly those modules, out of every pack under DIR
  wave_pack.py fetch --lib DIR --modules closure.txt --repo R --run ID --key K --shards 1,2   the same, each pack downloaded when its turn comes and deleted after
  wave_pack.py place --from DIR --lib DIR                                 moves what was restored into the library, once the library is ready for it

A late job needs most of a 60,000-module library and a whole pack would not fit beside it, so a restore takes only the files of the job's closure. A module no pack knows stops the job: a lost job upstream
must not look like a module that failed to build. A module a pack lists with no files is one its job could not build, and tolerant_build --own reports it as blocked."""

import argparse
import json
import os
import subprocess
import sys
import tempfile
import time
from pathlib import Path, PurePosixPath

sys.path.insert(0, str(Path(__file__).resolve().parent))

import tolerant_build as tb  # noqa: E402

OUT = PurePosixPath(".lake/build/lib/lean")
SUFFIXES = tb.SUFFIXES  # everything Lean writes for a module (tolerant_build.py says why each is needed)
ARCHIVE, MANIFEST = "pack.tar.zst", "manifest.json"


def files_of(lib: Path, mod: str, source: str) -> list[str]:
    """The files of a module that exist, relative to the library. Nothing when it left no olean: a source with no olean is not a built module."""
    parts = tb.split_mod(mod)
    stem = OUT.joinpath(*parts)
    if not (lib / f"{stem}.olean").exists():
        return []
    built = [f"{stem}{s}" for s in SUFFIXES if (lib / f"{stem}{s}").exists()]
    return sorted([*built, f".bump-cache/{mod}.key", f".bump-cache/{mod}.log.json", source])


def _listing(paths: list[str]) -> tempfile.NamedTemporaryFile:
    """Each path behind ./ so that no name reads as an option of tar (the same words on Linux's tar and the BSD tar of a laptop)."""
    f = tempfile.NamedTemporaryFile("w", encoding="utf-8", suffix=".list")
    f.write("".join(f"./{p}\n" for p in paths))
    f.flush()
    return f


def _create(archive: Path, lib: Path, paths: list[str]) -> None:
    with _listing(paths) as f, subprocess.Popen(["tar", "-cf", "-", "-C", str(lib), "-h", "-T", f.name], stdout=subprocess.PIPE) as t:  # -h: a source linked into place (sources.json srcdir) travels as the text the job built
        subprocess.run(["zstd", "-T0", "-q", "-f", "-o", str(archive)], stdin=t.stdout, check=True)
        t.stdout.close()
        if t.wait():
            raise RuntimeError(f"tar could not pack {archive}")


def _extract(archive: Path, lib: Path, paths: list[str]) -> None:
    with _listing(paths) as f, subprocess.Popen(["zstd", "-dc", "-q", str(archive)], stdout=subprocess.PIPE) as z:
        subprocess.run(["tar", "-xf", "-", "-C", str(lib), "-T", f.name], stdin=z.stdout, check=True)
        z.stdout.close()
        if z.wait():
            raise RuntimeError(f"{archive} is damaged")


def built_in(report: dict) -> set[str]:
    """The modules the job's LAST build produced (tolerant_build's report). A module whose import stopped building in a later repair round keeps the olean of the round before: that file is stale, and handing
    it on would let later jobs build on a module that no longer stands."""
    return {m for m, st in report["status"].items() if st["state"] in ("clean", "errors")}


def pack(lib: Path, sources: dict[str, Path], modules: list[str], out: Path, built: set[str]) -> dict[str, list[str]]:
    unknown = [m for m in modules if m not in sources]
    if unknown:
        raise ValueError(f"{len(unknown)} modules are not in the library (first: {unknown[:3]})")
    manifest = {m: files_of(lib, m, str(sources[m].relative_to(lib))) if m in built else [] for m in modules}
    out.mkdir(parents=True, exist_ok=True)
    listing = sorted({f for fs in manifest.values() for f in fs})
    if listing:
        _create(out / ARCHIVE, lib, listing)
    (out / MANIFEST).write_text(json.dumps(manifest, sort_keys=True), encoding="utf-8")
    return manifest


def _checked(manifest: dict[str, list[str]], where: Path) -> None:
    for m, fs in manifest.items():
        for f in fs:
            p = PurePosixPath(f)
            if p.is_absolute() or ".." in p.parts:
                raise ValueError(f"{where}: module {m} lists a file outside the library: {f}")


def _from_pack(found: Path, lib: Path, wanted: set[str], owner: dict[str, Path]) -> tuple[int, int]:
    manifest = json.loads(found.read_text(encoding="utf-8"))
    _checked(manifest, found)
    listing: list[str] = []
    restored = empty = 0
    for m in sorted(wanted & set(manifest)):
        if m in owner:
            raise ValueError(f"{m} is in two packs: {owner[m]} and {found}")
        owner[m] = found
        listing += manifest[m]
        restored += bool(manifest[m])
        empty += not manifest[m]
    if listing:
        _extract(found.parent / ARCHIVE, lib, listing)
    return restored, empty


def _lost(wanted: set[str], owner: dict[str, Path]) -> None:
    lost = sorted(wanted - set(owner))
    if lost:
        raise ValueError(f"{len(lost)} modules are in no pack (first: {lost[:5]}): a job before this one is missing")


def restore(lib: Path, packs: Path, modules: list[str]) -> dict[str, int]:
    wanted, owner = set(modules), {}
    restored = empty = 0
    for found in sorted(packs.rglob(MANIFEST)):
        r, e = _from_pack(found, lib, wanted, owner)
        restored, empty = restored + r, empty + e
    _lost(wanted, owner)
    return {"restored": restored, "no_olean": empty}


def fetch_all(lib: Path, modules: list[str], shards: list[int], download, work: Path) -> dict[str, int]:
    """restore, with the packs fetched one at a time and each deleted once read: a late job's closure is most of the library, and every pack on disk at once would not fit beside it"""
    lib.mkdir(parents=True, exist_ok=True)
    work.mkdir(parents=True, exist_ok=True)
    wanted, owner = set(modules), {}
    restored = empty = 0
    for s in shards:
        with tempfile.TemporaryDirectory(dir=work) as d:
            download(s, Path(d))
            r, e = _from_pack(Path(d) / MANIFEST, lib, wanted, owner)
            restored, empty = restored + r, empty + e
    _lost(wanted, owner)
    return {"restored": restored, "no_olean": empty}


def run_of(shard: int, run: str, reuse_run: str, reuse_packs: set[int]) -> str:
    """the run a shard's pack comes from: the earlier run for a good pack (lane_reuse.py good_packs: every good pack, of a kept job or of one that runs again, such as a
    job stopped in Gate 2 after its pack), this run for any other"""
    return reuse_run if reuse_run and shard in reuse_packs else run


def gh_download(repo: str, run: str, key: str, tries: int = 4, wait: int = 30, runner=subprocess.run, sleep=time.sleep, reuse_run: str = "", reuse_packs: frozenset[int] = frozenset()):
    def download(shard: int, into: Path) -> None:
        source = run_of(shard, run, reuse_run, set(reuse_packs))
        for attempt in range(1, tries + 1):
            r = runner(["gh", "run", "download", source, "-R", repo, "-n", f"wave-{key}-{shard}", "-D", str(into)], check=False)
            if r.returncode == 0:
                return
            if attempt < tries:
                sleep(attempt * wait)
        raise RuntimeError(f"the pack of shard {shard} could not be fetched in {tries} tries")

    return download


def place(src: Path, lib: Path) -> int:
    """Moves what was restored into the library, a moved file replacing what is there: the restored text is what the earlier job built."""
    moved = 0
    for f in sorted(p for p in src.rglob("*") if p.is_file() and not p.is_symlink()):
        dst = lib / f.relative_to(src)
        dst.parent.mkdir(parents=True, exist_ok=True)
        os.replace(f, dst)
        moved += 1
    return moved


def _names(path: str) -> list[str]:
    return [ln.strip() for ln in Path(path).read_text(encoding="utf-8").splitlines() if ln.strip()]


def main() -> None:
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("pack")
    p.add_argument("--lib", required=True)
    p.add_argument("--roots", required=True)
    p.add_argument("--modules", required=True)
    p.add_argument("--out", required=True)
    p.add_argument("--report", required=True, help="tolerant_build's report of the last build")
    r = sub.add_parser("restore")
    r.add_argument("--lib", required=True)
    r.add_argument("--packs", required=True)
    r.add_argument("--modules", required=True)
    f = sub.add_parser("fetch")
    f.add_argument("--lib", required=True)
    f.add_argument("--modules", required=True)
    f.add_argument("--repo", required=True)
    f.add_argument("--run", required=True)
    f.add_argument("--key", required=True)
    f.add_argument("--shards", required=True, help="comma list")
    f.add_argument("--work", default="wave-packs")
    f.add_argument("--reuse-run", default="", help="an earlier run of the build-once whose packs this run reuses (bump-waves.yml reuse_from)")
    f.add_argument("--reuse-packs", default="", help="comma list: the shards whose pack comes from --reuse-run (lane_reuse.py)")
    m = sub.add_parser("place")
    m.add_argument("--from", dest="src", required=True)
    m.add_argument("--lib", required=True)
    a = ap.parse_args()
    lib = Path(a.lib).resolve()
    if a.cmd == "fetch":
        reuse = frozenset(int(x) for x in a.reuse_packs.split(",") if x)
        print(fetch_all(lib, _names(a.modules), [int(x) for x in a.shards.split(",") if x], gh_download(a.repo, a.run, a.key, reuse_run=a.reuse_run, reuse_packs=reuse), Path(a.work)))
    elif a.cmd == "place":
        print(f"placed {place(Path(a.src), lib)} files")
    elif a.cmd == "pack":
        m = pack(lib, tb.module_files(lib, [x for x in a.roots.split(",") if x], follow_imports=True), _names(a.modules), Path(a.out), built_in(json.loads(Path(a.report).read_text(encoding="utf-8"))))
        print(f"packed {sum(bool(v) for v in m.values())} of {len(m)} modules")
    else:
        print(restore(lib, Path(a.packs), _names(a.modules)))


if __name__ == "__main__":
    main()
