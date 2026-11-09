#!/usr/bin/env python3
"""wave_pack.py: what one job of a build-once hands to the jobs after it (build_waves.py plans the jobs).

  wave_pack.py pack --lib DIR --roots R,R --modules own.txt --out DIR     this job's oleans, their cache entries and the sources it repaired, with a manifest
  wave_pack.py restore --lib DIR --packs DIR --modules closure.txt        the files of exactly those modules, out of every pack under DIR

A late job needs most of a 60,000-module library and a whole pack would not fit beside it, so a restore takes only the files of the job's closure. A module no pack knows stops the job: a lost job upstream
must not look like a module that failed to build. A module a pack lists with no files is one its job could not build, and tolerant_build --own reports it as blocked."""

import argparse
import json
import subprocess
import sys
import tempfile
from pathlib import Path, PurePosixPath

sys.path.insert(0, str(Path(__file__).resolve().parent))

import tolerant_build as tb  # noqa: E402

OUT = PurePosixPath(".lake/build/lib/lean")
SUFFIXES = (".olean", ".olean.server", ".olean.private", ".ilean", ".ir")
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


def pack(lib: Path, sources: dict[str, Path], modules: list[str], out: Path) -> dict[str, list[str]]:
    unknown = [m for m in modules if m not in sources]
    if unknown:
        raise ValueError(f"{len(unknown)} modules are not in the library (first: {unknown[:3]})")
    manifest = {m: files_of(lib, m, str(sources[m].relative_to(lib))) for m in modules}
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


def restore(lib: Path, packs: Path, modules: list[str]) -> dict[str, int]:
    wanted = set(modules)
    owner: dict[str, Path] = {}
    restored = empty = 0
    for found in sorted(packs.rglob(MANIFEST)):
        manifest = json.loads(found.read_text(encoding="utf-8"))
        _checked(manifest, found)
        listing: list[str] = []
        for m in sorted(wanted & set(manifest)):
            if m in owner:
                raise ValueError(f"{m} is in two packs: {owner[m]} and {found}")
            owner[m] = found
            listing += manifest[m]
            restored += bool(manifest[m])
            empty += not manifest[m]
        if listing:
            _extract(found.parent / ARCHIVE, lib, listing)
    lost = sorted(wanted - set(owner))
    if lost:
        raise ValueError(f"{len(lost)} modules are in no pack (first: {lost[:5]}): a job before this one is missing")
    return {"restored": restored, "no_olean": empty}


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
    r = sub.add_parser("restore")
    r.add_argument("--lib", required=True)
    r.add_argument("--packs", required=True)
    r.add_argument("--modules", required=True)
    a = ap.parse_args()
    lib = Path(a.lib).resolve()
    if a.cmd == "pack":
        m = pack(lib, tb.module_files(lib, [x for x in a.roots.split(",") if x], follow_imports=True), _names(a.modules), Path(a.out))
        print(f"packed {sum(bool(v) for v in m.values())} of {len(m)} modules")
    else:
        print(restore(lib, Path(a.packs), _names(a.modules)))


if __name__ == "__main__":
    main()
