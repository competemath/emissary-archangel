#!/usr/bin/env python3
"""shard_pack.py — what a shard sends to the merge, and how the merge reads it.

pack   --lib DIR --out DIR      the repaired sources and range sidecars of the shard's modules, its verdicts, the constants its passed
                                theorems are made of (BUNDLE_KEEP), the error lines and the passed names
merge  --shards DIR --out DIR   the shards' packs side by side as ONE library directory (sources + sidecars, first copy wins: a module
                                several shards built was repaired the same way), the logs concatenated, passed.json merged — exactly what
                                `bundle.py compose` reads from a single-job run
"""

import argparse
import json
import re
import shutil
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import tolerant_build as tb  # noqa: E402


def pack(a: argparse.Namespace) -> None:
    lib, out = Path(a.lib), Path(a.out)
    roots = [r for r in a.roots.split(",") if r]
    (out / "src").mkdir(parents=True, exist_ok=True)
    mods = tb.module_files(lib, roots)
    build = {ln.strip() for ln in Path(a.modules).read_text().splitlines() if ln.strip()} if a.modules else set(mods)
    for m, path in mods.items():
        if m in build:
            rel = path.relative_to(lib)
            (out / "src" / rel).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(path, out / "src" / rel)
    base = lib / ".lake" / "build" / "lib" / "lean"
    for f in base.rglob("*.olean.ranges.json"):
        rel = f.relative_to(base)
        (out / "ranges" / rel).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(f, out / "ranges" / rel)
    def filtered(src: str, dst: str, pat: str) -> None:
        if Path(src).exists():
            lines = [ln for ln in Path(src).read_text(errors="replace").splitlines() if re.search(pat, ln)]
            (out / dst).write_text("\n".join(lines) + "\n")

    filtered(a.gate2, "gate2.log", r"GATE2B_(PASS|FAIL) ")
    filtered(a.errors, "errors.log", r"^error: ")
    if Path(a.passed).exists():
        shutil.copy2(a.passed, out / "passed.json")
    if Path(a.keep).exists():
        shutil.copy2(a.keep, out / "bundle-deps.log")
    print(f"packed {len(build)} modules")


def merge(a: argparse.Namespace) -> None:
    out = Path(a.out)
    (out / ".lake" / "build" / "lib" / "lean").mkdir(parents=True, exist_ok=True)
    passed: dict[str, set[str]] = {}
    logs = {"gate2.log": [], "errors.log": [], "bundle-deps.log": []}
    for d in sorted(Path(a.shards).glob("*")):
        d = next(iter(d.glob("shard-pack")), d) if d.is_dir() else d
        if not (d / "src").exists():
            continue
        for f in (d / "src").rglob("*"):
            if f.is_file():
                dst = out / f.relative_to(d / "src")
                if not dst.exists():
                    dst.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(f, dst)
        for f in (d / "ranges").rglob("*.json") if (d / "ranges").exists() else []:
            dst = out / ".lake" / "build" / "lib" / "lean" / f.relative_to(d / "ranges")
            if not dst.exists():
                dst.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(f, dst)
        for name, acc in logs.items():
            if (d / name).exists():
                acc.append((d / name).read_text(errors="replace"))
        if (d / "passed.json").exists():
            for m, ns in json.loads((d / "passed.json").read_text()).items():
                passed.setdefault(m, set()).update(ns)
    for name, acc in logs.items():
        (Path(a.logs) / name).write_text("\n".join(acc))
    (Path(a.logs) / "passed.json").write_text(json.dumps({m: sorted(v) for m, v in passed.items()}))
    print(f"merged: {sum(len(v) for v in passed.values())} passed names in {len(passed)} modules")


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("pack")
    for f in ("lib", "roots", "out", "gate2", "errors", "passed", "keep"):
        p.add_argument(f"--{f}", required=True)
    p.add_argument("--modules", default="")
    m = sub.add_parser("merge")
    for f in ("shards", "out", "logs"):
        m.add_argument(f"--{f}", required=True)
    a = ap.parse_args()
    pack(a) if a.cmd == "pack" else merge(a)
