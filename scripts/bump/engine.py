#!/usr/bin/env python3
"""engine.py repair — one round of deterministic repairs on a library that was built against a newer Mathlib.

Mathlib moves itself to a new Lean by building everything, reading what the compiler reports and applying the
mechanical fixes it can name (its own scripts/fix_deprecations.py rewrites Lean's "X is deprecated, use Y" warnings).
This does the same for a library that was left behind. A round reads the build log and applies, in order:

  moved-imports   `bad import 'Mathlib.X'`: X no longer exists. mine_moves.py says where its content went (a move, a
                  split, a merge, a deprecated stub's target); the import is replaced by those modules. A module nothing
                  is known about, or a replacement that a later round finds insufficient, becomes `import Mathlib`:
                  correct by construction (the content is somewhere in Mathlib), only heavier.
  deprecations    Mathlib's fix_deprecations.py algorithm over the warnings of the last build log (position-exact rewrites).

  normalize       `normalize-imports`: every external import of a library file (Mathlib, Batteries, Aesop, Qq, ProofWidgets, …)
                  becomes the umbrella imports. That is the environment a record is verified in anyway: the Tengoku tree
                  holds ALL of Mathlib, Batteries, Aesop, Qq and ProofWidgets, and a record's own imports are stripped.
                  Moved, split and merged Mathlib modules then stop mattering, and an instance that used to arrive through
                  a module the library imported (and no longer does) is simply there.

Every repair is checked by the next build, not trusted. Only the library's own files are edited, never a statement on
purpose: imports and call-site names. Whether a statement still means what it did is Gate 2's job (gate2_batch.py).

  engine.py repair --lib DIR --log build.log --roots R,R --moves moves.json --state state.json --round N --out round.json
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
from pathlib import Path

# The deprecation fixer below is Mathlib's scripts/fix_deprecations.py (Apache-2.0, Mathlib contributors) reading our own build
# log instead of running `lake build --no-build` (which replays only warnings Lake itself built; the tolerant build is not Lake's)
DEPRECATED_AT = re.compile(r"^warning: (?:\./)*(\S+?\.lean):(\d+):(\d+): .*?`([^`]+)` has been deprecated.*?[Uu]se `([^`]+)` instead")
BAD_IMPORT = re.compile(r"error: (\S+\.lean): bad import '([^']+)'")
UNKNOWN = re.compile(r"error: (\S+\.lean):\d+:\d+: .*?[Uu]nknown (?:identifier|constant|namespace)")
IMPORT_LINE = re.compile(r"^(?P<pre>\s*(?:(?:public|private|meta)\s+)*import\s+)(?P<mod>[\w.«»]+)\s*$")


def lean_files(lib: Path, roots: list[str]) -> list[Path]:
    files = []
    for r in roots:
        if (lib / f"{r}.lean").exists():
            files.append(lib / f"{r}.lean")
        if (lib / r).is_dir():
            files += sorted((lib / r).rglob("*.lean"))
    return files


def rewrite_imports(path: Path, replace: dict[str, list[str]]) -> dict[str, list[str]]:
    """Replace each `import X` (X in `replace`) by `import T` for T in replace[X]; returns what was done to this file."""
    lines = path.read_text().splitlines()
    have = {m.group("mod") for ln in lines if (m := IMPORT_LINE.match(ln))}
    out, done = [], {}
    for ln in lines:
        m = IMPORT_LINE.match(ln)
        if m and m.group("mod") in replace:
            targets = [t for t in replace[m.group("mod")] if t not in have or t == m.group("mod")]
            for t in targets:
                out.append(m.group("pre") + t)
                have.add(t)
            done[m.group("mod")] = replace[m.group("mod")]
            continue
        out.append(ln)
    if done:
        path.write_text("\n".join(out) + "\n")
    return done


def fix_deprecations(lib: Path, log: str) -> tuple[int, int]:
    """Mathlib's scripts/fix_deprecations.py, on a log: at each `file:line:col` of a deprecation warning, the deprecated name
    (as written, qualified or with namespace prefixes dropped) is replaced by the one the message names. Returns (rewrites, files)."""
    by_file: dict[str, list[tuple[int, int, str, str]]] = {}
    for ln in log.splitlines():
        m = DEPRECATED_AT.match(ln)
        if m and (lib / m.group(1)).exists():
            by_file.setdefault(m.group(1), []).append((int(m.group(2)), int(m.group(3)), m.group(4), m.group(5)))
    total = files = 0
    for f, ws in sorted(by_file.items()):
        path = lib / f
        lines = path.read_text().splitlines(keepends=True)
        changed = False
        for line_no, col, old, new in sorted(set(ws), reverse=True):  # last position first: an edit never shifts a pending one
            if line_no - 1 >= len(lines):
                continue
            text = lines[line_no - 1]
            op, np = old.split("."), new.split(".")
            for i in range(len(op)):
                o = ".".join(op[i:])
                n = ".".join(np[i:]) if i < len(np) else new
                if text[col : col + len(o)] == o:
                    lines[line_no - 1] = text[:col] + n + text[col + len(o) :]
                    changed = True
                    total += 1
                    break
        if changed:
            path.write_text("".join(lines))
            files += 1
    return total, files


UMBRELLA_ROOTS = ("Mathlib", "Batteries", "Aesop", "Qq", "ProofWidgets", "Plausible", "LeanSearchClient", "ImportGraph")
UMBRELLA_IMPORTS = ["Mathlib", "Batteries", "Aesop", "Qq", "ProofWidgets"]


def normalize_imports(lib: Path, roots: list[str], lean_path: str = "") -> dict:
    """Replace each file's imports of the umbrella packages' modules by the umbrella imports (the first replaced line's
    `public`/`meta` prefix is kept); every other import (the library's own, other packages) is untouched. An umbrella is only
    imported if its root module exists on `lean_path` (ProofWidgets has no root olean in some builds)."""
    umbrellas = UMBRELLA_IMPORTS
    if lean_path:
        dirs = [Path(d) for d in lean_path.split(":") if d]
        umbrellas = [m for m in UMBRELLA_IMPORTS if any((d / f"{m}.olean").exists() for d in dirs)] or ["Mathlib"]
    changed = removed = 0
    for path in lean_files(lib, roots):
        lines = path.read_text().split("\n")
        # the header: up to the first line that is not blank, a comment line, `module`/`prelude` or an import (block comments are skipped whole)
        out, i, first, prefix, dropped, in_block = [], 0, None, "", 0, 0
        while i < len(lines):
            ln = lines[i]
            s = ln.strip()
            if in_block:
                in_block += s.count("/-") - s.count("-/")
                out.append(ln)
            elif s.startswith("/-"):
                in_block = max(1, s.count("/-") - s.count("-/")) if "-/" not in s or s.count("/-") > s.count("-/") else 0
                out.append(ln)
            elif not s or s.startswith("--") or s in ("module", "prelude"):
                out.append(ln)
            else:
                m = IMPORT_LINE.match(ln)
                if not m:
                    break
                mod = m.group("mod")
                if mod.split(".")[0] in UMBRELLA_ROOTS:
                    if first is None:
                        first, prefix = len(out), m.group("pre").replace("import all", "import")
                    dropped += 1
                else:
                    out.append(ln)
            i += 1
        if first is None:
            continue
        keep_prefix = prefix if prefix.strip() else "import "
        ins = [keep_prefix + m for m in umbrellas]
        new = out[:first] + ins + out[first:] + lines[i:]
        if new != lines:
            path.write_text("\n".join(new))
            changed += 1
            removed += dropped
    return {"files_changed": changed, "imports_replaced": removed}


def repair(a: argparse.Namespace) -> None:
    lib = Path(a.lib)
    roots = [r for r in a.roots.split(",") if r]
    log = Path(a.log).read_text(errors="replace")
    moves = json.loads(Path(a.moves).read_text())["moves"] if a.moves and Path(a.moves).exists() else {}
    state_path = Path(a.state)
    state = json.loads(state_path.read_text()) if state_path.exists() else {"replaced": {}}
    summary = {"round": a.round, "moved_imports": 0, "fell_back_to_all": 0, "deprecations_fixed": 0, "files_changed": []}

    # 0. deprecations: Mathlib's fixer, over the warnings of the last build log. Done before the import edits: a warning's line
    #    and column are positions in the file that was built, and a rewritten import line shifts every line below it
    if a.deprecations:
        n, nfiles = fix_deprecations(lib, log)
        summary["deprecations_fixed"] = n
        if nfiles:
            summary["files_changed"].append(f"({nfiles} files by fix_deprecations)")
    # 1. a replacement that a later build found insufficient (the file now has unknown names) becomes `import Mathlib`
    files_with_unknown = {m.group(1) for m in UNKNOWN.finditer(log)}
    for f, repl in list(state["replaced"].items()):
        if not any(f.endswith(u) or u.endswith(f) for u in files_with_unknown):
            continue
        fallback = {}
        for old, targets in repl.items():
            if targets != ["Mathlib"]:
                fallback.update({t: ["Mathlib"] for t in targets})
                repl[old] = ["Mathlib"]
        p = lib / f
        if fallback and p.exists():
            rewrite_imports(p, fallback)
            summary["fell_back_to_all"] += len(fallback)
            summary["files_changed"].append(f)

    # 2. imports of modules that no longer exist
    mine_set = set()
    for r in roots:
        mine_set.add(r)
    per_file: dict[str, dict[str, list[str]]] = {}
    for f, mod in BAD_IMPORT.findall(log):
        if mod == "Mathlib" or mod.startswith(tuple(r + "." for r in roots)) or mod in mine_set:
            continue  # the library's own module: blocked behind a failure, nothing to repair here
        per_file.setdefault(f, {})[mod] = moves.get(mod) or ["Mathlib"]
    for f, repl in per_file.items():
        p = lib / f
        if not p.exists():
            continue
        done = rewrite_imports(p, repl)
        if done:
            state["replaced"].setdefault(f, {}).update(done)
            summary["moved_imports"] += len(done)
            summary["files_changed"].append(f)

    state_path.write_text(json.dumps(state, indent=1))
    summary["changed"] = bool(summary["moved_imports"] or summary["fell_back_to_all"] or summary["deprecations_fixed"])
    Path(a.out).write_text(json.dumps(summary, indent=1))
    print(json.dumps({k: v for k, v in summary.items() if k != "files_changed"}))


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("repair")
    for f in ("lib", "log", "roots", "state", "out"):
        r.add_argument(f"--{f}", required=True)
    r.add_argument("--moves", default="")
    r.add_argument("--round", type=int, default=1)
    r.add_argument("--deprecations", action="store_true")
    n = sub.add_parser("normalize-imports")
    n.add_argument("--lib", required=True)
    n.add_argument("--roots", required=True)
    n.add_argument("--lean-path", default="", help="only umbrellas whose root olean is on this LEAN_PATH")
    args = ap.parse_args()
    if args.cmd == "normalize-imports":
        print(json.dumps(normalize_imports(Path(args.lib), [r for r in args.roots.split(",") if r], args.lean_path)))
    else:
        repair(args)
