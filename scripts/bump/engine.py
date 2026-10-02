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
    args = ap.parse_args()
    repair(args)
