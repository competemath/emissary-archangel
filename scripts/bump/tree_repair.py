#!/usr/bin/env python3
"""tree_repair.py — mend what the tree refuses only because a limit is too small, and say so in the module.

tree_verify.py builds the bundle's new modules in the tree's own environment. A module can fail there for a reason that is not wrong mathematics: a declaration runs out of
heartbeats because the tree's environment is bigger than the library's (navier-stokes-euler's `PositiveAxisSystem`: two `whnf` timeouts at 200000, and everything after them an
"unknown constant"; tauceti's `Levi/Geometry` and `FiniteDual/BaseChange`: typeclass searches at 20000). The proof is the library's, unchanged. What it needs is room.

Rule R2 (heartbeats). For every `(deterministic) timeout at …, maximum number of heartbeats (N) has been reached` in a new module:
  * the declaration the error sits in gets `set_option maxHeartbeats M in` (or `synthInstance.maxHeartbeats`, whichever Lean's own note names) on the line above it, M = 8 N, never
    more than 8 times Lean's default (1 600 000, and 400 000 for the typeclass search): a declaration that needs more is not repaired and goes the way it went before;
  * the module gets one line of module docstring per repair, right after the imports, that says what was done and to what: `/-! Tengoku repair: … -/`.
Both options are on the allowlist (schemas/allowed-options.json) and the text of the declaration is not touched. One round only: the repaired modules are built again, and a module
that still fails is refused like one that never had a repair. Nothing here decides that a module is right; the tree's build does, on the repaired bytes.

  tree_repair.py plan  --log out/build.log --new out/new.json --tree CHECKOUT --out OUT   read the build, write the repaired modules into the checkout, OUT/repairs.json, and update
                                                                                           OUT/new.json (the new bytes; `repaired: true`); prints what it did
  tree_repair.py merge --out F A.json B.json …                                             the repairs of several verified modes in one file (the same module with other bytes is an error)

A module has the same text in every mode, and a heartbeat timeout is deterministic, so the verified modes repair a module identically; one that did not would make `check` refuse the
bundle (never ship other bytes than the tree accepted), which is the loud outcome, and `merge` already refuses two different repairs of one module.

`plan` appends nothing to the log; the workflow adds MARKER and the second build. `tree_verify.py collect` reads the log in two parts at MARKER (a module that was repaired is judged on
the second). `bundle.py compose --tree-repairs F` makes the same edit, to the same bytes, in the bundle that ships (`apply_to_text`), and `tree_verify.py check` then proves it.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import bundle_rehead as rehead  # noqa: E402

MARKER = "=== tengoku repair round: the build again, with the limits of the declarations that timed out raised ==="
FINISHED = re.compile(r"Build completed successfully|Some required targets logged failures|error: build failed")
FACTOR = 8
CAPS = {"maxHeartbeats": 1_600_000, "synthInstance.maxHeartbeats": 400_000}  # 8 x Lean's defaults (200000, 20000)
FAITHFUL_NOTE_START = "/-! Tengoku: the imports are the original's"

HEADER = re.compile(r"^(?:\S+\s+)?(?P<sev>error|warning|info): (?P<path>Tengoku/[^/\s]+/\S+?\.lean):(?P<line>\d+):(?P<col>\d+): (?P<msg>.*)$")
STOP = re.compile(r"^(?:[✔✖⚠] |trace: |Some required targets|- Tengoku\.|(?:\S+\s+)?(?:error|warning|info): )")
TIMEOUT = re.compile(r"\(deterministic\) timeout at `(?P<what>[^`]*)`, maximum number of heartbeats \((?P<limit>\d+)\) has been reached")
OPTION = re.compile(r"[Uu]se `set_option (?P<opt>[\w.]+) <num>`")

_MODS = r"(?:(?:private|protected|noncomputable|unsafe|partial|nonrec|public|meta|scoped|local)\s+)*"
DECL = re.compile(r"^ ?(?:@\[[^\n]*?\]\s*)?" + _MODS + r"(?P<kw>theorem|lemma|def|instance|example|abbrev|structure|class|inductive|irreducible_def)\b")
NAME = re.compile(r"(?:theorem|lemma|def|abbrev|structure|class|inductive|irreducible_def)\s+(?P<n>[^\s:({\[⦃]+)")
# a command that is not a declaration: an error that sits after one of these is not in a declaration the repair can wrap
OTHER = re.compile(r"^ ?(?:end|namespace|section|variable|open|universe|mutual|import|export|attribute|notation|macro|syntax|elab|initialize|set_option|noncomputable\s+section|#\w+)\b")
ATTRIBUTE_LINE = re.compile(r"^@\[.*\]\s*$")
DOC_SCAN = 300  # lines: a longer docstring is not looked for


def sha256(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def blocks(log: str) -> list[dict]:
    """Every message of a Lake log that names a file: severity, path, line, column and the whole text of the message (its first line and what follows it)."""
    out: list[dict] = []
    cur: dict | None = None
    for ln in log.split("\n"):
        m = HEADER.match(ln)
        if m:
            cur = {"sev": m["sev"], "path": m["path"], "line": int(m["line"]), "col": int(m["col"]), "text": m["msg"]}
            out.append(cur)
        elif cur is not None and not STOP.match(ln):
            cur["text"] += "\n" + ln
        else:
            cur = None
    return out


def new_limit(option: str, limit: int) -> int | None:
    """The limit a repair asks for, or None when the declaration already has all the room a repair gives."""
    cap = CAPS[option]
    return None if limit >= cap else min(limit * FACTOR, cap)


def timeouts(log: str) -> list[dict]:
    """The heartbeat timeouts of the log that a repair can answer: path, line, the option Lean names (or the one for the kind of search) and the limit that was reached."""
    out = []
    for b in blocks(log):
        m = TIMEOUT.search(b["text"])
        if b["sev"] != "error" or not m:
            continue
        o = OPTION.search(b["text"])
        option = o["opt"] if o else ("synthInstance.maxHeartbeats" if m["what"] == "typeclass" else "maxHeartbeats")
        if option in CAPS:
            out.append({"path": b["path"], "line": b["line"], "option": option, "limit": int(m["limit"])})
    return out


def doc_start(lines: list[str], end: int) -> int | None:
    """The index of the line a docstring that closes on line `end` opens on, or None when that comment is not a docstring (a plain `/- … -/` has no `/--`, and the
    `/--` further up that the search would reach closes before it)."""
    for k in range(end, max(end - DOC_SCAN, -1), -1):
        if "/--" in lines[k]:
            return k if sum(ln.count("-/") for ln in lines[k : end + 1]) == 1 else None
    return None


def anchor(lines: list[str], line: int) -> tuple[int, str] | None:
    """(the 1-based line a `set_option … in` goes on, the declaration's name) for an error reported on `line` (1-based), or None when the error is not inside a declaration.

    The declaration starts at the nearest line above that begins one (at most one space of indent: the pruner leaves one where it removed `private`); a command that is not a declaration
    in between means the error is not in one. The `set_option` goes above the docstring and the attributes of the declaration, and below any `set_option … in` that is already there."""
    i = min(line, len(lines)) - 1
    while i >= 0 and not DECL.match(lines[i]):
        if OTHER.match(lines[i]):
            return None
        i -= 1
    if i < 0:
        return None
    nm = NAME.search(lines[i])
    name = nm["n"] if nm else f"{DECL.match(lines[i])['kw']} at line {i + 1}"  # type: ignore[index]
    start = i
    while start > 0:
        prev = lines[start - 1]
        if ATTRIBUTE_LINE.match(prev):
            start -= 1
        elif prev.rstrip().endswith("-/") and (d := doc_start(lines, start - 1)) is not None:
            start = d
        else:
            break
    return start + 1, name


def plan_text(text: str, errors: list[dict]) -> tuple[list[dict], list[str]]:
    """(the repairs for one module, and why some errors got none). One repair per (declaration, option): two timeouts in one declaration ask for the larger limit."""
    lines = text.split("\n")
    end, _ = rehead.header_end(lines)
    if not any(rehead.IMPORT.match(lines[k]) for k in range(end)):
        return [], ["the module has no import line to put the note after"]
    best: dict[tuple[int, str], dict] = {}
    skipped: list[str] = []
    for e in errors:
        to = new_limit(e["option"], e["limit"])
        if to is None:
            skipped.append(f"line {e['line']}: {e['option']} is already {e['limit']}")
            continue
        a = anchor(lines, e["line"])
        if a is None:
            skipped.append(f"line {e['line']}: not inside a declaration")
            continue
        at, name = a
        key = (at, e["option"])
        cur = best.get(key)
        if cur is None or to > cur["to"]:
            best[key] = {"line": e["line"], "at": at, "name": name, "option": e["option"], "from": e["limit"], "to": to}
    return sorted(best.values(), key=lambda r: (r["at"], r["option"])), skipped


def note(r: dict) -> str:
    return f"/-! Tengoku repair: `{r['name']}` ran out of heartbeats in the tree; `{r['option']}` is {r['to']} for it (was {r['from']}). -/"


def repair_text(text: str, repairs: list[dict]) -> str:
    """The module with each repair made: `set_option OPT TO in` on the line `at` (1-based, in `text`), one `/-! Tengoku repair … -/` per repair after the imports."""
    lines = text.split("\n")
    by_at: dict[int, list[dict]] = {}
    for r in repairs:
        by_at.setdefault(r["at"], []).append(r)
    for at in sorted(by_at, reverse=True):
        lines[at - 1 : at - 1] = [f"set_option {r['option']} {r['to']} in" for r in sorted(by_at[at], key=lambda r: r["option"])]
    orig = text.split("\n")
    end, _ = rehead.header_end(orig)
    last = max(k for k in range(end) if rehead.IMPORT.match(orig[k]))
    faithful = orig[last + 1 : last + 2] == [""] and orig[last + 2 : last + 3] != [] and orig[last + 2].startswith(FAITHFUL_NOTE_START)
    pos = last + 3 if faithful else last + 1
    block = [note(r) for r in sorted(repairs, key=lambda r: (r["at"], r["option"]))]
    lines[pos:pos] = block if faithful else ["", *block]
    return "\n".join(lines)


def apply_to_text(text: str, entry: dict) -> str | None:
    """`text` with the repairs of `entry` (one module of repairs.json) made, or None when `text` is not the text they were planned on. A result that is not the planned `after` is a bug."""
    if sha256(text) != entry["before"]:
        return None
    out = repair_text(text, entry["repairs"])
    if sha256(out) != entry["after"]:
        raise ValueError("the repair of this module is not reproducible: planned bytes differ from the ones made now")
    return out


def cmd_plan(a: argparse.Namespace) -> None:
    new = json.loads(Path(a.new).read_text())
    mods = new["modules"]
    log = Path(a.log).read_text(errors="replace")
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    result: dict = {"rule": "R2", "modules": {}}
    notes: list[str] = []
    if MARKER in log:
        notes.append("the log already has a repair round: no second round")
    elif not FINISHED.search(log):
        notes.append("the build log has no ending: nothing is repaired from an unfinished build")
    else:
        by_path: dict[str, list[dict]] = {}
        for e in timeouts(log):
            by_path.setdefault(e["path"], []).append(e)
        for mod, spec in sorted(mods.items()):
            errs = by_path.get(spec["path"])
            if not errs:
                continue
            if getattr(a, "skip_repaired", False) and spec.get("repaired"):
                notes.append(f"{mod}: already repaired once: not again (a second round on the same module would not be one edit of the bytes the build had)")
                continue
            tree_file = Path(a.tree) / spec["path"]
            text = tree_file.read_text(encoding="utf-8")
            if sha256(text) != spec["sha256"]:
                notes.append(f"{mod}: the checkout's file is not the bundle's: not repaired")
                continue
            repairs, skipped = plan_text(text, errs)
            notes += [f"{mod}: {s}" for s in skipped]
            if not repairs:
                continue
            fixed = repair_text(text, repairs)
            tree_file.write_text(fixed, encoding="utf-8")
            spec["original_sha256"], spec["sha256"], spec["repaired"] = spec["sha256"], sha256(fixed), True
            lib = mod.removeprefix(f"Tengoku.{new['ns']}.")
            result["modules"][lib] = {"module": mod, "path": spec["path"], "before": sha256(text), "after": sha256(fixed), "repairs": repairs}
    (out / "repairs.json").write_text(json.dumps(result, indent=1, ensure_ascii=False) + "\n")
    Path(a.new).write_text(json.dumps(new, indent=1) + "\n")
    n = sum(len(v["repairs"]) for v in result["modules"].values())
    print(f"{n} repair(s) in {len(result['modules'])} module(s)" + "".join(f"\n  {x}" for x in notes[:20]))
    for lib, v in result["modules"].items():
        for r in v["repairs"]:
            print(f"  {lib}: {r['name']} (line {r['line']}): {r['option']} {r['from']} -> {r['to']}")


def cmd_merge(a: argparse.Namespace) -> None:
    merged: dict = {"rule": "R2", "modules": {}}
    for f in a.inputs:
        for lib, v in json.loads(Path(f).read_text())["modules"].items():
            if lib in merged["modules"] and merged["modules"][lib] != v:
                sys.exit(f"{lib}: two verified modes repaired it from different bytes ({f}): refusing to guess which")
            merged["modules"][lib] = v
    Path(a.out).write_text(json.dumps(merged, indent=1, ensure_ascii=False) + "\n")
    print(f"{len(merged['modules'])} repaired module(s) from {len(a.inputs)} file(s)")


def main(argv: list[str] | None = None) -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("plan")
    p.add_argument("--log", required=True)
    p.add_argument("--new", required=True)
    p.add_argument("--tree", required=True)
    p.add_argument("--out", required=True)
    p.add_argument("--skip-repaired", action="store_true", help="leave a module alone that an earlier round repaired (the rounds after the first of the build of the importers on the tree's modules)")
    p.set_defaults(fn=cmd_plan)
    p = sub.add_parser("merge")
    p.add_argument("--out", required=True)
    p.add_argument("inputs", nargs="+")
    p.set_defaults(fn=cmd_merge)
    a = ap.parse_args(argv)
    a.fn(a)


if __name__ == "__main__":
    main()
