#!/usr/bin/env python3
"""trial-library-build.py — the Mathlib-style pass over one registered library, for the trial-library-build workflow.

Mathlib moves to a new Lean by building the whole library in dependency order and fixing what the compiler reports.
The translation pipeline instead compiles every declaration as its own synthetic file. This script supports the
whole-library way, measured on one library, with no Leak service and no Claude:

  meta KEY                       print "<repo> <commit> <toolchain> <root> <root> ..." from data/exports/KEY/setup.ci.json
  retarget DIR MATHLIB TOOLCHAIN point the library at a Mathlib tag and a Lean toolchain (its lakefile and lean-toolchain;
                                 the manifest is dropped so `lake update` resolves everything again)
  analyze  DIR KEY LABEL LOG     which modules built (an .olean exists), which failed with their own error, which were
                                 blocked behind a failure; the first error of each failing module, classified; the
                                 deprecation warnings (what Mathlib's fix_deprecations.py rewrites); and what share of
                                 the library's ledger entries live in modules that built. Writes LABEL.json and a
                                 markdown summary (also to $GITHUB_STEP_SUMMARY).
"""

from __future__ import annotations

import json
import os
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

ERROR = re.compile(r"^error: (?:\./)*(\S+?\.lean):(\d+):(\d+): (.*)$")
WARNING = re.compile(r"^warning: (?:\./)*(\S+?\.lean):(\d+):(\d+): (.*)$")
DEPRECATED = re.compile(r"`([^`]+)` has been deprecated.*?[Uu]se `([^`]+)` instead")


def meta(key: str) -> None:
    d = json.loads(Path(f"data/exports/{key}/setup.ci.json").read_text())
    print(d["repo"], d["commit"], d["toolchain"], *d["roots"])


# Packages a library requires for its own development (blueprint checks, docs, export tools): no module imports them,
# and each pins its own Lean version, so a retargeted build drops them.
DEV_ONLY = ("checkdecls", "doc-gen4", "lean4export", "Comparator")


def retarget(lib: str, mathlib: str, toolchain: str) -> None:
    root = Path(lib)
    (root / "lean-toolchain").write_text(toolchain + "\n")
    toml, lean = root / "lakefile.toml", root / "lakefile.lean"
    if toml.exists():
        out, block, lines = [], [], toml.read_text().splitlines()

        def flush() -> None:
            if block and any(re.match(r'\s*name\s*=\s*"mathlib"', b) for b in block):
                block[:] = [b for b in block if not re.match(r"\s*(rev|version)\s*=", b)]
                block.append(f'rev = "{mathlib}"')
            if block and block[0].strip() == "[[require]]" and any(
                re.match(r'\s*name\s*=\s*"[«]?(' + "|".join(map(re.escape, DEV_ONLY)) + r')[»]?"', b) for b in block
            ):
                block.clear()  # a development-only requirement: dropped
            out.extend(block)
            block.clear()

        for line in lines:
            if re.match(r"\s*\[\[?[^\]]+\]\]?\s*$", line):  # a new table starts: close the previous require block
                flush()
            block.append(line)
        flush()
        text = "\n".join(out) + "\n"
        if f'rev = "{mathlib}"' not in text:
            # Mathlib arrives only through another requirement (seymour requires `linters`, which requires Mathlib): the library's
            # modules import it all the same, so it becomes a direct requirement (the root's wins over an inherited one)
            text += f'\n[[require]]\nname = "mathlib"\ngit = "https://github.com/leanprover-community/mathlib4.git"\nrev = "{mathlib}"\n'
        toml.write_text(text)
    elif lean.exists():
        lean.write_text(retarget_lean(lean.read_text(), mathlib))
    else:
        sys.exit("no lakefile")
    for stale in ("lake-manifest.json",):
        (root / stale).unlink(missing_ok=True)


def retarget_lean(text: str, mathlib: str) -> str:
    """lakefile.lean: each `require` is a statement (it may continue on indented lines). A development-only one is
    dropped whole; Mathlib's is pointed at `mathlib`, in whichever of its spellings the file uses:
        require mathlib from git "url" @ "rev"          (also with the url on the next line)
        require "leanprover-community" / "mathlib" @ git "rev"
    """
    lines, out, i = text.splitlines(), [], 0
    dev = re.compile(r'["«](?:' + "|".join(map(re.escape, DEV_ONLY)) + r')["»]|require\s+(?:' + "|".join(map(re.escape, DEV_ONLY)) + r')\b')
    mathlib_re = re.compile(r'require\s+(?:«?mathlib»?\b|"[^"]+"\s*/\s*"mathlib")')
    seen = False
    while i < len(lines):
        if not re.match(r"\s*require\b", lines[i]):
            out.append(lines[i])
            i += 1
            continue
        j = i + 1
        while j < len(lines) and lines[j].strip() and lines[j][0] in " \t":
            j += 1
        stmt = "\n".join(lines[i:j])
        if dev.search(lines[i]):
            # dropped whole, with the `meta if get_config? env = some "dev" then` guard that sits directly above it: left behind,
            # that guard would take whatever is appended to the file (Gate 2's `lean_lib Vendor`) as its body
            while out and not out[-1].strip():
                out.pop()
            if out and re.match(r"\s*(?:meta\s+)?if\b.*\bthen\s*$", out[-1]):
                out.pop()
        elif mathlib_re.search(lines[i]):
            seen = True
            if re.search(r'@\s*git\s*"[^"]*"', stmt):
                stmt = re.sub(r'(@\s*git\s*)"[^"]*"', lambda m: f'{m.group(1)}"{mathlib}"', stmt, count=1)
            elif re.search(r'@\s*"[^"]*"', stmt):
                stmt = re.sub(r'(@\s*)"[^"]*"', lambda m: f'{m.group(1)}"{mathlib}"', stmt, count=1)
            else:
                stmt += f' @ git "{mathlib}"' if "/" in lines[i] else f' @ "{mathlib}"'
            out.append(stmt)
        else:
            out.append(stmt)
        i = j
    text = "\n".join(out) + "\n"
    if not seen:  # Mathlib only through another requirement: a direct one (the root's wins over an inherited one)
        text += f'\nrequire mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "{mathlib}"\n'
    return text


def modules(lib: str, roots: list[str]) -> dict[str, Path]:
    """module name -> source path, for every .lean file under the roots (a root is a directory and/or a root file)."""
    base, found = Path(lib), {}
    for r in roots:
        top = base / f"{r}.lean"
        if top.exists():
            found[r] = top
        for p in sorted((base / r).rglob("*.lean")) if (base / r).is_dir() else []:
            found[".".join(p.relative_to(base).with_suffix("").parts)] = p
    return found


def classify(msg: str) -> str:
    m = msg.lower()
    if re.search(r"unexpected (token|identifier)|expected (command|term|'|identifier)|unterminated", m):
        return "syntax / parse"
    if re.search(r"unknown (identifier|constant|namespace)|unknown free variable", m):
        return "unknown name (rename / removal)"
    if re.search(r"invalid field|invalid projection|does not contain", m):
        return "missing API (field / lemma gone)"
    if re.search(r"unsolved goals|made no progress|failed to prove|linarith failed|omega|simp failed|\brfl\b|norm_num|did not find|failed to rewrite|motive", m):
        return "tactic / proof behaviour"
    if re.search(r"type mismatch|failed to synthesize|application type|has type|ambiguous|typeclass|overload", m):
        return "elaboration (types / instances)"
    if re.search(r"timeout|maximum recursion|heartbeat", m):
        return "timeout"
    return "other"


def parse_log(text: str):
    errors, warnings = defaultdict(list), defaultdict(list)
    cur = None  # the last error/warning, so continuation lines join its message
    for line in text.splitlines():
        m = ERROR.match(line)
        if m:
            cur = (errors[m.group(1)], [int(m.group(2)), int(m.group(3)), m.group(4)])
            cur[0].append(cur[1])
            continue
        m = WARNING.match(line)
        if m:
            cur = (warnings[m.group(1)], [int(m.group(2)), int(m.group(3)), m.group(4)])
            cur[0].append(cur[1])
            continue
        if cur and line.startswith((" ", "\t")) and line.strip():
            cur[1][2] += " " + line.strip()
        elif not line.startswith(("trace:", "✔", "✖", "⚠", "info:")):
            pass
    return errors, warnings


def ledger_entries(key: str):
    """sourcePath -> number of distinct names the pipeline knows for it, and the pipeline's own outcome per name."""
    p = Path(f"data/translate/{key}.jsonl")
    latest = {}
    if p.exists():
        for line in p.read_text().splitlines():
            try:
                r = json.loads(line)
            except ValueError:
                continue
            latest[r["name"]] = r
    per = defaultdict(int)
    for r in latest.values():
        per[r["sourcePath"]] += 1
    outcomes = Counter(r["outcome"] for r in latest.values())
    return per, outcomes


def analyze(lib: str, key: str, label: str, log_path: str) -> None:
    setup = json.loads(Path(f"data/exports/{key}/setup.ci.json").read_text())
    mods = modules(lib, setup["roots"])
    errors, warnings = parse_log(Path(log_path).read_text(errors="replace"))
    built, failed, blocked = [], [], []
    for mod, src in mods.items():
        rel = str(src.relative_to(lib))
        olean = Path(lib) / ".lake" / "build" / "lib" / "lean" / (mod.replace(".", "/") + ".olean")
        has_errors = any(k.endswith(rel) or rel.endswith(k) for k in errors)
        if olean.exists() and not has_errors:
            built.append(mod)
        elif has_errors:  # lake leaves no olean for it; the tolerant build (scripts/bump/tolerant_build.py) does, and downstream goes on
            failed.append(mod)
        else:
            blocked.append(mod)
    first = {}
    for k, es in errors.items():
        first[k] = min(es)  # the earliest by position
    cats = Counter(classify(m[2]) for m in first.values())
    all_errors = Counter(classify(e[2]) for es in errors.values() for e in es)
    deps = Counter()
    for k, ws in warnings.items():
        for _, _, msg in ws:
            m = DEPRECATED.search(msg)
            if m:
                deps[(m.group(1), m.group(2))] += 1
    # imports of modules that no longer exist: the library's own modules are blocked behind a failure, an EXTERNAL one
    # (Mathlib's) was moved or renamed between the library's Mathlib and the target
    log_text = Path(log_path).read_text(errors="replace")
    bad = re.findall(r"error: (\S+\.lean): bad import '([^']+)'", log_text)
    mine = set(mods)
    missing_external = Counter(m for _, m in bad if m not in mine and not m.startswith(tuple(r + "." for r in setup["roots"])))
    per, outcomes = ledger_entries(key)
    by_src = {str(src.relative_to(lib)): mod for mod, src in mods.items()}
    entries = Counter()
    for sp, n in per.items():
        mod = by_src.get(sp)
        status = "built" if mod in built else "failed" if mod in failed else "blocked" if mod in blocked else "no module"
        entries[status] += n
    n_err = sum(len(es) for es in errors.values())
    total = sum(entries.values()) or 1
    res = {
        "label": label,
        "modules": {"total": len(mods), "built": len(built), "failed_own_error": len(failed), "blocked_behind_failure": len(blocked)},
        "errors": {"distinct_error_messages": n_err, "first_error_by_module": dict(cats), "all_errors_by_class": dict(all_errors)},
        "missing_external_modules": dict(missing_external),
        "deprecation_warnings": {"total": sum(deps.values()), "distinct_names": len(deps), "top": [[o, n, c] for (o, n), c in deps.most_common(10)]},
        "ledger": {"entries_by_module_status": dict(entries), "pipeline_outcomes": dict(outcomes)},
        "failed_modules": {m: first[next(k for k in first if k.endswith(str(mods[m].relative_to(lib))))][2][:200] for m in failed if any(k.endswith(str(mods[m].relative_to(lib))) for k in first)},
    }
    Path(f"{label}.json").write_text(json.dumps(res, indent=2))
    pct = lambda n, d: f"{100 * n / max(d, 1):.1f}%"
    md = [
        f"### {key}: {label}",
        "",
        f"- Modules: **{len(built)} of {len(mods)} built unchanged ({pct(len(built), len(mods))})**; {len(failed)} fail with their own error; {len(blocked)} blocked behind a failed import.",
        f"- Ledger entries (what the per-theorem pipeline counts) in modules that built: **{entries['built']} of {total} ({pct(entries['built'], total)})**; in failing modules {entries['failed']}; blocked {entries['blocked']}.",
        f"- Errors reported: {n_err}. First error per failing module: " + ", ".join(f"{k} {v}" for k, v in cats.most_common()) + ".",
        f"- Modules that no longer exist upstream (imports that fail): {dict(missing_external) or 'none'}.",
        f"- Deprecation warnings (rewritten mechanically by Mathlib's fix_deprecations.py): {sum(deps.values())} over {len(deps)} names.",
        f"- The per-theorem pipeline's own outcomes for this library: {dict(outcomes)}.",
    ]
    text = "\n".join(md) + "\n"
    print(text)
    if os.environ.get("GITHUB_STEP_SUMMARY"):
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a") as f:
            f.write(text + "\n")


if __name__ == "__main__":
    a = sys.argv[1:]
    if a[:1] == ["meta"] and len(a) == 2:
        meta(a[1])
    elif a[:1] == ["retarget"] and len(a) == 4:
        retarget(a[1], a[2], a[3])
    elif a[:1] == ["analyze"] and len(a) == 5:
        analyze(a[1], a[2], a[3], a[4])
    else:
        print(__doc__)
        sys.exit(2)
