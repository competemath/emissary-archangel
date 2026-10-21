#!/usr/bin/env python3
"""tree_verify.py — build the bundle in the TREE's own environment before it is cut into parts.

The factory builds a library in the library's own environment and checks every proof again against the tree's Mathlib, but until now the first time the shipped TEXT was
compiled in the tree was the merge queue, one part at a time: a part came back for every module the tree behaves differently on (typeclass searches that time out in a bigger
instance set, a Mathlib that differs, an instance the text never names). This does that build ahead of time, for every module the tree does not have yet at once, with the queue's
own command (`lake build Tengoku.<Ns>.<module> …`) on a checkout seeded from the tree's cache. The modules that fail are dropped (with their importers) by `bundle.py compose
--tree-failures`, and `check` then proves that every module that ships is byte for byte a module that was built there.

  tree_verify.py apply   --bundle DIR --tree CHECKOUT --out OUT   copy the bundle's new modules into the checkout, write OUT/targets.txt (what to build) and OUT/new.json
  tree_verify.py collect --new OUT/new.json --log build.log --out OUT [--axioms axioms.txt] [--clashes clashes.txt] [--allow-unfinished]   read the build (and the axiom check of what built): OUT/failing.txt (library modules),
                                                                          OUT/ok.json (module -> sha256), OUT/built.txt (the modules to run ModuleAxioms.lean on), OUT/summary.txt
  tree_verify.py union-input [--root Tengoku.All] --new OUT/new.json --keep OUT/built.txt --excluded X --out U.lean   the file that imports the whole tree plus the new modules that are still in play
  tree_verify.py union-next  --message M --new OUT/new.json --keep OUT/built.txt --excluded X --bundle DIR      read Lean's refusal of that file, exclude the new module (and its importers)
  tree_verify.py check   --bundle DIR --new OUT/new.json --ok OUT/ok.json   exit 1 unless every new module of the final bundle was built there with the same bytes

The queue also checks the axioms of every declaration of the modules it built (scripts/bump/ModuleAxioms.lean is that check with the module of each offender in its
output): a module with a declaration on an axiom other than propext, Classical.choice, Quot.sound is refused like one that does not compile. Gate 2 only checks theorems.

The queue also imports the whole tree at once (`Tengoku.All`): two modules of different libraries that declare the same name stop it ("environment already contains"), and no module of one
library imports another. scripts/bump/ModuleClashes.lean reads the names every module declares and lists the pairs that share one when one of the two is new (lean-pool part 10,
2026-10-12: its vendored copy of AddCombi against the tree's AddCombi). The new module of such a pair is refused like one that does not compile; the one already in the tree stays.

`apply` and `check` take the bundle as `compose` wrote it (DIR/Tengoku/<Ns>.lean, DIR/Tengoku/<Ns>/**.lean). "New" is what the tree's umbrella `Tengoku/<Ns>.lean` does not import
(bundle_layers.tree_modules): the modules the parts will carry. The build runs no token and the job that runs it signs nothing: the library's own code is compiled there.
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
import bundle_layers as bl  # noqa: E402
import tree_repair as tr  # noqa: E402

ERROR = re.compile(r"^(?:\S+\s+)?error: (?P<path>Tengoku/[^/\s]+/\S+?\.lean):\d+:\d+: ", re.M)
SORRY = re.compile(r"^(?:\S+\s+)?warning: (?P<path>Tengoku/[^/\s]+/\S+?\.lean):\d+:\d+: declaration uses .sorry.", re.M)
BUILT = re.compile(r"Built (?P<mod>Tengoku\.\S+)(?: \(|\s*$)", re.M)
SUCCESS = re.compile(r"Build completed successfully")
# the workflow writes this line between the build of the bundle and the second build of tree_dups.py (the importers of the copies, built again on the tree's module), which it appends to the same log
DUPS_MARKER = "=== tengoku dups round: the importers of the copies of tree modules, built again on the tree's module ==="
FAILED_TARGET = re.compile(r"^(?:\S+\s+)?- (?P<mod>Tengoku\.\S+)\s*$", re.M)
AXIOM_LINE = re.compile(r"^AXIOM\t(?P<mod>[^\t\n]+)\t(?P<decl>[^\t\n]+)\t(?P<axioms>[^\n]*)$", re.M)
AXIOM_DONE = re.compile(r"^axioms: (?P<checked>\d+) declarations checked, (?P<bad>\d+) with non-standard axioms$", re.M)
CLASH_LINE = re.compile(r"^CLASH\t(?P<mod>[^\t\n]+)\t(?P<other>[^\t\n]+)\t(?P<count>\d+)\t(?P<first>[^\n]*)$", re.M)
CLASH_DONE = re.compile(r"^clashes: (?P<pairs>\d+) module pair\(s\), (?P<names>\d+) name\(s\)$", re.M)
# the name is quoted by single quotes and may contain some (`mul_comm'`): it runs up to the LAST `' from ` of the line (CodeRabbit)
IMPORT_FAIL = re.compile(r"import (?P<x>\S+) failed, environment already contains '(?P<name>.+)' from (?P<y>\S+)\s*$", re.M)
FINISHED = tr.FINISHED


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def new_modules(files: dict[str, bytes], ns: str, tree_umbrella: str | None) -> dict[str, str]:
    """module -> path of the bundle's modules the tree does not have yet (`Deps` is the marker of the library, no module)."""
    mods = bl.own_modules(files, ns)
    have = bl.tree_modules(tree_umbrella, ns) if tree_umbrella else {f"Tengoku.{ns}.Deps"}
    return {m: p for m, p in mods.items() if m not in have}


def dependents(failing: set[str], graph: dict[str, list[str]]) -> set[str]:
    """Every module that imports a failing one, directly or not (the build never reports them: it does not reach them)."""
    out: set[str] = set()
    todo = list(failing)
    while todo:
        x = todo.pop()
        for m, deps in graph.items():
            if x in deps and m not in out:
                out.add(m)
                todo.append(m)
    return out


def imports_of(roots: set[str], graph: dict[str, list[str]]) -> set[str]:
    """Every module that one of `roots` imports, directly or not: Lean elaborated the root, so it had each of these built."""
    out: set[str] = set()
    todo = list(roots)
    while todo:
        for d in graph.get(todo.pop(), []):
            if d not in out:
                out.add(d)
                todo.append(d)
    return out


def failures_from_log(log: str, ns: str) -> set[str]:
    """The modules (as Lean spells them) the build refused: an error in them, a `sorry` (the queue treats it as an error), or a failing target the build lists."""
    prefix = f"Tengoku/{ns}/"
    out = {bl.module_name(m.group("path")) for m in ERROR.finditer(log) if m.group("path").startswith(prefix)}
    out |= {bl.module_name(m.group("path")) for m in SORRY.finditer(log) if m.group("path").startswith(prefix)}
    out |= {m.group("mod") for m in FAILED_TARGET.finditer(log) if m.group("mod").startswith(f"Tengoku.{ns}.")}
    return out


def plain(module: str) -> str:
    """`Tengoku.Lib.«A-B»` -> `Tengoku.Lib.A-B`: how ModuleAxioms.lean reads its list, and the spelling the two sides are compared in (Lean may quote more than we do)."""
    return module.replace("«", "").replace("»", "")


def axiom_offenders(text: str, mods: set[str]) -> dict[str, list[str]]:
    """module -> ["declaration [axioms]", …] of the modules in `mods` that the axiom check reported. A run with no `axioms:` line did not finish; one whose count does not match
    its lines was cut short: both are refused, because a module that was never checked must not pass as clean."""
    done = AXIOM_DONE.search(text)
    if done is None:
        sys.exit("the axiom check has no ending (it crashed or was killed): nothing is known about the axioms; refusing to guess")
    lines = list(AXIOM_LINE.finditer(text))
    if int(done.group("bad")) != len(lines):
        sys.exit(f"the axiom check says {done.group('bad')} offender(s) and lists {len(lines)}: its output is incomplete; refusing to guess")
    by_plain = {plain(m): m for m in mods}
    out: dict[str, list[str]] = {}
    for ln in lines:
        mod = by_plain.get(plain(ln.group("mod")))
        if mod is not None:
            out.setdefault(mod, []).append(f"{ln.group('decl')} [{ln.group('axioms')}]")
    return out


def clash_offenders(text: str, mods: set[str]) -> dict[str, list[str]]:
    """module -> ["name (+n more) also declared by <other module>", …] for the modules in `mods` that share a declared name with another module. Like the axiom check, a run with no
    `clashes:` line did not finish and one whose count does not match its lines was cut short: both are refused."""
    done = CLASH_DONE.search(text)
    if done is None:
        sys.exit("the clash check has no ending (it crashed or was killed): nothing is known about name clashes; refusing to guess")
    lines = list(CLASH_LINE.finditer(text))
    if int(done.group("pairs")) != len(lines):
        sys.exit(f"the clash check says {done.group('pairs')} pair(s) and lists {len(lines)}: its output is incomplete; refusing to guess")
    by_plain = {plain(m): m for m in mods}
    out: dict[str, list[str]] = {}
    for ln in lines:
        extra = f" (+{int(ln.group('count')) - 1} more)" if int(ln.group("count")) > 1 else ""
        for mine, other in ((ln.group("mod"), ln.group("other")), (ln.group("other"), ln.group("mod"))):
            mod = by_plain.get(plain(mine))
            if mod is not None:
                out.setdefault(mod, []).append(f"{ln.group('first')}{extra} also declared by {plain(other)}")
    return out


def lean_module(name: str) -> str:
    """`Tengoku.Lib.A-B.C` -> `Tengoku.Lib.«A-B».C`: a module name as an `import` writes it (the same quoting as bundle_layers.module_name)."""
    return ".".join(c if re.fullmatch(r"[^\W\d][\w']*", c) else f"«{c}»" for c in name.split("."))


def union_failure(text: str) -> tuple[str, str, str] | None:
    """(the module whose import failed, the name, the module that already had it) from Lean's refusal of the union file, or None if the text is not that refusal."""
    m = IMPORT_FAIL.search(text)
    return (m.group("x"), m.group("name"), m.group("y")) if m else None


def read_lines(path: str) -> list[str]:
    return [ln.strip() for ln in Path(path).read_text().split("\n") if ln.strip()] if path and Path(path).is_file() else []


def cmd_union_input(a: argparse.Namespace) -> None:
    """The union file: `import Tengoku.All` (what the queue's last step builds: the tree as main has it) and every new module that built and has not been excluded (what the library's
    umbrella would import), elaborated by Lean itself, so that no rule of Lean's import (module-system files, subsumed duplicates) is re-implemented here. The tree is NOT enumerated: its source
    holds modules that are alternatives to each other and never imported together (Aesop's `DiscrKeyConfig` and `DiscrTreeConfig` both declare `Aesop.indexConfig`; the first attempt that imported every
    module was refused by that pair), and its cache holds the oleans of modules that no longer exist."""
    new = json.loads(Path(a.new).read_text())["modules"]
    keep = set(read_lines(a.keep))
    excluded = set(read_lines(a.excluded))
    out_of_play = {plain(m) for m in new if plain(m) not in keep} | excluded  # new modules that did not build, were refused, or were excluded are not imported
    mods = sorted({plain(m) for m in new} - out_of_play)
    Path(a.out).write_text(f"import {lean_module(a.root)}\n" + "".join(f"import {lean_module(m)}\n" for m in mods))
    print(f"{a.root} and {len(mods)} new module(s) to import ({len(out_of_play)} new module(s) out of play)")


def cmd_union_next(a: argparse.Namespace) -> None:
    text = Path(a.message).read_text(errors="replace")
    hit = union_failure(text)
    if hit is None:
        errs = [ln for ln in text.splitlines() if "error" in ln.lower()][:5] or text.splitlines()[-5:]
        sys.exit("the union import failed in a way that is not a name clash (or was killed): refusing to guess:\n  " + "\n  ".join(errs))
    x, name, y = hit
    new = json.loads(Path(a.new).read_text())
    mods = new["modules"]
    key_of = {plain(m): m for m in mods}
    in_play = (set(key_of) & set(read_lines(a.keep))) - set(read_lines(a.excluded))
    offender = plain(x) if plain(x) in in_play else plain(y) if plain(y) in in_play else None
    if offender is None:
        sys.exit(f"the tree does not import: {plain(x)} and {plain(y)} both declare `{name}` and neither is a new module still in play (the tree itself, or a module already excluded)")
    graph: dict[str, list[str]] = {}
    if a.bundle:
        bfiles = bl.read_bundle(Path(a.bundle))
        graph = {m: [d for d in deps if d in mods] for m, deps in bl.import_graph(bfiles, {m: p["path"] for m, p in mods.items()}).items()}
    gone = {offender} | {plain(m) for m in dependents({key_of[offender]}, graph)} & in_play
    with Path(a.excluded).open("a") as f:
        f.writelines(f"{m}\n" for m in sorted(gone))
    with Path(a.excluded).with_suffix(".reasons").open("a") as f:
        f.write(f"{offender}\t`{name}` is also declared by {plain(y) if offender == plain(x) else plain(x)}\n")
        f.writelines(f"{m}\timports {offender}\n" for m in sorted(gone - {offender}))
    print(f"excluded {offender} ({len(gone) - 1} importer(s) with it): `{name}` is declared by both {plain(x)} and {plain(y)}")


def library_module(module: str, ns: str) -> str:
    """`Tengoku.LeanPool.LeanPool.Foo` -> `LeanPool.Foo`: the library's own name, which `compose --tree-failures` takes."""
    return module.removeprefix(f"Tengoku.{ns}.")


def cmd_apply(a: argparse.Namespace) -> None:
    files = bl.read_bundle(Path(a.bundle))
    ns = bl.namespace(files)
    tree = Path(a.tree)
    umbrella_path = tree / "Tengoku" / f"{ns}.lean"
    umbrella = umbrella_path.read_text(encoding="utf-8") if umbrella_path.is_file() else None
    new = new_modules(files, ns, umbrella)
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    for p in new.values():
        dest = tree / p
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(files[p])
    (out / "targets.txt").write_text("".join(m + "\n" for m in sorted(new)))
    (out / "new.json").write_text(json.dumps({"ns": ns, "modules": {m: {"path": p, "sha256": sha256(files[p])} for m, p in sorted(new.items())}}, indent=1) + "\n")
    print(f"{len(new)} new module(s) of {len(bl.own_modules(files, ns))} in the bundle: copied into {tree}; targets in {out / 'targets.txt'}")


def cmd_collect(a: argparse.Namespace) -> None:
    new = json.loads(Path(a.new).read_text())
    ns, mods = new["ns"], new["modules"]
    log = Path(a.log).read_text(errors="replace")
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    # a repair round (tree_repair.py) appends a second build to the log after MARKER: a module that was repaired is judged on the second, the rest on the first as before
    last = log.rsplit(tr.MARKER, 1)[-1]
    repaired = {m for m, spec in mods.items() if spec.get("repaired")}
    # the build of the bundle, without the second build of tree_dups.py that the workflow appends after DUPS_MARKER: its ending is not the ending of this build
    main = log.split(DUPS_MARKER, 1)[0]
    unfinished = bool(mods) and not FINISHED.search(main.rsplit(tr.MARKER, 1)[-1])
    # a build that finished without a failure built every target it was given, whether or not Lake printed a `Built` line for it: it prints one only for a job that ran, and a target
    # whose artifacts were up to date gets none (2026-10-20, Navier: 67 of 917 new modules had no line in a build that completed, and the 676 modules that import them were built)
    complete = bool(SUCCESS.search(main.split(tr.MARKER, 1)[0]))
    if unfinished and not a.allow_unfinished:
        sys.exit("the build log has no ending (the build was killed or timed out): refusing to guess which modules the tree accepted (--allow-unfinished: those with a `Built` line are accepted, the rest wait for a later round)")
    failing = ((failures_from_log(log, ns) - repaired) | failures_from_log(last, ns)) & set(mods)
    built = {m.group("mod") for m in BUILT.finditer(log)} & set(mods)
    if unfinished and not built:
        # a build that never got going is not a build that ran out of its budget (2026-10-21, Navier: elan could not download the toolchain, `lake build` ended after seven seconds, and the partial
        # mode accepted the run with 0 of 1,066 modules built): nothing was tried, so there is nothing to cut
        sys.exit("the build log has no ending and no module was built: the build never got going (a toolchain that did not download, a runner that died); refusing to cut a bundle from it")
    offenders = axiom_offenders(Path(a.axioms).read_text(errors="replace"), set(mods)) if a.axioms else {}
    failing |= set(offenders)
    clashing = clash_offenders(Path(a.clashes).read_text(errors="replace"), set(mods)) if a.clashes else {}
    failing |= set(clashing)
    union_gone = set(read_lines(a.union_excluded)) if a.union_excluded else set()
    union_hit = {m for m in mods if plain(m) in union_gone}
    failing |= union_hit
    # modules that imported a copy of a tree module and are not exactly what they were on the tree's module (tree_dups.py after-verdict): `module<TAB>why`
    swapped = dict(ln.split("\t", 1) for ln in read_lines(a.extra_failing) if "\t" in ln) if a.extra_failing else {}
    swapped_hit = {m: swapped[plain(m)] if plain(m) in swapped else swapped[m] for m in mods if m in swapped or plain(m) in swapped}
    failing |= set(swapped_hit)
    graph: dict[str, list[str]] = {}
    if a.bundle:
        bfiles = bl.read_bundle(Path(a.bundle))
        graph = {m: [d for d in deps if d in mods] for m, deps in bl.import_graph(bfiles, {m: p["path"] for m, p in mods.items()}).items()}
    cascade = dependents(failing, graph)
    # a build that did not finish (or failed, and stopped there) is known to have reached a module by its `Built` line, or because a module that imports it was built
    reached = set(mods) if complete else built | imports_of(built, graph)
    unaccounted = set(mods) - failing - cascade - reached  # no error, no evidence that it was built, not downstream of a failure: the build did not reach it, so it was not verified
    failing |= unaccounted
    cascade = dependents(failing, graph)
    ok = {m: mods[m]["sha256"] for m in mods if m not in failing and m not in cascade}
    (out / "failing.txt").write_text("".join(library_module(m, ns) + "\n" for m in sorted(failing)))
    (out / "ok.json").write_text(json.dumps(ok, indent=1) + "\n")
    (out / "built.txt").write_text("".join(plain(m) + "\n" for m in sorted(ok)))
    summary = (
        f"{len(mods)} new module(s): {len(ok)} built in the tree, {len(failing)} refused ({len(unaccounted)} of them not reached, {len(offenders)} on an axiom, {len(clashing)} on a name another module declares, {len(union_hit)} on the import of the whole tree), "
        f"{len(cascade - failing)} more import a refused one and go with it"
    )
    mended = sorted(m for m in repaired if m in ok)
    if repaired:
        summary += f"\n  {len(mended)} of {len(repaired)} module(s) the tree timed out on were mended by a raised limit (tree_repair.py)"
        for m in mended[:10]:
            summary += f"\n  repaired: {library_module(m, ns)}"
    for m in sorted(swapped_hit)[:10]:
        summary += f"\n  swap: {library_module(m, ns)}: {swapped_hit[m]}"
    for m in sorted(clashing)[:10]:
        summary += f"\n  clash: {library_module(m, ns)}: {clashing[m][0]}" + (f" (+{len(clashing[m]) - 1} more pair(s))" if len(clashing[m]) > 1 else "")
    for ln in read_lines(str(Path(a.union_excluded).with_suffix(".reasons")) if a.union_excluded else "")[:10]:
        summary += f"\n  import: {ln.replace(chr(9), ': ')}"
    if unfinished:
        summary += "\n  the build did not finish (its budget ran out): the modules it did not reach are not in this cut; a later from-tree round continues with them"
    for m in sorted(offenders)[:10]:
        summary += f"\n  axiom: {library_module(m, ns)}: {offenders[m][0]}" + (f" (+{len(offenders[m]) - 1} more)" if len(offenders[m]) > 1 else "")
    (out / "summary.txt").write_text(summary + "\n")
    print(summary)


def cmd_check(a: argparse.Namespace) -> None:
    files = bl.read_bundle(Path(a.bundle))
    ns = bl.namespace(files)
    new = json.loads(Path(a.new).read_text())
    ok = json.loads(Path(a.ok).read_text())
    shipped = bl.own_modules(files, ns)
    problems = []
    for m, spec in sorted(new["modules"].items()):
        if m not in shipped:
            continue  # dropped: nothing to prove
        if m not in ok:
            problems.append(f"{m}: ships, but the tree's build did not accept it")
        elif sha256(files[shipped[m]]) != ok[m]:
            problems.append(f"{m}: ships with other bytes than the ones the tree's build accepted")
    if problems:
        sys.exit("the bundle ships what the tree's build did not verify:\n  " + "\n  ".join(problems[:20]) + (f"\n  … and {len(problems) - 20} more" if len(problems) > 20 else ""))
    print(f"every one of the {sum(1 for m in new['modules'] if m in shipped)} shipped new module(s) is byte for byte a module the tree's build accepted")


def main(argv: list[str] | None = None) -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("apply")
    p.add_argument("--bundle", required=True)
    p.add_argument("--tree", required=True)
    p.add_argument("--out", required=True)
    p.set_defaults(fn=cmd_apply)
    p = sub.add_parser("collect")
    p.add_argument("--new", required=True)
    p.add_argument("--log", required=True)
    p.add_argument("--out", required=True)
    p.add_argument("--bundle", default="", help="the bundle the modules came from: its import graph says which modules go with a refused one")
    p.add_argument("--allow-unfinished", action="store_true", help="a build that ran out of time still says which modules it built (a `Built` line is positive evidence): accept those, leave the rest for a later round")
    p.add_argument("--extra-failing", default="", help="module<TAB>why per line (tree_dups.py after-verdict): the modules that imported a copy of a tree module and are not what they were on the tree's module are refused")
    p.add_argument("--union-excluded", default="", help="the modules that `union-next` excluded (one per line): the import of the whole tree stopped at a name each of them declares, or at a module they import")
    p.add_argument("--clashes", default="", help="the output of ModuleClashes.lean on out/built.txt: a new module that declares a name another module of the tree declares is refused")
    p.add_argument("--axioms", default="", help="the output of ModuleAxioms.lean on out/built.txt: a module with a declaration on a non-standard axiom is refused")
    p.set_defaults(fn=cmd_collect)
    p = sub.add_parser("union-input")
    p.add_argument("--root", default="Tengoku.All", help="the module that stands for the tree (what the queue's last step builds)")
    p.add_argument("--new", required=True)
    p.add_argument("--keep", required=True)
    p.add_argument("--excluded", required=True)
    p.add_argument("--out", required=True)
    p.set_defaults(fn=cmd_union_input)
    p = sub.add_parser("union-next")
    p.add_argument("--message", required=True)
    p.add_argument("--new", required=True)
    p.add_argument("--keep", required=True)
    p.add_argument("--excluded", required=True)
    p.add_argument("--bundle", default="")
    p.set_defaults(fn=cmd_union_next)
    p = sub.add_parser("check")
    p.add_argument("--bundle", required=True)
    p.add_argument("--new", required=True)
    p.add_argument("--ok", required=True)
    p.set_defaults(fn=cmd_check)
    a = ap.parse_args(argv)
    a.fn(a)


if __name__ == "__main__":
    main()
