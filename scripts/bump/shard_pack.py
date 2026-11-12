#!/usr/bin/env python3
"""shard_pack.py — what a shard sends to the merge, and how the merge reads it.

pack   --lib DIR --out DIR      the repaired sources and range sidecars of the shard's modules, its verdicts, the constants its passed
                                theorems are made of (BUNDLE_KEEP), the error lines and the passed names
merge  --shards DIR --out DIR   the shards' packs side by side as ONE library directory (sources + sidecars, first copy wins: a module
                                several shards built was repaired the same way), the logs concatenated, passed.json merged — exactly what
                                `bundle.py compose` reads from a single-job run
select --planned JSON --only L  the shards a run builds: all of the plan, or only the listed ones (RESUME: the one that died)
fill   --shards DIR --fill DIR  RESUME: the shard artifacts of an earlier run (--fill) that this run did not produce are moved into --shards
complete --shards DIR --key K --planned JSON
                                every shard of the plan has its result: a shard whose job died leaves no artifact, and the merge, which reads what is there, would
                                take the library for one without that shard's modules (tengoku navier-stokes-euler, 2026-10-17: shard 1, two thirds of the lines,
                                died on a runner shutdown and the bundle was composed without it)
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
    mods = tb.module_files(lib, roots, follow_imports=True)
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
    if a.results and Path(a.results).exists():
        shutil.copy2(a.results, out / "gate2-results.json")
    if a.keep_drops and Path(a.keep_drops).exists():
        # the modules this shard's keep step left out (an import clash: two modules of the library declare one name), for compose to leave out with what imports them
        shutil.copy2(a.keep_drops, out / "keep-drops.txt")
    print(f"packed {len(build)} modules")


def merge(a: argparse.Namespace) -> None:
    out = Path(a.out)
    (out / ".lake" / "build" / "lib" / "lean").mkdir(parents=True, exist_ok=True)
    passed: dict[str, set[str]] = {}
    total: dict = {"shards": 0, "checked": 0, "pass": 0, "pass_equal": 0, "pass_entails": 0, "pass_private_not_records": 0, "pass_unattributed": [], "fail_reasons": {}, "definitions": {}, "controls_wrongly_passed": 0}
    logs = {"gate2.log": [], "errors.log": [], "bundle-deps.log": []}
    packs = 0
    killed: set[str] = set()
    keep_drops: set[str] = set()
    for d in sorted(Path(a.shards).glob("*")):
        artifact = d
        d = next(iter(d.glob("shard-pack")), d) if d.is_dir() else d
        if not (d / "src").exists():
            continue
        packs += 1
        # the modules this shard's Gate 2 gave no verdict (gate2_driver.py writes the file, empty when every module was judged). A shard without it is no proof that every module was judged:
        # the merge refuses it rather than read it as "none"
        kf = next((c for c in (artifact / "emissary" / "gate2-killed.json", d / "gate2-killed.json") if c.is_file()), None)
        if kf is None:
            sys.exit(f"merge: {artifact.name} has no gate2-killed.json: nothing says Gate 2 judged every module of this shard (re-run the shard)")
        data = json.loads(kf.read_text())
        if not isinstance(data, list) or not all(isinstance(x, str) for x in data):
            sys.exit(f"merge: {kf} is not a list of module names")
        killed.update(data)
        for f in (d / "src").rglob("*"):
            if f.is_file() and not f.is_symlink() and ".." not in f.relative_to(d / "src").parts:  # an artifact is data from a job that compiled someone's code
                dst = out / f.relative_to(d / "src")
                if not dst.exists():
                    dst.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(f, dst)
        for f in (d / "ranges").rglob("*.json") if (d / "ranges").exists() else []:
            if f.is_symlink() or ".." in f.relative_to(d / "ranges").parts:
                continue
            dst = out / ".lake" / "build" / "lib" / "lean" / f.relative_to(d / "ranges")
            if not dst.exists():
                dst.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(f, dst)
        if (d / "keep-drops.txt").is_file():
            keep_drops.update(x.strip() for x in (d / "keep-drops.txt").read_text(errors="replace").splitlines() if x.strip())
        for name, acc in logs.items():
            if (d / name).exists():
                acc.append((d / name).read_text(errors="replace"))
        if (d / "gate2-results.json").exists():
            r = json.loads((d / "gate2-results.json").read_text())
            total["shards"] += 1
            for k in ("checked", "pass", "pass_equal", "pass_entails", "pass_private_not_records"):  # the private passes no record was made of (gate2_batch.py parse)
                total[k] += r.get(k, 0)
            for k in ("fail_reasons",):
                for kk, v in r.get(k, {}).items():
                    total[k][kk] = total[k].get(kk, 0) + v
            for kk, v in r.get("definitions", {}).get("by_result", {}).items():
                total["definitions"][kk] = total["definitions"].get(kk, 0) + v
            total["controls_wrongly_passed"] += len(r.get("controls", {}).get("wrongly_passed", []))
            total["pass_unattributed"] = sorted(set(total["pass_unattributed"]) | set(r.get("pass_unattributed", [])))  # passes no judged module of their shard declares (gate2_batch.py attribute)
        if (d / "passed.json").exists():
            for m, ns in json.loads((d / "passed.json").read_text()).items():
                passed.setdefault(m, set()).update(ns)
    if not packs:  # 2026-10-08: a recut from a run without shard artifacts "succeeded" with an empty bundle (0 modules, 0 theorems)
        sys.exit(f"merge: no shard pack in {a.shards} (an artifact with a src/ folder): the run named by recut_from has none (expired, or it was a recut itself)")
    for name, acc in logs.items():
        (Path(a.logs) / name).write_text("\n".join(acc))
    (Path(a.logs) / "gate2-results.json").write_text(json.dumps(total, indent=1))
    (Path(a.logs) / "gate2-killed.json").write_text(json.dumps(sorted(killed)))
    (Path(a.logs) / "keep-drops.txt").write_text("".join(m + "\n" for m in sorted(keep_drops)))
    (Path(a.logs) / "passed.json").write_text(json.dumps({m: sorted(v) for m, v in passed.items()}))
    print(f"merged: {sum(len(v) for v in passed.values())} passed names in {len(passed)} modules; {len(killed)} modules without a Gate 2 verdict"
          + (f"; {len(keep_drops)} left out of the keep step for an import clash: {', '.join(sorted(keep_drops))}" if keep_drops else ""))


REGATE_COUNTS = ("checked", "pass", "pass_equal", "pass_entails", "pass_private_not_records")


def regate(a: argparse.Namespace) -> None:
    """A shard's Gate 2 ran out of its budget (its gate2-killed.json lists the targets it gave no verdict) and a later job judged those targets alone, on the
    shard's own build (bump-shard.yml regate): the shard's pack again, with the new verdicts in it. The sources, the ranges, the build's errors and the earlier
    verdicts stay as they were; a target judged now leaves the killed list; a target the new job could not judge either stays on it.

    flt-anthropic's job 43 (run 43146942669, 12 Nov 2026) built for 3 h 02 min, so Gate 2 had 139 minutes: 288 theorems judged, 125 passed, 114 target modules killed."""
    old = Path(a.old)
    old_pack = next(iter(old.glob("shard-pack")), old)
    if not (old_pack / "src").is_dir():
        sys.exit(f"regate: {old} holds no shard pack (no src/)")
    kf = next((c for c in (old / "emissary" / "gate2-killed.json", old_pack / "gate2-killed.json") if c.is_file()), None)
    if kf is None:
        sys.exit(f"regate: {old} has no gate2-killed.json")
    was_killed = set(json.loads(kf.read_text()))
    asked = {x for x in Path(a.asked).read_text().split() if x}
    if not asked or not asked <= was_killed:
        sys.exit(f"regate: the judged targets must be modules the shard left without a verdict ({len(asked - was_killed)} are not)")
    now_killed = set(json.loads(Path(a.killed).read_text())) if Path(a.killed).exists() else set(asked)  # no file: nothing says Gate 2 judged anything
    if not now_killed <= asked:
        sys.exit("regate: the new Gate 2 lists a module without a verdict that it was not asked to judge")
    old_passed = json.loads((old_pack / "passed.json").read_text()) if (old_pack / "passed.json").exists() else {}
    new_passed = json.loads(Path(a.passed).read_text()) if Path(a.passed).exists() else {}
    if not set(new_passed) <= asked - now_killed:
        sys.exit(f"regate: passes credited to modules it was not asked to judge, or gave no verdict: {sorted(set(new_passed) - (asked - now_killed))[:5]}")
    if set(new_passed) & set(old_passed):
        sys.exit("regate: a module has passes in both packs (a killed module has none in the first)")
    out = Path(a.out)
    if out.exists():
        shutil.rmtree(out)
    shutil.copytree(old_pack, out, symlinks=True)  # src/, ranges/, errors.log, keep-drops.txt: the build is the one the first job made
    merged = dict(old_passed)
    merged.update({m: sorted(ns) for m, ns in new_passed.items()})
    (out / "passed.json").write_text(json.dumps(merged))
    gate2 = [ln for ln in Path(a.gate2).read_text(errors="replace").splitlines() if re.search(r"GATE2B_(PASS|FAIL) ", ln)] if Path(a.gate2).exists() else []
    old_log = (old_pack / "gate2.log").read_text(errors="replace") if (old_pack / "gate2.log").exists() else ""
    (out / "gate2.log").write_text(old_log.rstrip("\n") + ("\n" if old_log.strip() else "") + "\n".join(gate2) + "\n")
    keep_old = (old_pack / "bundle-deps.log").read_text(errors="replace") if (old_pack / "bundle-deps.log").exists() else ""
    keep_new = Path(a.keep).read_text(errors="replace") if a.keep and Path(a.keep).exists() else ""
    (out / "bundle-deps.log").write_text(keep_old + ("\n" if keep_old and not keep_old.endswith("\n") else "") + keep_new)
    drops = set()
    for f in (old_pack / "keep-drops.txt", Path(a.keep_drops) if a.keep_drops else None):
        if f and f.is_file():
            drops.update(x.strip() for x in f.read_text().splitlines() if x.strip())
    (out / "keep-drops.txt").write_text("".join(m + "\n" for m in sorted(drops)))
    r_old = json.loads((old_pack / "gate2-results.json").read_text()) if (old_pack / "gate2-results.json").exists() else {}
    r_new = json.loads(Path(a.results).read_text()) if Path(a.results).exists() else {}
    res = dict(r_old)
    for k in REGATE_COUNTS:
        res[k] = r_old.get(k, 0) + r_new.get(k, 0)
    res["fail_reasons"] = dict(r_old.get("fail_reasons", {}))
    for k, v in r_new.get("fail_reasons", {}).items():
        res["fail_reasons"][k] = res["fail_reasons"].get(k, 0) + v
    res["pass_unattributed"] = sorted(set(r_old.get("pass_unattributed", [])) | set(r_new.get("pass_unattributed", [])))
    # the definitions and controls the new job checked too (shard_pack.merge sums definitions.by_result and counts controls.wrongly_passed; cubic, #180)
    defs = dict(r_old.get("definitions", {}))
    by = dict(defs.get("by_result", {}))
    for k, v in r_new.get("definitions", {}).get("by_result", {}).items():
        by[k] = by.get(k, 0) + v
    defs["by_result"] = by
    if "drifted" in defs or "drifted" in r_new.get("definitions", {}):
        defs["drifted"] = {**defs.get("drifted", {}), **r_new.get("definitions", {}).get("drifted", {})}  # {name: what drifted}
    res["definitions"] = defs
    ctl_old, ctl_new = r_old.get("controls", {}), r_new.get("controls", {})
    res["controls"] = {**ctl_old, "checked": ctl_old.get("checked", 0) + ctl_new.get("checked", 0),
                       "wrongly_passed": sorted(set(ctl_old.get("wrongly_passed", [])) | set(ctl_new.get("wrongly_passed", [])))}
    res["regate"] = {"asked": len(asked), "judged": len(asked - now_killed), "still_killed": len(now_killed)}
    (out / "gate2-results.json").write_text(json.dumps(res, indent=1))
    side = Path(a.out_emissary)
    side.mkdir(parents=True, exist_ok=True)
    (side / "gate2-killed.json").write_text(json.dumps(sorted((was_killed - asked) | now_killed)))
    (side / "gate2-results.json").write_text(json.dumps(res, indent=1))
    if (old / "emissary" / "tb-final.json").is_file():
        shutil.copy2(old / "emissary" / "tb-final.json", side / "tb-final.json")
    print(f"regate: {len(asked)} targets asked, {len(asked - now_killed)} judged, {sum(len(v) for v in new_passed.values())} new passes; {len(now_killed)} still without a verdict")


def has_pack(artifact: Path) -> bool:
    d = next(iter(artifact.glob("shard-pack")), artifact) if artifact.is_dir() else artifact
    return (d / "src").exists()


def select(a: argparse.Namespace) -> None:
    planned = json.loads(a.planned)
    only = [x for x in re.split(r"[,\s]+", a.only.strip()) if x]
    if not only:
        print(json.dumps(planned))
        return
    unknown = [x for x in only if x not in {str(s) for s in planned}]
    if unknown:
        sys.exit(f"select: shard(s) {unknown} are not in the plan {planned}")
    print(json.dumps([s for s in planned if str(s) in only]))


def fill(a: argparse.Namespace) -> None:
    shards, source = Path(a.shards), Path(a.fill)
    moved = 0
    for d in sorted(source.glob("*")) if source.is_dir() else []:
        if d.is_dir() and not d.is_symlink() and not (shards / d.name).exists():
            shutil.move(str(d), str(shards / d.name))
            moved += 1
    print(f"filled in {moved} shard(s) from the earlier run")


def complete(a: argparse.Namespace) -> None:
    planned = json.loads(a.planned)
    missing = [s for s in planned if not has_pack(Path(a.shards) / f"shard-{a.key}-{s}")]
    if missing:
        sys.exit(
            f"complete: no result for shard(s) {missing} of the {len(planned)} planned: the job died or the artifact is gone. "
            "Run them again (workflow input only_shards, with fill_from = this run for the others) and compose from that"
        )
    print(f"all {len(planned)} planned shards have a result")


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("pack")
    for f in ("lib", "roots", "out", "gate2", "errors", "passed", "keep"):
        p.add_argument(f"--{f}", required=True)
    p.add_argument("--modules", default="")
    p.add_argument("--results", default="")
    p.add_argument("--keep-drops", default="", help="the modules the keep step left out for an import clash, one a line")
    m = sub.add_parser("merge")
    for f in ("shards", "out", "logs"):
        m.add_argument(f"--{f}", required=True)
    s = sub.add_parser("select")
    s.add_argument("--planned", required=True)
    s.add_argument("--only", default="")
    fl = sub.add_parser("fill")
    for f in ("shards", "fill"):
        fl.add_argument(f"--{f}", required=True)
    rg = sub.add_parser("regate", help="the shard's pack again, with the verdicts of a job that judged its killed targets (bump-shard.yml regate)")
    for f in ("old", "asked", "gate2", "passed", "results", "killed", "out", "out-emissary"):
        rg.add_argument("--" + f, required=True)
    rg.add_argument("--keep", default="")
    rg.add_argument("--keep-drops", default="")
    c = sub.add_parser("complete")
    for f in ("shards", "key", "planned"):
        c.add_argument(f"--{f}", required=True)
    a = ap.parse_args()
    {"pack": pack, "merge": merge, "select": select, "fill": fill, "complete": complete, "regate": regate}[a.cmd](a)
