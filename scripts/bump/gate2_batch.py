#!/usr/bin/env python3
"""gate2_batch.py — Gate 2 (statement entailment) for a whole built library in ONE Lean process.

Today's Gate 2 (gate2/server.py) checks one declaration per call: it imports the tree (~90 s), parses the original's
whole module export (seconds to minutes), elaborates a synthetic candidate, replays the original's statement closure
and kernel-checks `NewType → OldType`. The mechanical pass therefore costs minutes per theorem, though no
mathematics happens in them. After a whole-library build the new declarations already exist, so ONE process can
import the environment once, parse each module's export once, and check every declaration of the module.

The check per declaration is Gate 2's own, from the same Lean code (the header is read out of gate2/server.py, not
copied: `statementReach`, `tengokuCompatible`, the export parser and replay are shared), with the differences the
whole-library setting forces, each stated here:

  * the new declaration is the library's real one, under the original's name (per-record Gate 2 renames its candidate
    to `<name>_archangel`, because the replayed original must be able to use the original name). Here the original is
    not replayed under its name at all: its exported TYPE is compared with the native declaration's type.
  * PASS via=equal: the two types are structurally equal (up to universe-parameter renaming, `mdata` and private-name
    mangling): identical statements, the strongest verdict, and no bridge proof is needed.
  * PASS via=entails: the types differ, and the bridge `fun h => h : NewType → OldType` (Gate 2's fixed bridge) is
    accepted by the kernel (`Lean.addDecl`) after peeling shared binders: exactly Gate 2's entailment.
  * everything else FAILs with a reason: the original is not in its export, the new name does not exist, a library
    definition the statement mentions changed type (`tengokuCompatible`, the same boundary check, with the library's
    own definitions compared like the candidate's own ones are today: abbrev bodies too), or the bridge is rejected.
  * each check runs inside `withoutModifyingEnv`, so replays never accumulate or collide between declarations.

Controls: `--controls N` also checks N pairs of UNRELATED declarations (old statement of A against the new B); all must
FAIL, or the checker is vacuous.

  gate2_batch.py generate --key K --lib DIR --exports DIR --ledger FILE --roots R,R --out check.lean [--controls N]
  gate2_batch.py parse    --log lean.log --ledger FILE --out results.json
"""

from __future__ import annotations

import argparse
import json
import random
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
SERVER = HERE.parents[1] / "gate2" / "server.py"

# What the batched check adds to Gate 2's header (which supplies statementReach, tengokuCompatible, stripMData,
# canonPrivate, the export parser and the replay).
BATCH_LEAN = r'''
open Lean Elab Command TengokuImport Meta

/-- One check: the original `oldN` (from the loaded export) against the native declaration `newN`. -/
def gate2bCheck (oldN newN : Name) : CommandElabM Unit := do
  let all ← importedConstantsRef.get
  withoutModifyingEnv do
    let env ← getEnv
    match all[oldN]?, env.find? newN with
    | none, _ => logInfo m!"GATE2B_FAIL old={oldN} new={newN} reason=old_name_not_in_export"
    | _, none => logInfo m!"GATE2B_FAIL old={oldN} new={newN} reason=new_name_not_found"
    | some oldCi, some newCi =>
      let closure := statementReach all [oldN]
      let delta := closure.filter (fun m _ => (env.find? m).isNone)
      -- the boundary: natives that a replayed declaration, or the original's own statement, mentions
      let mut boundary : NameSet := {}
      for (_, ci) in delta.toList do
        for c in ci.type.getUsedConstants do
          if (env.find? c).isSome then boundary := boundary.insert c
        if let some v := ci.value? then
          for c in v.getUsedConstants do
            if (env.find? c).isSome then boundary := boundary.insert c
      for c in oldCi.type.getUsedConstants do
        if (env.find? c).isSome then boundary := boundary.insert c
      boundary := boundary.erase oldN
      let mut collisions : List String := []
      for c in boundary.toList do
        match all[c]?, env.find? c with
        | some ci, some native =>
          -- a name the export has is the library's own: its abbrev bodies are compared too, as the candidate's own are today
          if !(tengokuCompatible false true ci native) then collisions := s!"{c}" :: collisions
        | _, _ => pure ()
      if !collisions.isEmpty then
        logInfo m!"GATE2B_FAIL old={oldN} new={newN} reason=name_collision names={String.intercalate "," collisions}"
      else
        liftCoreM (TengokuImport.replayIntoCoreEnv delta)
        if tengokuCompatible true true oldCi newCi then
          logInfo m!"GATE2B_PASS old={oldN} new={newN} via=equal"
        else if newCi.levelParams.length != oldCi.levelParams.length then
          logInfo m!"GATE2B_FAIL old={oldN} new={newN} reason=universe_param_count_mismatch"
        else
          match Lean.Parser.runParserCategory (← getEnv) `term "fun h => h" "gate2b_bridge" with
          | .error e => logInfo m!"GATE2B_FAIL old={oldN} new={newN} reason=parse_error msg={e}"
          | .ok stx =>
            let sharedLevels := newCi.levelParams.map Level.param
            let oldType := oldCi.type.instantiateLevelParams oldCi.levelParams sharedLevels
            let result ← liftTermElabM <| Term.withoutErrToSorry <| observing do
              peelSharedBinders newCi.type oldType #[] fun fvars newBody oldBody => do
                let goalType := Expr.forallE `h newBody oldBody BinderInfo.default
                let finalType ← Meta.mkForallFVars fvars goalType
                let proofTerm ← Elab.Term.elabTermEnsuringType stx (some goalType)
                Elab.Term.synthesizeSyntheticMVarsNoPostponing
                let proofTerm ← instantiateMVars proofTerm
                if proofTerm.hasSorry then throwError "contains_sorry"
                if proofTerm.hasExprMVar then throwError "unresolved_metavariables"
                let finalValue ← Meta.mkLambdaFVars fvars proofTerm
                Lean.addDecl (Declaration.thmDecl {
                  name := `_gate2b_bridge
                  levelParams := newCi.levelParams
                  type := finalType
                  value := finalValue
                })
            match result with
            | .ok _ => logInfo m!"GATE2B_PASS old={oldN} new={newN} via=entails"
            | .error e =>
              let msg ← e.toMessageData.toString
              logInfo m!"GATE2B_FAIL old={oldN} new={newN} reason=rejected msg={msg.take 160}"

/-- Every name in `names`, original and new under the same name. -/
elab "#gate2_batch " names:str : command => do
  for s in (names.getString.splitOn ",").filter (· != "") do
    let n := parseDottedName s
    gate2bCheck n n

/-- A control: the original statement of `oldS` against the native declaration `newS` (unrelated: must fail). -/
elab "#gate2_cross " oldS:str newS:str : command => do
  gate2bCheck (parseDottedName oldS.getString) (parseDottedName newS.getString)
'''


def server_header() -> str:
    s = SERVER.read_text()
    m = re.search(r'^_HEADER = """(.*?)^"""', s, re.S | re.M)
    if not m:
        sys.exit("gate2/server.py: _HEADER not found")
    return m.group(1)


def module_of(source_path: str) -> str:
    return source_path[:-5].replace("/", ".") if source_path.endswith(".lean") else source_path


def ledger_latest(path: Path) -> dict[str, dict]:
    latest: dict[str, dict] = {}
    for line in path.read_text().splitlines():
        try:
            r = json.loads(line)
        except ValueError:
            continue
        latest[r["name"]] = r  # later lines win (the file is in time order)
    return latest


def built_modules(lib: Path, roots: list[str]) -> set[str]:
    out = set()
    for p in (lib / ".lake" / "build" / "lib" / "lean").rglob("*.olean"):
        mod = ".".join(p.relative_to(lib / ".lake" / "build" / "lib" / "lean").with_suffix("").parts)
        if any(mod == r or mod.startswith(r + ".") for r in roots):
            out.add(mod)
    return out


def generate(a: argparse.Namespace) -> None:
    lib, exports = Path(a.lib), Path(a.exports)
    roots = [r for r in a.roots.split(",") if r]
    entries = ledger_latest(Path(a.ledger))
    built = built_modules(lib, roots)
    by_module: dict[str, list[str]] = defaultdict(list)
    for name, r in entries.items():
        by_module[module_of(r["sourcePath"])].append(name)
    plan, skipped = [], Counter()
    for mod, names in sorted(by_module.items()):
        if mod not in built:
            skipped["module_not_built"] += len(names)
            continue
        export = exports / f"{mod}.ndjson"
        namesf = exports / f"{mod}.names.json"
        if not export.exists() or not namesf.exists():
            skipped["no_export_for_module"] += len(names)
            continue
        have = set(json.loads(namesf.read_text()).get("names", []))
        present = [n for n in names if n in have]
        skipped["name_not_in_export_closure"] += len(names) - len(present)
        if present:
            plan.append((mod, export, present))
    header = server_header()
    imports = "".join(f"import {mod}\n" for mod, _, _ in plan)
    header = header.replace("import Mathlib\n", "import Mathlib\n" + imports, 1)
    body = [header, BATCH_LEAN]
    for mod, export, names in plan:
        body.append(f'\n-- {mod}: {len(names)} declarations\n#tengoku_import_parse "{export.resolve()}"\n')
        for i in range(0, len(names), 40):  # several per command line is fine; 40 keeps each message block small
            body.append(f'#gate2_batch "{",".join(names[i:i + 40])}"\n')
    if a.controls:
        rng = random.Random(7)
        # unrelated pairs inside one module: the original statement of A against the new B
        mods = [(m, e, n) for m, e, n in plan if len(n) >= 2]
        for k in range(a.controls):
            if not mods:
                break
            mod, export, names = mods[k % len(mods)]
            x, y = rng.sample(names, 2)
            body.append(f'\n-- control {k}: the original statement of {x} against the new {y}\n#tengoku_import_parse "{export.resolve()}"\n')
            body.append(f'#gate2_cross "{x}" "{y}"\n')
    Path(a.out).write_text("".join(body))
    meta = {"modules_checked": len(plan), "declarations": sum(len(n) for _, _, n in plan), "skipped": dict(skipped), "controls": a.controls}
    Path(a.out).with_suffix(".plan.json").write_text(json.dumps(meta, indent=2))
    print(json.dumps(meta))


LINE = re.compile(r"GATE2B_(PASS|FAIL) old=(\S+) new=(\S+)(?: via=(\w+))?(?: reason=(\w+))?")


def parse(a: argparse.Namespace) -> None:
    text = Path(a.log).read_text(errors="replace")
    verdicts: dict[tuple[str, str], tuple[str, str]] = {}
    for m in LINE.finditer(text):
        kind, old, new, via, reason = m.groups()
        verdicts[(old, new)] = (kind, via or reason or "")
    entries = ledger_latest(Path(a.ledger))
    own = {k: v for k, v in verdicts.items() if k[0] == k[1]}
    cross = {k: v for k, v in verdicts.items() if k[0] != k[1]}
    by_outcome: dict[str, Counter] = defaultdict(Counter)
    for (old, _), (kind, why) in own.items():
        r = entries.get(old)
        if r:
            by_outcome[r["outcome"]][f"{kind}:{why}"] += 1
    res = {
        "checked": len(own),
        "pass": sum(1 for v in own.values() if v[0] == "PASS"),
        "pass_equal": sum(1 for v in own.values() if v == ("PASS", "equal")),
        "pass_entails": sum(1 for v in own.values() if v == ("PASS", "entails")),
        "fail_reasons": dict(Counter(v[1] for v in own.values() if v[0] == "FAIL")),
        "controls": {"checked": len(cross), "wrongly_passed": [list(k) for k, v in cross.items() if v[0] == "PASS"]},
        "by_pipeline_outcome": {k: dict(v) for k, v in by_outcome.items()},
    }
    Path(a.out).write_text(json.dumps(res, indent=2))
    print(json.dumps(res, indent=2))


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    g = sub.add_parser("generate")
    for f in ("key", "lib", "exports", "ledger", "roots", "out"):
        g.add_argument(f"--{f}", required=True)
    g.add_argument("--controls", type=int, default=0)
    q = sub.add_parser("parse")
    for f in ("log", "ledger", "out"):
        q.add_argument(f"--{f}", required=True)
    args = ap.parse_args()
    generate(args) if args.cmd == "generate" else parse(args)
