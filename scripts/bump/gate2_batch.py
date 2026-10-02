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

  * a library DEFINITION the statement mentions must mean what it meant (not merely have the same type): identical type
    and value, or the kernel accepts `new = original` by `Eq.refl` with the original replayed beside it (gate2bSameDef).
  * the new declaration is the library's real one, under the original's name (per-record Gate 2 renames its candidate
    to `<name>_archangel`, because the replayed original must be able to use the original name). Here the original is
    not replayed under its name at all: its exported TYPE is compared with the native declaration's type.
  * PASS via=equal: the two types are structurally equal (up to universe-parameter renaming, `mdata` and private-name
    mangling): identical statements, the strongest verdict, and no bridge proof is needed.
  * PASS via=entails: the types differ, and the bridge `fun h => h : NewType → OldType` (Gate 2's fixed bridge) is
    accepted by the kernel (`Lean.addDecl`) after peeling shared binders: exactly Gate 2's entailment.
  * a declaration that uses `sorryAx` (a proof that failed in a tolerant build, or built on one) or any axiom beyond
    propext/Classical.choice/Quot.sound FAILs first (uses_sorry, nonstandard_axiom).
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
import glob
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

def gate2bKind : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot" | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor" | .recInfo _ => "rec"


/-- The copy of an original constant that lives beside its native twin while one definition is compared. -/
def gate2bCopyName (n : Name) : Name := Name.mkStr n "_gate2old"

def gate2bRename (own : NameSet) (e : Expr) : Expr :=
  e.replace fun
    | .const n ls => if own.contains n then some (.const (gate2bCopyName n) ls) else none
    | _ => none

def gate2bIsDef : ConstantInfo → Bool
  | .defnInfo _ => true
  | _ => false

def gate2bRenamable : ConstantInfo → Bool
  | .defnInfo _ | .axiomInfo _ | .opaqueInfo _ => true
  | _ => false

def gate2bRenameCi (own : NameSet) (ci : ConstantInfo) : ConstantInfo :=
  let ren := gate2bRename own
  let rn (n : Name) : Name := if own.contains n then gate2bCopyName n else n
  match ci with
  | .defnInfo i => .defnInfo { i with name := rn i.name, type := ren i.type, value := ren i.value, all := i.all.map rn }
  | .axiomInfo i => .axiomInfo { i with name := rn i.name, type := ren i.type }
  | .opaqueInfo i => .opaqueInfo { i with name := rn i.name, type := ren i.type, value := ren i.value, all := i.all.map rn }
  | other => other

/-- Does the library definition `c` mean in this environment what it meant in the original (`all`, the committed export)?
Identical type and value: yes. Otherwise the KERNEL decides: the original definition and the original library definitions
it is built from are replayed under copy names beside the native ones (the original's theorems as statement-only axioms:
proofs are irrelevant to definitional equality), and `c = c._gate2old` is added as a theorem proved by `Eq.refl`. That
declaration is accepted exactly when the native definition and the original's are definitionally equal, their types
included, so a changed instance path or auxiliary lemma passes and a changed meaning does not. -/
def gate2bSameDefCore (all : Std.HashMap Name ConstantInfo) (oldC c : Name) : CommandElabM (Bool × String) := do
  let env ← getEnv
  let some oldCi := all[oldC]? | return (false, "not in the export")
  let some newCi := env.find? c | return (false, "no native definition")
  if oldCi.levelParams.length != newCi.levelParams.length then return (false, "universe parameter count differs")
  let lvls := newCi.levelParams.map Level.param
  let inst (e : Expr) : Expr := canonPrivate (stripMData (e.instantiateLevelParams oldCi.levelParams lvls))
  let sameValue := match oldCi, newCi with
    | .defnInfo a, .defnInfo b => (inst a.value).eqv (canonPrivate (stripMData b.value))
    | _, _ => false
  if (inst oldCi.type).eqv (canonPrivate (stripMData newCi.type)) && sameValue then return (true, "identical")
  let closure := statementReach all [oldC]
  let mut own : NameSet := {}
  for (n, ci) in closure.toList do
    if (env.find? n).isSome && gate2bRenamable ci then own := own.insert n
  let mut copies : Std.HashMap Name ConstantInfo := {}
  for (n, ci) in closure.toList do
    if own.contains n then copies := copies.insert (gate2bCopyName n) (gate2bRenameCi own ci)
  withoutModifyingEnv do
    try
      liftCoreM (TengokuImport.replayIntoCoreEnv copies)
      let oldTy := gate2bRename own (oldCi.type.instantiateLevelParams oldCi.levelParams lvls)
      let r ← liftTermElabM <| observing do
        let u ← Meta.getLevel oldTy
        Lean.addDecl (Declaration.thmDecl {
          name := Name.mkStr c "_gate2b_defeq"
          levelParams := newCi.levelParams
          type := mkApp3 (mkConst ``Eq [u]) oldTy (mkConst c lvls) (mkConst (gate2bCopyName oldC) lvls)
          value := mkApp2 (mkConst ``Eq.refl [u]) oldTy (mkConst c lvls)
        })
      match r with
      | .ok _ => return (true, "defeq")
      | .error e => return (false, s!"not definitionally equal: {(← e.toMessageData.toString).take 300}")
    catch e => return (false, s!"replay failed: {(← e.toMessageData.toString).take 300}")

def gate2bSameDef (all : Std.HashMap Name ConstantInfo) (c : Name) : CommandElabM (Bool × String) := do
  if let some r := (← gate2bDefMemo.get)[c]? then return r
  let r ← gate2bSameDefCore all c c
  gate2bDefMemo.modify (·.insert c r)
  let (ok, msg) := r
  logInfo m!"GATE2B_DEF {c} result={if ok then msg else "drift"} GATE2B_DEFMSG {if ok then "" else msg} GATE2B_END"
  return r


/-- Controls for the definition check: pairs of library definitions with the SAME type and DIFFERENT values (the original of one
against the native other). The kernel must refuse every one: if it accepts any, the check proves nothing. -/
elab "#gate2_defcontrols " n:num : command => do
  let all ← importedConstantsRef.get
  let env ← getEnv
  let mut byType : Std.HashMap UInt64 (List Name) := {}
  for (c, ci) in all.toList do
    match ci, env.find? c with
    | .defnInfo _, some (.defnInfo _) => byType := byType.insert ci.type.hash (c :: (byType.getD ci.type.hash []))
    | _, _ => pure ()
  let mut done := 0
  for (_, names) in byType.toList do
    if done ≥ n.getNat then break
    match names with
    | a :: b :: _ =>
      let some (.defnInfo av) := all[a]? | continue
      let some (.defnInfo bv) := env.find? b | continue
      if (all[a]!).type.eqv bv.type && !(av.value.eqv bv.value) && av.levelParams.isEmpty && bv.levelParams.isEmpty then
        -- two names for the same thing are not a control (`recOn`/`casesOn` of a structure, `IsRegularPrime := IsRegularNumber`):
        -- only a pair the elaborator itself cannot identify is expected to be refused
        if (← liftTermElabM (Meta.isDefEq (mkConst a) (mkConst b))) then continue
        let (ok, msg) ← gate2bSameDefCore all a b
        logInfo m!"GATE2B_DEFCONTROL {a} {b} result={if ok then "WRONGLY_PASSED" else "rejected"} GATE2B_DEFMSG {msg.take 120} GATE2B_END"
        done := done + 1
    | _ => pure ()

/-- One check: the original `oldN` (from the loaded export) against the native declaration `newN`. -/
def gate2bCheck (oldN newN : Name) : CommandElabM Unit := do
  let all ← importedConstantsRef.get
  withoutModifyingEnv do
    let env ← getEnv
    match all[oldN]?, env.find? newN with
    | none, _ => logInfo m!"GATE2B_FAIL old={oldN} new={newN} reason=old_name_not_in_export"
    | _, none => logInfo m!"GATE2B_FAIL old={oldN} new={newN} reason=new_name_not_found"
    | some oldCi, some newCi =>
      -- the tolerant build keeps a module whose declaration failed: that declaration then stands on `sorryAx`, and so does
      -- everything built on it. Only a declaration with nothing but the three standard axioms is a translation.
      let axs ← collectAxioms newN
      let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
      let extra := axs.filter (fun a => !(std.contains a))
      if axs.contains ``sorryAx then
        logInfo m!"GATE2B_FAIL old={oldN} new={newN} reason=uses_sorry"
        return
      if !extra.isEmpty then
        logInfo m!"GATE2B_FAIL old={oldN} new={newN} reason=nonstandard_axiom axioms={extra.toList}"
        return
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
      let mut defsToCheck : List Name := []
      let mut firstDiff : MessageData := m!""
      for c in boundary.toList do
        match all[c]?, env.find? c with
        | some ci, some native =>
          -- a library DEFINITION: same type is not enough, the meaning must be the same (decided below, by the kernel)
          if gate2bIsDef ci && gate2bIsDef native then
            defsToCheck := c :: defsToCheck
          else if !(tengokuCompatible false true ci native) then
            if collisions.isEmpty then firstDiff := m!"{c}: kinds old={gate2bKind ci} new={gate2bKind native}; old type = {ci.type} || new type = {native.type}"
            collisions := s!"{c}" :: collisions
        | _, _ => pure ()
      if !collisions.isEmpty then
        logInfo m!"GATE2B_FAIL old={oldN} new={newN} reason=name_collision names={String.intercalate "," collisions} GATE2B_DIFF {firstDiff} GATE2B_END"
      else
        liftCoreM (TengokuImport.replayIntoCoreEnv delta)
        let mut drift : List String := []
        let mut why : String := ""
        for c in defsToCheck do
          let (ok, msg) ← gate2bSameDef all c
          if !ok then
            if drift.isEmpty then why := s!"{c}: {msg}"
            drift := s!"{c}" :: drift
        if !drift.isEmpty then
          logInfo m!"GATE2B_FAIL old={oldN} new={newN} reason=name_collision names={String.intercalate "," drift} GATE2B_DIFF {why} GATE2B_END"
        else if tengokuCompatible true true oldCi newCi then
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


def esc(part: str) -> str:
    """A path component as Lean writes it in a module name: a directory `1102.4662` is «1102.4662»."""
    return part if re.fullmatch(r"[^\W\d][\w']*", part) else f"«{part}»"


def emit_vendor(a: argparse.Namespace) -> None:
    """Gate 2's helper Lean code as COMPILED modules of the Vendor project: Vendor/Core.lean is the definitions of gate2/server.py's
    `_HEADER` (one source of truth, taken from it), Vendor/Batch.lean is BATCH_LEAN. The generated check file then holds only
    commands. Parsed inside the check file, that code is read with the syntax of every library it imports, and a library that
    defines a global notation breaks it (quantumoptimization's Dirac `|ψ⟩` made `| .mdata _ e => …` unparseable); compiled in
    a project that imports only Lean, it cannot be, and a compile error shows up in the smoke test instead of after a 30 minute run."""
    out = Path(a.out)
    (out / "Vendor").mkdir(parents=True, exist_ok=True)
    header = server_header()
    core = header.replace("import Mathlib\n", "", 1)
    assert "Elab.async false" in core
    # Core is imported, so its `open` and `set_option` lines are file-local: the check file repeats the ones it needs
    (out / "Vendor" / "Core.lean").write_text(core)
    (out / "Vendor" / "Batch.lean").write_text("import Lean\nimport Vendor.Importer\nimport Vendor.ReplayCore\nimport Vendor.DriverState\nimport Vendor.Gate2\nimport Vendor.Core\n\nset_option Elab.async false\n" + BATCH_LEAN)
    root = (out / "Vendor.lean").read_text() if (out / "Vendor.lean").exists() else ""
    for m in ("Vendor.Core", "Vendor.Batch"):
        if f"import {m}" not in root:
            root += f"import {m}\n"
    (out / "Vendor.lean").write_text(root)
    print(f"wrote {out}/Vendor/Core.lean, Batch.lean")


def module_of(source_path: str) -> str:
    return ".".join(esc(x) for x in source_path[:-5].split("/")) if source_path.endswith(".lean") else source_path


def ledger_latest(path: Path) -> dict[str, dict]:
    latest: dict[str, dict] = {}
    for line in path.read_text().splitlines():
        try:
            r = json.loads(line)
        except ValueError:
            continue
        latest[r["name"]] = r  # later lines win (the file is in time order)
    return latest


def tentative_entries(paths: list[str]) -> dict[str, dict]:
    """The entry list of a library: the statement records tengoku harvested (data/tentative/<lib>.jsonl and data/tentative/<lib>/*.jsonl).
    The ledger only knows what the per-theorem pipeline got to (lean-pool: 2.9k of 137k)."""
    out: dict[str, dict] = {}
    for f in paths:
        for line in Path(f).read_text(errors="replace").splitlines():
            try:
                r = json.loads(line)
            except ValueError:
                continue
            m = re.search(r"/blob/[0-9a-f]{7,40}/([^#]+\.lean)", r.get("source_url", ""))
            if r.get("name") and m:
                out[r["name"]] = {"name": r["name"], "sourcePath": m.group(1), "outcome": "untriaged"}
    return out


def built_modules(lib: Path, roots: list[str]) -> set[str]:
    out = set()
    for p in (lib / ".lake" / "build" / "lib" / "lean").rglob("*.olean"):
        mod = ".".join(esc(x) for x in p.relative_to(lib / ".lake" / "build" / "lib" / "lean").with_suffix("").parts)
        if any(mod == r or mod.startswith(r + ".") for r in roots):
            out.add(mod)
    return out


def generate(a: argparse.Namespace) -> None:
    lib, exports = Path(a.lib), Path(a.exports)
    roots = [r for r in a.roots.split(",") if r]
    entries = ledger_latest(Path(a.ledger)) if Path(a.ledger).exists() else {}
    if a.tentative:
        tent = tentative_entries([f for pat in a.tentative.split(",") if pat for f in sorted(glob.glob(pat))])
        for n, r in tent.items():
            entries.setdefault(n, r)  # the ledger's row (with the pipeline's outcome) wins
    built = built_modules(lib, roots)
    by_module: dict[str, list[str]] = defaultdict(list)
    for name, r in entries.items():
        by_module[module_of(r["sourcePath"])].append(name)
    plan, skipped = [], Counter()
    excluded = {m for m in a.exclude.split(",") if m}
    only = {m for m in a.only.split(",") if m}
    sys.path.insert(0, str(HERE))
    import tolerant_build as tb

    imports_memo: dict[str, set[str]] = {}

    def closure(m: str) -> set[str]:
        """m and every library module it imports, directly or not."""
        if m not in imports_memo:
            imports_memo[m] = {m}
            parts = tb.split_mod(m)
            path = lib.joinpath(*parts[:-1], parts[-1] + ".lean")
            if path.exists():
                for d in tb.header_imports(path.read_text(errors="replace")):
                    if d.split(".")[0] in roots:
                        imports_memo[m] |= closure(d)
        return imports_memo[m]

    clashed: list[str] = []
    for mod, names in sorted(by_module.items()):
        if mod not in built:
            skipped["module_not_built"] += len(names)
            continue
        if only and mod not in only:
            continue
        # Importing the modules together failed on `excluded`: a name one declares is already declared by another (two copies of the
        # same file, a notation Mathlib also has). The modules that import it go too; they get a pass of their own.
        if closure(mod) & excluded:
            skipped["import_clash"] += len(names)
            clashed.append(mod)
            continue
        plain = mod.replace("«", "").replace("»", "")  # exports may be filed under either spelling
        export = next((exports / f"{m}.ndjson" for m in (mod, plain) if (exports / f"{m}.ndjson").exists()), exports / f"{mod}.ndjson")
        namesf = next((exports / f"{m}.names.json" for m in (mod, plain) if (exports / f"{m}.names.json").exists()), exports / f"{mod}.names.json")
        if not export.exists() or not namesf.exists():
            skipped["no_export_for_module"] += len(names)
            continue
        have = set(json.loads(namesf.read_text()).get("names", []))
        present = [n for n in names if n in have]
        skipped["name_not_in_export_closure"] += len(names) - len(present)
        if present:
            plan.append((mod, export, present))
    imports = "".join(f"import {mod}\n" for mod, _, _ in plan)
    # A library that never imports Mathlib (lean4-analysis-tao: "tactic shims that replace the bits of Mathlib") is checked
    # without it: Gate 2's logic needs only Lean, and the library may declare names (a notation `≃`) Mathlib also declares,
    # which would make the two unimportable together.
    uses_mathlib = any(
        re.match(r"\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(?:Mathlib|Batteries|Aesop|Qq|ProofWidgets|Plausible)\b", ln)
        for f in lib.rglob("*.lean") if ".lake" not in f.parts and f.name not in ("gate2-check.lean", "records-deps.lean")
        for ln in f.read_text(errors="replace").splitlines()[:80]
    )
    # The helper code is compiled (Vendor.Core, Vendor.Batch: `emit-vendor`); only commands are parsed here, so no notation a
    # library imports can touch them. The kernel must answer inside each check (see the comment in gate2/server.py's header).
    header = "import Lean\n" + ("import Mathlib\n" if uses_mathlib else "") + imports + "import Vendor.Batch\n\nset_option maxErrors 0\nset_option Elab.async false\n"
    body = [header]
    for k, (mod, export, names) in enumerate(plan):
        body.append(f'\n-- {mod}: {len(names)} declarations\n#tengoku_import_parse "{export.resolve()}"\n')
        for i in range(0, len(names), 40):  # several per command line is fine; 40 keeps each message block small
            body.append(f'#gate2_batch "{",".join(names[i:i + 40])}"\n')
        if k < 3:  # same type, different value: the kernel must refuse (a few, with a small budget: asking it to prove two big unequal definitions equal is slow)
            body.append("set_option maxHeartbeats 20000 in\n#gate2_defcontrols 1\n")
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
    meta = {"modules_checked": len(plan), "declarations": sum(len(n) for _, _, n in plan), "skipped": dict(skipped), "controls": a.controls, "excluded_modules": clashed}
    Path(a.out).with_suffix(".plan.json").write_text(json.dumps(meta, indent=2))
    print(json.dumps(meta))


DEFLINE = re.compile(r"GATE2B_DEF (\S+) result=(\S+) GATE2B_DEFMSG (.*?) GATE2B_END", re.S)
LINE = re.compile(r"GATE2B_(PASS|FAIL) old=(\S+) new=(\S+)(?: via=(\w+))?(?: reason=(\w+))?")


def parse(a: argparse.Namespace) -> None:
    text = Path(a.log).read_text(errors="replace")
    verdicts: dict[tuple[str, str], tuple[str, str]] = {}
    for m in LINE.finditer(text):
        kind, old, new, via, reason = m.groups()
        verdicts[(old, new)] = (kind, via or reason or "")
    entries = ledger_latest(Path(a.ledger)) if Path(a.ledger).exists() else {}
    if a.tentative:
        for n, r in tentative_entries([f for pat in a.tentative.split(",") if pat for f in sorted(glob.glob(pat))]).items():
            entries.setdefault(n, r)
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
        # library definitions the statements are built on: identical, definitionally equal (kernel-checked), or changed meaning
        "definition_controls": {
            "rejected": len(re.findall(r"GATE2B_DEFCONTROL \S+ \S+ result=rejected", text)),
            "wrongly_passed": re.findall(r"GATE2B_DEFCONTROL (\S+) (\S+) result=WRONGLY_PASSED", text),
        },
        "definitions": {
            "by_result": dict(Counter(m.group(2) for m in DEFLINE.finditer(text))),
            "drifted": {m.group(1): re.sub(r"\s+", " ", m.group(3))[:300] for m in DEFLINE.finditer(text) if m.group(2) == "drift"},
        },
    }
    Path(a.out).write_text(json.dumps(res, indent=2))
    # the declarations that passed, by module: what scripts/bump/records.py turns into records
    passed: dict[str, list[str]] = defaultdict(list)
    for (old, _), (kind, _) in own.items():
        r = entries.get(old)
        if kind == "PASS" and r:
            passed[module_of(r["sourcePath"])].append(old)
    Path(a.out).with_name("passed.json").write_text(json.dumps({m: sorted(ns) for m, ns in passed.items()}))
    print(json.dumps(res, indent=2))


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    g = sub.add_parser("generate")
    for f in ("key", "lib", "exports", "ledger", "roots", "out"):
        g.add_argument(f"--{f}", required=True)
    g.add_argument("--controls", type=int, default=0)
    g.add_argument("--tentative", default="", help="comma list of globs of tengoku tentative records: the entries the ledger does not know")
    g.add_argument("--exclude", default="", help="modules whose import failed: they and their importers are left out (comma list)")
    g.add_argument("--only", default="", help="check only these modules (comma list): a pass for what an earlier pass had to leave out")
    v = sub.add_parser("emit-vendor")
    v.add_argument("--out", required=True, help="the Vendor project directory (holds Vendor.lean and Vendor/)")
    q = sub.add_parser("parse")
    for f in ("log", "ledger", "out"):
        q.add_argument(f"--{f}", required=True)
    q.add_argument("--tentative", default="")
    args = ap.parse_args()
    {"generate": generate, "parse": parse, "emit-vendor": emit_vendor}[args.cmd](args)
