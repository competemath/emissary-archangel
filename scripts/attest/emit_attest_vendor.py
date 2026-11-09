#!/usr/bin/env python3
"""emit_attest_vendor.py: Gate 2's own Lean modules for a STATEMENT attestation, in a Lake project of their own.

  emit_attest_vendor.py --out vendorproj      (after:  cp -r gate2/Vendor.lean gate2/Vendor vendorproj/)

It writes what scripts/bump/gate2_batch.py `emit-vendor` writes (Vendor/Core.lean, Vendor/Batch.lean: Gate 2's checks, taken from gate2/server.py and gate2_batch.py, one
source of truth), then Vendor/Attest.lean: the batch check `gate2bCheck` re-derived by TEXT TRANSFORMATION from gate2_batch.BATCH_LEAN, with exactly these differences
(every anchor must be found exactly once, or this script stops, so a change to the batch check can never be missed silently):

  * the check's `uses_sorry` / `nonstandard_axiom` refusal is replaced by the STATEMENT-ONLY rule. The new declaration must be a theorem. Its PROOF may stand on `sorryAx` (these are
    statements); nothing that gives its STATEMENT meaning may: every constant its type mentions must stand on the three standard axioms only, and the proof may use no axiom
    besides those and `sorryAx`;
  * a definition the original's statement reaches must not stand on `sorryAx` either (a statement about a hole is not a statement);
  * MIGRATION TABLE (data/attest/fate-x/migration.lean, hand-written): old-library constants the tree no longer has (`Monoid.toNatPow`, `algebraMap`, ...) are defined, for the time of
    one problem's check, by the tree's own constants (`#attest_env_save` .. `#attest_env_restore`). The check refuses to pass if one of them is missing or stands on `sorryAx`, and reports which
    of them the original's statement reaches (`GATE2S_MIGRATED`) and which constants it still lacks (`GATE2S_MISSING`). A pass is then RELATIVE to that table (the attestation carries it, hashed);
  * every verdict is `GATE2S_PASS` / `GATE2S_FAIL`, never `GATE2B_*`: nothing that reads the batch's verdicts (scripts/bump/gate2_batch.py parse, the bump bundles' records) can mistake one for the other.

Everything else (the replay of the original around the tree's own declarations, the kernel-checked sameness of definitions, `equal` or the bridge `fun h => h`) is the batch check's own code.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
BUMP = HERE.parent / "bump"

SORRY_BLOCK = re.compile(
    r"      -- the tolerant build keeps a module whose declaration failed.*?"
    r"      if !extra\.isEmpty then\n"
    r"        logInfo m!\"GATE2B_FAIL old=\{oldN\} new=\{newN\} reason=nonstandard_axiom axioms=\{extra\.toList\}\"\n"
    r"        return\n",
    re.S,
)

STATEMENT_ONLY = '''      -- the migration table (hand-written definitions of old-library names, see `#attest_env_save`): each must exist and may not stand on `sorryAx`
      for m in (← attestMigrationRef.get) do
        match env.find? m with
        | none =>
          logInfo m!"GATE2S_FAIL old={oldN} new={newN} reason=migration_missing names={m}"
          return
        | some _ =>
          let a ← collectAxioms m
          if a.any (fun x => !(([``propext, ``Classical.choice, ``Quot.sound] : List Name).contains x)) then
            logInfo m!"GATE2S_FAIL old={oldN} new={newN} reason=migration_uses_sorry names={m}"
            return
      -- STATEMENT-ONLY (scripts/attest/emit_attest_vendor.py). The new declaration is a theorem whose PROOF may stand on `sorryAx`; its STATEMENT may not, nor anything the
      -- statement mentions, and the proof may use no axiom besides the three standard ones and `sorryAx`.
      let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
      if !(match newCi with | .thmInfo _ => true | _ => false) then
        logInfo m!"GATE2S_FAIL old={oldN} new={newN} reason=not_a_theorem"
        return
      let mut sorryIn : List Name := []
      for c in newCi.type.getUsedConstants do
        let a ← collectAxioms c
        if a.any (fun x => !(std.contains x)) then sorryIn := c :: sorryIn
      if !sorryIn.isEmpty then
        logInfo m!"GATE2S_FAIL old={oldN} new={newN} reason=statement_uses_sorry names={String.intercalate "," (sorryIn.map toString)}"
        return
      let proofAxs ← collectAxioms newN
      let extra := proofAxs.filter (fun a => !(std.contains a) && a != ``sorryAx)
      if !extra.isEmpty then
        logInfo m!"GATE2S_FAIL old={oldN} new={newN} reason=nonstandard_axiom axioms={extra.toList}"
        return
'''

ALL_ANCHOR = "  let all ← importedConstantsRef.get\n"
ALL_RENAMED = '''  let all ← importedConstantsRef.get
  -- the original's references to a constant whose signature changed are read as references to the hand-written wrapper with the old signature (the migration table's `renames`)
  let ren ← attestRenameRef.get
  let all := if ren.isEmpty then all else all.map (fun _ ci => attestRenameCi ren ci)
  -- instance arguments of the original that do not typecheck against the tree's constants are re-synthesized by the tree (counted, reported)
  attestRepairCount.set 0
  let repairedL ← liftTermElabM (all.toList.mapM fun (n, ci) => do return (n, ← attestRepairCi ci))
  let all : Std.HashMap Name ConstantInfo := Std.HashMap.ofList repairedL
  let nRepaired ← attestRepairCount.get
  if nRepaired > 0 then logInfo m!"GATE2S_REPAIRED old={oldN} count={nRepaired} GATE2S_END"
'''
CLOSURE_ANCHOR = "      let closure := statementReach all [oldN]\n"
GOAL_ANCHOR = "                let goalType := Expr.forallE `h newBody oldBody BinderInfo.default\n"
GOAL_DIAG = '''                let d1 ← attestFirstDiff newBody oldBody
                let d2 ← try
                    Meta.check oldBody
                    (pure none : MetaM (Option String))
                  catch e =>
                    let m ← e.toMessageData.toString
                    pure (some m)
                attestDiagRef.set s!"{d1.getD "none"} || the original's statement on its own: {d2.getD "well typed"}"
'''
RESULT_ANCHOR = "            let result ← liftTermElabM <| Term.withoutErrToSorry <| observing do\n"
REFUSED_ANCHOR = '''              logInfo m!"GATE2B_FAIL old={oldN} new={newN} reason=rejected msg={first} GATE2B_DIFF old type = {oldCi.type} || new type = {newCi.type} GATE2B_END"\n'''
REFUSED_REPLACEMENT = '''              let whereDiff := s!"{← attestDiagRef.get} || full message: {(msg.replace "\\n" " ").take 900}"
              logInfo m!"GATE2B_FAIL old={oldN} new={newN} reason=rejected msg={first} GATE2B_DIFF old type = {oldCi.type} || new type = {newCi.type} GATE2B_FIRSTDIFF {whereDiff} GATE2B_END"
'''
BRIDGE_ANCHOR = '`term "fun h => h" "gate2b_bridge"'
BRIDGE_REPLACEMENT = '`term (← attestBridgeRef.get) "gate2b_bridge"'
DRIFT_ANCHOR = '            if drift.isEmpty then why := s!"{c}: {msg}"\n'
DRIFT_REPLACEMENT = '''            if drift.isEmpty then
              -- diagnostics: where the original definition's value and the tree's first differ (what the elaborator does not see through)
              let dd ← (try liftTermElabM (do
                  match all[c]?, env.find? c with
                  | some (.defnInfo a), some (.defnInfo b) =>
                    if a.levelParams.length == b.levelParams.length then
                      let ls := b.levelParams.map Level.param
                      let av := a.value.instantiateLevelParams a.levelParams ls
                      let r ← attestFirstDiff av b.value
                      match r with
                      | some t => pure t
                      | none =>
                        -- the elaborator sees them as equal and the kernel does not: both bodies, instances explicit
                        let pa : String ← (try withOptions (fun o => o.setBool `pp.explicit true) (do return toString (← Meta.ppExpr av)) catch _ => pure "?")
                        let pb : String ← (try withOptions (fun o => o.setBool `pp.explicit true) (do return toString (← Meta.ppExpr b.value)) catch _ => pure "?")
                        pure s!"none (kernel-only). ORIGINAL BODY: {(pa.replace "\\n" " ").take 1200} TREE BODY: {(pb.replace "\\n" " ").take 1200}"
                    else pure "universe parameters differ"
                  | _, _ => pure "not both definitions") catch _ => pure "diagnostic failed")
              why := s!"{c}: {msg} FIRSTDIFF {dd}"
'''
BOUNDARY_ANCHOR = "      boundary := boundary.erase oldN\n"
MISSING_AND_MIGRATED = '''      -- what the original's statement (and the declarations replayed for it) still lacks in the tree, and which migration-table entries it reaches
      let mut missing : NameSet := {}
      let mut reached : NameSet := {}
      for (_, ci) in delta.toList do
        for c in (ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]) do
          reached := reached.insert c
          if (env.find? c).isNone && !(delta.contains c) then missing := missing.insert c
      for c in oldCi.type.getUsedConstants do
        reached := reached.insert c
        if (env.find? c).isNone && !(delta.contains c) && c != oldN then missing := missing.insert c
      let usedMigration := (← attestMigrationRef.get).filter (fun m => reached.contains m)
      if !usedMigration.isEmpty then
        logInfo m!"GATE2S_MIGRATED old={oldN} names={String.intercalate "," (usedMigration.toList.map toString)} GATE2S_END"
      if !missing.isEmpty then
        logInfo m!"GATE2S_MISSING old={oldN} names={String.intercalate "," (missing.toList.map toString)} GATE2S_END"
'''

ORIGINAL_SORRY = '''      let origSorry := closure.toList.filter (fun (_, ci) => match ci with
        | .defnInfo d => d.value.getUsedConstants.contains ``sorryAx
        | .opaqueInfo d => d.value.getUsedConstants.contains ``sorryAx
        | _ => false)
      if !origSorry.isEmpty then
        logInfo m!"GATE2S_FAIL old={oldN} new={newN} reason=original_definition_uses_sorry names={String.intercalate "," (origSorry.map (fun (n, _) => toString n))}"
        return
'''

HELPERS = '''
initialize attestSavedEnv : IO.Ref (Option Environment) ← IO.mkRef none
/-- The migration table's names while one problem is checked (set by `#attest_env_save`). -/
initialize attestMigrationRef : IO.Ref (Array Name) ← IO.mkRef #[]
/-- Old names whose signature changed in the tree: the original's references to `old` are read as references to `new` (a hand-written wrapper with the old signature). -/
initialize attestRenameRef : IO.Ref (Std.HashMap Name Name) ← IO.mkRef {}

def attestRenameExpr (ren : Std.HashMap Name Name) (e : Expr) : Expr :=
  e.replace fun
    | .const n ls => (ren[n]?).map (fun m => Expr.const m ls)
    | _ => none

def attestRenameCi (ren : Std.HashMap Name Name) (ci : ConstantInfo) : ConstantInfo :=
  let r := attestRenameExpr ren
  match ci with
  | .defnInfo i => .defnInfo { i with type := r i.type, value := r i.value }
  | .thmInfo i => .thmInfo { i with type := r i.type, value := r i.value }
  | .axiomInfo i => .axiomInfo { i with type := r i.type }
  | .opaqueInfo i => .opaqueInfo { i with type := r i.type, value := r i.value }
  | other => other

/-- Instance arguments of the original that do not typecheck against the tree's constants (a constant whose instance argument is now `NonAssocRing` where the original passed a `Ring`, a class renamed) are
re-synthesized by the tree. Counted per problem and reported (`GATE2S_REPAIRED`); the kernel then still has to accept `fun h => h` between the translation and the repaired original. -/
initialize attestRepairCount : IO.Ref Nat ← IO.mkRef 0

def attestRepairApp (e : Expr) : MetaM TransformStep := do
  unless e.isApp do return .continue
  let f := e.getAppFn
  let mut args := e.getAppArgs
  let mut fty ← (try Meta.inferType f catch _ => pure (Expr.sort Level.zero))
  let mut changed := false
  for i in [0:args.size] do
    fty ← Meta.whnf fty
    match fty with
    | .forallE _ d b bi =>
      if bi.isInstImplicit then
        let aty ← (try Meta.inferType args[i]! catch _ => pure d)
        let ok ← (try Meta.isDefEq aty d catch _ => pure true)
        if !ok then
          match (← (try Meta.synthInstance? d catch _ => pure none)) with
          | some inst =>
            args := args.set! i inst
            changed := true
            attestRepairCount.modify (· + 1)
          | none => pure ()
      fty := b.instantiate1 args[i]!
    | _ => break
  if changed then return .done (mkAppN f args) else return .continue

def attestRepairCi (ci : ConstantInfo) : MetaM ConstantInfo := do
  let rep (e : Expr) : MetaM Expr := (try Meta.transform e (post := attestRepairApp) catch _ => pure e)
  match ci with
  | .defnInfo i => return .defnInfo { i with type := ← rep i.type, value := ← rep i.value }
  | .thmInfo i => return .thmInfo { i with type := ← rep i.type }
  | .axiomInfo i => return .axiomInfo { i with type := ← rep i.type }
  | .opaqueInfo i => return .opaqueInfo { i with type := ← rep i.type }
  | other => return other

/-- The bridge term tried between the translated and the original statement: `fun h => h` first; the driver runs the problems it refuses once more with another (`#attest_bridge`). The kernel checks
every bridge: a different term is a different proof of the same implication, never a different claim. -/
initialize attestBridgeRef : IO.Ref String ← IO.mkRef "fun h => h"

/-- Diagnostics only, set while a bridge is tried: the first difference the elaborator does not see through, and whether the original's statement is well typed on its own (`Meta.check`). -/
initialize attestDiagRef : IO.Ref String ← IO.mkRef ""

/-- Diagnostics only: the first place where two types differ, as text (heads and the two subterms), so that a refused bridge can be read without a Lean build. -/
partial def attestFirstDiff (a b : Expr) : MetaM (Option String) := do
  if a.eqv b then return none
  -- a difference the elaborator sees through (a reducible wrapper, an instance path) is not the cause: skip it
  if (← try Meta.isDefEq a b catch _ => pure false) then return none
  let shw (x : Expr) : MetaM String := do
    let s ← try pure (toString (← Meta.ppExpr x)) catch _ => pure (toString x)
    pure s!"{(s.replace "\\n" " ").take 260}"
  match a, b with
  | .forallE n t1 b1 bi, .forallE _ t2 b2 _ =>
    if !t1.eqv t2 then attestFirstDiff t1 t2
    else Meta.withLocalDecl n bi t1 fun x => attestFirstDiff (b1.instantiate1 x) (b2.instantiate1 x)
  | .lam n t1 b1 bi, .lam _ t2 b2 _ =>
    if !t1.eqv t2 then attestFirstDiff t1 t2
    else Meta.withLocalDecl n bi t1 fun x => attestFirstDiff (b1.instantiate1 x) (b2.instantiate1 x)
  | _, _ =>
    let fa := a.getAppFn
    let fb := b.getAppFn
    let xs := a.getAppArgs
    let ys := b.getAppArgs
    if fa.eqv fb && xs.size == ys.size then
      for i in [0:xs.size] do
        if !(xs[i]!.eqv ys[i]!) then
          let r ← attestFirstDiff xs[i]! ys[i]!
          let h ← shw fa
          return (r.map fun t => s!"arg {i} of {h}: {t}")
      return none
    else
      let withAll ← try Meta.withTransparency .all (Meta.isDefEq a b) catch _ => pure false
      return some s!"{← shw a}  VERSUS  {← shw b}  [defeq at all transparency: {withAll}]"
'''

COMMANDS = '''
/-- Every name in `names`, original and new under the same name: a STATEMENT check (`GATE2S_*` verdicts). -/
elab "#gate2_statements " names:str : command => do
  for s in (names.getString.splitOn ",").filter (· != "") do
    let n := parseDottedName s
    gate2sCheck n n

/-- Start of a problem's migration table: remember the environment (the table's definitions are added to it for this problem's check only) and the table's names. -/
elab "#attest_env_save " names:str rens:str : command => do
  attestSavedEnv.set (some (← getEnv))
  attestMigrationRef.set (((names.getString.splitOn ",").filter (· != "")).map parseDottedName).toArray
  let mut m : Std.HashMap Name Name := {}
  for pr in (rens.getString.splitOn ",").filter (· != "") do
    match pr.splitOn "=" with
    | [a, b] => m := m.insert (parseDottedName a) (parseDottedName b)
    | _ => pure ()
  attestRenameRef.set m

/-- The bridge term for the problems that follow (default `fun h => h`). -/
elab "#attest_bridge " t:str : command => attestBridgeRef.set t.getString

/-- End of it: the environment as it was, so that the next problem's statement is elaborated without the old names. -/
elab "#attest_env_restore" : command => do
  if let some e ← attestSavedEnv.get then setEnv e
  attestSavedEnv.set none
  attestMigrationRef.set #[]
  attestRenameRef.set {}

/-- A marker the driver splits the log by: what follows, up to the next marker, is one problem's. -/
elab "#attest_begin " id:str : command => logInfo m!"ATTEST_BEGIN {id.getString}"
'''


def batch_lean() -> str:
    sys.path.insert(0, str(BUMP))
    import gate2_batch  # noqa: E402

    return gate2_batch.BATCH_LEAN


def derive(batch: str) -> str:
    """The text of Vendor/Attest.lean, from gate2_batch.BATCH_LEAN."""
    a = batch.index("/-- One check:")
    e = batch.index("/-- Every name in `names`")
    chk = batch[a:e]
    if len(SORRY_BLOCK.findall(chk)) != 1:
        sys.exit("emit_attest_vendor: the batch check's sorry/axiom block was not found exactly once; the transformation needs updating for this gate2_batch.py")
    chk = SORRY_BLOCK.sub(lambda _m: STATEMENT_ONLY, chk)
    if chk.count(CLOSURE_ANCHOR) != 1:
        sys.exit("emit_attest_vendor: `let closure := statementReach all [oldN]` not found exactly once")
    chk = chk.replace(CLOSURE_ANCHOR, CLOSURE_ANCHOR + ORIGINAL_SORRY, 1)
    for anchor in (BRIDGE_ANCHOR, DRIFT_ANCHOR):
        if chk.count(anchor) != 1:
            sys.exit(f"emit_attest_vendor: `{anchor.strip()}` not found exactly once")
    chk = chk.replace(BRIDGE_ANCHOR, BRIDGE_REPLACEMENT, 1).replace(DRIFT_ANCHOR, DRIFT_REPLACEMENT, 1)
    if chk.count(ALL_ANCHOR) != 1:
        sys.exit("emit_attest_vendor: `let all ← importedConstantsRef.get` not found exactly once in the check")
    chk = chk.replace(ALL_ANCHOR, ALL_RENAMED, 1)
    if chk.count(BOUNDARY_ANCHOR) != 1:
        sys.exit("emit_attest_vendor: `boundary := boundary.erase oldN` not found exactly once")
    chk = chk.replace(BOUNDARY_ANCHOR, BOUNDARY_ANCHOR + MISSING_AND_MIGRATED, 1)
    for anchor in (GOAL_ANCHOR, RESULT_ANCHOR):
        if chk.count(anchor) != 1:
            sys.exit(f"emit_attest_vendor: `{anchor.strip()}` not found exactly once")
    chk = chk.replace(GOAL_ANCHOR, GOAL_ANCHOR + GOAL_DIAG, 1)
    chk = chk.replace(RESULT_ANCHOR, "            attestDiagRef.set \"\"\n" + RESULT_ANCHOR, 1)
    if chk.count(REFUSED_ANCHOR) != 1:
        sys.exit("emit_attest_vendor: the refused-bridge log line was not found exactly once")
    chk = chk.replace(REFUSED_ANCHOR, REFUSED_REPLACEMENT, 1)
    if chk.count("def gate2bCheck (oldN newN : Name)") != 1:
        sys.exit("emit_attest_vendor: `def gate2bCheck` not found exactly once")
    chk = chk.replace("def gate2bCheck (oldN newN : Name)", "def gate2sCheck (oldN newN : Name)", 1)
    chk = chk.replace("GATE2B_", "GATE2S_")
    if "GATE2B_" in chk or "uses_sorry\"" in chk.replace("statement_uses_sorry", "").replace("original_definition_uses_sorry", ""):
        sys.exit("emit_attest_vendor: a batch verdict or the batch sorry refusal is left in the statement check")
    # the helpers it calls (gate2bSameDef, gate2bKind, ...) stay the batch's own: they are in Vendor.Batch
    header = "import Lean\nimport Vendor.Importer\nimport Vendor.ReplayCore\nimport Vendor.DriverState\nimport Vendor.Gate2\nimport Vendor.Core\nimport Vendor.Batch\n\nset_option Elab.async false\nopen Lean Elab Command TengokuImport Meta\n\n"
    return header + HELPERS + chk + COMMANDS


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    a = ap.parse_args(argv)
    sys.path.insert(0, str(BUMP))
    import gate2_batch

    out = Path(a.out)
    gate2_batch.emit_vendor(argparse.Namespace(out=str(out)))
    (out / "Vendor" / "Attest.lean").write_text(derive(batch_lean()))
    root = (out / "Vendor.lean").read_text()
    if "import Vendor.Attest" not in root:
        (out / "Vendor.lean").write_text(root + "import Vendor.Attest\n")
    print(f"wrote {out}/Vendor/Attest.lean")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
