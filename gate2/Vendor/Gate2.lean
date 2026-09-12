import Lean
import Vendor.Importer
import Vendor.ReplayCore
import Vendor.DriverState

/-!
Gate 2 — Statement Entailment Gate, for Emissary-Archangel-0.0.1.

v0.0.2 design (v0.0.1 had a real bug — see below).

Verifies, deterministically, that a submitted proof establishes
`NewType → OldType` — "new proves at least as much as old" — where `NewType`
and `OldType` are the *already-elaborated* types of two named declarations
already sitting in the environment (the translated theorem, and the
replayed-from-export original).

v0.0.1 mistake, documented rather than silently dropped: the first attempt
asked for surface syntax like `theorem bridge : newName → oldName`, then
inspected the resulting type's head symbol to check it mentioned newName/
oldName. This does not work in Lean: a theorem's *name*, referenced in term
position, denotes its *proof*, not its statement — `newName → oldName` tries
to use two proof terms as if they were types, which the elaborator correctly
rejects ("type expected, got ..."). There is also no head symbol to check for
a closed proposition like `X.card = 133` — its head is `Eq`, not the
theorem's own name. The whole "check the head constant" approach was built on
a category error.

v0.0.2 fix: never ask for `newName`/`oldName` as surface syntax at all. Pull
their `.type` fields directly (already fully-elaborated Exprs, since both
declarations already compiled), build the goal type `NewType → OldType`
programmatically via `Lean.Meta.mkArrow` (no re-parsing, no delaboration
round-trip), parse *only* the agent-submitted proof text against that
concrete goal, and require it to pass `Lean.addDecl` — the same primitive
that certifies every other declaration in this project, so Gate 2's
"pass" carries the identical kernel guarantee as everything else built this
session, not a separate or weaker one.

v0.0.3: shared leading binders (universe AND term-level). v0.0.2 flatly
rejected anything with non-empty `levelParams` — which in practice is almost
every real theorem, since any implicit `{α : Type u}` argument forces Lean to
auto-generalize a universe variable. That made v0.0.2 only usable on fully
ground/closed statements (numerals, no type variables) — fine for
CompeteMath's competition-style problems, useless for anything from a real
formalization project (e.g. equational_theories' `FreeMagma`, generic over
`{α}`).

Fix, in two parts:
1. Universe params: require newCi/oldCi to have the SAME NUMBER of universe
   params (can't safely match up polymorphism of different arity — that's a
   real "these aren't comparable" case, not something to guess through), then
   instantiate oldCi's type by substituting ITS level params with newCi's
   (positionally) via `Expr.instantiateLevelParams` — newCi's params become
   the canonical ones for the whole check.
2. Term-level binders: `peelSharedBinders` walks newCi's and oldCi's
   (now-unified) types IN LOCKSTEP, introducing one shared local variable per
   matching leading Pi (checked via `isDefEq` on the domains — the same
   notion of "compatible" Lean itself uses for application typechecking) and
   substituting it into both bodies, stopping the moment either side isn't a
   Pi anymore or a domain pair stops unifying. Whatever's left on either side
   after that point (e.g. new has one extra hypothesis old doesn't) just
   becomes part of the arrow's antecedent/consequent — the submitted
   proof_text has to discharge it, and `Lean.addDecl`'s kernel check is what
   actually guarantees soundness here, exactly as before. Not a new kind of
   trust — the same one, applied under a real local context instead of only
   at the top level.
-/

open Lean Elab Command TengokuImport Meta

def parseDottedName (s : String) : Name :=
  (s.splitOn ".").foldl (fun n part => Name.mkStr n part) Name.anonymous

/-- Walks `new`/`old` together, introducing one shared local (fvar) per
matching leading Pi-binder (domains checked defeq — same notion of
"compatible" application typechecking already uses), until either side stops
being a Pi or a domain pair fails to unify. `k` receives the accumulated
fvars plus whatever's left of each side once peeling stops — that remainder
is the real "body" the arrow gets built from. CPS or the growing local
context from nested `withLocalDecl` calls doesn't survive to a plain return.
Binder names/info come from `new` throughout — this only affects how the
final generalized bridge lemma displays/infers its arguments, not soundness
(the kernel check on the fully-generalized term is what guarantees that). -/
partial def peelSharedBinders {α} (new old : Expr) (fvars : Array Expr)
    (k : Array Expr → Expr → Expr → Elab.TermElabM α) : Elab.TermElabM α := do
  match new, old with
  | .forallE name newDom newBody bi, .forallE _ oldDom oldBody _ =>
    if ← Meta.isDefEq newDom oldDom then
      Meta.withLocalDecl name bi newDom fun fvar =>
        peelSharedBinders (newBody.instantiate1 fvar) (oldBody.instantiate1 fvar) (fvars.push fvar) k
    else
      k fvars new old
  | _, _ => k fvars new old

/-- The actual gate. Looks up `newName`/`oldName` in the current environment,
unifies their universe params, peels shared leading binders (v0.0.3), builds
`NewBody → OldBody` under that shared context, parses `proofText` as a term
against that exact goal, generalizes the whole thing back into a closed
term, and requires the result to pass `Lean.addDecl` under a fresh name.
Reports GATE2_PASS/GATE2_FAIL with a specific, inspectable reason — never a
bare "it worked" or "it didn't" with no diagnosis. -/
elab "#gate2_verify " newName:str oldName:str bridgeDeclName:str proofText:str : command => do
  let env ← getEnv
  let newN := parseDottedName newName.getString
  let oldN := parseDottedName oldName.getString
  -- v0.0.4 soundness guard. Found live: 31 "verified" translations had NEVER
  -- been checked against their original. The replay of the old theorem had
  -- silently found nothing (no export for that old_id, or an unqualified
  -- name), leaving its name unclaimed — so when the agent named its OWN new
  -- theorem identically to old_theorem_name, `env.find? oldN` resolved to the
  -- agent's fresh declaration too, and the "entailment" degenerated to
  -- NewType → NewType: a tautology, always provable by `fun h => h`,
  -- certifying nothing. The environment alone cannot tell "the replayed
  -- original" from "whatever currently answers to that name", so this
  -- anchors both sides to the export itself: the old name MUST be one the
  -- export actually contains, and the new name MUST NOT be.
  let imported ← importedConstantsRef.get
  match env.find? newN, env.find? oldN with
  | none, _ => logInfo m!"GATE2_FAIL reason=new_name_not_found name={newN}"
  | _, none => logInfo m!"GATE2_FAIL reason=old_name_not_found name={oldN}"
  | some newCi, some oldCi =>
    if (imported[oldN]?).isNone then
      logInfo m!"GATE2_FAIL reason=old_not_from_export name={oldN} — this name is not in the loaded export, so it was never replayed; whatever it currently resolves to is NOT the original theorem (missing per-id export, or an unqualified/misspelled old name)"
    else if (imported[newN]?).isSome then
      logInfo m!"GATE2_FAIL reason=new_name_is_an_export_name name={newN} — the translated theorem must be a FRESH declaration; reusing a name from the original export (including the original's own name) makes the entailment check a tautology"
    else if newCi.levelParams.length != oldCi.levelParams.length then
      logInfo m!"GATE2_FAIL reason=universe_param_count_mismatch new={newCi.levelParams} old={oldCi.levelParams}"
    else liftTermElabM do
      -- newCi's level params are canonical from here on; oldCi's type gets
      -- rewritten onto them (positionally) so both sides speak the same
      -- universe variables before anything else happens.
      let sharedLevels := newCi.levelParams.map Level.param
      let oldType := oldCi.type.instantiateLevelParams oldCi.levelParams sharedLevels
      -- Pretty-printed once, up front, so EVERY outcome below (pass or fail)
      -- carries the two actual statements — the driving agent should never
      -- have to guess what it's supposed to be relating.
      let newTypeStr ← Meta.ppExpr newCi.type
      let oldTypeStr ← Meta.ppExpr oldType
      let context := m!"new_statement={newTypeStr} old_statement={oldTypeStr}"
      match Lean.Parser.runParserCategory env `term proofText.getString "gate2_proof" with
      | .error parseErr =>
        logInfo m!"GATE2_FAIL reason=parse_error msg={parseErr} {context}"
      | .ok proofStx =>
        let bridgeName := parseDottedName bridgeDeclName.getString
        -- Written from inside the peeling callback below (where the actual
        -- peeled goal — under whatever shared binders were found — first
        -- exists), read back after `observing` settles either way. A plain
        -- local `let` can't escape that scope; this can.
        let goalStrRef ← IO.mkRef (m!"" : MessageData)
        let result ← Term.withoutErrToSorry <| observing do
          peelSharedBinders newCi.type oldType #[] fun fvars newBody oldBody => do
            -- Non-dependent arrow over whatever's left after peeling — oldBody
            -- can still reference the shared fvars (that's the whole point of
            -- peeling them together), but never a bvar pointing at newBody's
            -- own (unshared) tail, so this arrow itself needs no dependency.
            let goalType := Expr.forallE `h newBody oldBody BinderInfo.default
            -- Re-close over the shared binders up front — the bridge lemma is
            -- stated and proved at top level, exactly like before peeling
            -- existed, just now `∀ <shared binders>, newBody → oldBody`
            -- instead of a flat arrow. Computed before elaborating the proof
            -- so the diagnostic ref is populated even if elaboration fails.
            let finalType ← Meta.mkForallFVars fvars goalType
            goalStrRef.set (← Meta.ppExpr finalType)
            let proofTerm ← Elab.Term.elabTermEnsuringType proofStx (some goalType)
            Elab.Term.synthesizeSyntheticMVarsNoPostponing
            let proofTerm ← instantiateMVars proofTerm
            if proofTerm.hasSorry then
              throwError "contains_sorry"
            if proofTerm.hasExprMVar then
              throwError "unresolved_metavariables"
            let finalValue ← Meta.mkLambdaFVars fvars proofTerm
            Lean.addDecl (Declaration.thmDecl {
              name := bridgeName
              levelParams := newCi.levelParams
              type := finalType
              value := finalValue
            })
        let goalStr ← goalStrRef.get
        match result with
        | .ok _ =>
          logInfo m!"GATE2_PASS new={newN} old={oldN} goal={goalStr} {context}"
        | .error e =>
          let msg ← e.toMessageData.toString
          logInfo m!"GATE2_FAIL reason=rejected msg={msg} goal={goalStr} {context}"

/-- Transitive-closure walk used by `#gate2_list_dependencies` below. A
top-level `partial def`, not an inline `let rec` — `NameSet` has no derived
structural-recursion recursor, so Lean's termination checker can't prove this
terminates on its own (it does, via the visited-set guard, but not in a way
the checker can see automatically); `partial` is the same honest escape hatch
`reachableFrom` uses elsewhere in this codebase for the identical pattern. -/
partial def gate2CollectDeps (env : Environment) (visited : NameSet) (stack : List Name) : NameSet :=
  match stack with
  | [] => visited
  | m :: rest =>
    if visited.contains m then gate2CollectDeps env visited rest
    else
      let visited := visited.insert m
      match env.find? m with
      | none => gate2CollectDeps env visited rest
      | some mci =>
        let deps := mci.getUsedConstantsAsSet.toList.filter (fun d => !visited.contains d)
        gate2CollectDeps env visited (deps ++ rest)

/-- Dedup support: after a translation passes both gates, the harness needs to
know exactly which declarations it actually depends on, to record them in the
vendoring registry (and skip re-recording anything already known). Lists the
FULL transitive closure of `name`'s dependencies — the harness diffs this
against its own registry rather than Gate2 needing to know anything about
that registry itself (kept as a plain reporting tool, not another gate). -/
elab "#gate2_list_dependencies " name:str : command => do
  let env ← getEnv
  let n := parseDottedName name.getString
  match env.find? n with
  | none => logInfo m!"GATE2_DEPS_FAIL reason=name_not_found name={n}"
  | some _ =>
    let all := gate2CollectDeps env {} [n]
    let names := all.toList.map toString
    logInfo m!"GATE2_DEPS {String.intercalate "," names}"
