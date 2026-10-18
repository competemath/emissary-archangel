/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Meta.ProveContinuous
import LeanCert.Tactic.LeanCert.Normalize


-- @@ L9-15 verbatim
/-!
# Proof-Carrying Reification

The reifier's syntax result is not itself a semantic bridge.  This module
packages the reflected AST with a kernel-checked equality between its evaluator
and the original function.  Solver capabilities are derived separately.
-/


-- @@ L17-17 verbatim
open Lean Meta Elab Tactic


-- @@ L19-19 verbatim
namespace LeanCert.Tactic.Bridge


-- @@ L21-29 verbatim
structure ReifiedFunction where
  arity : Nat
  ast : Lean.Expr
  original : Lean.Expr
  /-- A proof of `∀ x₀ ... xₙ, Expr.eval ρ ast = original x₀ ... xₙ`,
  where `ρ i` reads the corresponding argument and defaults to zero. -/
  evalEq : Lean.Expr
  unfolded : Array Name := #[]
  deriving Inhabited


-- @@ L31-35 verbatim
structure FunctionCapabilities where
  supportedCore : Option Lean.Expr := none
  continuousCore : Option Lean.Expr := none
  domainValid : Option Lean.Expr := none
  deriving Inhabited


-- @@ L37-39 verbatim
private def mkEnvironment (arguments : Array Lean.Expr) : MetaM Lean.Expr := do
  let values ← mkListLit (mkConst ``Real) arguments.toList
  mkAppM ``LeanCert.Tactic.Bridge.realEnvironment #[values]


-- @@ L41-62 verbatim
private def closeBridgeGoal (report : LeanCert.Meta.ReifyReport)
    (proposition : Lean.Expr) : TacticM Lean.Expr := do
  let originalGoals ← getGoals
  let saved ← saveState
  let proof ← mkFreshExprMVar proposition MetavarKind.syntheticOpaque
  setGoals [proof.mvarId!]
  try
    LeanCert.Tactic.closeReificationBridge report
    let remaining ← getGoals
    unless remaining.isEmpty do
      let rendered ← remaining.mapM fun goal => goal.withContext do
        ppExpr (← goal.getType)
      throwError "reification equality normalization left proof obligations:\n\
        {MessageData.joinSep rendered m!"\n"}"
    let proof ← instantiateMVars proof
    if proof.hasMVar then
      throwError "reification equality contains metavariables"
    setGoals originalGoals
    return proof
  catch exception =>
    saved.restore
    throw exception


-- @@ L64-83 verbatim
/-- Reify a closed real-valued function and prove evaluator agreement. -/
def reifyFunction (function : Lean.Expr) : TacticM ReifiedFunction := do
  let report ← LeanCert.Meta.reifyWithReport function
  lambdaTelescope function fun arguments body => do
    for argument in arguments do
      let type ← inferType argument
      unless ← isDefEq type (mkConst ``Real) do
        throwError "proof-carrying reification currently requires real arguments"
    let environment ← mkEnvironment arguments
    let evaluated ← mkAppM ``LeanCert.Core.Expr.eval #[environment, report.expr]
    let localType ← mkAppM ``Eq #[evaluated, body]
    let localProof ← closeBridgeGoal report localType
    let evalEq ← mkLambdaFVars arguments localProof
    return {
      arity := arguments.size
      ast := report.expr
      original := function
      evalEq
      unfolded := report.unfolded
    }


-- @@ L85-99 verbatim
/-- Derive expression-fragment capabilities independently from semantic
reification equality.  Failure to derive a capability is expected and does not
invalidate `evalEq`. -/
def deriveCapabilities (function : ReifiedFunction) : MetaM FunctionCapabilities := do
  let supportedCore : Option Lean.Expr ←
    try
      pure (some (← LeanCert.Meta.mkSupportedCoreProof function.ast))
    catch _ =>
      pure none
  let continuousCore : Option Lean.Expr ←
    try
      pure (some (← LeanCert.Meta.mkContinuousCoreProof function.ast))
    catch _ =>
      pure none
  return { supportedCore, continuousCore }


-- @@ L101-101 verbatim
end LeanCert.Tactic.Bridge
