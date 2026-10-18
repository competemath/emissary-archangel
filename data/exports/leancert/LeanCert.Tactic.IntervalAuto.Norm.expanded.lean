/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Lean
import LeanCert.Tactic.IntervalAuto.Types


-- @@ L9-16 verbatim
/-!
# Goal Normalization for Interval Tactics

This module provides utilities for normalizing goal structure before parsing:
- Bridge theorems for converting between Set.Icc and arrow/And forms
- Detection of goal patterns that need normalization
- The `interval_norm` tactic
-/


-- @@ L18-18 verbatim
open Lean Meta Elab Tactic


-- @@ L20-20 verbatim
namespace LeanCert.Tactic.Auto


-- @@ L22-22 verbatim
/-! ## Bridge Theorems -/


-- @@ L24-28 verbatim
/-- Bridge: Set.Icc bound to arrow chain (lo ≤ x → x ≤ hi). -/
theorem forall_arrow_of_Icc {α} [Preorder α] {lo hi : α} {P : α → Prop} :
    (∀ x ∈ Set.Icc lo hi, P x) → ∀ x, lo ≤ x → x ≤ hi → P x := by
  intro h x hxlo hxhi
  exact h x ⟨hxlo, hxhi⟩


-- @@ L30-34 verbatim
/-- Bridge: Set.Icc bound to reversed arrow chain (x ≤ hi → lo ≤ x). -/
theorem forall_arrow_of_Icc_rev {α} [Preorder α] {lo hi : α} {P : α → Prop} :
    (∀ x ∈ Set.Icc lo hi, P x) → ∀ x, x ≤ hi → lo ≤ x → P x := by
  intro h x hxhi hxlo
  exact h x ⟨hxlo, hxhi⟩


-- @@ L36-40 verbatim
/-- Bridge: Set.Icc bound to conjunctive domain (lo ≤ x ∧ x ≤ hi). -/
theorem forall_and_of_Icc {α} [Preorder α] {lo hi : α} {P : α → Prop} :
    (∀ x ∈ Set.Icc lo hi, P x) → ∀ x, (lo ≤ x ∧ x ≤ hi) → P x := by
  intro h x hx
  exact h x hx


-- @@ L42-46 verbatim
/-- Bridge: Set.Icc bound to reversed conjunctive domain (x ≤ hi ∧ lo ≤ x). -/
theorem forall_and_of_Icc_rev {α} [Preorder α] {lo hi : α} {P : α → Prop} :
    (∀ x ∈ Set.Icc lo hi, P x) → ∀ x, (x ≤ hi ∧ lo ≤ x) → P x := by
  intro h x hx
  exact h x ⟨hx.2, hx.1⟩


-- @@ L48-48 verbatim
/-! ## Goal Structure Detection -/


-- @@ L50-104 verbatim
private def goalNeedsIccWrapper (goalType : Lean.Expr) : MetaM Bool := do
  let goalType ← whnf goalType
  if !goalType.isForall then
    return false
  let .forallE name ty body _ := goalType | return false
  withLocalDeclD name ty fun x => do
    let bodyRaw := body.instantiate1 x
    let bodyWhnf ← whnf bodyRaw
    if !bodyWhnf.isForall then
      return false
    let .forallE _ memTy innerBody _ := bodyWhnf | return false
    let memTyRaw :=
      match bodyRaw with
      | .forallE _ memTyRaw _ _ => memTyRaw
      | _ => memTy

    let isMembership : MetaM Bool := do
      match_expr memTyRaw with
      | Membership.mem _ _ _ _ _ => return true
      | _ => return false

    if (← isMembership) then
      return false

    let isAnd (e : Lean.Expr) : Bool :=
      match e with
      | .app (.app (.const ``And _) _) _ => true
      | _ => false

    let getLeArgs (e : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
      let fn := e.getAppFn
      let args := e.getAppArgs
      if fn.isConstOf ``LE.le && args.size >= 4 then
        return some (args[2]!, args[3]!)
      if fn.isConstOf ``LT.lt && args.size >= 4 then
        return some (args[2]!, args[3]!)
      return none

    let isBoundProp (e : Lean.Expr) : MetaM Bool := do
      if let some (a, b) ← getLeArgs e then
        if (← isDefEq a x) || (← isDefEq b x) then
          return true
      return false

    let memTyWhnf ← withTransparency TransparencyMode.all <| whnf memTy
    if isAnd memTy || isAnd memTyWhnf then
      return true

    if innerBody.isForall then
      let .forallE _ memTy2 _ _ := innerBody | return false
      let memTy2Whnf ← withTransparency TransparencyMode.all <| whnf memTy2
      if (← isBoundProp memTy) || (← isBoundProp memTyWhnf) then
        if (← isBoundProp memTy2) || (← isBoundProp memTy2Whnf) then
          return true
    return false


-- @@ L106-115 verbatim
private partial def hasNonPropBinder (e : Lean.Expr) : MetaM Bool := do
  let eWhnf ← whnf e
  if !eWhnf.isForall then
    return false
  let .forallE name ty body _ := eWhnf | return false
  if (← isProp ty) then
    withLocalDeclD name ty fun h => do
      hasNonPropBinder (body.instantiate1 h)
  else
    return true


-- @@ L117-130 verbatim
private def goalIsMultivariate (goalType : Lean.Expr) : MetaM Bool := do
  let goalType ← whnf goalType
  if !goalType.isForall then
    return false
  let .forallE name ty body _ := goalType | return false
  withLocalDeclD name ty fun x => do
    let body := body.instantiate1 x
    let bodyWhnf ← whnf body
    if !bodyWhnf.isForall then
      return false
    let .forallE _ memTy innerBody _ := bodyWhnf | return false
    withLocalDeclD `hx memTy fun _hx => do
      let innerInst := innerBody.instantiate1 _hx
      hasNonPropBinder innerInst


-- @@ L132-147 verbatim
/-- Try to normalize goal to Set.Icc form -/
def tryNormalizeGoalToIcc : TacticM Bool := do
  let goal ← getMainGoal
  if ← goalNeedsIccWrapper (← goal.getType) then
    try
      evalTactic (← `(tactic|
        first
        | refine (forall_arrow_of_Icc ?_)
        | refine (forall_arrow_of_Icc_rev ?_)
        | refine (forall_and_of_Icc ?_)
        | refine (forall_and_of_Icc_rev ?_)
      ))
      return true
    catch _ => return false
  else
    return false


-- @@ L149-149 verbatim
/-! ## rpow Normalization Helpers -/


-- @@ L151-154 verbatim
/-- Normalize `x ^ (1/2)` into `sqrt x`. -/
private theorem rpow_one_half_eq_sqrt (x : ℝ) :
    x ^ ((1 : ℝ) / 2) = Real.sqrt x := by
  rw [Real.sqrt_eq_rpow]


-- @@ L156-160 verbatim
/-- Normalize `x ^ (2⁻¹)` into `sqrt x`. -/
private theorem rpow_inv_two_eq_sqrt (x : ℝ) :
    x ^ ((2 : ℝ)⁻¹) = Real.sqrt x := by
  have hInv : ((2 : ℝ)⁻¹) = ((1 : ℝ) / 2) := by norm_num
  rw [hInv, rpow_one_half_eq_sqrt]


-- @@ L162-170 verbatim
/-- Normalize `x ^ (3/2)` into `x * sqrt x`. -/
private theorem rpow_three_halves_eq_mul_sqrt (x : ℝ) :
    x ^ ((3 : ℝ) / 2) = x * Real.sqrt x := by
  by_cases hx : x = 0
  · subst hx
    norm_num
  · have hsplit : ((3 : ℝ) / 2) = ((1 : ℝ) / 2) + (1 : ℕ) := by norm_num
    rw [hsplit, Real.rpow_add_natCast hx ((1 : ℝ) / 2) 1, pow_one]
    simp [Real.sqrt_eq_rpow, mul_comm]


-- @@ L172-176 verbatim
/-- Normalize `x ^ 1.5` into `x * sqrt x`. -/
private theorem rpow_one_point_five_eq_mul_sqrt (x : ℝ) :
    x ^ (1.5 : ℝ) = x * Real.sqrt x := by
  have hDec : (1.5 : ℝ) = ((3 : ℝ) / 2) := by norm_num
  rw [hDec, rpow_three_halves_eq_mul_sqrt]


-- @@ L178-178 verbatim
/-! ## Canonicalization Simp Sets -/


-- @@ L180-186 verbatim
/-- Apply robust, non-expansive normalization rewrites. -/
private def intervalNormSafeSimp : TacticM Unit := do
  evalTactic (← `(tactic|
    simp only [ge_iff_le, gt_iff_lt, sub_eq_add_neg, Rat.divInt_eq_div,
      Set.mem_ofPred, pow_two, sq,
      rpow_one_half_eq_sqrt, rpow_inv_two_eq_sqrt,
      rpow_three_halves_eq_mul_sqrt, rpow_one_point_five_eq_mul_sqrt] at *))


-- @@ L188-190 verbatim
/-- Apply goal-level cleanup rewrites after safe normalization. -/
private def intervalNormGoalSimp : TacticM Unit := do
  evalTactic (← `(tactic| simp only [pow_zero, pow_one, one_mul, mul_one] at *))


-- @@ L192-192 verbatim
/-! ## Main Normalization -/


-- @@ L194-206 verbatim
/-- Normalize common goal patterns for interval tactics. -/
def intervalNormCore : TacticM Unit := do
  try
    intervalNormSafeSimp
  catch _ =>
    pure ()
  try
    intervalNormGoalSimp
  catch _ =>
    pure ()
  -- Try to normalize the outermost variable to Set.Icc form.
  -- The parser handles mixed forms, so partial normalization is fine for multivariate goals.
  discard <| tryNormalizeGoalToIcc


-- @@ L208-212 verbatim
/-- The interval_norm tactic.

    Normalizes inequalities, subtraction, rational division, and domain syntax
    to reduce goal-shape variation before parsing. -/
syntax (name := intervalNormTac) "interval_norm" : tactic


-- @@ L214-215 verbatim
@[tactic intervalNormTac]
def elabIntervalNorm : Tactic := fun _ => intervalNormCore


-- @@ L217-217 verbatim
end LeanCert.Tactic.Auto
