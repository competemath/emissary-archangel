/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.CenteredMaximal.Statement


-- @@ L10-18 verbatim
/-!
# Basic API for the centred maximal function and its weak type constant

* `le_maximalFunction`: every cube average is at most the maximal function;
* `exists_lt_average_of_lt_maximalFunction`: a level below the maximal function is exceeded by
  some cube average;
* `volume_closedBall_eq`: the cube of radius `r` has volume `(2r)ᵈ`;
* `weakTypeConstant_le`, `le_weakTypeConstant`: the constant is the least weak type bound.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
open MeasureTheory Metric

-- @@ L25-25 verbatim
open scoped ENNReal


-- @@ L27-27 verbatim
namespace LeanPool.CenteredMaximal


-- @@ L29-29 verbatim
variable {d : ℕ}


-- @@ L31-35 verbatim
/-- Every cube average is at most the maximal function. -/
theorem le_maximalFunction (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) {r : ℝ} (hr : 0 < r) :
    (volume (closedBall x r))⁻¹ * ∫⁻ y in closedBall x r, ‖f y‖ₑ ≤ maximalFunction f x :=
  le_iSup₂ (f := fun r (_ : 0 < r) =>
    (volume (closedBall x r))⁻¹ * ∫⁻ y in closedBall x r, ‖f y‖ₑ) r hr


-- @@ L37-43 verbatim
/-- A level strictly below the maximal function is exceeded by some cube average. -/
theorem exists_lt_average_of_lt_maximalFunction {f : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    {α : ℝ≥0∞} (h : α < maximalFunction f x) :
    ∃ r, 0 < r ∧ α < (volume (closedBall x r))⁻¹ * ∫⁻ y in closedBall x r, ‖f y‖ₑ := by
  obtain ⟨r, hr⟩ := lt_iSup_iff.1 h
  obtain ⟨hr₀, hr⟩ := lt_iSup_iff.1 hr
  exact ⟨r, hr₀, hr⟩


-- @@ L45-48 verbatim
/-- The closed cube of radius `r` (side `2r`) in `ℝᵈ` has volume `(2r)ᵈ`. -/
theorem volume_closedBall_eq (x : Fin d → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volume (closedBall x r) = ENNReal.ofReal ((2 * r) ^ d) := by
  simpa using Real.volume_pi_closedBall x hr


-- @@ L50-53 verbatim
/-- A weak type bound stays a weak type bound when it is increased. -/
theorem IsWeakTypeBound.mono {C C' : ℝ≥0∞} (h : IsWeakTypeBound d C) (hCC' : C ≤ C') :
    IsWeakTypeBound d C' :=
  fun f hf α => (h f hf α).trans (mul_le_mul_left hCC' _)


-- @@ L55-57 verbatim
/-- The weak type constant is at most every weak type bound. -/
theorem weakTypeConstant_le {C : ℝ≥0∞} (h : IsWeakTypeBound d C) : weakTypeConstant d ≤ C :=
  sInf_le h


-- @@ L59-62 verbatim
/-- A lower bound for every weak type bound is a lower bound for the weak type constant. -/
theorem le_weakTypeConstant {c : ℝ≥0∞} (h : ∀ C, IsWeakTypeBound d C → c ≤ C) :
    c ≤ weakTypeConstant d :=
  le_sInf h


-- @@ L64-64 verbatim
end LeanPool.CenteredMaximal
