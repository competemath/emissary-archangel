/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QuantumMechanics.HilbertSpaces.OneDimension.SchwartzSubmodule
public import Physlib.QuantumMechanics.Operators.OneDimension.Unbounded
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Analysis.Calculus.ContDiff.Operations

-- @@ L12-16 verbatim
/-!

# Parity operator

-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
namespace QuantumMechanics


-- @@ L22-22 verbatim
namespace OneDimension

-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
namespace HilbertSpace

-- @@ L26-26 verbatim
open MeasureTheory SchwartzMap


-- @@ L28-32 verbatim
/-!

## The parity operator on functions

-/


-- @@ L34-43 verbatim
/-- The parity operator is defined as linear map from `ℝ → ℂ` to itself, such that
  `ψ` is taken to `fun x => ψ (-x)`. -/
def parityOperator : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ) where
  toFun ψ := fun x => ψ (-x)
  map_add' ψ1 ψ2 := by
    funext x
    simp
  map_smul' a ψ1 := by
    funext x
    simp


-- @@ L45-49 verbatim
/-!

## The parity operator on Schwartz maps

-/


-- @@ L51-82 verbatim
/-- The parity operator on the Schwartz maps is defined as the linear map from
  `𝓢(ℝ, ℂ)` to itself, such that `ψ` is taken to `fun x => ψ (-x)`. -/
def parityOperatorSchwartz : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) := by
  refine (SchwartzMap.compCLM ℂ (g := (fun x => - x : ℝ → ℝ)) ⟨?_, ?_⟩ ?_)
  · fun_prop
  · intro n
    simp only [Real.norm_eq_abs]
    use 1, 1
    intro x
    simp only [pow_one, one_mul]
    rw [show (fun x : ℝ => -x) = -(fun x : ℝ => x) from rfl]
    rw [iteratedFDeriv_neg_apply]
    simp only [norm_neg]
    match n with
    | 0 => simp
    | 1 =>
      rw [iteratedFDeriv_succ_eq_comp_right]
      simp [ContinuousLinearMap.norm_id]
    | .succ (.succ n) =>
      rw [iteratedFDeriv_succ_eq_comp_right]
      simp only [Nat.succ_eq_add_one, fderiv_fun_id, Function.comp_apply,
        LinearIsometryEquiv.norm_map, ge_iff_le]
      rw [iteratedFDeriv_const_of_ne]
      simp only [Pi.zero_apply, norm_zero]
      apply add_nonneg
      · exact zero_le_one' ℝ
      · exact abs_nonneg x
      simp
  · simp
    use 1, 1
    intro x
    simp


-- @@ L84-86 verbatim
/-- The unbounded parity operator, whose domain is Schwartz maps. -/
def parityOperatorUnbounded : UnboundedOperator schwartzIncl schwartzIncl_injective :=
  UnboundedOperator.ofSelfCLM parityOperatorSchwartz


-- @@ L88-93 verbatim
@[simp]
lemma parityOperatorSchwartz_parityOperatorSchwartz (ψ : 𝓢(ℝ, ℂ)) :
    parityOperatorSchwartz (parityOperatorSchwartz ψ) = ψ := by
  ext x
  show ψ (- - x) = ψ x
  rw [neg_neg]


-- @@ L95-99 verbatim
/-!

## Parity operator is symmetric

-/


-- @@ L101-101 verbatim
open InnerProductSpace


-- @@ L103-114 verbatim
lemma parityOperatorUnbounded_isSymmetric :
    parityOperatorUnbounded.IsSymmetric := by
  intro ψ1 ψ2
  dsimp [parityOperatorUnbounded]
  rw [schwartzIncl_inner, schwartzIncl_inner]
  let f (x : ℝ) :=
    (starRingEnd ℂ) ((ψ1) (-x)) * (ψ2) x
  change ∫ (x : ℝ), f x = _
  trans ∫ (x : ℝ), f (- x)
  · exact Eq.symm (integral_neg_eq_self f volume)
  · simp only [neg_neg, f]
    rfl


-- @@ L116-116 verbatim
end HilbertSpace

-- @@ L117-117 verbatim
end

-- @@ L118-118 verbatim
end OneDimension

-- @@ L119-119 verbatim
end QuantumMechanics
