/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QuantumMechanics.HilbertSpaces.OneDimension.PositionStates
public import Physlib.QuantumMechanics.Operators.OneDimension.Unbounded
public import Physlib.Mathematics.Distribution.PowMul
public import Physlib.QuantumMechanics.HilbertSpaces.OneDimension.SchwartzSubmodule

-- @@ L12-22 verbatim
/-!

# Position operator

In this module we define:
- The position operator on functions `ℝ → ℂ`
- The position operator on Schwartz maps as an unbounded operator on the Hilbert space.

We show that position wavefunctions are generalized eigenvectors of the position operator.

-/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
open Physlib


-- @@ L28-28 verbatim
namespace QuantumMechanics


-- @@ L30-30 verbatim
namespace OneDimension

-- @@ L31-31 verbatim
noncomputable section

-- @@ L32-32 verbatim
open _root_.QuantumMechanics.OneDimension.HilbertSpace


-- @@ L34-38 verbatim
/-!

## The position operator on functions `ℝ → ℂ`

-/


-- @@ L40-51 verbatim
/-- The position operator is defined as the linear map from `ℝ → ℂ` to `ℝ → ℂ` taking
  `ψ` to `x * ψ`. -/
def positionOperator : (ℝ → ℂ) →ₗ[ℂ] ℝ → ℂ where
  toFun ψ := fun x ↦ x * ψ x
  map_add' ψ1 ψ2 := by
    funext x
    simp only [Pi.add_apply]
    ring
  map_smul' a ψ1 := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

-- @@ L52-56 verbatim
/-!

## The position operator on Schwartz maps

-/


-- @@ L58-58 verbatim
open ContDiff


-- @@ L60-60 verbatim
open SchwartzMap


-- @@ L62-64 verbatim
/-- The position operator on the Schwartz maps is defined as the linear map from
  `𝓢(ℝ, ℂ)` to itself, such that `ψ` is taken to `fun x => x * ψ x`. -/
def positionOperatorSchwartz : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) := Distribution.powOneMul ℂ


-- @@ L66-69 verbatim
lemma positionOperatorSchwartz_apply_fun (ψ : 𝓢(ℝ, ℂ)) :
    (positionOperatorSchwartz ψ) = fun x => x * ψ x := by
  simp [positionOperatorSchwartz]
  rfl


-- @@ L71-75 verbatim
@[simp]
lemma positionOperatorSchwartz_apply (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (positionOperatorSchwartz ψ) x = x * ψ x := by
  simp [positionOperatorSchwartz]
  rfl


-- @@ L77-79 verbatim
/-- The unbounded position operator, whose domain is Schwartz maps. -/
def positionOperatorUnbounded : UnboundedOperator schwartzIncl schwartzIncl_injective :=
  UnboundedOperator.ofSelfCLM positionOperatorSchwartz


-- @@ L81-85 verbatim
/-!

## Generalized eigenvectors of the position operator

-/


-- @@ L87-92 verbatim
lemma positionStates_generalized_eigenvector_positionOperatorUnbounded (x : ℝ) :
    positionOperatorUnbounded.IsGeneralizedEigenvector (positionState x) x := by
  dsimp [positionOperatorUnbounded]
  rw [UnboundedOperator.isGeneralizedEigenvector_ofSelfCLM_iff]
  intro ψ
  simp [positionState_apply]


-- @@ L94-98 verbatim
/-!

## Position operator is symmetric

-/


-- @@ L100-108 verbatim
lemma positionOperatorUnbounded_isSymmetric :
    positionOperatorUnbounded.IsSymmetric := by
  intro ψ1 ψ2
  dsimp [positionOperatorUnbounded]
  rw [schwartzIncl_inner, schwartzIncl_inner]
  congr
  funext x
  simp only [positionOperatorSchwartz_apply, map_mul, Complex.conj_ofReal]
  ring


-- @@ L110-110 verbatim
end

-- @@ L111-111 verbatim
end OneDimension

-- @@ L112-112 verbatim
end QuantumMechanics
