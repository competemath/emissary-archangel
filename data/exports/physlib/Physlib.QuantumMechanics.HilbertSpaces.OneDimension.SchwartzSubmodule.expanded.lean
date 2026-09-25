/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QuantumMechanics.HilbertSpaces.OneDimension.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Physlib.Meta.TODO.Basic

-- @@ L11-18 verbatim
/-!

# Schwartz submodule of the Hilbert space

This can be used to define e.g.
the rigged Hilbert space.

-/


-- @@ L20-20 verbatim
TODO "Remove 1d Schwartz submodule once dependencies are all generalized to SpaceDHilbertSpace."


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
namespace QuantumMechanics


-- @@ L26-26 verbatim
namespace OneDimension


-- @@ L28-28 verbatim
noncomputable section


-- @@ L30-30 verbatim
namespace HilbertSpace

-- @@ L31-31 verbatim
open MeasureTheory

-- @@ L32-32 verbatim
open SchwartzMap InnerProductSpace


-- @@ L34-36 verbatim
/-- The continuous linear map including Schwartz functions into the hilbert space. -/
def schwartzIncl : 𝓢(ℝ, ℂ) →L[ℂ] HilbertSpace :=
  SchwartzMap.toLpCLM ℂ (E := ℝ) ℂ 2 MeasureTheory.volume


-- @@ L38-39 verbatim
lemma schwartzIncl_injective : Function.Injective schwartzIncl :=
  SchwartzMap.injective_toLp _ _


-- @@ L41-42 verbatim
lemma schwartzIncl_coe_ae (ψ : 𝓢(ℝ, ℂ)) :
    ψ.1 =ᶠ[ae volume] (schwartzIncl ψ) := (SchwartzMap.coeFn_toLp _ 2 volume).symm


-- @@ L44-55 verbatim
lemma schwartzIncl_inner (ψ1 ψ2 : 𝓢(ℝ, ℂ)) :
    ⟪schwartzIncl ψ1, schwartzIncl ψ2⟫_ℂ = ∫ x : ℝ, starRingEnd ℂ (ψ1 x) * ψ2 x := by
  apply MeasureTheory.integral_congr_ae
  have h1 : ψ1.1 =ᶠ[ae volume] (schwartzIncl ψ1) :=
    schwartzIncl_coe_ae ψ1
  have h2 : ψ2.1 =ᶠ[ae volume] (schwartzIncl ψ2) :=
    schwartzIncl_coe_ae ψ2
  filter_upwards [h1, h2] with _ h1 h2
  rw [← h1, ← h2]
  simp only [RCLike.inner_apply]
  rw [mul_comm]
  rfl


-- @@ L57-57 verbatim
end HilbertSpace

-- @@ L58-58 verbatim
end

-- @@ L59-59 verbatim
end OneDimension

-- @@ L60-60 verbatim
end QuantumMechanics
