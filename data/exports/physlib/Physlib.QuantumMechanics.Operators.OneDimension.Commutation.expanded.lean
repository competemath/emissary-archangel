/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QuantumMechanics.Operators.OneDimension.Position
public import Physlib.QuantumMechanics.Operators.OneDimension.Momentum

-- @@ L10-16 verbatim
/-!

# Commutation relations

The commutation relations between different operators.

-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
namespace QuantumMechanics


-- @@ L22-22 verbatim
namespace OneDimension

-- @@ L23-23 verbatim
noncomputable section

-- @@ L24-24 verbatim
open Constants

-- @@ L25-25 verbatim
open _root_.QuantumMechanics.OneDimension.HilbertSpace

-- @@ L26-26 verbatim
open SchwartzMap


-- @@ L28-32 verbatim
/-!

## Commutation relation between position and momentum operators

-/


-- @@ L34-45 verbatim
lemma positionOperatorSchwartz_commutation_momentumOperatorSchwartz
    (ψ : 𝓢(ℝ, ℂ)) : positionOperatorSchwartz (momentumOperatorSchwartz ψ)
    - momentumOperatorSchwartz (positionOperatorSchwartz ψ)
    = (Complex.I * ℏ) • ψ := by
  ext x
  simp [momentumOperatorSchwartz_apply, positionOperatorSchwartz_apply,
    positionOperatorSchwartz_apply_fun]
  have h1 : deriv Complex.ofReal x = 1 := Complex.ofRealCLM.deriv.trans (by simp)
  rw [deriv_fun_mul, h1]
  ring
  · exact Complex.ofRealCLM.differentiableAt
  · exact ψ.differentiableAt


-- @@ L47-51 verbatim
lemma positionOperatorSchwartz_momentumOperatorSchwartz_eq (ψ : 𝓢(ℝ, ℂ)) :
    positionOperatorSchwartz (momentumOperatorSchwartz ψ)
    = momentumOperatorSchwartz (positionOperatorSchwartz ψ)
    + (Complex.I * ℏ) • ψ :=
  sub_eq_iff_eq_add'.mp (positionOperatorSchwartz_commutation_momentumOperatorSchwartz ψ)


-- @@ L53-57 verbatim
lemma momentumOperatorSchwartz_positionOperatorSchwartz_eq (ψ : 𝓢(ℝ, ℂ)) :
    momentumOperatorSchwartz (positionOperatorSchwartz ψ)
    = positionOperatorSchwartz (momentumOperatorSchwartz ψ)
    - (Complex.I * ℏ) • ψ := by
  simp [← positionOperatorSchwartz_commutation_momentumOperatorSchwartz ψ]


-- @@ L59-59 verbatim
end

-- @@ L60-60 verbatim
end OneDimension

-- @@ L61-61 verbatim
end QuantumMechanics
