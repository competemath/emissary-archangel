/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.Operators.Position
public import Physlib.QuantumMechanics.Operators.Momentum

-- @@ L10-42 verbatim
/-!

# Angular momentum operator

## i. Overview

In this module we introduce several angular momentum operators for quantum mechanics on `Space d`.

## ii. Key results

Definitions:
- `angularMomentumOperator` : (components of) the angular momentum operator acting on Schwartz maps
    `𝓢(Space d, ℂ)` as `𝐱ᵢ∘𝐩ⱼ - 𝐱ⱼ∘𝐩ᵢ`.
- `angularMomentumOperatorSqr` : the operator acting on Schwartz maps `𝓢(Space d, ℂ)`
    as `½ ∑ᵢⱼ 𝐋ᵢⱼ∘𝐋ᵢⱼ`.
- `angularMomentumOperator2D` : the (pseudo)scalar angular momentum operator for `d = 2`.
- `angularMomentumOperator3D` : the (pseudo)vector angular momentum operator for `d = 3`.

Notation:
- `𝐋` for `angularMomentumOperator`
- `𝐋²` for `angularMomentumOperatorSqr`

## iii. Table of contents

- A. Angular momentum operator
  - A.1 Antisymmetry
- B. Angular momentum squared operator
- C. Special cases in low dimensions

## iv. References

* None.
-/


-- @@ L44-44 verbatim
@[expose] public section


-- @@ L46-46 verbatim
namespace QuantumMechanics

-- @@ L47-47 verbatim
noncomputable section

-- @@ L48-48 verbatim
open Constants

-- @@ L49-49 verbatim
open ContDiff SchwartzMap


-- @@ L51-55 verbatim
/-!

## A. Angular momentum operator

-/


-- @@ L57-60 expanded
/-- Component `i j` of the angular momentum operator is the continuous linear map
from `𝓢(Space d, ℂ)` to itself defined by `𝐋ᵢⱼ ≔ 𝐱ᵢ∘𝐩ⱼ - 𝐱ⱼ∘𝐩ᵢ`. -/
def angularMomentumOperator {d : ℕ} (i j : Fin d) : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  positionCLM i ∘L momentumCLM j - positionCLM j ∘L momentumCLM i


-- @@ L62-63 verbatim
@[inherit_doc angularMomentumOperator]
notation "𝐋" => angularMomentumOperator


-- @@ L65-66 verbatim
@[inherit_doc angularMomentumOperator]
notation "𝐋[" d' "]" => angularMomentumOperator (d := d')


-- @@ L68-69 expanded
lemma angularMomentumOperator_apply_fun {d : ℕ} (i j : Fin d) (ψ : 𝓢(Space d, ℂ)) :
    angularMomentumOperator i j ψ =
      positionCLM i (momentumCLM j ψ) - positionCLM j (momentumCLM i ψ) :=
  rfl


-- @@ L71-72 expanded
lemma angularMomentumOperator_apply {d : ℕ} (i j : Fin d) (ψ : 𝓢(Space d, ℂ)) (x : Space d) :
    angularMomentumOperator i j ψ x =
      positionCLM i (momentumCLM j ψ) x - positionCLM j (momentumCLM i ψ) x :=
  rfl


-- @@ L74-78 verbatim
/-!

### A.1 Antisymmetry

-/


-- @@ L80-82 expanded
/-- The angular momentum operator is antisymmetric, `𝐋ᵢⱼ = -𝐋ⱼᵢ` -/
lemma angularMomentumOperator_antisymm {d : ℕ} (i j : Fin d) :
    angularMomentumOperator i j = -angularMomentumOperator j i :=
  Eq.symm (neg_sub _ _)


-- @@ L84-85 expanded
/-- Angular momentum operator components with repeated index vanish, `𝐋ᵢᵢ = 0`. -/
lemma angularMomentumOperator_eq_zero {d : ℕ} (i : Fin d) : angularMomentumOperator i i = 0 :=
  sub_self _


-- @@ L87-91 verbatim
/-!

## B. Angular momentum squared operator

-/


-- @@ L93-95 expanded
/-- The square of the angular momentum operator, `𝐋² ≔ ½ ∑ᵢⱼ 𝐋ᵢⱼ∘𝐋ᵢⱼ`. -/
def angularMomentumOperatorSqr {d : ℕ} : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  (2 : ℂ)⁻¹ • ∑ i, ∑ j, angularMomentumOperator i j ∘L angularMomentumOperator i j


-- @@ L97-98 verbatim
@[inherit_doc angularMomentumOperatorSqr]
notation "𝐋²" => angularMomentumOperatorSqr


-- @@ L100-101 verbatim
@[inherit_doc angularMomentumOperatorSqr]
notation "𝐋²[" d' "]" => angularMomentumOperatorSqr (d := d')


-- @@ L103-106 expanded
lemma angularMomentumOperatorSqr_apply_fun {d : ℕ} (ψ : 𝓢(Space d, ℂ)) :
    angularMomentumOperatorSqr ψ =
      (2 : ℂ)⁻¹ • ∑ i, ∑ j, angularMomentumOperator i j (angularMomentumOperator i j ψ) :=
  by
  simp only [angularMomentumOperatorSqr, FunLike.coe_sum, FunLike.coe_smul,
    ContinuousLinearMap.coe_comp, Finset.sum_apply, Pi.smul_apply, Function.comp_apply]


-- @@ L108-110 expanded
lemma angularMomentumOperatorSqr_apply {d : ℕ} (ψ : 𝓢(Space d, ℂ)) (x : Space d) :
    angularMomentumOperatorSqr ψ x =
      (2 : ℂ)⁻¹ * ∑ i, ∑ j, angularMomentumOperator i j (angularMomentumOperator i j ψ) x :=
  by simp only [angularMomentumOperatorSqr_apply_fun, smul_apply, sum_apply, smul_eq_mul]


-- @@ L112-125 verbatim
/-!

## C. Special cases in low dimensions

  • d = 1 : The angular momentum operator is trivial.

  • d = 2 : The angular momentum operator has only one independent component, 𝐋₀₁, which may
            be thought of as a (pseudo)scalar operator.

  • d = 3 : The angular momentum operator has three independent components, 𝐋₀₁, 𝐋₁₂ and 𝐋₂₀.
            Dualizing using the Levi-Civita symbol produces the familiar (pseudo)vector angular
            momentum operator with components 𝐋₀ = 𝐋₁₂, 𝐋₁ = 𝐋₂₀ and 𝐋₂ = 𝐋₀₁.

-/


-- @@ L127-130 expanded
/-- In one dimension the angular momentum operator is trivial. -/
lemma angularMomentumOperator1D_trivial : angularMomentumOperator (d := 1) = 0 :=
  by
  ext i j
  simp [Subsingleton.elim i j, angularMomentumOperator_eq_zero]


-- @@ L132-133 expanded
/-- The angular momentum (pseudo)scalar operator in two dimensions, `𝐋 ≔ 𝐋₀₁`. -/
def angularMomentumOperator2D : 𝓢(Space 2, ℂ) →L[ℂ] 𝓢(Space 2, ℂ) :=
  angularMomentumOperator 0 1


-- @@ L135-140 expanded
/-- The angular momentum (pseudo)vector operator in three dimension, `𝐋ᵢ ≔ ½ ∑ⱼₖ εᵢⱼₖ 𝐋ⱼₖ`. -/
def angularMomentumOperator3D (i : Fin 3) : 𝓢(Space 3, ℂ) →L[ℂ] 𝓢(Space 3, ℂ) :=
  match i with
  | 0 => angularMomentumOperator 1 2
  | 1 => angularMomentumOperator 2 0
  | 2 => angularMomentumOperator 0 1


-- @@ L142-142 verbatim
end

-- @@ L143-143 verbatim
end QuantumMechanics
