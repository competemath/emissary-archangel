/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.Mathematics.KroneckerDelta.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Tensorial
public import Physlib.QuantumMechanics.Operators.AngularMomentum

-- @@ L11-49 verbatim
/-!

# Commutation relations

## i. Overview

In this module we compute the commutators for common operators acting on Schwartz maps on `Space d`.

Commutator lemmas come in three flavors:
  - 1. `a_commutation_b` lemmas are of the form `⁅a, b⁆ = (⋯)`.
  - 2. `a_comp_b_commute` and `a_comp_commute` lemmas are of the form `a ∘ b = b ∘ a`.
  - 3. `a_comp_b_eq` lemmas are of the form `a ∘ b = b ∘ a + (⋯)`.

## ii. Key results

- `position_commutation_momentum` : The canonical commutation relations.
- `angularMomentum_commutation_position` : The position operator transforms as a vector under
    infinitessimal rotations.
- `angularMomentum_commutation_radiusRegPow` : Functions of `‖x‖²` commute with the angular momenta.
- `angularMomentum_commutation_momentum` : The momentum operator transforms as a vector under
    infinitessimal rotations.
- `angularMomentum_commutation_angularMomentum` : Angular momenta generate an `𝔰𝔬(d)` algebra.
- `angularMomentumSqr_commutation_angularMomentum` : `𝐋²` is a quadratic Casimir of `𝔰𝔬(d)`.

## iii. Table of contents

- A. General
- B. Commutators
  - B.1. Position / position
  - B.2. Momentum / momentum
  - B.3. Position / momentum
  - B.4. Angular momentum / position
  - B.5. Angular momentum / momentum
  - B.6. Angular momentum / angular momentum

## iv. References

* None.
-/


-- @@ L51-51 verbatim
@[expose] public section


-- @@ L53-53 verbatim
namespace QuantumMechanics

-- @@ L54-54 verbatim
noncomputable section

-- @@ L55-55 verbatim
open Complex Constants

-- @@ L56-56 verbatim
open KroneckerDelta

-- @@ L57-57 verbatim
open Bracket

-- @@ L58-58 verbatim
open SchwartzMap ContinuousLinearMap


-- @@ L60-60 verbatim
variable {d : ℕ} (i j k l : Fin d) (ε : ℝˣ) (s t : ℝ)


-- @@ L62-66 verbatim
/-!

## A. General

-/


-- @@ L68-71 verbatim
lemma leibniz_lie (A B C : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) :
    ⁅A ∘L B, C⁆ = A ∘L ⁅B, C⁆ + ⁅A, C⁆ ∘L B := by
  dsimp only [Bracket.bracket]
  simp only [ContinuousLinearMap.mul_def, comp_assoc, comp_sub, sub_comp, sub_add_sub_cancel]


-- @@ L73-76 verbatim
lemma lie_leibniz (A B C : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) :
    ⁅A, B ∘L C⁆ = B ∘L ⁅A, C⁆ + ⁅A, B⁆ ∘L C := by
  dsimp only [Bracket.bracket]
  simp only [ContinuousLinearMap.mul_def, comp_assoc, comp_sub, sub_comp, sub_add_sub_cancel']


-- @@ L78-81 verbatim
lemma comp_eq_comp_add_commute (A B : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) :
    A ∘L B = B ∘L A + ⁅A, B⁆ := by
  dsimp only [Bracket.bracket]
  simp only [ContinuousLinearMap.mul_def, add_sub_cancel]


-- @@ L83-86 verbatim
lemma comp_eq_comp_sub_commute (A B : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) :
    A ∘L B = B ∘L A - ⁅B, A⁆ := by
  dsimp only [Bracket.bracket]
  simp only [ContinuousLinearMap.mul_def, sub_sub_cancel]


-- @@ L88-92 verbatim
/-!

## B. Commutators

-/


-- @@ L94-98 verbatim
/-!

### B.1. Position / position

-/


-- @@ L100-104 expanded
/-- Position operators commute: `[xᵢ, xⱼ] = 0`. -/
@[simp]
lemma position_commutation_position : ⁅positionCLM i, positionCLM j⁆ = 0 :=
  by
  ext
  simp [bracket, ← mul_assoc, mul_comm]


-- @@ L106-107 expanded
lemma position_comp_commute : positionCLM i ∘L positionCLM j = positionCLM j ∘L positionCLM i := by
  rw [comp_eq_comp_add_commute, position_commutation_position, add_zero]


-- @@ L109-112 expanded
@[simp]
lemma position_commutation_radiusRegPow : ⁅positionCLM i, (radiusRegPowCLM (d := d)) ε s⁆ = 0 :=
  by
  ext
  simp [bracket, ← mul_assoc, mul_comm]


-- @@ L114-115 expanded
lemma position_comp_radiusRegPow_commute :
    positionCLM i ∘L radiusRegPowCLM ε s = radiusRegPowCLM ε s ∘L positionCLM i := by
  rw [comp_eq_comp_add_commute, position_commutation_radiusRegPow, add_zero]


-- @@ L117-119 expanded
@[simp]
lemma radiusRegPow_commutation_radiusRegPow :
    ⁅(radiusRegPowCLM (d := d)) ε s, (radiusRegPowCLM (d := d)) ε t⁆ = 0 := by
  simp [bracket, mul_def, radiusRegPowCLM_comp_eq, add_comm]


-- @@ L121-125 verbatim
/-!

### B.2. Momentum / momentum

-/


-- @@ L127-134 expanded
/-- Momentum operators commute: `[pᵢ, pⱼ] = 0`. -/
@[simp]
lemma momentum_commutation_momentum : ⁅momentumCLM i, momentumCLM j⁆ = 0 :=
  by
  ext ψ x
  have hdiff (k : Fin d) : Differentiable ℝ ((deriv k) ψ) :=
    Space.deriv_differentiable (ψ.smooth 2) k
  show momentumCLM i (momentumCLM j ψ) x - momentumCLM j (momentumCLM i ψ) x = 0
  simp only [momentumCLM_apply_fun, Space.deriv_const_smul _ (hdiff _),
    Space.deriv_commute _ (ψ.smooth 2), sub_self]


-- @@ L136-137 expanded
lemma momentum_comp_commute : momentumCLM i ∘L momentumCLM j = momentumCLM j ∘L momentumCLM i := by
  rw [comp_eq_comp_add_commute, momentum_commutation_momentum, add_zero]


-- @@ L139-139 verbatim
attribute [local instance 100] LieRing.ofAssociativeRing


-- @@ L141-143 expanded
@[simp]
lemma momentumSqr_commutation_momentum : ⁅momentumCLM (d := d) ⬝ᵥ momentumCLM, momentumCLM i⁆ = 0 :=
  by simp [dotProduct, mul_def, sum_lie, leibniz_lie]


-- @@ L145-146 expanded
lemma momentumSqr_comp_momentum_commute :
    (momentumCLM ⬝ᵥ momentumCLM) ∘L momentumCLM i = momentumCLM i ∘L (momentumCLM ⬝ᵥ momentumCLM) :=
  by rw [comp_eq_comp_add_commute, momentumSqr_commutation_momentum, add_zero]


-- @@ L148-152 verbatim
/-!

### B.3. Position / momentum

-/


-- @@ L154-166 expanded
/-- The canonical commutation relations: `[xᵢ, pⱼ] = iℏ δᵢⱼ𝟙`. -/
lemma position_commutation_momentum :
    ⁅positionCLM i, momentumCLM j⁆ =
      (I * ℏ) • kroneckerDelta i j • ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ) :=
  by
  ext ψ x
  show positionCLM i (momentumCLM j ψ) x - momentumCLM j (positionCLM i ψ) x = _
  trans (I * ℏ) * (-x i * (deriv j) ψ x + (deriv j) ((fun x : Space d ↦ x i) • ⇑ψ) x)
  · simp only [positionCLM_apply, momentumCLM_apply, positionCLM_apply_fun]
    ring
  rw [Space.deriv_smul (by fun_prop) (by fun_prop)]
  rw [Space.deriv_component]
  rcases eq_or_ne i j with (rfl | hne)
  · simp
  · simp [eq_zero_of_ne hne, hne.symm]


-- @@ L168-170 expanded
lemma momentum_comp_position_eq :
    momentumCLM j ∘L positionCLM i =
      positionCLM i ∘L momentumCLM j -
        (I * ℏ) • kroneckerDelta i j • ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ) :=
  by rw [comp_eq_comp_sub_commute, position_commutation_momentum]


-- @@ L172-175 expanded
lemma position_position_commutation_momentum :
    ⁅positionCLM i ∘L positionCLM j, momentumCLM k⁆ =
      (I * ℏ) • (kroneckerDelta i k • positionCLM j + kroneckerDelta j k • positionCLM i) :=
  by
  simp only [leibniz_lie, position_commutation_momentum, comp_smul, smul_comp, comp_id, id_comp,
    smul_add, add_comm]


-- @@ L177-180 expanded
lemma position_commutation_momentum_momentum :
    ⁅positionCLM i, momentumCLM j ∘L momentumCLM k⁆ =
      (I * ℏ) • (kroneckerDelta i k • momentumCLM j + kroneckerDelta i j • momentumCLM k) :=
  by
  simp only [lie_leibniz, position_commutation_momentum, comp_smul, smul_comp, comp_id, id_comp,
    smul_add]


-- @@ L182-184 expanded
lemma position_commutation_momentumSqr :
    ⁅positionCLM i, momentumCLM ⬝ᵥ momentumCLM⁆ = (2 * I * ℏ) • momentumCLM i := by
  simp only [dotProduct, mul_def, lie_sum, lie_leibniz, position_commutation_momentum, comp_smul,
    smul_comp, comp_id, id_comp, ← two_smul ℂ, smul_smul, mul_assoc, ← Finset.smul_sum, sum_smul]


-- @@ L186-205 expanded
lemma radiusRegPow_commutation_momentum :
    ⁅(radiusRegPowCLM (d := d)) ε s, momentumCLM i⁆ =
      (s * I * ℏ) • radiusRegPowCLM ε (s - 2) ∘L positionCLM i :=
  by
  ext ψ x
  have hne := Ne.symm (ne_of_lt <| Space.norm_sq_add_unit_sq_pos ε x)
  have hdiff1 : DifferentiableAt ℝ (fun x => (‖x‖ ^ 2 + ↑ε ^ 2) ^ (s / 2)) x :=
    by
    refine DifferentiableAt.rpow_const ?_ (Or.intro_left _ hne)
    exact Differentiable.differentiableAt (by fun_prop)
  have hdiff2 := Real.differentiableAt_rpow_const_of_ne (s / 2) hne
  have hdiff3 : DifferentiableAt ℝ (fun x ↦ ‖x‖ ^ 2 + ε ^ 2) x :=
    Differentiable.differentiableAt (by fun_prop)
  show
    radiusRegPowCLM ε s (momentumCLM i ψ) x - momentumCLM i (radiusRegPowCLM ε s ψ) x =
      (s * I * ℏ) * radiusRegPowCLM ε (s - 2) (positionCLM i ψ) x
  simp only [momentumCLM_apply, positionCLM_apply, radiusRegPowCLM_apply_fun]
  rw [← Pi.smul_def', Space.deriv_smul hdiff1 (by fun_prop)]
  suffices
    (deriv i) (fun x ↦ (‖x‖ ^ 2 + ε ^ 2) ^ (s / 2)) x = s * (‖x‖ ^ 2 + ε ^ 2) ^ (s / 2 - 1) * x i
    by
    simp only [this, real_smul, ofReal_mul]
    ring_nf
  change (deriv i) ((fun r ↦ r ^ (s / 2)) ∘ (fun x ↦ ‖x‖ ^ 2 + ε ^ 2)) x = _
  rw [Space.deriv_eq, fderiv_comp x hdiff2 hdiff3, fderiv_add_const, fderiv_norm_sq_apply]
  simp [Real.deriv_rpow_const, mul_comm, ← mul_assoc, mul_div_cancel₀ s (NeZero.ne' 2).symm]


-- @@ L207-209 expanded
lemma momentum_comp_radiusRegPow_eq :
    momentumCLM i ∘L radiusRegPowCLM ε s =
      radiusRegPowCLM ε s ∘L momentumCLM i -
        (s * I * ℏ) • radiusRegPowCLM ε (s - 2) ∘L positionCLM i :=
  by rw [comp_eq_comp_sub_commute, radiusRegPow_commutation_momentum]


-- @@ L211-236 expanded
lemma radiusRegPow_commutation_momentumSqr :
    ⁅(radiusRegPowCLM (d := d)) ε s, momentumCLM (d := d) ⬝ᵥ momentumCLM⁆ =
      (2 * s * I * ℏ) • radiusRegPowCLM ε (s - 2) ∘L (positionCLM ⬝ᵥ momentumCLM) +
          (s * (d + s - 2) * ℏ ^ 2) • radiusRegPowCLM ε (s - 2) -
        (ε ^ 2 * s * (s - 2) * ℏ ^ 2) • radiusRegPowCLM ε (s - 4) :=
  by
  calc
    _ =
        (s * I * ℏ) •
          ∑ i,
            ((momentumCLM i ∘L radiusRegPowCLM ε (s - 2)) ∘L positionCLM i +
              radiusRegPowCLM ε (s - 2) ∘L positionCLM i ∘L momentumCLM i) :=
      by
      simp [dotProduct, mul_def, lie_sum, lie_leibniz, radiusRegPow_commutation_momentum,
        ← smul_add, ← Finset.smul_sum, comp_assoc]
    _ =
        (s * I * ℏ) •
          ∑ i,
            (radiusRegPowCLM ε (s - 2) ∘L momentumCLM i ∘L positionCLM i +
                radiusRegPowCLM ε (s - 2) ∘L positionCLM i ∘L momentumCLM i -
              (↑(s - 2) * I * ℏ) • radiusRegPowCLM ε (s - 4) ∘L positionCLM i ∘L positionCLM i) :=
      by
      simp only [momentum_comp_radiusRegPow_eq, sub_comp, smul_comp, sub_add_eq_add_sub, comp_assoc]
      ring_nf
    _ =
        (s * I * ℏ) •
          ∑ i,
            ((2 : ℂ) • radiusRegPowCLM ε (s - 2) ∘L positionCLM i ∘L momentumCLM i -
                (I * ℏ) • radiusRegPowCLM ε (s - 2) -
              ((s - 2) * I * ℏ) • radiusRegPowCLM ε (s - 4) ∘L positionCLM i ∘L positionCLM i) :=
      by simp [momentum_comp_position_eq, sub_add_eq_add_sub, ← two_smul ℂ]
    _ =
        (s * I * ℏ) •
          ((2 : ℂ) • radiusRegPowCLM ε (s - 2) ∘L (positionCLM ⬝ᵥ momentumCLM) -
              (d * I * ℏ) • radiusRegPowCLM ε (s - 2) -
            ((s - 2) * I * ℏ) • radiusRegPowCLM ε (s - 4) ∘L ∑ i, positionCLM i ∘L positionCLM i) :=
      by
      simp [Finset.sum_sub_distrib, ← Finset.smul_sum, ← comp_finsetSum, ← Nat.cast_smul_eq_nsmul ℂ,
        smul_smul, dotProduct, mul_def, mul_assoc]
    _ =
        (2 * s * I * ℏ) • radiusRegPowCLM ε (s - 2) ∘L (positionCLM ⬝ᵥ momentumCLM) +
            (s * (d + s - 2) * ℏ ^ 2) • radiusRegPowCLM ε (s - 2) -
          (ε ^ 2 * s * (s - 2) * ℏ ^ 2) • radiusRegPowCLM ε (s - 4) :=
      by
      simp_rw [positionSqCLM_eq ε, comp_sub, comp_smul, comp_id, radiusRegPowCLM_comp_eq]
      simp only [smul_sub, smul_smul, ← Complex.coe_smul, ofReal_mul, ofReal_add, ofReal_sub,
        ofReal_pow, ofReal_ofNat, ofReal_natCast]
      ring_nf
      simp_rw [← sub_add, sub_sub, ← add_smul, I_sq, sub_eq_add_neg, ← neg_smul]
      ring_nf


-- @@ L238-242 verbatim
/-!

### B.4. Angular momentum / position

-/


-- @@ L244-249 expanded
lemma angularMomentum_commutation_position :
    ⁅angularMomentumOperator i j, positionCLM k⁆ =
      (I * ℏ) • (kroneckerDelta i k • positionCLM j - kroneckerDelta j k • positionCLM i) :=
  by
  trans
    positionCLM i ∘L ⁅momentumCLM j, positionCLM k⁆ -
      positionCLM j ∘L ⁅momentumCLM i, positionCLM k⁆
  · simp [angularMomentumOperator, leibniz_lie]
  simp only [← lie_skew (momentumCLM _), comp_neg, sub_neg_eq_add, add_comm, ← sub_eq_add_neg,
    position_commutation_momentum, comp_smul, comp_id, smul_sub, symm k _]


-- @@ L251-256 expanded
@[simp]
lemma angularMomentum_commutation_radiusRegPow :
    ⁅angularMomentumOperator i j, (radiusRegPowCLM (d := d)) ε s⁆ = 0 :=
  by
  trans
    positionCLM i ∘L ⁅momentumCLM j, radiusRegPowCLM ε s⁆ -
      positionCLM j ∘L ⁅momentumCLM i, radiusRegPowCLM ε s⁆
  · simp [angularMomentumOperator, leibniz_lie]
  simp [← lie_skew (momentumCLM _), radiusRegPow_commutation_momentum, comp_neg,
    ← position_comp_radiusRegPow_commute, ← comp_assoc, position_comp_commute]


-- @@ L258-259 expanded
lemma angularMomentum_comp_radiusRegPow_commute :
    angularMomentumOperator i j ∘L radiusRegPowCLM ε s =
      radiusRegPowCLM ε s ∘L angularMomentumOperator i j :=
  by rw [comp_eq_comp_add_commute, angularMomentum_commutation_radiusRegPow, add_zero]


-- @@ L261-263 expanded
@[simp]
lemma angularMomentumSqr_commutation_radiusRegPow :
    ⁅angularMomentumOperatorSqr (d := d), (radiusRegPowCLM (d := d)) ε s⁆ = 0 := by
  simp [angularMomentumOperatorSqr, sum_lie, leibniz_lie]


-- @@ L265-266 expanded
lemma angularMomentumSqr_comp_radiusRegPow_commute :
    angularMomentumOperatorSqr ∘L (radiusRegPowCLM (d := d)) ε s =
      radiusRegPowCLM ε s ∘L angularMomentumOperatorSqr :=
  by rw [comp_eq_comp_add_commute, angularMomentumSqr_commutation_radiusRegPow, add_zero]


-- @@ L268-272 verbatim
/-!

### B.5. Angular momentum / momentum

-/


-- @@ L274-278 expanded
lemma angularMomentum_commutation_momentum :
    ⁅angularMomentumOperator i j, momentumCLM k⁆ =
      (I * ℏ) • (kroneckerDelta i k • momentumCLM j - kroneckerDelta j k • momentumCLM i) :=
  by
  trans
    ⁅positionCLM i, momentumCLM k⁆ ∘L momentumCLM j -
      ⁅positionCLM j, momentumCLM k⁆ ∘L momentumCLM i
  · simp [angularMomentumOperator, leibniz_lie]
  simp only [position_commutation_momentum, smul_comp, id_comp, smul_sub]


-- @@ L280-282 expanded
lemma momentum_comp_angularMomentum_eq :
    momentumCLM k ∘L angularMomentumOperator i j =
      angularMomentumOperator i j ∘L momentumCLM k -
        (I * ℏ) • (kroneckerDelta i k • momentumCLM j - kroneckerDelta j k • momentumCLM i) :=
  by rw [comp_eq_comp_sub_commute, angularMomentum_commutation_momentum]


-- @@ L284-288 expanded
@[simp]
lemma angularMomentum_commutation_momentumSqr :
    ⁅angularMomentumOperator i j, momentumCLM (d := d) ⬝ᵥ momentumCLM⁆ = 0 := by
  simp only [dotProduct, mul_def, lie_sum, lie_leibniz, angularMomentum_commutation_momentum,
    comp_smul, comp_sub, smul_comp, sub_comp, ← smul_add, ← Finset.smul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, sum_smul, sub_add_sub_cancel, sub_self, smul_zero]


-- @@ L290-291 expanded
lemma momentumSqr_comp_angularMomentum_commute :
    (momentumCLM ⬝ᵥ momentumCLM) ∘L angularMomentumOperator i j =
      angularMomentumOperator i j ∘L (momentumCLM ⬝ᵥ momentumCLM) :=
  by rw [comp_eq_comp_sub_commute, angularMomentum_commutation_momentumSqr, sub_zero]


-- @@ L293-295 expanded
@[simp]
lemma angularMomentumSqr_commutation_momentumSqr :
    ⁅angularMomentumOperatorSqr (d := d), momentumCLM (d := d) ⬝ᵥ momentumCLM⁆ = 0 := by
  simp [angularMomentumOperatorSqr, sum_lie, leibniz_lie]


-- @@ L297-301 verbatim
/-!

### B.6. Angular momentum / angular momentum

-/


-- @@ L303-313 expanded
lemma angularMomentum_commutation_angularMomentum :
    ⁅angularMomentumOperator i j, angularMomentumOperator k l⁆ =
      (I * ℏ) •
        (kroneckerDelta i k • angularMomentumOperator j l -
              kroneckerDelta i l • angularMomentumOperator j k -
            kroneckerDelta j k • angularMomentumOperator i l +
          kroneckerDelta j l • angularMomentumOperator i k) :=
  by
  nth_rw 2 [angularMomentumOperator]
  simp only [angularMomentum_commutation_position, angularMomentum_commutation_momentum, lie_sub,
    lie_leibniz, comp_smul, smul_comp, comp_sub, sub_comp, ← smul_add, ← smul_sub]
  dsimp [angularMomentumOperator]
  ext
  simp only [nsmul_eq_mul, smul_apply, sub_apply, add_apply, mul_apply_eq_comp, comp_apply,
    _root_.natCast_apply, positionCLM_apply, momentumCLM_apply, neg_mul, mul_neg, smul_neg,
    sub_neg_eq_add, smul_eq_mul, smul_add]
  ring


-- @@ L315-322 expanded
@[simp]
lemma angularMomentumSqr_commutation_angularMomentum :
    ⁅angularMomentumOperatorSqr (d := d), angularMomentumOperator i j⁆ = 0 :=
  by
  simp only [angularMomentumOperatorSqr, smul_lie, sum_lie, leibniz_lie, ← smul_add, comp_smul,
    comp_add, comp_sub, smul_comp, add_comp, sub_comp, angularMomentum_commutation_angularMomentum,
    angularMomentumOperator_antisymm _ i, angularMomentumOperator_antisymm j _, symm _ i, symm _ j,
    sum_smul, ← Finset.smul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  abel_nf
  simp [smul_zero]


-- @@ L324-324 verbatim
end

-- @@ L325-325 verbatim
end QuantumMechanics
