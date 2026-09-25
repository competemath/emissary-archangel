/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.Hydrogen.Basic
public import Physlib.QuantumMechanics.Operators.Commutation

-- @@ L10-24 verbatim
/-!

# Laplace-Runge-Lenz vector

In this file we define
- The (regularized) LRL vector operator for the quantum mechanical hydrogen atom,
  `𝐀(ε)ᵢ ≔ ½(𝐩ⱼ𝐋ᵢⱼ + 𝐋ᵢⱼ𝐩ⱼ) - mk·𝐫(ε)⁻¹𝐱ᵢ`.

The main results are
- The commutators `⁅𝐋ᵢⱼ, 𝐀(ε)ₖ⁆ = iℏ(δᵢₖ𝐀(ε)ⱼ - δⱼₖ𝐀(ε)ᵢ)` in `angularMomentum_commutation_lrl`
- The commutators `⁅𝐀(ε)ᵢ, 𝐀(ε)ⱼ⁆ = (-2iℏm·𝐇(ε) + iℏmkε²·𝐫(ε)⁻³))𝐋ᵢⱼ` in `lrl_commutation_lrl`
- The commutators `⁅𝐇(ε), 𝐀(ε)ᵢ⁆ = iℏε²(⋯)` in `hamiltonianReg_commutation_lrl`
- The relation `𝐀(ε)² = 2m 𝐇(ε)(𝐋² + ¼ℏ²(d-1)²) + m²k² + ε²(⋯)` in `lrlOperatorSqr_eq`

-/


-- @@ L26-26 verbatim
@[expose] public section


-- @@ L28-28 verbatim
namespace QuantumMechanics

-- @@ L29-29 verbatim
namespace HydrogenAtom

-- @@ L30-30 verbatim
noncomputable section

-- @@ L31-31 verbatim
open Complex Constants

-- @@ L32-32 verbatim
open KroneckerDelta

-- @@ L33-33 verbatim
open ContinuousLinearMap SchwartzMap


-- @@ L35-35 verbatim
variable (H : HydrogenAtom)


-- @@ L37-37 verbatim
attribute [local instance 100] LieRing.ofAssociativeRing


-- @@ L39-42 expanded
/-- The (regularized) Laplace-Runge-Lenz vector operator for the `d`-dimensional hydrogen atom,
  `𝐀(ε)ᵢ ≔ ½(𝐩ⱼ𝐋ᵢⱼ + 𝐋ᵢⱼ𝐩ⱼ) - mk·𝐫(ε)⁻¹𝐱ᵢ`. -/
def lrlOperator (ε : ℝˣ) (i : Fin H.d) : 𝓢(Space H.d, ℂ) →L[ℂ] 𝓢(Space H.d, ℂ) :=
  (2 : ℝ)⁻¹ •
      (momentumCLM ⬝ᵥ angularMomentumOperator i + angularMomentumOperator i ⬝ᵥ momentumCLM) -
    (H.m * H.k) • radiusRegPowCLM ε (-1) ∘L positionCLM i


-- @@ L44-67 expanded
/-- `𝐀(ε)ᵢ = 𝐱ᵢ𝐩² - (𝐱ⱼ𝐩ⱼ)𝐩ᵢ + ½iℏ(d-1)𝐩ᵢ - mk·𝐫(ε)⁻¹𝐱ᵢ` -/
lemma lrlOperator_eq (ε : ℝˣ) (i : Fin H.d) :
    H.lrlOperator ε i =
      positionCLM i ∘L (momentumCLM ⬝ᵥ momentumCLM) -
            (positionCLM ⬝ᵥ momentumCLM) ∘L momentumCLM i +
          (2⁻¹ * I * ℏ * (H.d - 1)) • momentumCLM i -
        (H.m * H.k) • radiusRegPowCLM ε (-1) ∘L positionCLM i :=
  by
  rw [lrlOperator, sub_left_inj] -- mk·r⁻¹x terms match exactly
    
  calc
    _ =
        (2 : ℝ)⁻¹ •
          ∑ j,
            ((momentumCLM j ∘L positionCLM i) ∘L momentumCLM j +
                positionCLM i ∘L momentumCLM j ∘L momentumCLM j -
              ((momentumCLM j ∘L positionCLM j) ∘L momentumCLM i +
                positionCLM j ∘L momentumCLM j ∘L momentumCLM i)) :=
      by
      simp_rw [dotProduct, mul_def, ← Finset.sum_add_distrib, angularMomentumOperator, comp_sub,
        sub_comp, comp_assoc, momentum_comp_commute, ← sub_sub, add_sub, sub_add_eq_add_sub]
    _ =
        (2 : ℂ)⁻¹ •
          ∑ j,
            ((2 : ℂ) • positionCLM i ∘L momentumCLM j ∘L momentumCLM j -
                (I * ℏ) • kroneckerDelta i j • momentumCLM j -
              ((2 : ℂ) • (positionCLM j ∘L momentumCLM j) ∘L momentumCLM i -
                (I * ℏ) • momentumCLM i)) :=
      by
      simp only [momentum_comp_position_eq, sub_comp, comp_assoc, smul_comp, id_comp, ofReal_ofNat,
        sub_add_eq_add_sub, eq_one_of_same, one_smul, ← Complex.coe_smul, ofReal_inv, two_smul]
    _ =
        (2 : ℂ)⁻¹ •
          ∑ j,
            ((2 : ℂ) • positionCLM i ∘L momentumCLM j ∘L momentumCLM j -
                  (2 : ℂ) • (positionCLM j ∘L momentumCLM j) ∘L momentumCLM i +
                (I * ℏ) • momentumCLM i -
              (I * ℏ) • kroneckerDelta i j • momentumCLM j) :=
      by simp_rw [sub_sub_sub_comm, sub_sub_eq_add_sub]
    _ =
        positionCLM i ∘L (momentumCLM ⬝ᵥ momentumCLM) -
            (positionCLM ⬝ᵥ momentumCLM) ∘L momentumCLM i +
          ((2⁻¹ * I * ℏ) • H.d • momentumCLM i - (2⁻¹ * I * ℏ) • momentumCLM i) :=
      by
      simp only [add_sub_assoc, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum,
        ← comp_finsetSum, ← finsetSum_comp, sum_smul, smul_add, smul_sub, smul_smul, mul_assoc]
      norm_num
      rfl
    _ =
        positionCLM i ∘L (momentumCLM ⬝ᵥ momentumCLM) -
            (positionCLM ⬝ᵥ momentumCLM) ∘L momentumCLM i +
          (2⁻¹ * I * ℏ * (H.d - 1)) • momentumCLM i :=
      by simp only [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← sub_smul, mul_sub, mul_one]


-- @@ L69-76 expanded
/-- `𝐀(ε)ᵢ = 𝐋ᵢⱼ𝐩ⱼ + ½iℏ(d-1)𝐩ᵢ - mk·𝐫(ε)⁻¹𝐱ᵢ` -/
lemma lrlOperator_eq' (ε : ℝˣ) (i : Fin H.d) :
    H.lrlOperator ε i =
      angularMomentumOperator i ⬝ᵥ momentumCLM + (2⁻¹ * I * ℏ * (H.d - 1)) • momentumCLM i -
        (H.m * H.k) • radiusRegPowCLM ε (-1) ∘L positionCLM i :=
  by
  rw [lrlOperator_eq, sub_left_inj, add_left_inj]
  symm
  trans
    ∑ j, positionCLM i ∘L momentumCLM j ∘L momentumCLM j -
      ∑ j, (positionCLM j ∘L momentumCLM j) ∘L momentumCLM i
  · simp [dotProduct, mul_def, angularMomentumOperator, comp_assoc, momentum_comp_commute]
  simp [← comp_finsetSum, ← finsetSum_comp, dotProduct, mul_def]


-- @@ L78-94 expanded
/-- `𝐀(ε)ᵢ = 𝐩ⱼ𝐋ᵢⱼ - ½iℏ(d-1)𝐩ᵢ - mk·𝐫(ε)⁻¹𝐱ᵢ` -/
lemma lrlOperator_eq'' (ε : ℝˣ) (i : Fin H.d) :
    H.lrlOperator ε i =
      momentumCLM ⬝ᵥ angularMomentumOperator i - (2⁻¹ * I * ℏ * (H.d - 1)) • momentumCLM i -
        (H.m * H.k) • radiusRegPowCLM ε (-1) ∘L positionCLM i :=
  by
  trans (2 : ℝ) • H.lrlOperator ε i - H.lrlOperator ε i
  · simp [two_smul]
  nth_rw 2 [lrlOperator_eq']
  simp only [lrlOperator, smul_add, smul_sub, smul_smul]
  ring_nf
  ext
  simp only [one_smul, one_div, sub_apply, add_apply, smul_apply, comp_apply, radiusRegPowCLM_apply,
    positionCLM_apply, real_smul, ofReal_mul, ofReal_ofNat, momentumCLM_apply, neg_mul, smul_eq_mul,
    mul_neg, sub_neg_eq_add]
  ring
    /-
    ## Angular momentum / LRL vector commutators
    -/


-- @@ L96-108 expanded
/-- A supporting piece of `angularMomentum_commutation_lrl`: how `𝐋ᵢⱼ` commutes with the
dot-product term `𝐋ₖ⬝ᵥ𝐩` appearing in `H.lrlOperator`'s expanded form (`lrlOperator_eq'`). -/
lemma angularMomentum_commutation_Ldot_p (i j k : Fin H.d) :
    ⁅(angularMomentumOperator (d := H.d)) i j, angularMomentumOperator k ⬝ᵥ momentumCLM⁆ =
      (I * ℏ) •
        (kroneckerDelta i k • (angularMomentumOperator j ⬝ᵥ momentumCLM) -
          kroneckerDelta j k • (angularMomentumOperator i ⬝ᵥ momentumCLM)) :=
  by
  simp only [dotProduct, mul_def, lie_sum, lie_leibniz, angularMomentum_commutation_angularMomentum,
    angularMomentum_commutation_momentum, comp_smul, smul_comp, comp_sub, sub_comp, add_comp]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum,
    KroneckerDelta.sum_smul]
  rw [angularMomentumOperator_antisymm k i, angularMomentumOperator_antisymm k j]
  simp only [neg_comp]
  module


-- @@ L110-118 expanded
/-- `⁅𝐋ᵢⱼ, 𝐀(ε)ₖ⁆ = iℏ(δᵢₖ𝐀(ε)ⱼ - δⱼₖ𝐀(ε)ᵢ)` -/
lemma angularMomentum_commutation_lrl (ε : ℝˣ) (i j k : Fin H.d) :
    ⁅angularMomentumOperator i j, H.lrlOperator ε k⁆ =
      (I * ℏ) • (kroneckerDelta i k • H.lrlOperator ε j - kroneckerDelta j k • H.lrlOperator ε i) :=
  by
  simp_rw [H.lrlOperator_eq']
  rw [lie_sub, lie_add, angularMomentum_commutation_Ldot_p H i j k, lie_smul,
    angularMomentum_commutation_momentum, lie_smul, lie_leibniz,
    angularMomentum_commutation_radiusRegPow, angularMomentum_commutation_position]
  simp only [zero_comp, comp_sub, comp_smul, smul_sub]
  module


-- @@ L120-126 expanded
/-- `⁅𝐋ᵢⱼ, 𝐀(ε)²⁆ = 0` -/
@[simp]
lemma angularMomentum_commutation_lrlSqr (ε : ℝˣ) (i j : Fin H.d) :
    ⁅angularMomentumOperator i j, H.lrlOperator ε ⬝ᵥ H.lrlOperator ε⁆ = 0 := by
  simp only [dotProduct, mul_def, lie_sum, lie_leibniz, H.angularMomentum_commutation_lrl,
    comp_smul, comp_sub, smul_comp, sub_comp, ← smul_add, ← Finset.smul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, sum_smul, sub_add_sub_cancel, sub_self, smul_zero]


-- @@ L128-147 expanded
/-- `⁅𝐋², 𝐀(ε)²⁆ = 0` -/
@[simp]
lemma angularMomentumSqr_commutation_lrlSqr (ε : ℝˣ) :
    ⁅angularMomentumOperatorSqr (d := H.d), H.lrlOperator ε ⬝ᵥ H.lrlOperator ε⁆ = 0 := by
  simp [angularMomentumOperatorSqr, sum_lie, leibniz_lie]
    /-
    
    ## LRL / LRL commutators
    
    To compute the commutator `⁅𝐀ᵢ(ε), 𝐀ⱼ(ε)⁆` we take the following approach:
    - Write `𝐀(ε)ᵢ = 𝐱ᵢ𝐩² - (𝐱ⱼ𝐩ⱼ)𝐩ᵢ + ½iℏ(d-1)𝐩ᵢ - mk·𝐫(ε)⁻¹𝐱ᵢ ≕ f1ᵢ - f2ᵢ + f3ᵢ - f4ᵢ`
    - Organize the sixteen terms which result from expanding `⁅f1ᵢ-f2ᵢ+f3ᵢ-f4ᵢ, f1ⱼ-f2ⱼ+f3ⱼ-f4ⱼ⁆`
      into four diagonal terms such as `⁅f1ᵢ, f1ⱼ⁆` and six off-diagonal pairs such as
      `⁅f1ᵢ, f3ⱼ⁆ + ⁅f3ᵢ, f1ⱼ⁆ = ⁅f1ᵢ, f3ⱼ⁆ - ⁅f1ⱼ, f3ᵢ⁆`.
    - Compute the diagonal commutators and off-diagonal pairs individually. Many vanish, and those
      that don't are all of the form `iℏ (⋯) 𝐋ᵢⱼ` (as they must to be antisymmetric in `i,j`).
    - Collect terms.
    
    -/


-- @@ L149-154 expanded
private lemma positionDotMomentum_commutation_position {d : ℕ} (i : Fin d) :
    ⁅positionCLM (d := d) ⬝ᵥ momentumCLM, positionCLM i⁆ = (-I * ℏ) • positionCLM i :=
  by
  trans ∑ j, positionCLM j ∘L ⁅momentumCLM j, positionCLM i⁆
  · simp [dotProduct, mul_def, sum_lie, leibniz_lie]
  simp_rw [← lie_skew (momentumCLM _), position_commutation_momentum, ← neg_smul, ← neg_mul,
    comp_smul, comp_id, ← Finset.smul_sum, sum_smul]


-- @@ L156-160 expanded
private lemma positionDotMomentum_commutation_momentum {d : ℕ} (i : Fin d) :
    ⁅positionCLM (d := d) ⬝ᵥ momentumCLM, momentumCLM i⁆ = (I * ℏ) • momentumCLM i :=
  by
  trans ∑ j, ⁅positionCLM j, momentumCLM i⁆ ∘L momentumCLM j
  · simp [dotProduct, mul_def, sum_lie, leibniz_lie]
  simp_rw [position_commutation_momentum, smul_comp, id_comp, ← Finset.smul_sum, symm _ i, sum_smul]


-- @@ L162-167 expanded
private lemma positionDotMomentum_commutation_momentumSqr (d : ℕ) :
    ⁅positionCLM (d := d) ⬝ᵥ momentumCLM, momentumCLM (d := d) ⬝ᵥ momentumCLM⁆ =
      (2 * I * ℏ) • (momentumCLM ⬝ᵥ momentumCLM) :=
  by
  trans ∑ i, ⁅positionCLM i, momentumCLM ⬝ᵥ momentumCLM⁆ ∘L momentumCLM i
  · rw [dotProduct]
    simp [mul_def, sum_lie, leibniz_lie, ← lie_skew (momentumCLM _) (momentumCLM ⬝ᵥ momentumCLM)]
  simp_rw [position_commutation_momentumSqr, smul_comp, ← Finset.smul_sum, dotProduct, mul_def]


-- @@ L169-176 expanded
private lemma positionDotMomentum_commutation_radiusRegPow (d : ℕ) (ε : ℝˣ) (s : ℝ) :
    ⁅positionCLM (d := d) ⬝ᵥ momentumCLM, (radiusRegPowCLM (d := d)) ε s⁆ =
      (-s * I * ℏ) • (radiusRegPowCLM ε s - ε.1 ^ 2 • radiusRegPowCLM ε (s - 2)) :=
  by
  calc
    _ = ∑ i, positionCLM i ∘L ⁅momentumCLM i, radiusRegPowCLM ε s⁆ := by
      simp [dotProduct, mul_def, sum_lie, leibniz_lie]
    _ = (-s * I * ℏ) • (∑ i, positionCLM i ∘L positionCLM i) ∘L radiusRegPowCLM ε (s - 2) := by
      simp [← lie_skew (momentumCLM _), radiusRegPow_commutation_momentum, Finset.smul_sum,
        position_comp_radiusRegPow_commute, finsetSum_comp, comp_assoc]
    _ = (-s * I * ℏ) • (radiusRegPowCLM ε s - ε.1 ^ 2 • radiusRegPowCLM ε (s - 2)) := by
      simp [positionSqCLM_eq ε]


-- @@ L178-188 expanded
private lemma positionCompMomentumSqr_comm {d : ℕ} (i j : Fin d) :
    ⁅positionCLM i ∘L (momentumCLM ⬝ᵥ momentumCLM), positionCLM j ∘L (momentumCLM ⬝ᵥ momentumCLM)⁆ =
      (-2 * I * ℏ) • (momentumCLM ⬝ᵥ momentumCLM) ∘L angularMomentumOperator i j :=
  by
  calc
    _ =
        (positionCLM j ∘L ⁅positionCLM i, momentumCLM (d := d) ⬝ᵥ momentumCLM⁆ +
            positionCLM i ∘L ⁅momentumCLM (d := d) ⬝ᵥ momentumCLM, positionCLM j⁆) ∘L
          (momentumCLM ⬝ᵥ momentumCLM) :=
      by simp [lie_leibniz, leibniz_lie, comp_assoc]
    _ = (2 * I * ℏ) • angularMomentumOperator j i ∘L (momentumCLM ⬝ᵥ momentumCLM) := by
      simp_rw [← lie_skew (momentumCLM ⬝ᵥ momentumCLM) _, position_commutation_momentumSqr,
        comp_neg, comp_smul, ← sub_eq_add_neg, ← smul_sub, smul_comp, angularMomentumOperator]
    _ = (-2 * I * ℏ) • (momentumCLM ⬝ᵥ momentumCLM) ∘L angularMomentumOperator i j := by
      rw [angularMomentumOperator_antisymm j i, neg_comp, smul_neg, ← neg_smul, ← neg_mul, ←
        neg_mul, momentumSqr_comp_angularMomentum_commute]


-- @@ L190-210 expanded
private lemma positionCompMomentumSqr_comm_positionDotMomentumCompMomentum_add {d : ℕ}
    (i j : Fin d) :
    ⁅positionCLM i ∘L (momentumCLM ⬝ᵥ momentumCLM), (positionCLM ⬝ᵥ momentumCLM) ∘L momentumCLM j⁆ +
        ⁅(positionCLM ⬝ᵥ momentumCLM) ∘L momentumCLM i,
          positionCLM j ∘L (momentumCLM ⬝ᵥ momentumCLM)⁆ =
      (-I * ℏ) • (momentumCLM ⬝ᵥ momentumCLM) ∘L angularMomentumOperator i j :=
  by
  suffices
    ∀ k l : Fin d,
      ⁅positionCLM k ∘L (momentumCLM ⬝ᵥ momentumCLM),
          (positionCLM ⬝ᵥ momentumCLM) ∘L momentumCLM l⁆ =
        (-I * ℏ) •
          (positionCLM k ∘L momentumCLM l - kroneckerDelta k l • (positionCLM ⬝ᵥ momentumCLM)) ∘L
            (momentumCLM ⬝ᵥ momentumCLM)
    by
    nth_rw 2 [← lie_skew]
    simp_rw [this, ← sub_eq_add_neg, ← smul_sub, ← sub_comp, symm j i, sub_sub_sub_cancel_right,
      momentumSqr_comp_angularMomentum_commute, angularMomentumOperator]
  intro k l
  calc
    _ =
        (positionCLM ⬝ᵥ momentumCLM) ∘L
              ⁅positionCLM k, momentumCLM l⁆ ∘L (momentumCLM ⬝ᵥ momentumCLM) +
            positionCLM k ∘L
              ⁅momentumCLM (d := d) ⬝ᵥ momentumCLM, positionCLM (d := d) ⬝ᵥ momentumCLM⁆ ∘L
                momentumCLM l +
          ⁅positionCLM k, positionCLM (d := d) ⬝ᵥ momentumCLM⁆ ∘L
            (momentumCLM ⬝ᵥ momentumCLM) ∘L momentumCLM l :=
      by simp [lie_leibniz, leibniz_lie, add_assoc, comp_assoc]
    _ =
        (positionCLM ⬝ᵥ momentumCLM) ∘L
            ⁅positionCLM k, momentumCLM l⁆ ∘L (momentumCLM ⬝ᵥ momentumCLM) +
          (-I * ℏ) • positionCLM k ∘L momentumCLM l ∘L (momentumCLM ⬝ᵥ momentumCLM) :=
      by
      simp only [← lie_skew _ (positionCLM ⬝ᵥ momentumCLM),
        positionDotMomentum_commutation_position, positionDotMomentum_commutation_momentumSqr,
        momentumSqr_comp_momentum_commute, ← neg_smul, ← neg_mul, smul_comp, comp_smul, add_assoc,
        ← add_smul]
      ring_nf
    _ =
        (-I * ℏ) •
          (positionCLM k ∘L momentumCLM l - kroneckerDelta k l • (positionCLM ⬝ᵥ momentumCLM)) ∘L
            (momentumCLM ⬝ᵥ momentumCLM) :=
      by
      simp_rw [position_commutation_momentum, sub_comp, smul_sub, smul_comp, comp_smul, id_comp,
        sub_eq_add_neg, ← neg_smul, neg_mul, neg_neg, comp_assoc, add_comm]


-- @@ L212-215 expanded
private lemma positionDotMomentumCompMomentum_comm {d : ℕ} (i j : Fin d) :
    ⁅(positionCLM ⬝ᵥ momentumCLM) ∘L momentumCLM i, (positionCLM ⬝ᵥ momentumCLM) ∘L momentumCLM j⁆ =
      0 :=
  by
  simp [lie_leibniz, leibniz_lie, momentum_comp_commute,
    ← lie_skew (momentumCLM _) (positionCLM ⬝ᵥ momentumCLM),
    positionDotMomentum_commutation_momentum, comp_assoc]


-- @@ L217-220 expanded
private lemma positionCompMomentumSqr_comm_momentum_add {d : ℕ} (i j : Fin d) :
    ⁅positionCLM i ∘L (momentumCLM ⬝ᵥ momentumCLM), momentumCLM j⁆ +
        ⁅momentumCLM i, positionCLM j ∘L (momentumCLM ⬝ᵥ momentumCLM)⁆ =
      0 :=
  by
  nth_rw 2 [← lie_skew]
  simp [leibniz_lie, position_commutation_momentum, symm j]


-- @@ L222-225 expanded
private lemma positionDotMomentumCompMomentum_comm_momentum_add {d : ℕ} (i j : Fin d) :
    ⁅(positionCLM ⬝ᵥ momentumCLM) ∘L momentumCLM i, momentumCLM j⁆ +
        ⁅momentumCLM i, (positionCLM ⬝ᵥ momentumCLM) ∘L momentumCLM j⁆ =
      0 :=
  by
  nth_rw 2 [← lie_skew]
  simp [leibniz_lie, positionDotMomentum_commutation_momentum, momentum_comp_commute]


-- @@ L227-251 expanded
private lemma positionCompMomentumSqr_comm_radiusRegInvCompPosition_add {d : ℕ} (ε : ℝˣ)
    (i j : Fin d) :
    ⁅positionCLM i ∘L (momentumCLM ⬝ᵥ momentumCLM), radiusRegPowCLM ε (-1) ∘L positionCLM j⁆ +
        ⁅radiusRegPowCLM ε (-1) ∘L positionCLM i, positionCLM j ∘L (momentumCLM ⬝ᵥ momentumCLM)⁆ =
      (-2 * I * ℏ) • radiusRegPowCLM ε (-1) ∘L angularMomentumOperator i j :=
  by
  let A := ⁅momentumCLM (d := d) ⬝ᵥ momentumCLM, (radiusRegPowCLM (d := d)) ε (-1)⁆
  have hA : positionCLM i ∘L A ∘L positionCLM j = positionCLM j ∘L A ∘L positionCLM i :=
    by
    suffices
      A =
        (2 * I * ℏ) • (radiusRegPowCLM (d := d)) ε (-3) ∘L (positionCLM ⬝ᵥ momentumCLM) +
            ((d - 3) * ℏ ^ 2 : ℝ) • radiusRegPowCLM ε (-3) +
          (3 * ε.1 ^ 2 * ℏ ^ 2) • radiusRegPowCLM ε (-5)
      by
      simp_rw [this, add_comp, comp_add, smul_comp, comp_smul, ← comp_assoc,
        position_comp_radiusRegPow_commute, comp_assoc,
        comp_eq_comp_add_commute (positionCLM ⬝ᵥ momentumCLM),
        positionDotMomentum_commutation_position, comp_add, comp_smul, ←
        comp_assoc (positionCLM _) (positionCLM _) _, position_comp_commute j i]
    simp_rw [A, ← lie_skew (momentumCLM ⬝ᵥ momentumCLM) _, radiusRegPow_commutation_momentumSqr,
      neg_sub, ← sub_sub, sub_eq_add_neg, ← neg_smul, ← neg_mul, neg_neg, ofReal_neg, ofReal_one,
      dotProduct, mul_def]
    ring_nf
    rw [add_rotate]
  calc
    _ =
        radiusRegPowCLM ε (-1) ∘L
              positionCLM i ∘L ⁅momentumCLM (d := d) ⬝ᵥ momentumCLM, positionCLM j⁆ +
            positionCLM i ∘L A ∘L positionCLM j -
          (radiusRegPowCLM ε (-1) ∘L
              positionCLM j ∘L ⁅momentumCLM (d := d) ⬝ᵥ momentumCLM, positionCLM i⁆ +
            positionCLM j ∘L A ∘L positionCLM i) :=
      by
      nth_rw 2 [← lie_skew]
      simp_rw [← sub_eq_add_neg, lie_leibniz, leibniz_lie, ← sub_sub]
      simp [A, comp_assoc]
    _ =
        radiusRegPowCLM ε (-1) ∘L
          (positionCLM i ∘L ⁅momentumCLM (d := d) ⬝ᵥ momentumCLM, positionCLM j⁆ -
            positionCLM j ∘L ⁅momentumCLM (d := d) ⬝ᵥ momentumCLM, positionCLM i⁆) :=
      by simp [hA]
    _ = (-2 * I * ℏ) • radiusRegPowCLM ε (-1) ∘L angularMomentumOperator i j := by
      simp_rw [← lie_skew _ (positionCLM _), position_commutation_momentumSqr, comp_neg, comp_smul,
        ← neg_smul, ← neg_mul, ← smul_sub, comp_smul, angularMomentumOperator]


-- @@ L253-256 expanded
private lemma momentum_comm_radiusRegPow_position_symm {d : ℕ} (ε : ℝˣ) (s : ℝ) (i j : Fin d) :
    ⁅momentumCLM i, radiusRegPowCLM ε s ∘L positionCLM j⁆ =
      ⁅momentumCLM j, radiusRegPowCLM ε s ∘L positionCLM i⁆ :=
  by
  simp [← lie_skew (momentumCLM _), leibniz_lie, position_commutation_momentum, symm j i,
    radiusRegPow_commutation_momentum, position_comp_commute j i, comp_assoc]


-- @@ L258-274 expanded
private lemma positionDotMomentumCompMomentum_comm_radiusRegInvCompPosition_add {d : ℕ} (ε : ℝˣ)
    (i j : Fin d) :
    ⁅(positionCLM ⬝ᵥ momentumCLM) ∘L momentumCLM i, radiusRegPowCLM ε (-1) ∘L positionCLM j⁆ +
        ⁅radiusRegPowCLM ε (-1) ∘L positionCLM i, (positionCLM ⬝ᵥ momentumCLM) ∘L momentumCLM j⁆ =
      (I * ℏ * ε.1 ^ 2) • radiusRegPowCLM ε (-3) ∘L angularMomentumOperator i j :=
  by
  suffices
    ∀ k,
      ⁅positionCLM (d := d) ⬝ᵥ momentumCLM, (radiusRegPowCLM (d := d)) ε (-1) ∘L positionCLM k⁆ =
        (-I * ℏ * ε.1 ^ 2) • radiusRegPowCLM ε (-3) ∘L positionCLM k
    by
    nth_rw 2 [← lie_skew]
    simp_rw [leibniz_lie, this, momentum_comm_radiusRegPow_position_symm, ← sub_eq_add_neg,
      add_sub_add_left_eq_sub, smul_comp, ← smul_sub, comp_assoc, ← comp_sub,
      angularMomentumOperator_antisymm i j, comp_neg, smul_neg, neg_mul, neg_smul,
      angularMomentumOperator]
  intro k
  calc
    _ = -(I * ℏ) • (ε.1 ^ 2) • radiusRegPowCLM ε (-1 - 2) ∘L positionCLM k := by
      simp [lie_leibniz, positionDotMomentum_commutation_position,
        positionDotMomentum_commutation_radiusRegPow, sub_comp, smul_sub, ← add_sub_assoc]
    _ = (-I * ℏ * ε.1 ^ 2) • radiusRegPowCLM ε (-3) ∘L positionCLM k :=
      by
      simp only [← Complex.coe_smul, ofReal_pow, smul_smul]
      ring_nf


-- @@ L276-278 expanded
private lemma momentum_comm_radiusRegInvCompPosition_add {d : ℕ} (ε : ℝˣ) (i j : Fin d) :
    ⁅momentumCLM i, radiusRegPowCLM ε (-1) ∘L positionCLM j⁆ +
        ⁅radiusRegPowCLM ε (-1) ∘L positionCLM i, momentumCLM j⁆ =
      0 :=
  by rw [← lie_skew _ (momentumCLM _), momentum_comm_radiusRegPow_position_symm, add_neg_cancel]


-- @@ L280-282 expanded
private lemma radiusRegInvCompPosition_comm {d : ℕ} (ε : ℝˣ) (i j : Fin d) :
    ⁅radiusRegPowCLM ε (-1) ∘L positionCLM i, radiusRegPowCLM ε (-1) ∘L positionCLM j⁆ = 0 := by
  simp [lie_leibniz, leibniz_lie, ← lie_skew (radiusRegPowCLM _ _) (positionCLM _)]


-- @@ L284-319 expanded
/-- `⁅𝐀(ε)ᵢ, 𝐀(ε)ⱼ⁆ = (-2iℏm·𝐇(ε) + iℏmkε²·𝐫(ε)⁻³)𝐋ᵢⱼ` -/
lemma lrl_commutation_lrl (ε : ℝˣ) (i j : Fin H.d) :
    ⁅H.lrlOperator ε i, H.lrlOperator ε j⁆ =
      ((-2 * I * ℏ * H.m) • H.hamiltonianRegCLM ε +
          (I * ℏ * H.m * H.k * ε.1 ^ 2) • radiusRegPowCLM ε (-3)) ∘L
        angularMomentumOperator i j :=
  by
  repeat rw [lrlOperator_eq]
  let c₁ : ℂ := 2⁻¹ * I * ℏ * (H.d - 1)
  let c₂ : ℂ := H.m * H.k
  trans
    ⁅positionCLM i ∘L (momentumCLM ⬝ᵥ momentumCLM), positionCLM j ∘L (momentumCLM ⬝ᵥ momentumCLM)⁆ +
                    ⁅(positionCLM ⬝ᵥ momentumCLM) ∘L momentumCLM i,
                      (positionCLM ⬝ᵥ momentumCLM) ∘L momentumCLM j⁆ +
                  (c₂ ^ 2) •
                    ⁅radiusRegPowCLM ε (-1) ∘L positionCLM i,
                      radiusRegPowCLM ε (-1) ∘L positionCLM j⁆ -
                (⁅positionCLM i ∘L (momentumCLM ⬝ᵥ momentumCLM),
                    (positionCLM ⬝ᵥ momentumCLM) ∘L momentumCLM j⁆ +
                  ⁅(positionCLM ⬝ᵥ momentumCLM) ∘L momentumCLM i,
                    positionCLM j ∘L (momentumCLM ⬝ᵥ momentumCLM)⁆) +
              c₁ •
                (⁅positionCLM i ∘L (momentumCLM ⬝ᵥ momentumCLM), momentumCLM j⁆ +
                  ⁅momentumCLM i, positionCLM j ∘L (momentumCLM ⬝ᵥ momentumCLM)⁆) -
            c₂ •
              (⁅positionCLM i ∘L (momentumCLM ⬝ᵥ momentumCLM),
                  radiusRegPowCLM ε (-1) ∘L positionCLM j⁆ +
                ⁅radiusRegPowCLM ε (-1) ∘L positionCLM i,
                  positionCLM j ∘L (momentumCLM ⬝ᵥ momentumCLM)⁆) -
          c₁ •
            (⁅(positionCLM ⬝ᵥ momentumCLM) ∘L momentumCLM i, momentumCLM j⁆ +
              ⁅momentumCLM i, (positionCLM ⬝ᵥ momentumCLM) ∘L momentumCLM j⁆) +
        c₂ •
          (⁅(positionCLM ⬝ᵥ momentumCLM) ∘L momentumCLM i,
              radiusRegPowCLM ε (-1) ∘L positionCLM j⁆ +
            ⁅radiusRegPowCLM ε (-1) ∘L positionCLM i,
              (positionCLM ⬝ᵥ momentumCLM) ∘L momentumCLM j⁆) -
      (c₁ * c₂) •
        (⁅momentumCLM i, radiusRegPowCLM ε (-1) ∘L positionCLM j⁆ +
          ⁅radiusRegPowCLM ε (-1) ∘L positionCLM i, momentumCLM j⁆)
  · simp only [lie_add, add_lie, lie_sub, sub_lie, lie_smul, smul_lie,
      momentum_commutation_momentum, smul_zero, add_zero, ← Complex.coe_smul, ofReal_mul]
    subst c₁ c₂
    ext
    simp only [sub_apply, add_apply, smul_apply, smul_eq_mul, smul_add]
    ring
  rw [positionCompMomentumSqr_comm, positionDotMomentumCompMomentum_comm,
    positionCompMomentumSqr_comm_positionDotMomentumCompMomentum_add,
    positionCompMomentumSqr_comm_momentum_add, positionDotMomentumCompMomentum_comm_momentum_add,
    positionCompMomentumSqr_comm_radiusRegInvCompPosition_add,
    positionDotMomentumCompMomentum_comm_radiusRegInvCompPosition_add,
    momentum_comm_radiusRegInvCompPosition_add, radiusRegInvCompPosition_comm]
  subst c₁ c₂
  simp_rw [hamiltonianRegCLM_eq, smul_zero, add_zero, sub_zero, ← sub_smul, ← Complex.coe_smul,
    ofReal_inv, ofReal_mul, ofReal_ofNat, smul_sub, smul_smul, add_comp, sub_comp, smul_comp]
  ring_nf
  simp
    /-
    ## Hamiltonian / LRL vector commutators
    -/


-- @@ L321-324 expanded
private lemma pSqr_comm_pL_Lp {d : ℕ} (i : Fin d) :
    ⁅momentumCLM (d := d) ⬝ᵥ momentumCLM,
        momentumCLM ⬝ᵥ angularMomentumOperator i + angularMomentumOperator i ⬝ᵥ momentumCLM⁆ =
      0 :=
  by
  show
    ⁅momentumCLM ⬝ᵥ momentumCLM,
        ∑ j, momentumCLM j ∘L angularMomentumOperator i j +
          ∑ j, angularMomentumOperator i j ∘L momentumCLM j⁆ =
      0
  simp [lie_sum, lie_leibniz, ← lie_skew (momentumCLM ⬝ᵥ momentumCLM) (angularMomentumOperator _ _)]


-- @@ L326-327 expanded
private lemma r_comm_rx {d : ℕ} (ε : ℝˣ) (i : Fin d) :
    ⁅(radiusRegPowCLM (d := d)) ε (-1), radiusRegPowCLM ε (-1) ∘L positionCLM i⁆ = 0 := by
  simp [lie_leibniz, ← lie_skew (radiusRegPowCLM _ _) (positionCLM _)]


-- @@ L329-346 expanded
private lemma xL_Lx_eq {d : ℕ} (ε : ℝˣ) (i : Fin d) :
    positionCLM ⬝ᵥ angularMomentumOperator i + angularMomentumOperator i ⬝ᵥ positionCLM =
      (2 : ℝ) • (positionCLM ⬝ᵥ momentumCLM) ∘L positionCLM i + (-I * ℏ * (d - 3)) • positionCLM i +
        ((-2 : ℝ) • radiusRegPowCLM ε 2 ∘L momentumCLM i + (2 * ε.1 ^ 2 : ℝ) • momentumCLM i) :=
  by
  -- Change summand
  
  simp_rw [dotProduct, mul_def, ← Finset.sum_add_distrib, angularMomentumOperator, comp_sub,
    sub_comp, comp_assoc, sub_add_sub_comm, momentum_comp_position_eq, comp_sub, comp_smul, comp_id,
    ← comp_assoc, position_comp_commute i _, ← add_sub_assoc, ← two_smul ℝ, sub_sub_eq_add_sub,
    sub_add_eq_add_sub, comp_assoc, comp_eq_comp_add_commute (positionCLM i) (momentumCLM _),
    position_commutation_momentum, symm _ i, comp_add, comp_smul, smul_add, comp_id, add_assoc, ←
    Complex.coe_smul, smul_smul, ← add_smul, ← comp_assoc, eq_one_of_same, one_smul]
    -- Split/do sums
    
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.smul_sum, ← finsetSum_comp,
    sum_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ,
    positionSqCLM_eq ε, sub_comp, smul_comp, id_comp, smul_sub]
    -- Clean up coefficients
    
  simp_rw [add_sub_assoc, add_right_inj, smul_smul, ← sub_smul, sub_eq_add_neg, neg_add, ← neg_smul,
    ← Complex.coe_smul, smul_smul, ofReal_neg, ofReal_mul, ofReal_pow, ofReal_ofNat, neg_neg]
  ring_nf


-- @@ L348-364 expanded
private lemma pSqr_comm_rx {d : ℕ} (ε : ℝˣ) (i : Fin d) :
    ⁅momentumCLM (d := d) ⬝ᵥ momentumCLM, radiusRegPowCLM ε (-1) ∘L positionCLM i⁆ =
      (I * ℏ) •
          radiusRegPowCLM ε (-3) ∘L
            (positionCLM ⬝ᵥ angularMomentumOperator i + angularMomentumOperator i ⬝ᵥ positionCLM) +
        ((-2 * I * ℏ * ε.1 ^ 2) • radiusRegPowCLM ε (-3) ∘L momentumCLM i +
          (3 * ℏ ^ 2 * ε.1 ^ 2) • radiusRegPowCLM ε (-5) ∘L positionCLM i) :=
  by
  trans
    (-2 * I * ℏ) • radiusRegPowCLM ε (-1) ∘L momentumCLM i +
          (2 * I * ℏ) • radiusRegPowCLM ε (-3) ∘L (positionCLM ⬝ᵥ momentumCLM) ∘L positionCLM i +
        (ℏ ^ 2 * (d - 3) : ℝ) • radiusRegPowCLM ε (-3) ∘L positionCLM i +
      (3 * ℏ ^ 2 * ε.1 ^ 2) • radiusRegPowCLM ε (-5) ∘L positionCLM i
  · rw [← lie_skew]
    simp_rw [leibniz_lie, position_commutation_momentumSqr, radiusRegPow_commutation_momentumSqr,
      sub_comp, add_comp, smul_comp, comp_smul, comp_assoc, neg_add, neg_sub', neg_add,
      sub_neg_eq_add, ← neg_smul, add_assoc, ofReal_neg, ofReal_one, dotProduct, mul_def]
    ring_nf
  rw [← add_assoc, add_left_inj, add_rotate]
  simp_rw [xL_Lx_eq ε i, comp_add, comp_smul, smul_add, ← Complex.coe_smul, smul_smul, ← comp_assoc,
    radiusRegPowCLM_comp_eq, comp_assoc, add_assoc, ← add_smul, ofReal_mul, ofReal_sub, ofReal_neg,
    ofReal_pow, ofReal_ofNat]
  ring_nf
  simp [I_sq]


-- @@ L366-379 expanded
private lemma r_comm_pL_Lp {d : ℕ} (ε : ℝˣ) (i : Fin d) :
    ⁅(radiusRegPowCLM (d := d)) ε (-1),
        momentumCLM ⬝ᵥ angularMomentumOperator i + angularMomentumOperator i ⬝ᵥ momentumCLM⁆ =
      -((I * ℏ) •
          radiusRegPowCLM ε (-3) ∘L
            (positionCLM ⬝ᵥ angularMomentumOperator i +
              angularMomentumOperator i ⬝ᵥ positionCLM)) :=
  by
  calc
    _ =
        ∑ j,
          (⁅(radiusRegPowCLM (d := d)) ε (-1), momentumCLM j⁆ ∘L angularMomentumOperator i j +
            angularMomentumOperator i j ∘L ⁅(radiusRegPowCLM (d := d)) ε (-1), momentumCLM j⁆) :=
      by
      simp [dotProduct, mul_def, ← Finset.sum_add_distrib, lie_sum, lie_leibniz,
        ← lie_skew _ (angularMomentumOperator _ _)]
    _ =
        -((I * ℏ) •
            ∑ j,
              (radiusRegPowCLM ε (-3) ∘L positionCLM j ∘L angularMomentumOperator i j +
                (angularMomentumOperator i j ∘L radiusRegPowCLM ε (-3)) ∘L positionCLM j)) :=
      by
      simp only [radiusRegPow_commutation_momentum, smul_comp, comp_smul, ← smul_add,
        ← Finset.smul_sum, comp_assoc, ofReal_neg, ofReal_one, ← neg_smul]
      ring_nf
    _ =
        -((I * ℏ) •
            radiusRegPowCLM ε (-3) ∘L
              (positionCLM ⬝ᵥ angularMomentumOperator i +
                angularMomentumOperator i ⬝ᵥ positionCLM)) :=
      by
      simp_rw [angularMomentum_comp_radiusRegPow_commute, comp_assoc, ← comp_add, ← comp_finsetSum,
        Finset.sum_add_distrib, dotProduct, mul_def]


-- @@ L381-407 expanded
/-- `⁅𝐇(ε), 𝐀(ε)ᵢ⁆ = iℏk·ε²𝐫(ε)⁻³𝐩ᵢ - 3ℏ²k/2·ε²𝐫(ε)⁻⁵𝐱ᵢ` -/
lemma hamiltonianReg_commutation_lrl (ε : ℝˣ) (i : Fin H.d) :
    ⁅H.hamiltonianRegCLM ε, H.lrlOperator ε i⁆ =
      (I * ℏ * H.k * ε.1 ^ 2) • radiusRegPowCLM ε (-3) ∘L momentumCLM i -
        (3 / 2 * ℏ ^ 2 * H.k * ε.1 ^ 2) • radiusRegPowCLM ε (-5) ∘L positionCLM i :=
  by
  trans
    (-2⁻¹ * H.k) •
      (⁅momentumCLM (d := H.d) ⬝ᵥ momentumCLM, radiusRegPowCLM ε (-1) ∘L positionCLM i⁆ +
        ⁅(radiusRegPowCLM (d := H.d)) ε (-1),
          momentumCLM ⬝ᵥ angularMomentumOperator i + angularMomentumOperator i ⬝ᵥ momentumCLM⁆)
  · have h : H.m * H.k * (H.m⁻¹ * 2⁻¹) = 2⁻¹ * H.k := by grind [H.m_ne_zero]
    simp only [hamiltonianRegCLM_eq, lrlOperator, lie_sub, sub_lie, smul_lie, lie_smul,
      pSqr_comm_pL_Lp]
    simp [r_comm_rx, h, smul_smul, sub_eq_neg_add, add_comm]
  simp_rw [pSqr_comm_rx, r_comm_pL_Lp, add_neg_cancel_comm, smul_add, sub_eq_add_neg, ← neg_smul, ←
    neg_mul, ← Complex.coe_smul, smul_smul, ofReal_mul, ofReal_neg, ofReal_inv, ofReal_div,
    ofReal_pow, ofReal_ofNat]
  ring_nf
    /-
    
    ## LRL vector squared
    
    To compute `𝐀(ε)²` we take the following approach:
    - Write `𝐀(ε)ᵢ = 𝐋ᵢⱼ𝐩ⱼ + ½iℏ(d-1)𝐩ᵢ - mk·𝐫(ε)⁻¹𝐱ᵢ` for the first term and
      `𝐀(ε)ᵢ = 𝐩ⱼ𝐋ᵢⱼ - ½iℏ(d-1)𝐩ᵢ - mk·𝐫(ε)⁻¹𝐱ᵢ` for the second.
    - Expand out to nine terms: one is a triple sum, two are double sums and the rest are single sums.
    - Compute each term, symmetrizing the sums (see `sum_symmetrize` and `sum_symmetrize'`).
    - Collect terms.
    
    -/


-- @@ L409-413 verbatim
private lemma sum_symmetrize {d : ℕ} (f : Fin d → Fin d → 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) :
    ∑ i, ∑ j, f i j = (2 : ℂ)⁻¹ • ∑ i, ∑ j, (f i j + f j i) := by
  simp only [Finset.sum_add_distrib]
  nth_rw 3 [Finset.sum_comm]
  rw [← two_smul ℂ, smul_smul, inv_mul_cancel_of_invertible, one_smul]


-- @@ L415-422 verbatim
private lemma sum_symmetrize' {d : ℕ}
    (f : Fin d → Fin d → Fin d → 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) :
    ∑ i, ∑ j, ∑ k, f i j k = (2 : ℂ)⁻¹ • ∑ i, ∑ k, ∑ j, (f i j k + f k j i) := by
  simp only [Finset.sum_add_distrib]
  nth_rw 3 [Finset.sum_comm]
  rw [← two_smul ℂ, smul_smul, inv_mul_cancel_of_invertible, one_smul]
  congr with
  rw [Finset.sum_comm]


-- @@ L424-429 expanded
private lemma sum_Lpp (d : ℕ) :
    ∑ i : Fin d, ∑ j, angularMomentumOperator i j ∘L momentumCLM j ∘L momentumCLM i = 0 :=
  by
  rw [sum_symmetrize]
  conv_lhs =>
    enter [2, 2, i, 2, j]
    rw [angularMomentumOperator_antisymm j i, momentum_comp_commute j i]
  simp


-- @@ L431-436 expanded
private lemma sum_ppL (d : ℕ) :
    ∑ i : Fin d, ∑ j, momentumCLM i ∘L momentumCLM j ∘L angularMomentumOperator i j = 0 :=
  by
  rw [sum_symmetrize]
  conv_lhs =>
    enter [2, 2, i, 2, j]
    rw [← comp_assoc, ← comp_assoc, angularMomentumOperator_antisymm j i, momentum_comp_commute j i]
  simp


-- @@ L438-457 expanded
private lemma sum_LppL (d : ℕ) :
    ∑ i : Fin d,
        ∑ j,
          ∑ k,
            angularMomentumOperator i j ∘L
              momentumCLM j ∘L momentumCLM k ∘L angularMomentumOperator i k =
      (momentumCLM ⬝ᵥ momentumCLM) ∘L angularMomentumOperatorSqr :=
  by
  rw [sum_symmetrize']
  conv_lhs =>
    enter [2, 2, i, 2, j, 2, k]
    calc
      _ =
          (angularMomentumOperator i k ∘L momentumCLM k ∘L momentumCLM j -
              angularMomentumOperator j k ∘L momentumCLM k ∘L momentumCLM i) ∘L
            angularMomentumOperator i j :=
        by simp [angularMomentumOperator_antisymm j i, comp_neg, ← comp_assoc, sub_eq_add_neg]
      _ =
          (positionCLM i ∘L momentumCLM k ∘L momentumCLM k ∘L momentumCLM j -
                positionCLM k ∘L momentumCLM i ∘L momentumCLM k ∘L momentumCLM j -
              (positionCLM j ∘L momentumCLM k ∘L momentumCLM k ∘L momentumCLM i -
                positionCLM k ∘L momentumCLM j ∘L momentumCLM k ∘L momentumCLM i)) ∘L
            angularMomentumOperator i j :=
        by simp_rw [angularMomentumOperator, sub_comp, comp_assoc]
      _ =
          (positionCLM i ∘L momentumCLM j ∘L momentumCLM k ∘L momentumCLM k -
              positionCLM j ∘L momentumCLM i ∘L momentumCLM k ∘L momentumCLM k) ∘L
            angularMomentumOperator i j :=
        by
        simp_rw [momentum_comp_commute k, ← comp_assoc (momentumCLM _), momentum_comp_commute k,
          momentum_comp_commute i j, sub_sub_sub_cancel_right]
      _ =
          angularMomentumOperator i j ∘L
            (momentumCLM k ∘L momentumCLM k) ∘L angularMomentumOperator i j :=
        by simp_rw [← comp_assoc, ← sub_comp, angularMomentumOperator]
  trans
    (2 : ℂ)⁻¹ •
      ∑ i,
        ∑ j,
          angularMomentumOperator i j ∘L (momentumCLM ⬝ᵥ momentumCLM) ∘L angularMomentumOperator i j
  · simp_rw [← comp_finsetSum, ← finsetSum_comp, ← comp_assoc, dotProduct, mul_def]
  simp_rw [← comp_assoc, ← momentumSqr_comp_angularMomentum_commute, comp_assoc, ← comp_finsetSum, ←
    comp_smul, angularMomentumOperatorSqr]


-- @@ L459-470 expanded
private lemma sum_Lprx (d : ℕ) (ε : ℝˣ) :
    ∑ i,
        ∑ j,
          angularMomentumOperator i j ∘L
            momentumCLM j ∘L (radiusRegPowCLM (d := d)) ε (-1) ∘L positionCLM i =
      radiusRegPowCLM ε (-1) ∘L angularMomentumOperatorSqr :=
  by
  simp_rw [← position_comp_radiusRegPow_commute, ← comp_assoc, ←
    finsetSum_comp _ (radiusRegPowCLM _ _)]
  rw [sum_symmetrize]
  conv_lhs =>
    enter [1, 2, 2, i, 2, j]
    calc
      _ =
          angularMomentumOperator i j ∘L
            (momentumCLM j ∘L positionCLM i - momentumCLM i ∘L positionCLM j) :=
        by simp [angularMomentumOperator_antisymm j i, comp_assoc, sub_eq_add_neg]
      _ = angularMomentumOperator i j ∘L angularMomentumOperator i j := by
        simp [momentum_comp_position_eq, symm j i, angularMomentumOperator]
  rw [← angularMomentumSqr_comp_radiusRegPow_commute, angularMomentumOperatorSqr]


-- @@ L472-480 expanded
private lemma sum_rxpL (d : ℕ) (ε : ℝˣ) :
    ∑ i,
        ∑ j,
          (radiusRegPowCLM (d := d)) ε (-1) ∘L
            positionCLM i ∘L momentumCLM j ∘L angularMomentumOperator i j =
      radiusRegPowCLM ε (-1) ∘L angularMomentumOperatorSqr :=
  by
  simp_rw [← comp_finsetSum (radiusRegPowCLM _ _)]
  rw [sum_symmetrize]
  conv_lhs =>
    enter [2, 2, 2, i, 2, j]
    rw [angularMomentumOperator_antisymm j i, comp_neg, comp_neg, ← sub_eq_add_neg, ← comp_assoc, ←
      comp_assoc, ← sub_comp, ← angularMomentumOperator]
  rw [angularMomentumOperatorSqr]


-- @@ L482-502 expanded
private lemma sum_prx (d : ℕ) (ε : ℝˣ) :
    ∑ i, momentumCLM i ∘L (radiusRegPowCLM (d := d)) ε (-1) ∘L positionCLM i =
      radiusRegPowCLM ε (-1) ∘L (positionCLM ⬝ᵥ momentumCLM) -
          (I * ℏ * (d - 1)) • radiusRegPowCLM ε (-1) -
        (I * ℏ * ε.1 ^ 2) • radiusRegPowCLM ε (-3) :=
  by
  calc
    _ =
        ∑ i,
          (radiusRegPowCLM ε (-1) ∘L momentumCLM i ∘L positionCLM i +
            (I * ℏ) • radiusRegPowCLM ε (-3) ∘L positionCLM i ∘L positionCLM i) :=
      by
      simp_rw [← comp_assoc, momentum_comp_radiusRegPow_eq]
      ring_nf
      simp
    _ =
        ∑ i,
          (radiusRegPowCLM ε (-1) ∘L positionCLM i ∘L momentumCLM i -
              (I * ℏ) • radiusRegPowCLM ε (-1) +
            (I * ℏ) • radiusRegPowCLM ε (-3) ∘L positionCLM i ∘L positionCLM i) :=
      by simp [momentum_comp_position_eq]
    _ =
        radiusRegPowCLM ε (-1) ∘L ∑ i, positionCLM i ∘L momentumCLM i +
            (-d * I * ℏ) • radiusRegPowCLM ε (-1) +
          (I * ℏ) • radiusRegPowCLM ε (-3) ∘L ∑ i, positionCLM i ∘L positionCLM i :=
      by
      simp [Finset.sum_add_distrib, ← comp_finsetSum, ← Finset.smul_sum, ← Nat.cast_smul_eq_nsmul ℂ,
        smul_smul, mul_assoc, sub_eq_add_neg]
    _ =
        radiusRegPowCLM ε (-1) ∘L (positionCLM ⬝ᵥ momentumCLM) -
            (I * ℏ * (d - 1)) • radiusRegPowCLM ε (-1) -
          (I * ℏ * ε.1 ^ 2) • radiusRegPowCLM ε (-3) :=
      by
      simp only [dotProduct, mul_def, positionSqCLM_eq ε, comp_sub, comp_smul, comp_id,
        radiusRegPowCLM_comp_eq, smul_sub, ← Complex.coe_smul, ofReal_pow, smul_smul]
      ring_nf
      simp_rw [← add_sub_assoc, add_assoc, ← add_smul, sub_eq_add_neg, ← neg_smul]
      ring_nf


-- @@ L504-505 expanded
private lemma sum_rxp (d : ℕ) (ε : ℝˣ) :
    ∑ i, (radiusRegPowCLM (d := d)) ε (-1) ∘L positionCLM i ∘L momentumCLM i =
      radiusRegPowCLM ε (-1) ∘L (positionCLM ⬝ᵥ momentumCLM) :=
  by rw [← comp_finsetSum]; rfl


-- @@ L507-512 expanded
private lemma sum_rxrx (d : ℕ) (ε : ℝˣ) :
    ∑ i,
        (radiusRegPowCLM (d := d)) ε (-1) ∘L
          positionCLM i ∘L radiusRegPowCLM ε (-1) ∘L positionCLM i =
      ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ) - (ε.1 ^ 2) • radiusRegPowCLM ε (-2) :=
  by
  simp_rw [← comp_finsetSum, ← comp_assoc, position_comp_radiusRegPow_commute, comp_assoc, ←
    comp_finsetSum, ← comp_assoc, radiusRegPowCLM_comp_eq, positionSqCLM_eq ε]
  ring_nf
  simp


-- @@ L514-537 expanded
set_option backward.isDefEq.respectTransparency false in
/-- The square of the (regularized) LRL vector operator is related to the (regularized) Hamiltonian
  `𝐇(ε)` of the hydrogen atom, square of the angular momentum `𝐋²` and powers of `𝐫(ε)` as
  `𝐀(ε)² = 2m·𝐇(ε)(𝐋² + ¼ℏ²(d-1)²) + m²k²(𝟙 - ε²·𝐫(ε)⁻²) - ½(d-1)mkℏ²ε²𝐫(ε)⁻³`. -/
lemma lrlOperatorSqr_eq (ε : ℝˣ) :
    H.lrlOperator ε ⬝ᵥ H.lrlOperator ε =
      (2 * H.m) •
            (H.hamiltonianRegCLM ε) ∘L
              (angularMomentumOperatorSqr +
                (4⁻¹ * ℏ ^ 2 * (H.d - 1) ^ 2 : ℝ) • ContinuousLinearMap.id ℂ 𝓢(Space H.d, ℂ)) +
          (H.m ^ 2 * H.k ^ 2) •
            (ContinuousLinearMap.id ℂ 𝓢(Space H.d, ℂ) - ε.1 ^ 2 • radiusRegPowCLM ε (-2)) -
        (2⁻¹ * ℏ ^ 2 * H.m * H.k * (H.d - 1) * ε.1 ^ 2) • radiusRegPowCLM ε (-3) :=
  by
  simp_rw [dotProduct, mul_def]
  conv_lhs => enter [2, i, 1]; rw [lrlOperator_eq']
  conv_lhs => enter [2, i, 2]; rw [lrlOperator_eq'']
  simp_rw [dotProduct, mul_def, sub_eq_add_neg, ← neg_smul, add_comp, comp_add, smul_comp,
    comp_smul, finsetSum_comp, comp_finsetSum, Finset.sum_add_distrib, ← Finset.smul_sum,
    comp_assoc, sum_LppL, sum_Lpp, sum_Lprx, sum_ppL, sum_prx, sum_rxpL, sum_rxp, sum_rxrx]
  simp only [dotProduct, mul_def, ← neg_mul, smul_zero, add_zero, ← Complex.coe_smul, ofReal_mul,
    ofReal_neg, smul_smul, zero_add, sub_eq_add_neg, ← neg_smul, smul_add, ofReal_pow,
    hamiltonianRegCLM_eq, ofReal_inv, ofReal_ofNat]
  ring_nf
  ext
  simp only [add_apply, _root_.smul_apply, _root_.add_apply, _root_.smul_apply, Function.comp_apply,
    coe_comp, coe_id', smul_eq_mul, ofReal_add, ofReal_neg, ofReal_one, ofReal_natCast]
  grind [I_sq, H.m_ne_zero, mul_inv_cancel₀, ofReal_eq_zero]


-- @@ L539-539 verbatim
end

-- @@ L540-540 verbatim
end HydrogenAtom

-- @@ L541-541 verbatim
end QuantumMechanics
