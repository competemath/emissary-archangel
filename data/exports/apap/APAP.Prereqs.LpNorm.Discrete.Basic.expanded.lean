module

public import APAP.Prereqs.LpNorm.Compact
public import APAP.Prereqs.LpNorm.Discrete.Defs
public import APAP.Prereqs.Mu
public import Mathlib.Algebra.Group.Translate
public import Mathlib.Algebra.Star.Conjneg

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Positivity.Finset


-- @@ L12-14 verbatim
/-!
# Lp norms
-/


-- @@ L16-16 verbatim
public section


-- @@ L18-18 verbatim
open Finset Function Real

-- @@ L19-19 verbatim
open scoped BigOperators ComplexConjugate ENNReal NNReal Indicator translate mu


-- @@ L21-21 verbatim
namespace MeasureTheory

-- @@ L22-22 verbatim
variable {ι G 𝕜 E R : Type*} [Finite ι] {mι : MeasurableSpace ι} [DiscreteMeasurableSpace ι]


-- @@ L24-28 expanded
omit [Finite ι] in
lemma cLpNorm_pow_eq_card_inv_mul_dLpNorm_pow [Fintype ι] {n : ℕ} (hn₀ : n ≠ 0) (f : ι → ℂ) :
    cLpNorm n f ^ n = (Fintype.card ι : ℝ)⁻¹ * dLpNorm n f ^ n :=
  by
  rw [cLpNorm_pow_eq_expect_norm hn₀, dLpNorm_pow_eq_sum_norm hn₀]
  simp [Fintype.expect_eq_sum_div_card, div_eq_mul_inv, mul_comm]


-- @@ L30-30 verbatim
/-! ### Indicator -/


-- @@ L32-32 verbatim
section Indicator

-- @@ L33-33 verbatim
variable [RCLike R] {s : Finset ι} {p : ℝ≥0}


-- @@ L35-42 expanded
lemma dLpNorm_rpow_indicator_one (hp : p ≠ 0) (s : Finset ι) :
    dLpNorm p 𝟭_[(s : Set ι), R] ^ (p : ℝ) = #s := by
  classical
  cases nonempty_fintype ι
  have : ∀ x, (ite (x ∈ s) 1 0 : ℝ) ^ (p : ℝ) = ite (x ∈ s) (1 ^ (p : ℝ)) (0 ^ (p : ℝ)) := fun x ↦
    by split_ifs <;> simp
  simp [dLpNorm_rpow_eq_sum_norm, hp, Set.indicator_apply, apply_ite norm, -sum_const,
    card_eq_sum_ones]


-- @@ L44-46 expanded
lemma dLpNorm_indicator_one (hp : p ≠ 0) (s : Finset ι) :
    dLpNorm p 𝟭_[(s : Set ι), R] = #s ^ (p⁻¹ : ℝ) := by
  refine (eq_rpow_inv ?_ ?_ ?_).2 (dLpNorm_rpow_indicator_one ?_ _) <;> positivity


-- @@ L48-50 expanded
lemma dLpNorm_pow_indicator_one {p : ℕ} (hp : p ≠ 0) (s : Finset ι) :
    dLpNorm p 𝟭_[(s : Set ι), R] ^ (p : ℝ) = #s := by
  simpa using dLpNorm_rpow_indicator_one (Nat.cast_ne_zero.2 hp) s


-- @@ L52-53 expanded
lemma dL2Norm_sq_indicator_one (s : Finset ι) : dLpNorm 2 𝟭_[(s : Set ι), R] ^ 2 = #s := by
  simpa using dLpNorm_pow_indicator_one two_ne_zero s


-- @@ L55-56 expanded
@[simp]
lemma dL2Norm_indicator_one (s : Finset ι) : dLpNorm 2 𝟭_[(s : Set ι), R] = Real.sqrt #s := by
  rw [eq_comm, sqrt_eq_iff_eq_sq, dL2Norm_sq_indicator_one] <;> positivity


-- @@ L58-59 expanded
@[simp]
lemma dL1Norm_indicator_one (s : Finset ι) : dLpNorm 1 𝟭_[(s : Set ι), R] = #s := by
  simpa using dLpNorm_pow_indicator_one one_ne_zero s


-- @@ L61-63 expanded
lemma dLpNorm_mu (hp : 1 ≤ p) (hs : s.Nonempty) :
    dLpNorm p ((@mu R _ _) s) = #s ^ ((p : ℝ)⁻¹ - 1) := by
  rw [mu, dLpNorm_const_smul ((#s)⁻¹ : R) (𝟭_[(s : Set ι), R]), dLpNorm_indicator_one, norm_inv,
      RCLike.norm_natCast, inv_mul_eq_div, ← Real.rpow_sub_one] <;>
    positivity


-- @@ L65-69 expanded
lemma dLpNorm_mu_le (hp : 1 ≤ p) : dLpNorm p ((@mu R _ _) s) ≤ #s ^ (p⁻¹ - 1 : ℝ) :=
  by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp only [mu_empty, dLpNorm_zero, card_empty, CharP.cast_eq_zero, NNReal.coe_inv]
    positivity
  · exact (dLpNorm_mu hp hs).le


-- @@ L71-72 expanded
@[simp]
lemma dL1Norm_mu (hs : s.Nonempty) : dLpNorm 1 ((@mu R _ _) s) = 1 := by
  simpa using dLpNorm_mu le_rfl hs


-- @@ L74-74 expanded
lemma dL1Norm_mu_le_one : dLpNorm 1 ((@mu R _ _) s) ≤ 1 := by simpa using dLpNorm_mu_le le_rfl


-- @@ L76-78 expanded
@[simp]
lemma dL2Norm_mu (hs : s.Nonempty) : dLpNorm 2 ((@mu R _ _) s) = #s ^ (-2⁻¹ : ℝ) :=
  by
  have : (2⁻¹ - 1 : ℝ) = -2⁻¹ := by norm_num
  simpa [sqrt_eq_rpow, this] using dLpNorm_mu one_le_two (R := R) hs


-- @@ L80-80 verbatim
end Indicator


-- @@ L82-82 verbatim
/-! ### Translation -/


-- @@ L84-84 verbatim
section dLpNorm

-- @@ L85-86 verbatim
variable {mG : MeasurableSpace G} [DiscreteMeasurableSpace G] [AddCommGroup G] [Finite G]
  {p : ℝ≥0∞}


-- @@ L88-98 expanded
@[simp]
lemma dLpNorm_translate [NormedAddCommGroup E] (a : G) (f : G → E) :
    dLpNorm p (τ a f) = dLpNorm p f :=
  by
  cases nonempty_fintype G
  obtain p | p := p
  · simp only [dLinftyNorm_eq_iSup_norm, ENNReal.none_eq_top, translate_apply]
    exact (Equiv.subRight _).iSup_congr fun _ ↦ rfl
  obtain rfl | hp := eq_or_ne p 0
  · simp only [dLpNorm_exponent_zero, ENNReal.some_eq_coe, ENNReal.coe_zero]
  · simp only [dLpNorm_eq_sum_norm hp, ENNReal.some_eq_coe, translate_apply]
    congr 1
    exact Fintype.sum_equiv (Equiv.subRight _) _ _ fun _ ↦ rfl


-- @@ L100-110 expanded
@[simp]
lemma dLpNorm_conjneg [RCLike E] (f : G → E) : dLpNorm p (conjneg f) = dLpNorm p f :=
  by
  cases nonempty_fintype G
  simp only [conjneg, dLpNorm_conj]
  obtain p | p := p
  · simp only [dLinftyNorm_eq_iSup_norm, ENNReal.none_eq_top]
    exact (Equiv.neg _).iSup_congr fun _ ↦ rfl
  obtain rfl | hp := eq_or_ne p 0
  · simp only [dLpNorm_exponent_zero, ENNReal.some_eq_coe, ENNReal.coe_zero]
  · simp only [dLpNorm_eq_sum_norm hp, ENNReal.some_eq_coe]
    congr 1
    exact Fintype.sum_equiv (Equiv.neg _) _ _ fun _ ↦ rfl


-- @@ L112-122 expanded
lemma dLpNorm_translate_sum_sub_le [NormedAddCommGroup E] (hp : 1 ≤ p) {ι : Type*} (s : Finset ι)
    (a : ι → G) (f : G → E) :
    dLpNorm p (τ (∑ i ∈ s, a i) f - f) ≤ ∑ i ∈ s, dLpNorm p (τ (a i) f - f) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s ih hs =>
    calc
      _ = dLpNorm p (τ (∑ j ∈ s, a j) (τ (a i) f - f) + (τ (∑ j ∈ s, a j) f - f)) := by
        rw [sum_cons, translate_add', translate_sub_right, sub_add_sub_cancel]
      _ ≤ dLpNorm p (τ (∑ j ∈ s, a j) (τ (a i) f - f)) + ∑ j ∈ s, dLpNorm p (τ (a j) f - f) := by
        grw [dLpNorm_add_le hp, hs]
      _ = _ := by rw [dLpNorm_translate, sum_cons]


-- @@ L124-124 verbatim
end dLpNorm

-- @@ L125-125 verbatim
end MeasureTheory
