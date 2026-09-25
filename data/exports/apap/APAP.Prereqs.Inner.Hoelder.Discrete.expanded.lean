module

public import APAP.Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import APAP.Prereqs.LpNorm.Discrete.Defs
public import Mathlib.Analysis.RCLike.Inner

import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.Bochner.Basic


-- @@ L10-10 verbatim
/-! # Inner product -/


-- @@ L12-12 verbatim
public section


-- @@ L14-14 verbatim
open Finset Function MeasureTheory RCLike Real

-- @@ L15-15 verbatim
open scoped ComplexConjugate ENNReal NNReal NNRat


-- @@ L17-17 verbatim
variable {ι 𝕜 S : Type*} [Fintype ι]


-- @@ L19-19 verbatim
namespace RCLike

-- @@ L20-20 verbatim
variable [RCLike 𝕜] {mι : MeasurableSpace ι} [DiscreteMeasurableSpace ι] {f : ι → 𝕜}


-- @@ L22-25 expanded
@[simp]
lemma wInner_one_self {_ : MeasurableSpace ι} [DiscreteMeasurableSpace ι] (f : ι → 𝕜) :
    ⟪f, f⟫_[𝕜] = ((dLpNorm 2 f : ℝ) : 𝕜) ^ 2 :=
  by
  simp_rw [← algebraMap.coe_pow]
  simp [dL2Norm_sq_eq_sum_norm, wInner_one_eq_sum]


-- @@ L27-29 expanded
set_option backward.isDefEq.respectTransparency false in
lemma dL1Norm_mul (f g : ι → 𝕜) : dLpNorm 1 (f * g) = ⟪fun i ↦ ‖f i‖, fun i ↦ ‖g i‖⟫_[ℝ] := by
  simp [wInner_one_eq_sum, dL1Norm_eq_sum_norm, mul_comm]


-- @@ L31-35 expanded
set_option backward.isDefEq.respectTransparency false in
/-- **Cauchy-Schwarz inequality** -/
lemma wInner_one_le_dL2Norm_mul_dL2Norm (f g : ι → ℝ) : ⟪f, g⟫_[ℝ] ≤ dLpNorm 2 f * dLpNorm 2 g := by
  simpa [dL2Norm_eq_sum_norm, PiLp.norm_eq_of_L2, sqrt_eq_rpow, wInner_one_eq_inner] using
    real_inner_le_norm ((WithLp.equiv 2 _).symm f) _


-- @@ L37-37 verbatim
end RCLike


-- @@ L39-39 verbatim
/-! ### Hölder inequality -/


-- @@ L41-41 verbatim
namespace MeasureTheory

-- @@ L42-42 verbatim
section Real

-- @@ L43-44 verbatim
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Fintype α] {p q : ℝ≥0∞}
  {f g : α → ℝ}


-- @@ L46-47 expanded
lemma dL1Norm_mul_of_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : dLpNorm 1 (f * g) = ⟪f, g⟫_[ℝ] := by
  convert dL1Norm_mul f g using 2 <;> ext a <;> refine (norm_of_nonneg ?_).symm; exacts [hf _, hg _]


-- @@ L49-73 expanded
set_option backward.isDefEq.respectTransparency false in
/-- **Hölder's inequality**, binary case. -/
lemma wInner_one_le_dLpNorm_mul_dLpNorm (p q : ℝ≥0∞) [p.HolderConjugate q] :
    ⟪f, g⟫_[ℝ] ≤ dLpNorm p f * dLpNorm q g :=
  by
  have hp0 : p ≠ 0 := ENNReal.HolderConjugate.ne_zero p q
  have hq0 : q ≠ 0 := ENNReal.HolderConjugate.ne_zero q p
  have hwInner : ⟪f, g⟫_[ℝ] = ∑ i, f i * g i := by simp [wInner_one_eq_sum, mul_comm]
  have hfg i : f i * g i ≤ ‖f i‖ * ‖g i‖ :=
    (le_abs_self _).trans_eq (by rw [abs_mul]; simp [Real.norm_eq_abs])
  obtain rfl | hpi := eq_or_ne p ∞
  · obtain rfl : q = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ∞ q).mp rfl
    simp only [hwInner, dL1Norm_eq_sum_norm, norm_eq_abs, dLinftyNorm_eq_iSup_norm, mul_sum]
    gcongr ∑ _, ?_ with i
    grw [le_abs_self (_ * _), abs_mul, ← le_ciSup (Finite.bddAbove_range _)]
  obtain rfl | hqi := eq_or_ne q ∞
  · obtain rfl : p = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ∞ p).mp rfl
    simp only [hwInner, dL1Norm_eq_sum_norm, norm_eq_abs, dLinftyNorm_eq_iSup_norm, sum_mul]
    gcongr ∑ _, ?_ with i
    grw [le_abs_self (_ * _), abs_mul, ← le_ciSup (Finite.bddAbove_range _)]
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpi
  have hqr : 0 < q.toReal := ENNReal.toReal_pos hq0 hqi
  have hreal : Real.HolderConjugate p.toReal q.toReal := by
    simpa using ENNReal.HolderTriple.toReal (p := p) (q := q) (r := 1) hpr hqr
  rw [hwInner, dLpNorm_eq_sum_norm' hp0 hpi, dLpNorm_eq_sum_norm' hq0 hqi]
  simpa using Real.inner_le_Lp_mul_Lq Finset.univ f g hreal


-- @@ L75-79 expanded
/-- **Hölder's inequality**, binary case. -/
lemma abs_wInner_one_le_dLpNorm_mul_dLpNorm [p.HolderConjugate q] (f g : α → ℝ) :
    |⟪f, g⟫_[ℝ]| ≤ dLpNorm p f * dLpNorm q g :=
  (abs_wInner_le zero_le_one).trans <|
    (wInner_one_le_dLpNorm_mul_dLpNorm p q).trans_eq <| by simp_rw [dLpNorm_abs .of_discrete]


-- @@ L81-81 verbatim
end Real


-- @@ L83-83 verbatim
section Hoelder

-- @@ L84-85 verbatim
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Fintype α] [RCLike 𝕜]
  {p q r : ℝ≥0∞} {f g : α → 𝕜}


-- @@ L87-89 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma norm_wInner_one_le (f g : α → 𝕜) : ‖⟪f, g⟫_[𝕜]‖ ≤ ⟪fun a ↦ ‖f a‖, fun a ↦ ‖g a‖⟫_[ℝ] := by
  grw [wInner_one_eq_sum, norm_sum_le]; simp [wInner_one_eq_sum]


-- @@ L91-97 expanded
/-- **Hölder's inequality**, binary case. -/
lemma norm_wInner_one_le_dLpNorm_mul_dLpNorm (p q : ℝ≥0∞) [p.HolderConjugate q] :
    ‖⟪f, g⟫_[𝕜]‖ ≤ dLpNorm p f * dLpNorm q g :=
  calc
    _ ≤ ⟪fun a ↦ ‖f a‖, fun a ↦ ‖g a‖⟫_[ℝ] := norm_wInner_one_le _ _
    _ ≤ (dLpNorm p fun a ↦ ‖f a‖) * dLpNorm q fun a ↦ ‖g a‖ :=
      (wInner_one_le_dLpNorm_mul_dLpNorm _ _)
    _ = dLpNorm p f * dLpNorm q g := by simp_rw [dLpNorm_norm .of_discrete]


-- @@ L99-99 verbatim
omit [Fintype α]

-- @@ L100-100 verbatim
variable [Finite α]


-- @@ L102-109 expanded
/-- **Hölder's inequality**, binary case. -/
lemma dLpNorm_mul_le (p q : ℝ≥0∞) [p.HolderTriple q r] :
    dLpNorm r (f * g) ≤ dLpNorm p f * dLpNorm q g :=
  by
  cases nonempty_fintype α
  change lpNorm (f * g) r .count ≤ lpNorm f p .count * lpNorm g q .count
  have hfg : AEStronglyMeasurable (f * g) .count := .of_discrete
  grw [← toReal_eLpNorm .of_discrete, ← toReal_eLpNorm .of_discrete, ← toReal_eLpNorm .of_discrete,
    ← ENNReal.toReal_mul, ← eLpNorm_mul_le_mul_eLpNorm (r := r) .of_discrete .of_discrete]
  exact (ENNReal.mul_lt_top eLpNorm_lt_top_of_finite eLpNorm_lt_top_of_finite).ne


-- @@ L111-131 expanded
/-- **Hölder's inequality**, finitary case. -/
lemma dLpNorm_prod_le {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {p : ι → ℝ≥0} (hp : ∀ i, p i ≠ 0)
    (q : ℝ≥0) (hpq : ∑ i ∈ s, ((p i)⁻¹ : ℝ≥0∞) = (q : ℝ≥0∞)⁻¹) (f : ι → α → 𝕜) :
    dLpNorm q (∏ i ∈ s, f i) ≤ ∏ i ∈ s, dLpNorm (p i) (f i) := by
  induction s using Finset.cons_induction generalizing q with
  | empty => cases not_nonempty_empty hs
  | cons i s hi ih =>
    obtain rfl | hs := s.eq_empty_or_nonempty
    · simp only [sum_cons, sum_empty, add_zero, inv_inj] at hpq
      simp [← hpq]
    simp_rw [prod_cons]
    rw [sum_cons, ← inv_inv (∑ _ ∈ _, _)] at hpq
    have : ENNReal.HolderTriple (p i) (↑(∑ i ∈ s, (p i)⁻¹)⁻¹) q :=
      ⟨by
        simpa [ENNReal.coe_inv (by simpa [hp] : (∑ j ∈ s, (p j)⁻¹ : ℝ≥0) ≠ 0), ENNReal.coe_inv,
          hp] using hpq⟩
    grw [dLpNorm_mul_le (p i) ↑(∑ i ∈ s, (p i)⁻¹)⁻¹, ih hs]
    rw [← ENNReal.coe_inv, inv_inv]
    · push_cast
      congr! with i
      exact (ENNReal.coe_inv <| hp _).symm
    · simpa [hp]


-- @@ L133-133 verbatim
end Hoelder

-- @@ L134-134 verbatim
end MeasureTheory
