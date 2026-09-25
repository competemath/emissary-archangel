module

public import APAP.Prereqs.Convolution.Discrete.Defs
public import APAP.Prereqs.LpNorm.Discrete.Defs
public import Mathlib.Analysis.RCLike.Inner

import APAP.Prereqs.LpNorm.Discrete.Basic
import Mathlib.Algebra.Order.Star.Conjneg
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Positivity


-- @@ L13-18 verbatim
/-!
# Norm of a convolution

This file characterises the L1-norm of the convolution of two functions and proves the Young
convolution inequality.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
open Finset Function MeasureTheory RCLike Real

-- @@ L23-23 verbatim
open scoped ComplexConjugate ENNReal NNReal Pointwise translate


-- @@ L25-25 verbatim
variable {G 𝕜 : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]


-- @@ L27-27 verbatim
section RCLike

-- @@ L28-28 verbatim
variable [RCLike 𝕜] {p : ℝ≥0∞}


-- @@ L30-32 expanded
lemma ddconv_eq_wInner_one (f g : G → 𝕜) (a : G) :
    (ddconv f g) a = ⟪conj f, τ a fun x ↦ g (-x)⟫_[𝕜] := by
  simp [wInner_one_eq_sum, ddconv_eq_sum_sub', mul_comm]


-- @@ L34-35 expanded
lemma dddconv_eq_wInner_one (f g : G → 𝕜) (a : G) : (dddconv f g) a = conj ⟪f, τ a g⟫_[𝕜] := by
  simp [wInner_one_eq_sum, dddconv_eq_sum_sub', map_sum, mul_comm]


-- @@ L37-49 expanded
lemma wInner_one_dddconv (f g h : G → 𝕜) :
    ⟪f, dddconv g h⟫_[𝕜] = ⟪conj g, ddconv (conj f) (conj h)⟫_[𝕜] := by
  calc
    _ = ∑ b, ∑ a, g a * conj (h b) * conj (f (a - b)) :=
      by
      simp_rw [wInner_one_eq_sum, RCLike.inner_apply, sum_dddconv_mul]
      exact sum_comm
    _ = ∑ b, ∑ a, conj (f a) * conj (h b) * g (a + b) :=
      by
      simp_rw [← Fintype.sum_prod_type']
      exact
        Fintype.sum_equiv ((Equiv.refl _).prodShear Equiv.subRight) _ _
          (by simp [mul_rotate, mul_right_comm])
    _ = _ :=
      by
      simp_rw [wInner_one_eq_sum, RCLike.inner_apply, sum_ddconv_mul, Pi.conj_apply,
        RCLike.conj_conj]
      exact sum_comm


-- @@ L51-52 expanded
lemma wInner_one_ddconv (f g h : G → 𝕜) :
    ⟪f, ddconv g h⟫_[𝕜] = ⟪conj g, dddconv (conj f) (conj h)⟫_[𝕜] := by
  simp_rw [wInner_one_dddconv, RCLike.conj_conj]


-- @@ L54-55 expanded
lemma dddconv_wInner_one (f g h : G → 𝕜) :
    ⟪dddconv f g, h⟫_[𝕜] = ⟪ddconv (conj h) (conj g), conj f⟫_[𝕜] := by
  rw [← conj_wInner_symm, wInner_one_dddconv, conj_wInner_symm]


-- @@ L57-58 expanded
lemma ddconv_wInner_one (f g h : G → 𝕜) :
    ⟪ddconv f g, h⟫_[𝕜] = ⟪dddconv (conj h) (conj g), conj f⟫_[𝕜] := by
  rw [← conj_wInner_symm, wInner_one_ddconv, conj_wInner_symm]


-- @@ L60-62 expanded
lemma dddconv_wInner_one_eq_wInner_one_ddconv (f g h : G → 𝕜) :
    ⟪dddconv f g, h⟫_[𝕜] = ⟪f, ddconv h g⟫_[𝕜] := by rw [dddconv_wInner_one];
  simp [wInner_one_eq_sum, mul_comm]


-- @@ L64-66 expanded
lemma wInner_one_dddconv_eq_ddconv_wInner_one (f g h : G → 𝕜) :
    ⟪f, dddconv h g⟫_[𝕜] = ⟪ddconv f g, h⟫_[𝕜] := by rw [wInner_one_dddconv];
  simp [wInner_one_eq_sum, mul_comm]


-- @@ L68-68 verbatim
variable [MeasurableSpace G] [DiscreteMeasurableSpace G]


-- @@ L70-78 expanded
omit [Fintype G] in
@[simp]
lemma dLpNorm_trivChar [Finite G] (hp : p ≠ 0) : dLpNorm p (trivChar : G → 𝕜) = 1 :=
  by
  cases nonempty_fintype G
  obtain _ | p := p
  · simp only [ENNReal.none_eq_top, dLinftyNorm_eq_iSup_norm, trivChar_apply, apply_ite, norm_one,
      norm_zero]
    exact IsLUB.ciSup_eq ⟨by aesop  (add simp mem_upperBounds), fun x hx ↦ hx ⟨0, ite_eq_left rfl⟩⟩
  · simp at hp
    simp [dLpNorm_eq_sum_norm hp, apply_ite, hp]


-- @@ L80-129 expanded
/-- A special case of **Young's convolution inequality**. -/
lemma dLpNorm_ddconv_le {p : ℝ≥0} (hp : 1 ≤ p) (f g : G → 𝕜) :
    dLpNorm p (ddconv f g) ≤ dLpNorm p f * dLpNorm 1 g :=
  by
  obtain rfl | hp := hp.eq_or_lt
  · simp_rw [ENNReal.coe_one, dL1Norm_eq_sum_norm, sum_mul_sum, ddconv_eq_sum_sub']
    calc
      ∑ x, ‖∑ y, f y * g (x - y)‖ ≤ ∑ x, ∑ y, ‖f y * g (x - y)‖ :=
        sum_le_sum fun x _ ↦ norm_sum_le _ _
      _ = _ := ?_
    rw [sum_comm]
    simp_rw [norm_mul]
    exact sum_congr rfl fun x _ ↦ Fintype.sum_equiv (Equiv.subRight x) _ _ fun _ ↦ rfl
  have hp₀ := zero_lt_one.trans hp
  rw [← rpow_le_rpow_iff _ _ hp₀, mul_rpow]
  any_goals positivity
  dsimp
  simp_rw [dLpNorm_rpow_eq_sum_norm hp₀.ne', ddconv_eq_sum_sub']
  have hpconj : (p : ℝ).HolderConjugate (1 - (p : ℝ)⁻¹)⁻¹ := ⟨by simp, mod_cast hp₀, by bound⟩
  have (x : G) :
    ‖∑ y, f y * g (x - y)‖ ^ (p : ℝ) ≤
      (∑ y, ‖f y‖ ^ (p : ℝ) * ‖g (x - y)‖) * (∑ y, ‖g (x - y)‖) ^ (p - 1 : ℝ) :=
    by
    rw [← le_rpow_inv_iff_of_pos, mul_rpow, ← rpow_mul, sub_one_mul, mul_inv_cancel₀]
    any_goals positivity
    calc
      _ ≤ ∑ y, ‖f y * g (x - y)‖ := norm_sum_le _ _
      _ = ∑ y, ‖f y‖ * ‖g (x - y)‖ ^ (p : ℝ)⁻¹ * ‖g (x - y)‖ ^ (1 - (p : ℝ)⁻¹) := ?_
      _ ≤ _ := (inner_le_Lp_mul_Lq _ _ _ hpconj)
      _ = _ := ?_
    · congr with t
      rw [norm_mul, mul_assoc, ← rpow_add' (by positivity), add_sub_cancel, rpow_one]
      simp
    · have : 1 - (p : ℝ)⁻¹ ≠ 0 := sub_ne_zero.2 (inv_ne_one.2 <| NNReal.coe_ne_one.2 hp.ne').symm
      simp [mul_rpow, rpow_nonneg, hp₀.ne', this, abs_rpow_of_nonneg]
  calc
    ∑ x, ‖∑ y, f y * g (x - y)‖ ^ (p : ℝ) ≤
        ∑ x, (∑ y, ‖f y‖ ^ (p : ℝ) * ‖g (x - y)‖) * (∑ y, ‖g (x - y)‖) ^ (p - 1 : ℝ) :=
      sum_le_sum fun i _ ↦ this _
    _ = _ := ?_
  have hg : ∀ x, ∑ y, ‖g (x - y)‖ = dLpNorm 1 g :=
    by
    simp_rw [dL1Norm_eq_sum_norm]
    exact fun x ↦ Fintype.sum_equiv (Equiv.subLeft _) _ _ fun _ ↦ rfl
  have hg' : ∀ y, ∑ x, ‖g (x - y)‖ = dLpNorm 1 g :=
    by
    simp_rw [dL1Norm_eq_sum_norm]
    exact fun x ↦ Fintype.sum_equiv (Equiv.subRight _) _ _ fun _ ↦ rfl
  simp_rw [hg]
  rw [← sum_mul, sum_comm]
  simp_rw [← mul_sum, hg']
  rw [← sum_mul, mul_assoc, ← rpow_one_add' (by positivity), add_sub_cancel]
  rw [add_sub_cancel]
  positivity


-- @@ L131-134 expanded
/-- A special case of **Young's convolution inequality**. -/
lemma dLpNorm_dddconv_le {p : ℝ≥0} (hp : 1 ≤ p) (f g : G → 𝕜) :
    dLpNorm p (dddconv f g) ≤ dLpNorm p f * dLpNorm 1 g := by
  simpa only [ddconv_conjneg, dLpNorm_conjneg] using dLpNorm_ddconv_le hp f (conjneg g)


-- @@ L136-136 verbatim
end RCLike


-- @@ L138-138 verbatim
section Real

-- @@ L139-141 verbatim
variable [MeasurableSpace G] [DiscreteMeasurableSpace G] {f g : G → ℝ} {n : ℕ}

--TODO: Include `f : G → ℂ`

-- @@ L142-145 expanded
lemma dL1Norm_ddconv (hf : 0 ≤ f) (hg : 0 ≤ g) :
    dLpNorm 1 (ddconv f g) = dLpNorm 1 f * dLpNorm 1 g :=
  by
  have : ∀ x, 0 ≤ ∑ y, f y * g (x - y) := fun x ↦ sum_nonneg fun y _ ↦ mul_nonneg (hf _) (hg _)
  simp [dL1Norm_eq_sum_norm, ← sum_ddconv, ddconv_eq_sum_sub', norm_of_nonneg (this _),
    norm_of_nonneg (hf _), norm_of_nonneg (hg _)]


-- @@ L147-148 expanded
lemma dL1Norm_dddconv (hf : 0 ≤ f) (hg : 0 ≤ g) :
    dLpNorm 1 (dddconv f g) = dLpNorm 1 f * dLpNorm 1 g := by
  simpa using dL1Norm_ddconv hf (conjneg_nonneg.2 hg)


-- @@ L150-150 verbatim
end Real
