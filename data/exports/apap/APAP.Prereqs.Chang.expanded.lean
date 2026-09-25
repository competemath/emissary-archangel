module

public import APAP.Prereqs.Energy
public import APAP.Prereqs.LargeSpec
public import Mathlib.Combinatorics.Additive.Dissociation

import AddCombi.Mathlib.Algebra.GroupWithZero.Indicator
import APAP.Prereqs.Rudin
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring.Common


-- @@ L14-16 verbatim
/-!
# Chang's lemma
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
open Finset Fintype Function MeasureTheory RCLike Real

-- @@ L21-21 verbatim
open scoped ComplexConjugate ComplexOrder NNReal Indicator


-- @@ L23-24 verbatim
variable {G : Type*} [AddCommGroup G] {f : G → ℂ} {x η : ℝ} {ψ : AddChar G ℂ}
  {Δ : Finset (AddChar G ℂ)} {m : ℕ}


-- @@ L26-26 verbatim
local notation "𝓛" x:arg => 1 + log x⁻¹


-- @@ L28-32 expanded
private lemma curlog_pos (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) : 0 < 1 + log x⁻¹ :=
  by
  obtain rfl | hx₀ := hx₀.eq_or_lt
  · simp
  have : 0 ≤ log x⁻¹ := by bound
  positivity


-- @@ L34-46 expanded
private lemma rpow_inv_neg_curlog_le (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) : x⁻¹ ^ (1 + log x⁻¹)⁻¹ ≤ exp 1 :=
  by
  obtain rfl | hx₀ := hx₀.eq_or_lt
  · simp only [inv_zero, log_zero, add_zero, inv_one, rpow_one]; positivity
  obtain rfl | hx₁ := hx₁.eq_or_lt
  · simp
  have hx := (one_lt_inv₀ hx₀).2 hx₁
  calc
    x⁻¹ ^ (1 + log x⁻¹)⁻¹ ≤ x⁻¹ ^ (log x⁻¹)⁻¹ :=
      by
      gcongr
      · exact hx.le
      · exact log_pos hx
      · simp
    _ ≤ exp 1 := x⁻¹.rpow_inv_log_le_exp_one


-- @@ L48-48 verbatim
noncomputable def changConst : ℝ := 32 * exp 1


-- @@ L50-50 verbatim
lemma one_lt_changConst : 1 < changConst := by unfold changConst; bound


-- @@ L52-52 verbatim
lemma changConst_pos : 0 < changConst := zero_lt_one.trans one_lt_changConst


-- @@ L54-54 verbatim
namespace Mathlib.Meta.Positivity

-- @@ L55-55 verbatim
open Lean.Meta Qq


-- @@ L57-61 verbatim
/-- Extension for the `positivity` tactic: `changConst` is positive. -/
@[positivity changConst] meta def evalChangConst : PositivityExt where eval _ pα? _ :=
  match pα? with
  | none => pure .none
  | some _ => pure (.positive (q(changConst_pos) : Lean.Expr))


-- @@ L63-63 verbatim
example : 0 < changConst := by positivity


-- @@ L65-65 verbatim
end Mathlib.Meta.Positivity


-- @@ L67-86 expanded
lemma AddDissociated.boringEnergy_le [MeasurableSpace G] [DiscreteMeasurableSpace G] [DecidableEq G]
    [Finite G] {s : Finset G} (hs : AddDissociated (s : Set G)) (n : ℕ) :
    boringEnergy n s ≤ changConst ^ n * n ^ n * #s ^ n :=
  by
  cases nonempty_fintype G
  obtain rfl | hn := eq_or_ne n 0
  · simp
  calc
    _ = (cLpNorm (↑(2 * n)) (dft 𝟭_[(s : Set G)]) ^ (2 * n) : ℝ) := by
      rw [cLpNorm_dft_indicator_one_pow]
    _ ≤ (4 * rexp 2⁻¹ * sqrt ↑(2 * n) * cLpNorm 2 (dft 𝟭_[(s : Set G)])) ^ (2 * n) :=
      by
      gcongr
      refine
        rudin_ineq (le_mul_of_one_le_right zero_le_two <| Nat.one_le_iff_ne_zero.2 hn)
          (dft 𝟭_[(s : Set G), ℂ]) ?_
      rwa [cft_dft, support_comp_eq_preimage, Set.support_indicator_one, Set.preimage_comp,
        Set.neg_preimage, addDissociated_neg, AddEquiv.addDissociated_preimage]
    _ = _ := by
      simp_rw [mul_pow, pow_mul, cL2Norm_dft_indicator_one]
      rw [← exp_nsmul, sq_sqrt (by positivity), sq_sqrt (by positivity)]
      simp_rw [← mul_pow]
      simp [changConst]
      ring_nf


-- @@ L88-88 verbatim
local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s


-- @@ L90-90 verbatim
variable [Fintype G] [MeasurableSpace G] [DiscreteMeasurableSpace G]


-- @@ L92-96 expanded
private lemma α_le_one (f : G → ℂ) : dLpNorm 1 f ^ 2 / dLpNorm 2 f ^ 2 / card G ≤ 1 :=
  by
  refine div_le_one_of_le₀ (div_le_of_le_mul₀ ?_ ?_ ?_) ?_
  any_goals positivity
  rw [dL1Norm_eq_sum_norm, dL2Norm_sq_eq_sum_norm]
  exact sq_sum_le_card_mul_sum_sq


-- @@ L98-165 expanded
lemma general_hoelder (hη : 0 ≤ η) (ν : G → ℝ≥0) (hfν : ∀ x, f x ≠ 0 → 1 ≤ ν x)
    (hΔ : Δ ⊆ largeSpec f η) (hm : m ≠ 0) :
    #Δ ^ (2 * m) * (η ^ (2 * m) * (dLpNorm 1 f ^ 2 / dLpNorm 2 f ^ 2)) ≤
      energy m Δ (dft fun a ↦ ν a) :=
  by
  obtain rfl | hf := eq_or_ne f 0
  · simp
  choose c norm_c hc using fun γ ↦ RCLike.exists_norm_eq_mul_self (dft f γ)
  have :=
    calc
      η * dLpNorm 1 f * #Δ ≤ ∑ γ ∈ Δ, ‖dft f γ‖ := ?_
      _ ≤ ‖∑ x, f x * ∑ γ ∈ Δ, c γ * conj (γ x)‖ := ?_
      _ ≤ ∑ x, ‖f x * ∑ γ ∈ Δ, c γ * conj (γ x)‖ := (norm_sum_le _ _)
      _ = ∑ x, ‖f x‖ * ‖∑ γ ∈ Δ, c γ * conj (γ x)‖ := by simp_rw [norm_mul]
      _ ≤ _ :=
        (inner_le_weight_mul_Lp_of_nonneg _ (p := m) ?_ _ _ (fun _ ↦ norm_nonneg _) fun _ ↦
          norm_nonneg _)
      _ =
          dLpNorm 1 f ^ (1 - (m : ℝ)⁻¹) *
            (∑ x, ‖f x‖ * ‖∑ γ ∈ Δ, c γ * conj (γ x)‖ ^ m) ^ (m⁻¹ : ℝ) :=
        by simp_rw [dL1Norm_eq_sum_norm, rpow_natCast]
  rotate_left
  · rw [← nsmul_eq_mul']
    exact card_nsmul_le_sum _ _ _ fun x hx ↦ mem_largeSpec.1 <| hΔ hx
  · simp_rw [mul_sum, mul_comm (f _), mul_assoc (c _), @sum_comm _ _ G, ← mul_sum, ← inner_apply', ←
      wInner_one_eq_sum, ← dft_apply, ← hc, ← RCLike.ofReal_sum, RCLike.norm_ofReal]
    exact le_abs_self _
  · norm_cast
    exact hm.bot_lt
  replace this := pow_le_pow_left₀ (by positivity) this m
  simp_rw [mul_pow] at this
  rw [rpow_inv_natCast_pow _ hm, ← rpow_mul_natCast, one_sub_mul, inv_mul_cancel₀, ← Nat.cast_pred,
    rpow_natCast, mul_assoc, mul_left_comm, ← pow_sub_one_mul, mul_assoc,
    mul_le_mul_iff_right₀] at this
  any_goals positivity
  replace hfν : ∀ x, ‖f x‖ ≤ ‖f x‖ * sqrt (ν x) :=
    by
    rintro x
    obtain hfx | hfx := eq_or_ne (f x) 0
    · simp [hfx]
    ·
      exact
        le_mul_of_one_le_right (norm_nonneg _) <| one_le_sqrt.2 <| NNReal.one_le_coe.2 <| hfν _ hfx
  replace this :=
    calc
      (dLpNorm 1 f * (η ^ m * #Δ ^ m)) ^ 2 ≤ (∑ x, ‖f x‖ * ‖∑ γ ∈ Δ, c γ * conj (γ x)‖ ^ m) ^ 2 :=
        by gcongr
      _ ≤ (∑ x, ‖f x‖ * sqrt (ν x) * ‖∑ γ ∈ Δ, c γ * conj (γ x)‖ ^ m) ^ 2 := by gcongr with x;
        exact hfν _
      _ = (∑ x, ‖f x‖ * (sqrt (ν x) * ‖∑ γ ∈ Δ, c γ * conj (γ x)‖ ^ m)) ^ 2 := by
        simp_rw [mul_assoc]
      _ ≤ (∑ x, ‖f x‖ ^ 2) * ∑ x, (sqrt (ν x) * ‖∑ γ ∈ Δ, c γ * conj (γ x)‖ ^ m) ^ 2 :=
        (sum_mul_sq_le_sq_mul_sq _ _ _)
      _ ≤ dLpNorm 2 f ^ 2 * ∑ x, ν x * (‖∑ γ ∈ Δ, c γ * conj (γ x)‖ ^ 2) ^ m :=
        by
        simp_rw [dL2Norm_sq_eq_sum_norm, mul_pow, sq_sqrt (NNReal.coe_nonneg _), pow_right_comm]
        rfl
  rw [mul_rotate', mul_left_comm, mul_pow, mul_pow, ← pow_mul', ← pow_mul', ←
    div_le_iff₀' (by positivity), mul_div_assoc, mul_div_assoc] at this
  calc
    _ ≤ _ := this
    _ = ‖(_ : ℂ)‖ := (Eq.symm <| RCLike.norm_of_nonneg <| sum_nonneg fun _ _ ↦ by positivity)
    _ =
        ‖∑ γ ∈ Δ ^^ m,
            ∑ δ ∈ Δ ^^ m,
              (∏ i, conj (c (γ i)) * c (δ i)) * conj (dft (fun a ↦ ν a) (∑ i, γ i - ∑ i, δ i))‖ :=
      ?_
    _ ≤
        ∑ γ ∈ Δ ^^ m,
          ∑ δ ∈ Δ ^^ m,
            ‖(∏ i, conj (c (γ i)) * c (δ i)) * conj (dft (fun a ↦ ν a) (∑ i, γ i - ∑ i, δ i))‖ :=
      ((norm_sum_le _ _).trans <| sum_le_sum fun _ _ ↦ norm_sum_le _ _)
    _ = _ := by simp [energy, norm_c, norm_prod]
  · push_cast
    simp_rw [← RCLike.conj_mul, dft_apply, wInner_one_eq_sum, inner_apply', map_sum, map_mul,
      RCLike.conj_conj, mul_pow, sum_pow', sum_mul, mul_sum, @sum_comm _ _ G, ←
      AddChar.inv_apply_eq_conj, ← AddChar.neg_apply', prod_mul_prod_comm, ← AddChar.add_apply, ←
      AddChar.sum_apply, mul_left_comm (Algebra.cast (ν _ : ℝ) : ℂ), ← mul_sum, ← sub_eq_add_neg,
      sum_sub_distrib, Complex.conj_ofReal, mul_comm (Algebra.cast (ν _ : ℝ) : ℂ)]
    rfl


-- @@ L167-167 verbatim
open scoped ComplexOrder


-- @@ L169-174 expanded
lemma spec_hoelder (hη : 0 ≤ η) (hΔ : Δ ⊆ largeSpec f η) (hm : m ≠ 0) :
    #Δ ^ (2 * m) * (η ^ (2 * m) * (dLpNorm 1 f ^ 2 / dLpNorm 2 f ^ 2 / card G)) ≤
      boringEnergy m Δ :=
  by
  have hG : (0 : ℝ) < card G := by positivity
  simpa [boringEnergy, mul_assoc, ← Pi.one_def, ← mul_div_right_comm, ← mul_div_assoc,
    div_le_iff₀ hG, energy_nsmul, -nsmul_eq_mul, ← nsmul_eq_mul'] using
    general_hoelder hη 1 (fun (_ : G) _ ↦ le_rfl) hΔ hm


-- @@ L176-208 expanded
/-- **Chang's lemma**. -/
lemma chang (hf : f ≠ 0) (hη : 0 < η) :
    ∃ Δ,
      Δ ⊆ largeSpec f η ∧
        #Δ ≤
            ⌈changConst * exp 1 * ⌈1 + log (↑(dLpNorm 1 f ^ 2 / dLpNorm 2 f ^ 2 / card G))⁻¹⌉₊ /
                η ^ 2⌉₊ ∧
          largeSpec f η ⊆ Δ.addSpan :=
  by
  refine exists_subset_addSpan_card_le_of_forall_addDissociated fun Δ hΔη hΔ ↦ ?_
  obtain hΔ' | hΔ' := eq_zero_or_pos #Δ
  · simp [hΔ']
  let α := dLpNorm 1 f ^ 2 / dLpNorm 2 f ^ 2 / card G
  have : 0 < α := by positivity
  set β := ⌈1 + log α⁻¹⌉₊
  have hβ : 0 < β := Nat.ceil_pos.2 (curlog_pos (by positivity) <| α_le_one _)
  have : 0 < dLpNorm 1 f := by positivity
  refine
    le_of_pow_le_pow_left₀ hβ.ne' zero_le <|
      Nat.cast_le.1 <| le_of_mul_le_mul_right ?_ (by positivity : 0 < #Δ ^ β * (η ^ (2 * β) * α))
  push_cast
  rw [← mul_assoc, ← pow_add, ← two_mul]
  refine ((spec_hoelder hη.le hΔη hβ.ne').trans <| hΔ.boringEnergy_le _).trans ?_
  refine le_trans ?_ <| mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ?_ (Nat.le_ceil _) _) ?_
  any_goals positivity
  rw [mul_right_comm, div_pow, mul_pow, mul_pow, exp_one_pow, ← pow_mul, mul_div_assoc]
  calc
    _ = (changConst * #Δ * β) ^ β := by ring
    _ ≤ (changConst * #Δ * β) ^ β * (α * exp β) := ?_
    _ ≤ (changConst * #Δ * β) ^ β * ((η / η) ^ (2 * β) * α * exp β) := by
      rw [div_self hη.ne', one_pow, one_mul]
    _ = _ := by ring
  refine le_mul_of_one_le_right (by positivity) ?_
  rw [← inv_le_iff_one_le_mul₀' (by positivity)]
  calc
    α⁻¹ = exp (0 + log α⁻¹) := by rw [zero_add, exp_log]; positivity
    _ ≤ exp ⌈0 + log α⁻¹⌉₊ := by gcongr; exact Nat.le_ceil _
    _ ≤ exp β := by unfold β; gcongr; exact zero_le_one

