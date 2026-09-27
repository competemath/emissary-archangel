/-
Copyright (c) 2026 Dominique Lawson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominique Lawson, Henning Basold, Peter Bruin
-/
module

public import LeanPool.DirectedTopologyLean4.SplitPath.SplitDipath
import LeanPool.DirectedTopologyLean4.FractionEqualities
import LeanPool.DirectedTopologyLean4.UnitIntervalAux
import Mathlib.CategoryTheory.Category.Init


-- @@ L13-13 verbatim
/-! ### General -/


-- @@ L15-19 verbatim
@[expose] public section

/-
  This file contains many lemmas about relations that the parts of a split path satisfy.
-/


-- @@ L21-21 verbatim
open scoped unitInterval

-- @@ L22-22 verbatim
open SplitDipath Set


-- @@ L24-24 verbatim
noncomputable section


-- @@ L26-26 verbatim
universe u


-- @@ L28-28 verbatim
variable {X : Type u} [DirectedSpace X] {x₀ x₁ : X}


-- @@ L30-34 verbatim
namespace SplitProperties


--TODO: Rework some of these statement to make them more general: that should make proving the
-- specfic versions easier.



-- @@ L37-38 verbatim
lemma firstPart_cast {x₀' x₁' : X} (γ : Dipath x₀ x₁) (hx₀ : x₀' = x₀) (hx₁ : x₁' = x₁) (T : I) :
  (FirstPart (γ.cast hx₀ hx₁) T) = (FirstPart γ T).cast hx₀ rfl := rfl


-- @@ L40-41 verbatim
lemma secondPart_cast {x₀' x₁' : X} (γ : Dipath x₀ x₁) (hx₀ : x₀' = x₀) (hx₁ : x₁' = x₁) (T : I) :
  (SecondPart (γ.cast hx₀ hx₁) T) = (SecondPart γ T).cast rfl hx₁ := rfl


-- @@ L43-44 verbatim
lemma firstPart_eq_of_split_point_eq (γ : Dipath x₀ x₁) {T T' : I} (hT : T = T') :
  (FirstPart γ T) = (FirstPart γ T').cast rfl (congr_arg γ hT) := by subst_vars; rfl


-- @@ L46-47 verbatim
lemma secondPart_eq_of_split_point_eq (γ : Dipath x₀ x₁) {T T' : I} (hT : T = T') :
  (SecondPart γ T) = (SecondPart γ T').cast (congr_arg γ hT) rfl := by subst_vars; rfl


-- @@ L49-50 verbatim
lemma firstPart_eq_of_point_eq (γ : Dipath x₀ x₁) {T T' : I} (h : T = T') (t : I) :
  (FirstPart γ T) t = (FirstPart γ T') t := by subst_vars; rfl


-- @@ L52-53 verbatim
lemma secondPart_eq_of_point_eq (γ : Dipath x₀ x₁) {T T' : I} (h : T = T') (t : I) :
  (SecondPart γ T) t = (SecondPart γ T') t := by subst_vars; rfl


-- @@ L55-57 verbatim
lemma interval_cast {γ : Dipath x₀ x₁} {A : Set X} {a b a' b' : I} (h_im : A = γ '' Icc a b)
      (ha : a' = a) (hb : b' = b) :
    A = γ '' Icc a' b' := by subst_vars; rfl



-- @@ L60-60 verbatim
/-! ### First Part -/


-- @@ L62-95 verbatim
lemma firstPart_image (γ : Dipath x₀ x₁) (T a b : I) (h_ab : a ≤ b) :
    (FirstPart γ T) '' Icc a b = γ '' Icc (T * a) (T * b) := by
  ext z
  constructor
  · rintro ⟨t, t_a_b, ht⟩
    rw [first_part_apply] at ht
    use T * t
    constructor
    constructor
    · exact Subtype.coe_le_coe.mp <| mul_le_mul_of_nonneg_left (Subtype.coe_le_coe.mpr t_a_b.1)
        T.2.1
    · exact Subtype.coe_le_coe.mp <| mul_le_mul_of_nonneg_left (Subtype.coe_le_coe.mpr t_a_b.2)
        T.2.1
    · exact ht
  · rintro ⟨t, t_Ta_Tb, ht⟩
    by_cases h : T = 0
    · exact ⟨a, ⟨le_rfl, h_ab⟩, by simp_all⟩
    have hT : 0 < T := lt_of_le_of_ne unitInterval.nonneg' (show T ≠ 0 by exact h).symm
    have h₁ : (a : ℝ) ≤ (t / T : ℝ) :=
      (le_div_iff₀ (Subtype.coe_lt_coe.mpr hT)).mpr <|
        mul_comm (a : ℝ) T ▸ Subtype.coe_le_coe.mpr t_Ta_Tb.1
    have h₂ : (t / T : ℝ) ≤ b :=
      (div_le_iff₀ (Subtype.coe_lt_coe.mpr hT)).mpr <|
        mul_comm (b : ℝ) T ▸ Subtype.coe_le_coe.mpr t_Ta_Tb.2
    use ⟨t / T, le_trans a.2.1 h₁, le_trans h₂ b.2.2⟩
    constructor
    · exact ⟨h₁, h₂⟩
    · rw [first_part_apply]
      convert ht using 2
      apply Subtype.coe_inj.mp
      change (T : ℝ) * ((t : ℝ) / T) = t
      rw [mul_div_left_comm, div_self]
      · exact mul_one (t : ℝ)
      · exact unitInterval.coe_ne_zero.mpr h


-- @@ L97-100 verbatim
lemma firstPart_range (γ : Dipath x₀ x₁) (T : I) :
    range (FirstPart γ T) = (γ '' Icc 0 T) := by
  rw [Dipath.range_eq_image_I _]
  convert firstPart_image γ T 0 1 zero_le_one <;> norm_num


-- @@ L102-104 verbatim
lemma firstPart_range_interval (γ : Dipath x₀ x₁) {n : ℕ} (h : 0 < n) :
    range (FirstPart γ (Fraction.ofPos h)) = γ ''  Icc 0 (Fraction.ofPos h) :=
  firstPart_range γ (Fraction.ofPos h)


-- @@ L106-109 verbatim
lemma firstPart_range_interval_coe (γ : Dipath x₀ x₁) {n : ℕ} (h : 0 < n) :
    range (FirstPart γ (Fraction.ofPos h)) = γ.extend '' Icc 0 (1 / (↑n)) := by
  rw [firstPart_range_interval γ h, ←Dipath.image_extend_eq_image, Fraction.ofPos_coe]
  rfl


-- @@ L111-136 verbatim
/-- If `γ` is a path, then the image of `[i/(d+1), (i+1)/(d+1)]` under `γ` split at `(d+1)/(n+1)` is
the
image of `[i/(n+1), (i+1)/(n+1)]` under `γ`
-/
lemma firstPart_range_interval_partial (γ : Dipath x₀ x₁) {n d i : ℕ} (hd : d.succ < n.succ)
    (hi : i < d.succ) :
  (FirstPart γ (Fraction (Nat.succ_pos n) (le_of_lt hd))) '' Icc -- First part at (d + 1)/(n + 1)
    (Fraction (Nat.succ_pos d) (le_of_lt hi)) -- frac i/(d+1)
    (Fraction (Nat.succ_pos d) (Nat.succ_le_of_lt hi)) -- frac (i+1)/(d+1)
    = γ ''  Icc
    (Fraction (Nat.succ_pos n) (le_of_lt (lt_trans hi hd))) -- frac i/(n+1)
    (Fraction (Nat.succ_pos n) (Nat.succ_le_of_lt (lt_trans hi hd))) -- frac (i+1)/(n+1)
  := by
  convert firstPart_image γ (Fraction (Nat.succ_pos n) (le_of_lt hd))
    (Fraction (Nat.succ_pos d) (le_of_lt hi)) (Fraction (Nat.succ_pos d) (Nat.succ_le_of_lt hi))
    (show _ ≤ _ by
      rw [← Subtype.coe_le_coe]
      simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
      apply div_le_div_of_nonneg_right (by linarith : (i : ℝ) ≤ i + 1)
        (by positivity)) <;>
  simp only [Nat.succ_eq_add_one] <;>
  apply Subtype.coe_inj.mp <;>
  simp only [Nat.cast_add, Nat.cast_one, Icc.coe_mul] <;>
  refine (FractionEqualities.frac_cancel' ?_).symm <;>
  rw [←Nat.cast_succ] <;>
  exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero d)


-- @@ L138-149 verbatim
/-- If `γ` is a path, then the image of `[i/(d+1), (i+1)/(d+1)]` under `γ` split at `(d+1)/(n+1)` is
the
image of `[i/(n+1), (i+1)/(n+1)]` under `γ`.
-/
lemma firstPart_range_interval_partial_coe (γ : Dipath x₀ x₁) {n d i : ℕ} (hd : d.succ < n.succ)
    (hi : i < d.succ) :
    (FirstPart γ (Fraction (Nat.succ_pos n) (le_of_lt hd))).extend '' Icc (↑i/(↑d+1))
        ((↑i+1)/(↑d+1))
      = γ.extend ''  Icc (↑i/(↑n+1)) ((↑i+1)/(↑n+1)) := by
  have := firstPart_range_interval_partial γ hd hi
  rw [←Dipath.image_extend_eq_image, ←Dipath.image_extend_eq_image] at this
  convert this <;> exact (Nat.cast_succ _).symm


-- @@ L151-151 verbatim
/-! ### Second Part -/


-- @@ L153-188 verbatim
lemma secondPart_image (γ : Dipath x₀ x₁) (T a b : I) (h_ab : a ≤ b) :
    (SecondPart γ T) '' Icc a b = γ '' Icc
      ⟨σ T * a + T, interp_left_mem_I T a⟩
      ⟨σ T * b + T, interp_left_mem_I T b⟩ := by
  ext z
  constructor
  · rintro ⟨t, t_a_b, ht⟩
    rw [second_part_apply] at ht
    use ⟨σ T * t + T, interp_left_mem_I T t⟩
    exact ⟨⟨unitIAux.interp_left_le_of_le T t_a_b.1, unitIAux.interp_left_le_of_le T t_a_b.2⟩, ht⟩
  · rintro ⟨t, t_Ta_Tb, ht⟩
    by_cases h : T = 1
    · exact ⟨a, ⟨le_rfl, h_ab⟩, by simp_all⟩
    have hT : T < 1 := lt_of_le_of_ne unitInterval.le_one' (show T ≠ 1 by exact h)
    have : (T : ℝ) < 1 := Subtype.coe_lt_coe.mpr hT
    have : (σ T : ℝ) > 0 := show (1 - T : ℝ) > 0 by linarith
    have h₁ : (a : ℝ) ≤ ((t - T) / (σ T) : ℝ) := by
      apply (le_div_iff₀ this).mpr
      have hbound : (σ T : ℝ) * a  + T ≤ t := t_Ta_Tb.1
      linarith
    have h₂ : ((t - T) / (1 - T) : ℝ) ≤ b := by
      apply (div_le_iff₀ this).mpr
      have hbound : (t : ℝ) ≤ (σ T : ℝ) * b + T := t_Ta_Tb.2
      have hσT : (σ T : ℝ) = 1 - T := by simp [unitInterval.symm]
      linarith
    use ⟨(t - T) / (1 - T), le_trans a.2.1 h₁, le_trans h₂ b.2.2⟩
    constructor
    · exact ⟨h₁, h₂⟩
    · rw [second_part_apply]
      convert ht using 2
      simp only [unitInterval.coe_symm_eq]
      apply Subtype.coe_inj.mp
      change (σ T : ℝ) * ((t-T)/(σ T)) + T = t
      rw [mul_div_left_comm, div_self]
      · ring
      exact ne_of_gt this


-- @@ L190-193 verbatim
lemma secondPart_range (γ : Dipath x₀ x₁) (T : I) :
    range (SecondPart γ T) = γ '' Icc T 1  := by
  rw [Dipath.range_eq_image_I _]
  convert secondPart_image γ T 0 1 zero_le_one using 3 <;> simp


-- @@ L195-238 verbatim
/-- When γ is a dipath, an we split it on the intervals [0, 1/(n+1)] and [1/(n+1), 1], then the
image of γ of
  [(i+1)/(n+1), (i+2)/(n+1)] is equal to the image the second part of γ of [i/n, (i+1)/n]
-/
lemma secondPart_range_interval (γ : Dipath x₀ x₁) {i n : ℕ} (hi : i < n) (hn : 0 < n) :
    (SecondPart γ (Fraction.ofPos (Nat.succ_pos n))) '' Icc
      (Fraction hn (le_of_lt hi)) (Fraction hn (Nat.succ_le_of_lt hi)) =
    γ ''  Icc (Fraction (Nat.succ_pos n) (show i+1 ≤ n+1 by exact (le_of_lt (Nat.succ_lt_succ hi))))
              (Fraction (Nat.succ_pos n)
                (show i+2 ≤ n+1 by exact Nat.succ_lt_succ (Nat.succ_le_of_lt hi))) := by
  have h₁ : (n : ℝ) * ((n : ℝ) + 1)⁻¹ = (1 - ((n : ℝ) + 1)⁻¹) := by
    have : (n + 1 : ℝ) ≠ 0 := ne_of_gt (add_pos (Nat.cast_pos.mpr hn) one_pos)
    nth_rewrite 2 [(div_self this).symm]
    ring
  have h₂ : (n + 1 : ℝ)⁻¹ = (1 - ((n : ℝ) + 1)⁻¹) * (↑n)⁻¹ := by
    have : (0 : ℝ) < ↑n := by exact Nat.cast_pos.mpr hn
    calc (n + 1 : ℝ)⁻¹
      _ = (n + 1 : ℝ)⁻¹ * (n : ℝ) / (n : ℝ) :=
        (mul_div_cancel_right₀ (n + 1 : ℝ)⁻¹ (show (n : ℝ) ≠ 0 by linarith)).symm
      _ = ↑n * (↑n + 1)⁻¹ * (↑n)⁻¹ := by ring
      _ =  (1 - (↑n + 1)⁻¹) * (↑n)⁻¹ := by rw [h₁]
  apply interval_cast (secondPart_image γ (Fraction.ofPos (Nat.succ_pos n)) _ _
    (le_of_lt (Fraction.lt_frac_succ hi)))
  · rw [← Subtype.coe_inj]
    simp only [Nat.succ_eq_add_one, unitInterval.coe_symm_eq, zero_add, Nat.cast_one, Nat.cast_add,
      one_div]
    calc (i + 1 : ℝ)/(↑n + 1)
      _ = ↑i/(↑n + 1) + 1/(↑n+1)                          := by ring
      _ = ↑i/(↑n + 1) + (↑n + 1)⁻¹                        := by rw [one_div]
      _ = (↑n + 1)⁻¹ * ↑i + (↑n + 1)⁻¹                    := by rw [div_eq_inv_mul]
      _ = (1 - (↑n + 1)⁻¹) * (↑n)⁻¹ * (↑i) + (↑n + 1)⁻¹   := by rw [←h₂]
      _ = (1 - (↑n + 1)⁻¹) * ((↑n)⁻¹ * (↑i)) + (↑n + 1)⁻¹ := by ring
      _ = (1 - (↑n + 1)⁻¹) * (↑i / ↑n) + (↑n + 1)⁻¹       := by rw [←div_eq_inv_mul (i : ℝ) ↑n]
  · rw [← Subtype.coe_inj]
    simp only [Nat.succ_eq_add_one, unitInterval.coe_symm_eq, zero_add, Nat.cast_one, Nat.cast_add,
      one_div]
    calc (i + 2 : ℝ)/(↑n + 1)
      _ = (↑i + 1)/(↑n + 1) + 1/(↑n+1)                        := by ring
      _ = (↑i + 1)/(↑n + 1) + (↑n + 1)⁻¹                      := by rw [one_div]
      _ = (↑n + 1)⁻¹ * (↑i + 1) + (↑n + 1)⁻¹                  := by rw [div_eq_inv_mul]
      _ = (1 - (↑n + 1)⁻¹) * (↑n)⁻¹ * (↑i + 1) + (↑n + 1)⁻¹   := by rw [←h₂]
      _ = (1 - (↑n + 1)⁻¹) * ((↑n)⁻¹ * (↑i + 1)) + (↑n + 1)⁻¹ := by ring
      _ = (1 - (↑n + 1)⁻¹) * ((↑i + 1) / ↑n) + (↑n + 1)⁻¹
          := by rw [←div_eq_inv_mul (i + 1 : ℝ) ↑n]


-- @@ L240-255 verbatim
/-- When γ is a dipath, an we split it on the intervals [0, 1/(n+1)] and [1/(n+1), 1], then the
image of γ of
  [(i+1)/(n+1), (i+2)/(n+1)] is equal to the image the second part of γ of [i/n, (i+1)/n].
  Version with interval of real numbers
-/
lemma secondPart_range_interval_coe (γ : Dipath x₀ x₁) {i n : ℕ} (hi : i < n) (hn : 0 < n) :
    (SecondPart γ (Fraction.ofPos (Nat.succ_pos n))).extend '' Icc (↑i/↑n) ((↑i+1)/↑n) =
    γ.extend ''  Icc ((↑i+1)/(↑n+1)) ((↑i+1+1)/(↑n+1)) := by
  have := secondPart_range_interval γ hi hn
  rw [←Dipath.image_extend_eq_image, ←Dipath.image_extend_eq_image] at this
  convert this
  · exact (Nat.cast_succ i).symm
  · exact (Nat.cast_succ i).symm
  · exact (Nat.cast_succ n).symm
  · rw [←Nat.cast_succ i, ←Nat.cast_succ i.succ]
  · exact (Nat.cast_succ n).symm


-- @@ L257-301 verbatim
/-- When γ is a dipath, an we split it on the intervals [0, (d+1)/(n+1)] and [(d+1)/(n+1), 1], then
the image of γ of
  [(i+d.succ)/(n+1), (i+d.succ+1)/(n+1)]
      is equal to the image the second part of γ of [(i/(n-d), (i+1)/(n-d)].
-/
lemma secondPart_range_partial_interval (γ : Dipath x₀ x₁) {i d n : ℕ} (hd : d.succ < n.succ)
    (hi : i < n - d) :
    (SecondPart γ (Fraction (Nat.succ_pos n) (le_of_lt hd))) '' Icc
      (Fraction (Nat.sub_pos_of_lt (Nat.lt_of_succ_lt_succ hd)) (le_of_lt hi)) -- i/(n-d)
      (Fraction (Nat.sub_pos_of_lt (Nat.lt_of_succ_lt_succ hd)) (Nat.succ_le_of_lt hi))
          -- (i+1)/(n-d)
      =
    γ ''  Icc
      (Fraction (Nat.succ_pos n) (show i+d.succ ≤ n.succ by
        apply le_of_lt
        have : i < n.succ - d.succ := (Nat.succ_sub_succ n d).symm ▸ hi
        exact lt_tsub_iff_right.mp this
      )) -- (i+d+1)/(n+1)
      (Fraction (Nat.succ_pos n) (show i+d.succ + 1 ≤ n.succ by
        apply Nat.succ_le_of_lt
        have : i < n.succ - d.succ := (Nat.succ_sub_succ n d).symm ▸ hi
        exact lt_tsub_iff_right.mp this
      )) -- (i+d+2)/(n+1)
    := by
  apply interval_cast (secondPart_image γ (Fraction (Nat.succ_pos n) (le_of_lt hd)) _ _
    (le_of_lt (Fraction.lt_frac_succ hi)))
  · rw [← Subtype.coe_inj]
    simp only [Nat.succ_eq_add_one, unitInterval.coe_symm_eq, Nat.cast_add, Nat.cast_one]
    have : d < n := Nat.lt_of_succ_lt_succ hd
    rw [Nat.cast_sub (le_of_lt this)]
    apply FractionEqualities.frac_special
    · exact (ne_of_lt (Nat.cast_lt.mpr this))
    · rw [←Nat.cast_succ]
      exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  · rw [← Subtype.coe_inj]
    simp only [Nat.succ_eq_add_one, unitInterval.coe_symm_eq, Nat.cast_add, Nat.cast_one]
    have : d < n := Nat.lt_of_succ_lt_succ hd
    rw [Nat.cast_sub (le_of_lt this)]
    rw [add_assoc]
    rw [add_comm (↑d + 1 : ℝ) 1]
    rw [←add_assoc]
    apply FractionEqualities.frac_special
    · exact (ne_of_lt (Nat.cast_lt.mpr this))
    · rw [←Nat.cast_succ]
      exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)


-- @@ L303-321 verbatim
/-- When γ is a dipath, an we split it on the intervals [0, (d+1)/(n+1)] and [(d+1)/(n+1), 1], then
the image of γ of
  [(i+d.succ)/(n+1), (i+d.succ+1)/(n+1)]
      is equal to the image the second part of γ of [i/(n-d), (i+1)/(n-d)].
-/
lemma secondPart_range_partial_interval_coe (γ : Dipath x₀ x₁) {i d n : ℕ} (hd : d.succ < n.succ)
    (hi : i < n - d) :
  (SecondPart γ (Fraction (Nat.succ_pos n) (le_of_lt hd))).extend '' Icc (↑i/(↑n-↑d))
      ((↑i+1)/(↑n-↑d))
    = γ.extend ''  Icc ((↑(i+d.succ))/(↑n+1)) ((↑(i+d.succ) + 1)/(↑n+1)) := by
  have := secondPart_range_partial_interval γ hd hi
  rw [←Dipath.image_extend_eq_image, ←Dipath.image_extend_eq_image] at this
  convert this
  · exact (Nat.cast_sub (le_of_lt <| Nat.lt_of_succ_lt_succ hd)).symm
  · exact (Nat.cast_succ _).symm
  · exact (Nat.cast_sub (le_of_lt <| Nat.lt_of_succ_lt_succ hd)).symm
  · exact (Nat.cast_succ _).symm
  · exact (Nat.cast_succ _).symm
  · exact (Nat.cast_succ _).symm


-- @@ L323-323 verbatim
/-! ### Mixed Parts -/


-- @@ L325-339 verbatim
/-- Splitting a dipath `γ` at `[0, k/n]` and then at `[0, 1/k]` is the same as splitting it at `[0,
1/n]`.
-/
lemma firstPart_of_firstPart (γ : Dipath x₀ x₁) {n k : ℕ} (hkn : k < n) (hk : 0 < k) :
    FirstPart
      (FirstPart γ (Fraction (lt_trans hk hkn) (le_of_lt hkn)))
        (Fraction.ofPos hk) -- 1/k
    = (FirstPart γ (Fraction.ofPos <| lt_trans hk hkn)).cast rfl
      (show γ _ = γ _ by { congr 1; rw [←Fraction.mul_inv hk (le_of_lt hkn)]; rfl }) := by
  ext x
  change γ _ = γ _
  congr 1
  rw [←Fraction.mul_inv hk (le_of_lt hkn)]
  simp only [Nat.succ_eq_add_one, zero_add, Nat.cast_one, one_div, Icc.coe_mul, Subtype.mk.injEq]
  rw [mul_assoc]


-- @@ L341-388 verbatim
/-- Splitting a dipath `[0, (k+1)/(n+1)]` and then `[1/(k+1), 1]` is the same as
  splitting it `[1/(n+1), 1]` and then `[0, k/n]`
-/
lemma first_part_of_second_part (γ : Dipath x₀ x₁) {n k : ℕ} (hkn : k < n) (hk : 0 < k) :
  SecondPart
    (FirstPart γ (Fraction (Nat.succ_pos n) (le_of_lt <| Nat.succ_lt_succ hkn))) -- (k+1)/(n+1)
    (Fraction.ofPos (Nat.succ_pos k)) -- 1/(k+1)
  =
  (FirstPart
      (SecondPart γ (Fraction.ofPos (Nat.succ_pos n))) -- 1/(n+1)
      (Fraction (lt_trans hk hkn) (le_of_lt hkn)) -- k/n
  ).cast
    (show γ _ = γ _ by
      congr 1
      apply Subtype.coe_inj.mp
      rw [←Fraction.mul_inv (Nat.succ_pos k) (le_of_lt (Nat.succ_lt_succ hkn))]
      rfl)
    (show γ _ = γ _ by
      congr 1
      rw [← Subtype.coe_inj]
      simp only [Nat.succ_eq_add_one, unitInterval.coe_symm_eq, zero_add, Nat.cast_one,
        Nat.cast_add, one_div]
      have : (n : ℝ) > 0 := Nat.cast_pos.mpr (lt_trans hk hkn)
      rw [← one_div, FractionEqualities.one_sub_inverse_of_add_one,
        FractionEqualities.frac_cancel', ← add_div]
      · linarith
      linarith)
    := by
  ext x
  change γ _ = γ _
  congr 1
  simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, unitInterval.coe_symm_eq, zero_add,
    one_div, Subtype.mk.injEq]
  have : (k : ℝ) > 0 := Nat.cast_pos.mpr hk
  have : (n : ℝ) > 0 := Nat.cast_pos.mpr (lt_trans hk hkn)
  rw [←one_div, ←one_div]
  rw [FractionEqualities.one_sub_inverse_of_add_one _]
  · rw [FractionEqualities.one_sub_inverse_of_add_one _]
    · rw [mul_comm ((k : ℝ)/(↑k + 1)) (x : ℝ)]
      rw [mul_div, ← add_div, FractionEqualities.frac_cancel']
      · rw [← mul_assoc ((n : ℝ) / (n+1 : ℝ)) (k/n : ℝ) (x : ℝ)]
        rw [FractionEqualities.frac_cancel']
        · rw [mul_comm ((k : ℝ)/(↑n + 1)) (x : ℝ)]
          rw [mul_div, ← add_div]
        · linarith
      · linarith
    · linarith
  · linarith


-- @@ L390-442 verbatim
/-- Splitting a dipath [(k+2)/(n+2), 1] is the same as splitting it [1/(n+2), 1] and then
[(k+1)/(n+1), 1]
-/
lemma second_part_of_second_part (γ : Dipath x₀ x₁) {n k : ℕ} (hkn : k < n) :
  SecondPart
    (SecondPart γ (Fraction.ofPos (Nat.succ_pos n.succ))) -- 1/(n+2)
    (Fraction (Nat.succ_pos n) (le_of_lt <| Nat.succ_lt_succ hkn)) -- (k+1)/(n+1)
  =
  (
    SecondPart γ (Fraction (Nat.succ_pos n.succ)
      (le_of_lt <| Nat.succ_lt_succ (Nat.succ_lt_succ hkn))) -- (k+2)/(n+2)
  ).cast
    (show γ _ = γ _ by
      congr 1
      rw [← Subtype.coe_inj]
      simp only [Nat.succ_eq_add_one, unitInterval.coe_symm_eq, zero_add, Nat.cast_one,
        Nat.cast_add, one_div]
      have : (n : ℝ) + 1 > 0 := by
        rw [←Nat.cast_succ]
        exact Nat.cast_pos.mpr (Nat.succ_pos n)
      rw [←one_div, FractionEqualities.one_sub_inverse_of_add_one,
        FractionEqualities.frac_cancel', ← add_div]
      · linarith
      · linarith
    )
    rfl := by
  ext x
  change γ _ = γ _
  congr 1
  simp only [Nat.succ_eq_add_one, unitInterval.coe_symm_eq, zero_add, Nat.cast_one, Nat.cast_add,
    one_div, Subtype.mk.injEq]
  have : (n : ℝ) > 0 := Nat.cast_pos.mpr (lt_of_le_of_lt (Nat.zero_le k) hkn)
  -- Rewrite left side to ... / (n+1+1)
  rw [← one_div]
  rw [FractionEqualities.one_sub_inverse_of_add_one _]
  · rw [FractionEqualities.one_sub_frac]
    · rw [FractionEqualities.one_sub_frac]
      · rw [mul_comm (((n : ℝ) - ↑k) / _) (x : ℝ)]
        rw [mul_div]
        rw [← add_div]
        rw [FractionEqualities.frac_cancel']
        · rw [← add_div]
          -- Rewrite right side to ... / (n+1+1)
          rw [mul_comm _ (x : ℝ)]
          rw [mul_div]
          rw [← add_div]
          -- Show that numerators are equal
          congr 1
          ring
        · linarith
      · linarith
    · linarith
  · linarith


-- @@ L444-444 verbatim
/-! ### Trans Parts -/


-- @@ L446-446 verbatim
variable {x₂ : X}


-- @@ L448-455 verbatim
/-- If `γ₁` and `γ₂` are two paths, then the first part of `γ₁.trans γ₂` split at `1/2` is `γ₁`
-/
lemma first_part_trans (γ₁ : Dipath x₀ x₁) (γ₂ : Dipath x₁ x₂) :
    (FirstPart (γ₁.trans γ₂) (Fraction.ofPos two_pos)) =
      γ₁.cast rfl (Dipath.trans_eval_at_half γ₁ γ₂) := by
  ext t
  rw [first_part_apply, Dipath.trans_apply]
  simp [t.2.2]


-- @@ L457-474 verbatim
/-- If `γ₁` and `γ₂` are two paths, then the second part of `γ₁.trans γ₂` split at `1/2` is `γ₂`
-/
lemma second_part_trans (γ₁ : Dipath x₀ x₁) (γ₂ : Dipath x₁ x₂) :
    (SecondPart (γ₁.trans γ₂) (Fraction.ofPos two_pos)) =
    γ₂.cast (Dipath.trans_eval_at_half γ₁ γ₂) rfl := by
  ext t
  rw [second_part_apply, Dipath.trans_apply]
  have h_two : 2 * (2⁻¹ : ℝ) = 1 := by norm_num
  have ht : 2 * (2⁻¹ * (t : ℝ) + 2⁻¹) - 1 = ↑t := by
    rw [mul_add, ←mul_assoc, h_two]
    ring
  have hone_sub : (1 - 2⁻¹ : ℝ) = 2⁻¹ := by norm_num
  simp only [unitInterval.coe_symm_eq, Nat.succ_eq_add_one, zero_add, Nat.cast_one,
    Nat.cast_ofNat, one_div, add_le_iff_nonpos_left, Dipath.cast_coe, hone_sub]
  by_cases h : 2⁻¹ * (t : ℝ) ≤ 0
  · have hz : t = 0 := Subtype.coe_inj.mp (show (t : ℝ) = 0 by linarith [t.2.1])
    simp [hz]
  · simp [h, ht]


-- @@ L476-503 verbatim
/-- If `γ₁` and `γ₂` are two paths, then the first part of `γ₁.trans γ₂` split at `1/(2n + 2)` is
the
same as `γ₁` split at `1/(n + 1)`.
-/
lemma trans_first_part (γ₁ : Dipath x₀ x₁) (γ₂ : Dipath x₁ x₂) (n : ℕ) (t : I) :
    (FirstPart (γ₁.trans γ₂) (Fraction.ofPos (Nat.succ_pos (n + n).succ))) t =
      (FirstPart γ₁ (Fraction.ofPos (Nat.succ_pos n))) t := by
  rw [first_part_apply, first_part_apply, Dipath.trans_apply]
  simp only [Nat.succ_eq_add_one, zero_add, Nat.cast_one, Nat.cast_add, one_div]
  have : (n + n + 1 + 1 : ℝ) ≥ 2 := by
    rw [←Nat.cast_add]
    have : (↑(n + n) : ℝ) ≥ 0 := Nat.cast_nonneg (n + n)
    linarith
  have h₁ : (n + n + 1 + 1 : ℝ)⁻¹ ≤ 2⁻¹ :=
    (inv_le_inv₀ (by linarith) two_pos).mpr this
  have : (n + n + 1 + 1 : ℝ)⁻¹ * ↑t ≤ 2⁻¹ := by
    rw [← mul_one (2⁻¹ : ℝ)]
    apply mul_le_mul h₁ t.2.2 t.2.1
    norm_num
  rw [dite_eq_left this]
  apply congr_arg
  ext
  change 2 * (((n : ℝ) + n + 1 + 1)⁻¹ * ↑t) = ((n : ℝ) + 1)⁻¹ * ↑t
  rw [←mul_assoc]
  congr 1
  have : (n + n + 1 + 1 : ℝ)  = (2 * (n + 1)) := by ring
  rw [this, mul_inv, ←mul_assoc]
  norm_num


-- @@ L505-505 verbatim
namespace AuxEqualities


-- @@ L507-507 verbatim
lemma h₁ (t : I) : 0 ≤ (t : ℝ) := t.2.1

-- @@ L508-508 verbatim
lemma h₂ (n : ℕ) : 0 ≤ (n : ℝ) := Nat.cast_nonneg n

-- @@ L509-509 verbatim
lemma h₃ (n : ℕ) : (n + 1 + 1 : ℝ) ≠ 0 := by linarith [h₂ n]

-- @@ L510-510 verbatim
lemma h₄ (n : ℕ) : (↑n + ↑n + 1 + 1 + 1 + 1 : ℝ) > 0 := by linarith [h₂ n]

-- @@ L511-511 verbatim
lemma h₅ (n : ℕ) : (↑n + ↑n + 1 + 1 + 1 + 1 : ℝ) = 2 * (↑n + 1 + 1) := by ring

-- @@ L512-517 verbatim
lemma h₆ (n : ℕ) : (↑n + 1 + 1 : ℝ) / (↑n + ↑n + 1 + 1 + 1 + 1) = 2⁻¹ := by
  rw [h₅ n]
  rw [mul_comm]
  rw [div_mul_eq_div_div]
  rw [div_self (h₃ n)]
  exact one_div _

-- @@ L518-518 verbatim
lemma h₇ (n : ℕ) : (n + n + 1 + 1 + 1: ℝ) ≠ 0 := by linarith [h₂ n]

-- @@ L519-519 verbatim
lemma h₈ (n : ℕ) : (↑n + 1 + (↑n + 1) + 1 + 1 : ℝ) = (↑n + ↑n + 1 + 1 + 1 + 1) := by ring


-- @@ L521-525 verbatim
lemma e₁ (n : ℕ) (t : I) :
    (1 - (n + 1 : ℝ) / (↑n + 1 + 1)) * ↑t + (↑n + 1) / (↑n + 1 + 1) =
    ((t : ℝ) + ↑n + 1) / (↑n + 1 + 1) := by
  nth_rewrite 1 [←div_self (h₃ n)]
  ring


-- @@ L527-532 verbatim
lemma e₂ (n : ℕ) (t : I) :
    ((1 - (n + n + 1 + 1 : ℝ) / (↑n + ↑n + 1 + 1 + 1)) * ↑t +
        (↑n + ↑n + 1 + 1) / (↑n + ↑n + 1 + 1 + 1)) =
    (↑t + ↑n + ↑n + 1 + 1) / (↑n + ↑n + 1 + 1 + 1) := by
  nth_rewrite 1 [←div_self (h₇ n)]
  ring


-- @@ L534-538 verbatim
lemma e₃ (n : ℕ) :
    (1 - (n + 1 + (n + 1) + 1 + 1 : ℝ)⁻¹) =
    (↑n + ↑n + 1 + 1 + 1) / (↑n + ↑n + 1 + 1 + 1 + 1) := by
  nth_rewrite 1 [←div_self (ne_of_gt (h₄ n))]
  ring_nf


-- @@ L540-545 verbatim
lemma e₄ (n : ℕ) (t : I) :
    ((↑n + ↑n + 1 + 1 + 1 : ℝ) / (↑n + ↑n + 1 + 1 + 1 + 1) *
        ((↑t + ↑n + ↑n + 1 + 1) / (↑n + ↑n + 1 + 1 + 1))) =
    (↑t + ↑n + ↑n + 1 + 1) / (↑n + ↑n + 1 + 1 + 1 + 1) := by
  rw [mul_comm]
  rw [div_mul_div_cancel₀ (h₇ n)]


-- @@ L547-552 verbatim
lemma e₅ (n : ℕ) (r : ℝ) :
    2 * (r / (n + n + 1 + 1 + 1 + 1 : ℝ) + ((n : ℝ) + 1 + (↑n + 1) + 1 + 1)⁻¹) =
    (r + 1) / (↑n + 1 + 1) := by
  have h_ne : (↑n + 1 + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  ring


-- @@ L554-557 verbatim
lemma e₆ (n : ℕ) (r : ℝ) :
  (1 - (n + 1 + 1 : ℝ)⁻¹) * r + (n + 1 + 1 : ℝ)⁻¹ = ((n + 1) * r + 1) / (n + 1 + 1) := by
  nth_rewrite 1 [←div_self (h₃ n)]
  ring


-- @@ L559-559 verbatim
end AuxEqualities

-- @@ L560-560 verbatim
open AuxEqualities


-- @@ L562-632 verbatim
/-- If `γ₁` and `γ₂` are two paths, then
  `γ₁.trans γ₂` --> `[1/(2n + 4), 1]` --> `[0, (2n + 2)/(2n + 3)]` (so taking `[1/(2n + 4), (2n +
  3)/(2n + 4)]`)
is the same as
  `γ₁` --> `[1/(n+2), 1]`, added to `γ₂` --> `[0, (n+1)/(n+2)]`
-/
lemma trans_first_part_of_second_part (γ₁ : Dipath x₀ x₁) (γ₂ : Dipath x₁ x₂) (n : ℕ) (t : I) :
  (FirstPart
    (SecondPart (γ₁.trans γ₂) (Fraction.ofPos <| Nat.succ_pos (n.succ + n.succ).succ))
    (Fraction (Nat.succ_pos (n + n).succ.succ) (le_of_lt (Nat.lt_succ_self ((n + n).succ.succ))))
   ) t
  =
  ((SecondPart γ₁ (Fraction.ofPos (Nat.succ_pos n.succ)))).trans
   (FirstPart γ₂ (Fraction (Nat.succ_pos n.succ) (Nat.le_succ n.succ))) t := by
  rw [first_part_apply, second_part_apply, Dipath.trans_apply, Dipath.trans_apply]
  have : (n : ℝ) + ↑n + 2 + 1 = ↑n + ↑n + 1 + 1 + 1 := by ring
  split_ifs with h ht ht
  · rw [second_part_apply]
    apply congr_arg
    simp only [Nat.succ_eq_add_one, unitInterval.coe_symm_eq, zero_add, Nat.cast_one, Nat.cast_add,
      one_div, Nat.cast_ofNat, Subtype.mk.injEq]
    rw [e₃, mul_comm _ (t : ℝ), mul_div, mul_comm (_/_) (_/_), this,
      div_mul_div_cancel₀ (h₇ n), e₆, e₅]
    ring
  · exfalso
    revert h
    apply not_le.mpr
    simp only [one_div, Nat.succ_eq_add_one, unitInterval.coe_symm_eq, zero_add, Nat.cast_one,
      Nat.cast_add, Nat.cast_ofNat]
    rw [e₃, mul_comm _ (t : ℝ), mul_div, mul_comm (_/_) (_/_), this,
      div_mul_div_cancel₀ (h₇ n)]
    apply (mul_lt_mul_iff_of_pos_left (show 0 < (2 : ℝ) by norm_num)).mp
    rw [e₅]
    apply (lt_div_iff₀ (show (n + 1 + 1 : ℝ) > 0 by linarith [h₂ n])).mpr
    norm_num
    push Not at ht
    calc (n + 1 : ℝ)
      _ = 1 * (n + 1 : ℝ) := by rw [one_mul]
      _ = (2⁻¹ * 2) * (n + 1 : ℝ) :=
        by rw [inv_mul_cancel₀ (show (2 : ℝ) ≠ 0 by norm_num)]
      _ = 2⁻¹ * (n + n + 1 + 1 : ℝ) := by ring
      _ = 1/2 * (n + n + 1 + 1 : ℝ) := by rw [one_div]
      _ < t * (n + n + 1 + 1 : ℝ) :=
        (mul_lt_mul_iff_of_pos_right (by linarith [h₂ n])).mpr ht
  · exfalso
    revert h
    apply imp_false.mpr
    apply not_not.mpr
    simp only [Nat.succ_eq_add_one, unitInterval.coe_symm_eq, zero_add, Nat.cast_one, Nat.cast_add,
      one_div, Nat.cast_ofNat]
    rw [e₃, mul_comm _ (t : ℝ), mul_div, mul_comm (_/_) (_/_), this,
      div_mul_div_cancel₀ (h₇ n)]
    apply (mul_le_mul_iff_of_pos_left (show 0 < (2 : ℝ) by norm_num)).mp
    rw [e₅]
    apply (div_le_iff₀ (show (n + 1 + 1 : ℝ) > 0 by linarith [h₂ n])).mpr
    norm_num
    calc ↑t * (n + n + 1 + 1 : ℝ)
      _ ≤ 1/2 * (n + n + 1 + 1 : ℝ) :=
        (mul_le_mul_iff_of_pos_right (by linarith [h₂ n])).mpr ht
      _ = (1/2 * 2) * (n + 1 : ℝ)   := by ring
      _ = 1 * (n + 1 : ℝ)           :=
        by rw [div_mul_cancel₀ (1 : ℝ) (show (2 : ℝ) ≠ 0 by norm_num)]
      _ = (n + 1 : ℝ)               := by rw [one_mul]
  · rw [first_part_apply]
    apply congr_arg
    simp only [Nat.succ_eq_add_one, unitInterval.coe_symm_eq, zero_add, Nat.cast_one, Nat.cast_add,
      one_div, Nat.cast_ofNat, Subtype.mk.injEq]
    rw [e₃, mul_comm _ (t : ℝ), mul_div, mul_comm (_/_) (_/_), this,
      div_mul_div_cancel₀ (h₇ n), e₅]
    nth_rewrite 6 [←div_self (h₃ n)]
    ring


-- @@ L634-668 verbatim
/-- If `γ₁` and `γ₂` are two paths, then
  `γ₁.trans γ₂` --> `[1/(2n + 4), 1]` --> `[(2n+2)/(2n+3), 1]` (so to `[(2n+3)/(2n+4), 1]`)
is the same as
  `γ₂` --> `[(n+1)/(n+2), 1]`
-/
lemma trans_second_part_second_part (γ₁ : Dipath x₀ x₁) (γ₂ : Dipath x₁ x₂) (n : ℕ) (t : I) :
  (SecondPart
    (SecondPart (γ₁.trans γ₂) <| Fraction.ofPos <| Nat.succ_pos (n.succ + n.succ).succ)
    (Fraction (Nat.succ_pos (n + n).succ.succ) (Nat.le_succ (n + n).succ.succ))
   ) t
  =
    (SecondPart γ₂ (Fraction (Nat.succ_pos n.succ) (Nat.le_succ n.succ))) t := by
  rw [second_part_apply, second_part_apply, second_part_apply, Dipath.trans_apply]
  simp only [Nat.succ_eq_add_one, unitInterval.coe_symm_eq, zero_add, Nat.cast_one, Nat.cast_add,
    one_div, Nat.cast_ofNat]
  have : (n : ℝ) + ↑n + 2 = ↑n + ↑n + 1 + 1 := by ring
  split_ifs with h
  · exfalso
    rw [this, e₂, e₃, e₄, ←one_div, h₈] at h
    have hne : (↑n + ↑n + 1 + 1 + 1 + 1 : ℝ) ≠ 0 := (h₄ n).ne'
    have hcombine : (↑t + ↑n + ↑n + 1 + 1) / (↑n + ↑n + 1 + 1 + 1 + 1) +
        1 / (↑n + ↑n + 1 + 1 + 1 + 1 : ℝ) =
        (↑t + ↑n + ↑n + 1 + 1 + 1) / (↑n + ↑n + 1 + 1 + 1 + 1 : ℝ) := by
      field_simp
    rw [hcombine] at h
    have h2 : (↑n + 1 + 1 : ℝ) < (↑t + ↑n + ↑n + 1 + 1 + 1) := by linarith [h₂ n, h₁ t]
    have hfinal := lt_of_lt_of_le (div_lt_div_of_pos_right h2 (h₄ n)) h
    rw [h₆] at hfinal
    exact lt_irrefl _ hfinal
  apply congr_arg
  simp only [Subtype.mk.injEq]
  rw [this, e₁, e₂, e₃, e₄, e₅]
  nth_rewrite 6 [←div_self (h₃ n)]
  rw [div_sub_div_same]
  ring


-- @@ L670-677 verbatim
/-- If `γ₁` and `γ₂` are two paths, then `γ₁.trans γ₂` evaluated at `1/(2n+2)` is the same as
`γ₁` evaluated at `1/(n+1)`.
-/
lemma trans_image_inv_eq_first (γ₁ : Dipath x₀ x₁) (γ₂ : Dipath x₁ x₂) (n : ℕ) :
    (γ₁.trans γ₂) (Fraction.ofPos (Nat.succ_pos (n + n).succ)) =
      γ₁ (Fraction.ofPos (Nat.succ_pos n)) := by
  have := trans_first_part γ₁ γ₂ n 1
  simp_all


-- @@ L679-704 verbatim
/-- If `γ₁` and `γ₂` are two paths, then `γ₁.trans γ₂` --> `[1/(2n+4), 1]` evaluated at
`(2n+2)/(2n+3)` is the same as
`γ₂` evaluated at `(n+1)/(n+2)`.
-/
lemma second_part_trans_eval_at_end (γ₁ : Dipath x₀ x₁) (γ₂ : Dipath x₁ x₂) (n : ℕ) :
    (SecondPart (γ₁.trans γ₂) <| Fraction.ofPos <| Nat.succ_pos (n.succ + n.succ).succ)
    (Fraction (Nat.succ_pos (n+n).succ.succ) (le_of_lt (Nat.lt_succ_self _)))
    = γ₂ (Fraction (Nat.succ_pos (n.succ)) (le_of_lt (Nat.lt_succ_self _))) := by
  rw [second_part_apply, Dipath.trans_apply]
  have : (n : ℝ) + ↑n + 2 = ↑n + ↑n + 1 + 1 := by ring
  rw [dite_eq_right]
  · apply congr_arg
    rw [← Subtype.coe_inj]
    simp only [Nat.succ_eq_add_one, unitInterval.coe_symm_eq, zero_add, Nat.cast_one, Nat.cast_add,
      one_div, Nat.cast_ofNat]
    rw [e₃, mul_comm (_ / _) (_ / _), this, div_mul_div_cancel₀ (h₇ n), e₅ n (↑n + ↑n + 1 + 1)]
    nth_rewrite 6 [←div_self (h₃ n)]
    ring
  simp only [Nat.succ_eq_add_one, unitInterval.coe_symm_eq, zero_add, Nat.cast_one, Nat.cast_add,
    one_div, Nat.cast_ofNat, not_le]
  rw [e₃, mul_comm, this, div_mul_div_cancel₀ (h₇ n), h₈, ← one_div (n + n + 1 + 1 + 1 + 1 : ℝ)]
  have hpos : (0 : ℝ) < ↑n + ↑n + 1 + 1 + 1 + 1 := by linarith [h₂ n]
  rw [div_add_div _ _ hpos.ne' hpos.ne', show (2⁻¹ : ℝ) = 1/2 from by norm_num,
    div_lt_div_iff₀ (by norm_num) (by positivity)]
  ring_nf
  nlinarith [sq_nonneg ((n : ℝ) - 1), sq_nonneg ((n : ℝ) + 1), h₂ n]


-- @@ L706-706 verbatim
end SplitProperties
