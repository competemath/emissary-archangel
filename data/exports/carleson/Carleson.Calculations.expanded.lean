/-
This is a file for arithmetical lemmas -
lemmas that don't depend on any of Carleson's project definitions, or, really,
on any fancy definitions period.

Roughly speaking, if a lemma is in this file, it should be purely calculational/arithmetical,
e.g. `lemma calculation_1 : 2 + 2 = 4`.
All lemmas are prepended with a prefix `calculation_`.
-/
module

public import Carleson.ProofData


-- @@ L14-14 verbatim
public section


-- @@ L16-16 verbatim
open ShortVariables

-- @@ L17-17 verbatim
open scoped NNReal ENNReal

-- @@ L18-18 verbatim
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}


-- @@ L20-24 verbatim
lemma sixteen_times_le_cube (ha : 4 ≤ a) : 16 * a ≤ a ^ 3 := calc
  16 * a
  _ = 4 * 4 * a := by ring
  _ ≤ a * a * a := by gcongr
  _ = a ^ 3 := by ring


-- @@ L26-29 verbatim
lemma four_times_sq_le_cube (ha : 4 ≤ a) : 4 * a ^ 2 ≤ a ^ 3 := calc
  4 * a ^ 2
  _ ≤ a * a ^ 2 := by gcongr
  _ = a ^ 3 := by ring


-- @@ L31-34 verbatim
lemma add_le_pow_two {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
    {p q r s : ℕ} (hp : p ≤ r) (hq : q ≤ r) (hr : r + 1 ≤ s) :
    (2 : R) ^ p + 2 ^ q ≤ 2 ^ s := by
  grw [hp, hq, ← mul_two, ← pow_succ, hr] <;> norm_num


-- @@ L36-42 verbatim
lemma add_le_pow_two₃ {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
    {p q r s t : ℕ} (hp : p ≤ s) (hq : q ≤ s) (hr : r ≤ s + 1) (ht : s + 2 ≤ t) :
    (2 : R) ^ p + 2 ^ q + 2 ^ r ≤ 2 ^ t := calc
  (2 : R) ^ p + 2 ^ q + 2 ^ r
  _ ≤ 2 ^ (s + 1) + 2 ^ r := by
    gcongr; apply add_le_pow_two hp hq le_rfl
  _ ≤ 2 ^ t := add_le_pow_two le_rfl (by linarith) ht


-- @@ L44-49 verbatim
lemma add_le_pow_two_add_cube {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
    {p q r : ℕ} (ha : 4 ≤ a) (hp : p ≤ r) (hq : q ≤ r) :
    (2 : R) ^ p + 2 ^ q ≤ 2 ^ (r + a ^ 3) := by
  apply add_le_pow_two hp hq
  have : 1 ≤ a ^ 3 := one_le_pow₀ (by linarith)
  linarith


-- @@ L51-62 expanded
lemma calculation_1 (s : ℤ) :
    4 * (defaultD a : ℝ) ^ (-2 : ℝ) * defaultD a ^ (s + 3) = 4 * defaultD a ^ (s + 1) :=
  by
  have D_pos : (0 : ℝ) < defaultD a := realD_pos a
  calc
    4 * (defaultD a : ℝ) ^ (-2 : ℝ) * defaultD a ^ (s + 3)
    _ = 4 * (defaultD a ^ (-2 : ℝ) * defaultD a ^ (s + 3)) := by ring
    _ = 4 * defaultD a ^ (-2 + (s + 3)) := by
      congr
      have pow_th := Real.rpow_add (x := (defaultD a : ℝ)) (y := (-2)) (z := (s + 3)) D_pos
      rw_mod_cast [pow_th]
    _ = 4 * defaultD a ^ (s + 1) := by ring_nf


-- @@ L64-75 expanded
lemma calculation_2 (s : ℤ) :
    ((8 : ℝ)⁻¹ * defaultD a ^ (-3 : ℝ)) * defaultD a ^ (s + 3) = 8⁻¹ * defaultD a ^ s :=
  by
  have D_pos : (0 : ℝ) < defaultD a := realD_pos a
  calc
    (8 : ℝ)⁻¹ * (defaultD a : ℝ) ^ (-3 : ℝ) * defaultD a ^ (s + 3)
    _ = (8 : ℝ)⁻¹ * (defaultD a ^ (-3 : ℝ) * defaultD a ^ (s + 3)) := by ring
    _ = (8 : ℝ)⁻¹ * defaultD a ^ (-3 + (s + 3)) :=
      by
      congr
      have pow_th := Real.rpow_add (x := (defaultD a : ℝ)) (y := (-3)) (z := (s + 3)) D_pos
      rw_mod_cast [pow_th]
    _ = (8 : ℝ)⁻¹ * defaultD a ^ s := by norm_num


-- @@ L77-83 expanded
lemma calculation_10 (h : (100 : ℝ) < defaultD a) :
    ((100 : ℝ) + 4 * defaultD a ^ (-2 : ℝ) + 8⁻¹ * defaultD a ^ (-3 : ℝ)) * defaultD a ^ (-1 : ℝ) <
      2 :=
  by
  calc
    ((100 : ℝ) + 4 * defaultD a ^ (-2 : ℝ) + 8⁻¹ * defaultD a ^ (-3 : ℝ)) * defaultD a ^ (-1 : ℝ)
    _ ≤ ((100 : ℝ) + 4 * 100 ^ (-2 : ℝ) + 8⁻¹ * 100 ^ (-3 : ℝ)) * 100 ^ (-1 : ℝ) := by
      gcongr (100 + 4 * ?_ + 8⁻¹ * ?_) * ?_ <;>
        apply Real.rpow_le_rpow_of_nonpos (by norm_num) h.le (by norm_num)
    _ < _ := by norm_num


-- @@ L85-103 expanded
lemma calculation_3 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] {x y : ℤ} (h : x + 3 < y) :
    100 * defaultD a ^ (x + 3) + ((4 * defaultD a ^ (-2 : ℝ)) * defaultD a ^ (x + 3)) +
          (((8 : ℝ)⁻¹ * defaultD a ^ (-3 : ℝ)) * defaultD a ^ (x + 3)) +
        8 * defaultD a ^ y <
      10 * defaultD a ^ y :=
  by
  rw [← show (2 : ℝ) + 8 = 10 by norm_num, right_distrib]
  gcongr
  rw [← distrib_three_right ..]
  calc
    (100 + 4 * (defaultD a : ℝ) ^ (-2 : ℝ) + 8⁻¹ * defaultD a ^ (-3 : ℝ)) * defaultD a ^ (x + 3)
    _ ≤
        (100 + 4 * (defaultD a : ℝ) ^ (-2 : ℝ) + 8⁻¹ * defaultD a ^ (-3 : ℝ)) *
          defaultD a ^ (y - 1) :=
      by
      have h1 : x + 3 ≤ y - 1 := by lia
      gcongr
      linarith [four_le_realD X]
    _ =
        (100 + 4 * (defaultD a : ℝ) ^ (-2 : ℝ) + 8⁻¹ * defaultD a ^ (-3 : ℝ)) *
          (defaultD a ^ (y) * defaultD a ^ (-1 : ℝ)) :=
      by
      congr
      exact_mod_cast Real.rpow_add (y := y) (z := (-1)) (hx := realD_pos a)
    _ < 2 * defaultD a ^ y := by
      nth_rw 4 [mul_comm ..]
      rw [← mul_assoc ..]
      have D_pos : (0 : ℝ) < defaultD a := realD_pos a
      gcongr
      exact calculation_10 (hundred_lt_realD X)


-- @@ L105-131 expanded
lemma calculation_4 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] {s_1 s_2 s_3 : ℤ}
    {dist_a dist_b dist_c dist_d : ℝ} (lt_1 : dist_a < 100 * defaultD a ^ (s_1 + 3))
    (lt_2 : dist_b < 8 * defaultD a ^ s_3) (lt_3 : dist_c < 8⁻¹ * defaultD a ^ s_1)
    (lt_4 : dist_d < 4 * defaultD a ^ s_2) (three : s_1 + 3 < s_3) (plusOne : s_2 = s_1 + 1) :
    dist_a + dist_d + dist_c + dist_b < 10 * defaultD a ^ s_3 := by
  calc
    dist_a + dist_d + dist_c + dist_b
    _ ≤ 100 * defaultD a ^ (s_1 + 3) + dist_d + dist_c + dist_b :=
      by
      change dist_a < 100 * defaultD a ^ (s_1 + 3) at lt_1
      gcongr
    _ ≤ 100 * defaultD a ^ (s_1 + 3) + 4 * defaultD a ^ (s_1 + 1) + dist_c + dist_b :=
      by
      gcongr
      apply le_of_lt
      rw [← plusOne]
      exact lt_4
    _ ≤
        100 * defaultD a ^ (s_1 + 3) + 4 * defaultD a ^ (s_1 + 1) + 8⁻¹ * defaultD a ^ s_1 +
          dist_b :=
      by gcongr
    _ ≤
        100 * defaultD a ^ (s_1 + 3) + 4 * defaultD a ^ (s_1 + 1) + 8⁻¹ * defaultD a ^ s_1 +
          8 * defaultD a ^ s_3 :=
      by gcongr
    _ =
        100 * defaultD a ^ (s_1 + 3) + ((4 * defaultD a ^ (-2 : ℝ)) * defaultD a ^ (s_1 + 3)) +
            8⁻¹ * defaultD a ^ s_1 +
          8 * defaultD a ^ s_3 :=
      by rw [calculation_1 (s := s_1)]
    _ =
        100 * defaultD a ^ (s_1 + 3) + ((4 * defaultD a ^ (-2 : ℝ)) * defaultD a ^ (s_1 + 3)) +
            (((8 : ℝ)⁻¹ * defaultD a ^ (-3 : ℝ)) * defaultD a ^ (s_1 + 3)) +
          8 * defaultD a ^ s_3 :=
      by rw [calculation_2 (s := s_1)]
    _ < 10 * defaultD a ^ s_3 := by exact calculation_3 (h := three) (X := X)


-- @@ L133-137 expanded
lemma calculation_logD_64 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] :
    Real.logb (defaultD a) 64 < 1 :=
  by
  apply (Real.logb_lt_iff_lt_rpow (by linarith [hundred_lt_realD X]) (by linarith)).mpr
  rw [Real.rpow_one]
  linarith [hundred_lt_realD X]


-- @@ L139-149 verbatim
lemma calculation_5 {dist_1 dist_2 : ℝ}
    (h : dist_1 ≤ (2 ^ (a : ℝ)) ^ (6 : ℝ) * dist_2) :
    2 ^ ((-𝕔 : ℝ) * a) * dist_1 ≤ 2 ^ ((-(𝕔 - 6) : ℝ) * a) * dist_2 := by
  apply (mul_le_mul_iff_right₀ (show 0 < (2 : ℝ) ^ (𝕔 * (a : ℝ)) by positivity)).mp
  rw [← mul_assoc, neg_mul,
    Real.rpow_neg (by positivity),
    mul_inv_cancel₀ (a := (2 : ℝ) ^ (𝕔 * (a : ℝ))) (by positivity),
    ← mul_assoc, ← Real.rpow_add (by positivity)]
  ring_nf
  rw [Real.rpow_mul (x := (2 : ℝ)) (hx:=by positivity) (y := a) (z := 6)]
  exact_mod_cast h


-- @@ L151-155 expanded
lemma calculation_6 (a : ℕ) (s : ℤ) :
    (defaultD a : ℝ) ^ (s + 3) = (defaultD a : ℝ) ^ (s + 2) * (defaultD a : ℝ) :=
  by
  rw [zpow_add₀ (by linarith [realD_pos a]) s 3, zpow_add₀ (by linarith [realD_pos a]) s 2,
    mul_assoc]
  congr


-- @@ L157-163 expanded
lemma calculation_7 (a : ℕ) (s : ℤ) :
    100 * (defaultD a ^ (s + 2) * defaultD a) =
      (defaultA a) ^ (𝕔 * a) * (100 * (defaultD a : ℝ) ^ (s + 2)) :=
  by
  rw [← mul_assoc (a := 100), mul_comm]
  congr
  norm_cast
  rw [← pow_mul 2 a (𝕔 * a), mul_comm (a := a), defaultD]
  ring


-- @@ L165-170 verbatim
lemma calculation_8 {dist_1 dist_2 : ℝ}
    (h : dist_1 * 2 ^ ((𝕔 : ℝ) * a) ≤ dist_2) :
    dist_1 ≤ 2 ^ ((-𝕔 : ℝ) * a) * dist_2 := by
  rw [neg_mul, Real.rpow_neg (by positivity), mul_comm (a := (2 ^ (𝕔 * (a : ℝ)))⁻¹)]
  apply (le_mul_inv_iff₀ (by positivity)).mpr
  exact h


-- @@ L172-183 verbatim
lemma calculation_9 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G]
    (h : 1 ≤ (2 : ℝ) ^ (-((𝕔 - 6) : ℝ) * a)) :
    False := by
  have : (2 : ℝ) ^ (-((𝕔 - 6) : ℝ) * a) < 1 ^ (-((𝕔 - 6) : ℝ) * a) := by
    apply Real.rpow_lt_rpow_of_neg (by norm_num) (by norm_num)
    simp only [neg_sub, sub_mul, sub_neg]
    norm_cast
    gcongr
    · linarith [four_le_a X]
    · linarith [seven_le_c]
  simp at h this
  linarith


-- @@ L185-192 expanded
lemma calculation_11 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] (s : ℤ) :
    100 * (defaultD a : ℝ) ^ (s + 2) + 4 * defaultD a ^ (s + 1) < 128 * defaultD a ^ (s + 2) :=
  by
  rw [show (128 : ℝ) = 100 + 28 by norm_num]
  rw [right_distrib]
  gcongr
  · linarith
  · exact one_lt_realD (X := X)
  · linarith


-- @@ L194-227 expanded
lemma calculation_12 (s : ℝ) :
    128 * (defaultD a : ℝ) ^ (s + 2) = 2 ^ (2 * 𝕔 * a ^ 2 + 4) * (8 * defaultD a ^ s) :=
  by
  simp only [defaultD]
  have leftSide :=
    calc
      128 * ((2 : ℝ) ^ (𝕔 * a ^ 2)) ^ (s + 2)
      _ = 128 * 2 ^ (𝕔 * a ^ 2 * (s + 2)) := by
        congrm 128 * ?_
        have fact := Real.rpow_mul (x := 2) (y := 𝕔 * a ^ 2) (z := s + 2) (by positivity)
        rw_mod_cast [fact]
      _ = 128 * 2 ^ ((𝕔 * a ^ 2 * s) + (𝕔 * a ^ 2 * 2)) :=
        by
        congrm 128 * (2 ^ ?_)
        ring
      _ = (2 ^ 7) * 2 ^ ((𝕔 * a ^ 2 * s) + (𝕔 * a ^ 2 * 2)) := by norm_num
      _ = 2 ^ (7 + ((𝕔 * a ^ 2 * s) + (𝕔 * a ^ 2 * 2))) :=
        by
        have fact :=
          Real.rpow_add (x := 2) (y := 7) (z := 𝕔 * a ^ 2 * s + 𝕔 * a ^ 2 * 2) (by positivity)
        rw_mod_cast [fact]
  have rightSide :=
    calc
      2 ^ (2 * 𝕔 * a ^ 2 + 4) * (8 * ((2 : ℝ) ^ (𝕔 * a ^ 2)) ^ s)
      _ = 2 ^ (2 * 𝕔 * a ^ 2 + 4) * ((2 ^ 3) * ((2 ^ (𝕔 * a ^ 2)) ^ s)) := by norm_num
      _ = 2 ^ (2 * 𝕔 * a ^ 2 + 4) * (2 ^ 3 * 2 ^ (𝕔 * a ^ 2 * s)) :=
        by
        rw [Real.rpow_mul (x := 2) (by positivity)]
        norm_cast
      _ = 2 ^ (2 * 𝕔 * a ^ 2 + 4) * 2 ^ (3 + 𝕔 * a ^ 2 * s) :=
        by
        have fact := Real.rpow_add (x := 2) (y := 3) (z := 𝕔 * a ^ 2 * s) (by positivity)
        rw_mod_cast [fact]
      _ = 2 ^ (2 * 𝕔 * a ^ 2 + 4 + (3 + 𝕔 * a ^ 2 * s)) :=
        by
        nth_rw 2 [Real.rpow_add]
        · norm_cast
        · positivity
      _ = 2 ^ (7 + ((𝕔 * a ^ 2 * s) + (𝕔 * a ^ 2 * 2))) :=
        by
        congrm 2 ^ ?_
        linarith
  rw_mod_cast [leftSide]
  rw_mod_cast [rightSide]


-- @@ L229-233 verbatim
lemma calculation_13 : (2 : ℝ) ^ (2 * 𝕔 * a ^ 3 + 4 * a) = (defaultA a) ^ (2 * 𝕔 * a ^ 2 + 4) := by
  simp only [defaultA, Nat.cast_pow, Nat.cast_ofNat]
  have fact := Real.rpow_mul (x := 2) (y := a) (z := 2 * 𝕔 * a ^ 2 + 4) (by positivity)
  rw_mod_cast [← fact]
  ring


-- @@ L235-246 expanded
lemma calculation_14 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] (n : ℕ) :
    (2 : ℝ) ^ ((defaultZ a : ℝ) * n / 2 - (2 * 𝕔 + 1) * a ^ 3) ≤
      2 ^ ((defaultZ a : ℝ) * n / 2 - (2 * 𝕔 * a ^ 3 + 4 * a)) :=
  by
  gcongr
  · linarith
  rw [show (2 * 𝕔 + 1) * (a : ℝ) ^ 3 = 2 * 𝕔 * (a : ℝ) ^ 3 + a ^ 3 by ring]
  gcongr _ + ?_
  rw [show (a : ℝ) ^ 3 = a ^ 2 * a by ring]
  gcongr
  suffices 4 ^ 2 ≤ (a : ℝ) ^ 2 by linarith
  apply pow_le_pow_left₀ (ha := by linarith)
  exact_mod_cast four_le_a X


-- @@ L248-255 verbatim
lemma calculation_15 {dist zon : ℝ}
    (h : 2 ^ zon ≤ 2 ^ (2 * 𝕔 * a ^ 3 + 4 * a) * dist) :
    2 ^ (zon - (2 * 𝕔 * a^3 + 4*a)) ≤ dist := by
  rw [Real.rpow_sub (hx := by linarith)]
  rw [show dist = 2 ^ (2 * 𝕔 * a ^ 3 + 4 * a) * dist / 2 ^ (2 * 𝕔 * a ^ 3 + 4 * a) by simp]
  have := (div_le_div_iff_of_pos_right (c := 2 ^ (2 * 𝕔 * a ^ 3 + 4 * a))
    (hc := by positivity)).mpr h
  exact_mod_cast this


-- @@ L257-262 expanded
lemma calculation_16 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] (s : ℤ) :
    4 * (defaultD a : ℝ) ^ s < 100 * defaultD a ^ (s + 1) :=
  by
  gcongr
  · linarith
  · exact one_lt_realD (X := X)
  · linarith


-- @@ L264-279 expanded
lemma calculation_7_7_4 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] {n : ℕ} :
    (1 : ℝ) ≤ 2 ^ (defaultZ a * (n + 1)) - 4 :=
  by
  rw [le_sub_iff_add_le]
  trans 2 ^ 3
  · norm_num
  apply pow_right_mono₀ (one_le_two)
  rw [← mul_one 3]
  have : 3 ≤ defaultZ a := by
    simp only [defaultZ]
    have := a_pos X
    trans 2 ^ 12
    · norm_num
    gcongr
    · norm_num
    lia
  exact Nat.mul_le_mul this (Nat.le_add_left 1 n)


-- @@ L281-293 verbatim
/-- A bound on the sum of a geometric series whose ratio is close to 1. -/
lemma near_1_geometric_bound {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    (1 - 2 ^ (-t))⁻¹ ≤ 2 * (ENNReal.ofReal t)⁻¹ := by
  obtain ⟨lb, ub⟩ := ht
  rw [ENNReal.inv_le_iff_inv_le, ENNReal.mul_inv (.inl two_ne_zero) (.inl ENNReal.ofNat_ne_top),
    inv_inv, ← ENNReal.div_eq_inv_mul, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_rpow_of_pos (by positivity),
    ← ENNReal.ofReal_sub _ (by positivity)]
  apply ENNReal.ofReal_le_ofReal; change t / 2 ≤ 1 - 2 ^ (-t)
  have bne := rpow_one_add_le_one_add_mul_self (show -1 ≤ -1 / 2 by norm_num) lb ub
  rw [show (1 : ℝ) + -1 / 2 = 2⁻¹ by norm_num, Real.inv_rpow zero_le_two,
    ← Real.rpow_neg zero_le_two] at bne
  linarith only [bne]


-- @@ L295-311 expanded
lemma calculation_convexity_bound [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] {n : ℕ} {t : ℝ}
    (ht : t ∈ Set.Icc 0 1) :
    ∑ k ∈ Finset.range n, ((defaultD a : ENNReal) ^ (-t)) ^ k ≤ 2 * (ENNReal.ofReal t)⁻¹ :=
  by
  have a4 := four_le_a X
  refine le_trans ?_ (near_1_geometric_bound ht)
  calc
    _ ≤ ∑ k ∈ Finset.range n, ((2 : ENNReal) ^ (-t)) ^ k :=
      by
      refine Finset.sum_le_sum fun k mk ↦ pow_le_pow_left' ?_ k
      rw [ENNReal.rpow_neg, ENNReal.rpow_neg, ENNReal.inv_le_inv]
      refine ENNReal.rpow_le_rpow ?_ ht.1
      unfold defaultD
      norm_cast
      apply Nat.le_pow
      have : 0 < 𝕔 := by linarith [seven_le_c]
      positivity
    _ ≤ ∑' k : ℕ, ((2 : ENNReal) ^ (-t)) ^ k := (ENNReal.sum_le_tsum _)
    _ = _ := ENNReal.tsum_geometric _


-- @@ L313-327 expanded
lemma calculation_7_6_2 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] {n : ℕ} :
    ∑ k ∈ Finset.range n, ((defaultD a : ENNReal) ^ (-(defaultκ a / 2))) ^ k ≤ 2 ^ (10 * a + 2) :=
  calc
    _ ≤ 2 * (ENNReal.ofReal (defaultκ a / 2))⁻¹ :=
      by
      apply calculation_convexity_bound (X := X)
      have := κ_nonneg (a := a)
      have := κ_le_one (a := a)
      rw [Set.mem_Icc]; constructor <;> linarith
    _ = _ := by
      rw [ENNReal.ofReal_div_of_pos zero_lt_two, ENNReal.ofReal_ofNat,
        ENNReal.inv_div (.inl ENNReal.ofNat_ne_top) (.inl two_ne_zero), ← mul_div_assoc,
        ENNReal.div_eq_inv_mul, defaultκ, ← ENNReal.ofReal_rpow_of_pos zero_lt_two, ←
        ENNReal.inv_rpow, ← ENNReal.rpow_neg_one, ← ENNReal.rpow_mul,
        show -1 * (-10 * (a : ℝ)) = (10 * a : ℕ) by simp, ENNReal.rpow_natCast, ← sq,
        ENNReal.ofReal_ofNat, ← pow_add]


-- @@ L329-342 expanded
lemma calculation_150 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] :
    𝕔 * (3 / 2) * a ^ 2 * defaultκ a ≤ 1 :=
  by
  rw [defaultκ, neg_mul, Real.rpow_neg zero_le_two]
  refine mul_inv_le_one_of_le₀ ?_ (by positivity); norm_cast
  rw [show 2 ^ (10 * a) = 2 ^ (8 * a) * (2 ^ a) ^ 2 by ring]
  simp only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
  gcongr
  ·
    calc
      _ ≤ (2 : ℝ) ^ (8 * 4) :=
        by
        have : (𝕔 : ℝ) * (3 / 2) ≤ 100 * (3 / 2) := by gcongr; exact_mod_cast c_le_100
        linarith
      _ ≤ _ := by gcongr; exacts [one_le_two, four_le_a X]
  · norm_cast
    exact Nat.lt_two_pow_self.le


-- @@ L344-352 verbatim
lemma sq_le_two_pow_of_four_le (a4 : 4 ≤ a) : a ^ 2 ≤ 2 ^ a := by
  induction a, a4 using Nat.le_induction with
  | base => lia
  | succ a a4 ih =>
    rw [pow_succ 2, mul_two, add_sq, one_pow, mul_one, add_assoc]; gcongr
    calc
      _ ≤ 3 * a := by lia
      _ ≤ a * a := by gcongr; lia
      _ ≤ _ := by rwa [← sq]


-- @@ L354-358 verbatim
lemma calculation_6_1_6 (a4 : 4 ≤ a) : 8 * a ^ 4 ≤ 2 ^ (2 * a + 3) := by
  calc
    _ = 2 ^ 3 * a ^ 2 * a ^ 2 := by ring
    _ ≤ 2 ^ 3 * 2 ^ a * 2 ^ a := by gcongr _ * ?_ * ?_ <;> exact sq_le_two_pow_of_four_le a4
    _ = _ := by ring
