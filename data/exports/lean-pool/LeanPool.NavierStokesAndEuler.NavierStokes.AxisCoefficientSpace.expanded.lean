/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Tactic.FieldSimp


-- @@ L18-25 verbatim
/-!
# A complete coefficient space with compatible actual derivatives

Normalized bounded continuous jets are restricted by closed, linear
fundamental-theorem-of-calculus identities. Thus a point of the resulting
Banach space determines genuine smooth coefficient functions, not unrelated
arrays masquerading as their derivatives.
-/


-- @@ L27-27 verbatim
section


-- @@ L29-36 verbatim
/-!
# Concrete coefficient estimates for the natural-axis norm

Products are actual
finite coefficient convolutions with the Leibniz binomial factors. In particular,
the mixed derivative estimate is proved after the radial inverse; no boundedness
of either differentiation operator on its own is assumed.
-/


-- @@ L38-38 verbatim
@[expose] public section


-- @@ L40-40 verbatim
namespace NavierStokes.AxisWeightEstimates


-- @@ L42-42 verbatim
open scoped BigOperators

-- @@ L43-43 verbatim
open Finset Finset.Nat


-- @@ L45-45 verbatim
noncomputable section


-- @@ L47-50 verbatim
/-- The exact coefficient weight printed in the candidate manuscript. -/
def weight (ε : ℝ) (n m : ℕ) : ℝ :=
  (1 / 20 : ℝ) ^ n * (ε⁻¹) ^ m * (m.factorial : ℝ) * ((n + m).choose m : ℝ) /
    (((n : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) ^ 2)


-- @@ L52-54 verbatim
/-- The analytic part of the weight, before the two square-decay factors. -/
def coreWeight (ε : ℝ) (n m : ℕ) : ℝ :=
  (1 / 20 : ℝ) ^ n * (ε⁻¹) ^ m * (m.factorial : ℝ) * ((n + m).choose m : ℝ)


-- @@ L56-57 verbatim
/-- Square decay, given by `1 / ((n : ℝ) + 1) ^ 2`. -/
def squareDecay (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1) ^ 2


-- @@ L59-63 verbatim
theorem weight_eq_core_decay (ε : ℝ) (n m : ℕ) :
    weight ε n m = coreWeight ε n m * squareDecay n * squareDecay m := by
  unfold weight coreWeight squareDecay
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring


-- @@ L65-67 verbatim
theorem squareDecay_pos (n : ℕ) : 0 < squareDecay n := by
  unfold squareDecay
  positivity


-- @@ L69-74 verbatim
theorem coreWeight_pos {ε : ℝ} (hε : 0 < ε) (n m : ℕ) :
    0 < coreWeight ε n m := by
  unfold coreWeight
  have hc : 0 < ((n + m).choose m : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : m ≤ n + m)
  positivity


-- @@ L76-78 verbatim
theorem weight_pos {ε : ℝ} (hε : 0 < ε) (n m : ℕ) : 0 < weight ε n m := by
  rw [weight_eq_core_decay]
  exact mul_pos (mul_pos (coreWeight_pos hε n m) (squareDecay_pos n)) (squareDecay_pos m)


-- @@ L80-84 verbatim
theorem squareDecay_succ_le (n : ℕ) : squareDecay (n + 1) ≤ squareDecay n := by
  unfold squareDecay
  apply one_div_le_one_div_of_le (by positivity)
  push_cast
  linarith [show (0 : ℝ) ≤ n by positivity]


-- @@ L86-95 verbatim
theorem squareDecay_le_four_succ (n : ℕ) : squareDecay n ≤ 4 * squareDecay (n + 1) := by
  unfold squareDecay
  have hn : (0 : ℝ) ≤ n := by positivity
  have h₁ : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h₂ : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) + 1 := by positivity
  rw [show 4 * (1 / (((n + 1 : ℕ) : ℝ) + 1) ^ 2) =
    4 / (((n + 1 : ℕ) : ℝ) + 1) ^ 2 by ring]
  rw [div_le_div_iff₀ (sq_pos_of_pos h₁) (sq_pos_of_pos h₂)]
  push_cast
  nlinarith


-- @@ L97-105 verbatim
/-- Elementary telescoping majorant for the square summability estimate. -/
theorem reciprocal_square_telescope (x : ℝ) (hx : 1 ≤ x) :
    1 / x ^ 2 ≤ 2 / x - 2 / (x + 1) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x + 1 := by linarith
  have hid : 2 / x - 2 / (x + 1) = 2 / (x * (x + 1)) := by
    field_simp; ring
  rw [hid, div_le_div_iff₀ (sq_pos_of_pos hx0) (mul_pos hx0 hx1)]
  nlinarith


-- @@ L107-121 verbatim
theorem sum_squareDecay_le (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), squareDecay i) ≤ 2 - 2 / ((n : ℝ) + 2) := by
  induction n with
  | zero => norm_num [squareDecay]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hn : (0 : ℝ) ≤ n := by positivity
      have htel := reciprocal_square_telescope ((n : ℝ) + 2) (by linarith)
      have hid : squareDecay (n + 1) = 1 / ((n : ℝ) + 2) ^ 2 := by
        simp [squareDecay, Nat.cast_add, Nat.cast_one]
        ring
      rw [hid]
      push_cast
      ring_nf at ih htel ⊢
      linarith


-- @@ L123-127 verbatim
theorem sum_squareDecay_le_two (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), squareDecay i) ≤ 2 := by
  have h := sum_squareDecay_le n
  have hp : 0 ≤ 2 / ((n : ℝ) + 2) := by positivity
  linarith


-- @@ L129-143 verbatim
theorem squareDecay_product_le (i j : ℕ) :
    squareDecay i * squareDecay j ≤
      2 * squareDecay (i + j) * (squareDecay i + squareDecay j) := by
  have hi : 0 < (i : ℝ) + 1 := by positivity
  have hj : 0 < (j : ℝ) + 1 := by positivity
  have hij : 0 < ((i + j : ℕ) : ℝ) + 1 := by positivity
  have hpoly : (((i + j : ℕ) : ℝ) + 1) ^ 2 ≤
      2 * (((i : ℝ) + 1) ^ 2 + ((j : ℝ) + 1) ^ 2) := by
    push_cast
    linarith [sq_nonneg ((i : ℝ) - (j : ℝ))]
  have hh := div_le_div_of_nonneg_right hpoly (le_of_lt
    (mul_pos (mul_pos (sq_pos_of_pos hi) (sq_pos_of_pos hj)) (sq_pos_of_pos hij)))
  convert! hh using 1 <;> unfold squareDecay <;>
    field_simp [ne_of_gt hi, ne_of_gt hj, ne_of_gt hij]
  ring


-- @@ L145-167 verbatim
/-- The one-dimensional convolution constant is at most eight. -/
theorem squareDecay_convolution_le (n : ℕ) :
    (∑ ij ∈ antidiagonal n, squareDecay ij.1 * squareDecay ij.2) ≤ 8 * squareDecay n := by
  have hsum : (∑ ij ∈ antidiagonal n, squareDecay ij.1 * squareDecay ij.2) ≤
      ∑ ij ∈ antidiagonal n, 2 * squareDecay n * (squareDecay ij.1 + squareDecay ij.2) := by
    apply Finset.sum_le_sum
    intro ij hij
    have h := squareDecay_product_le ij.1 ij.2
    rw [mem_antidiagonal.mp hij] at h
    exact h
  have hfirst : (∑ ij ∈ antidiagonal n, squareDecay ij.1) ≤ 2 := by
    rw [sum_antidiagonal_eq_sum_range_succ_mk]
    exact sum_squareDecay_le_two n
  have hsecond : (∑ ij ∈ antidiagonal n, squareDecay ij.2) ≤ 2 := by
    have heq : (∑ ij ∈ antidiagonal n, squareDecay ij.2) =
        ∑ ij ∈ antidiagonal n, squareDecay ij.1 := by
      simpa only [Prod.fst_swap] using
        (sum_antidiagonal_swap (n := n) (f := fun ij => squareDecay ij.1))
    rw [heq]
    exact hfirst
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  have hd := (squareDecay_pos n).le
  nlinarith


-- @@ L169-178 verbatim
/-- A term of Vandermonde's sum gives the binomial estimate used in the norm. -/
theorem choose_product_le (i j k l : ℕ) :
    (i + k).choose k * (j + l).choose l ≤ ((i + j) + (k + l)).choose (k + l) := by
  have h := Finset.single_le_sum (fun p (_ : p ∈ antidiagonal (k + l)) =>
    Nat.zero_le ((i + k).choose p.1 * (j + l).choose p.2))
    (show (k, l) ∈ antidiagonal (k + l) from mem_antidiagonal.mpr rfl)
  rw [← Nat.add_choose_eq] at h
  have hindex : i + k + (j + l) = i + j + (k + l) := by omega
  rw [hindex] at h
  exact h


-- @@ L180-185 verbatim
theorem choose_factorials (k l : ℕ) :
    ((k + l).choose k : ℝ) * (k.factorial : ℝ) * (l.factorial : ℝ) =
      ((k + l).factorial : ℝ) := by
  have h := Nat.add_choose_mul_factorial_mul_factorial l k
  rw [Nat.add_comm l k, Nat.mul_right_comm] at h
  exact_mod_cast h


-- @@ L187-204 verbatim
/-- The analytic factors respect the Leibniz convolution with constant one. -/
theorem coreWeight_product_le {ε : ℝ} (hε : 0 < ε) (i j k l : ℕ) :
    ((k + l).choose k : ℝ) * coreWeight ε i k * coreWeight ε j l ≤
      coreWeight ε (i + j) (k + l) := by
  have hc : ((i + k).choose k : ℝ) * ((j + l).choose l : ℝ) ≤
      (((i + j) + (k + l)).choose (k + l) : ℝ) := by
    exact_mod_cast choose_product_le i j k l
  have hfac := choose_factorials k l
  have hnonneg : 0 ≤ (1 / 20 : ℝ) ^ (i + j) * (ε⁻¹) ^ (k + l) *
      ((k + l).factorial : ℝ) := by positivity
  calc
    _ = ((1 / 20 : ℝ) ^ (i + j) * (ε⁻¹) ^ (k + l) * ((k + l).factorial : ℝ)) *
        (((i + k).choose k : ℝ) * ((j + l).choose l : ℝ)) := by
      rw [← hfac]
      unfold coreWeight
      rw [pow_add, pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hc hnonneg


-- @@ L206-220 verbatim
/-- Factorial form used only to prove the exact shift identities. -/
theorem coreWeight_factorial (ε : ℝ) (n m : ℕ) :
    coreWeight ε n m =
      (1 / 20 : ℝ) ^ n * (ε⁻¹) ^ m * ((n + m).factorial : ℝ) / (n.factorial : ℝ) := by
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hf : (m.factorial : ℝ) * ((n + m).choose m : ℝ) * (n.factorial : ℝ) =
      ((n + m).factorial : ℝ) := by
    have h := Nat.add_choose_mul_factorial_mul_factorial n m
    exact_mod_cast (by simpa only [mul_comm, mul_left_comm, mul_assoc] using h)
  apply (eq_div_iff hn).2
  unfold coreWeight
  calc
    _ = (1 / 20 : ℝ) ^ n * (ε⁻¹) ^ m *
        ((m.factorial : ℝ) * ((n + m).choose m : ℝ) * (n.factorial : ℝ)) := by ring
    _ = _ := by rw [hf]


-- @@ L222-231 verbatim
theorem coreWeight_radial_identity {ε : ℝ} (hε : 0 < ε) (n m : ℕ) :
    coreWeight ε n m * ((n : ℝ) + m + 1) =
      20 * ((n : ℝ) + 1) * coreWeight ε (n + 1) m := by
  rw [coreWeight_factorial, coreWeight_factorial]
  have hindex : n + 1 + m = (n + m) + 1 := by omega
  rw [hindex, Nat.factorial_succ, Nat.factorial_succ, pow_succ]
  push_cast
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [ne_of_gt hε, hn, hn1]


-- @@ L233-246 verbatim
theorem coreWeight_radial_le {ε : ℝ} (hε : 0 < ε) (n m : ℕ) :
    coreWeight ε n m ≤ 20 * coreWeight ε (n + 1) m := by
  have hp : 0 < (n : ℝ) + 1 := by positivity
  apply (mul_le_mul_iff_left₀ hp).mp
  calc
    coreWeight ε n m * ((n : ℝ) + 1) ≤
        coreWeight ε n m * ((n : ℝ) + m + 1) := by
      exact mul_le_mul_of_nonneg_left (by
        have hm : (0 : ℝ) ≤ m := by positivity
        linarith)
        (coreWeight_pos hε n m).le
    _ = 20 * coreWeight ε (n + 1) m * ((n : ℝ) + 1) := by
      rw [coreWeight_radial_identity hε]
      ring


-- @@ L248-258 verbatim
theorem coreWeight_parameter_shift {ε : ℝ} (hε : 0 < ε) (i k : ℕ) :
    coreWeight ε i (k + 1) =
      (20 / ε) * ((i : ℝ) + 1) * coreWeight ε (i + 1) k := by
  rw [coreWeight_factorial, coreWeight_factorial]
  have hindex : i + 1 + k = i + (k + 1) := by omega
  rw [hindex, Nat.factorial_succ, pow_succ, pow_succ]
  push_cast
  have hi : (i.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hi1 : (i : ℝ) + 1 ≠ 0 := by positivity
  have he := ne_of_gt hε
  field_simp


-- @@ L260-269 verbatim
/-- A radial shift costs at most the printed factor `4 * 20 = 80`. -/
theorem weight_radial_shift {ε : ℝ} (hε : 0 < ε) (n m : ℕ) :
    weight ε n m ≤ 80 * weight ε (n + 1) m := by
  rw [weight_eq_core_decay, weight_eq_core_decay]
  calc
    _ ≤ (20 * coreWeight ε (n + 1) m) * (4 * squareDecay (n + 1)) * squareDecay m := by
      apply mul_le_mul_of_nonneg_right _ (squareDecay_pos m).le
      exact mul_le_mul (coreWeight_radial_le hε n m) (squareDecay_le_four_succ n)
        (squareDecay_pos n).le (mul_nonneg (by norm_num) (coreWeight_pos hε (n + 1) m).le)
    _ = _ := by ring


-- @@ L271-273 verbatim
theorem weight_radial_shift_ratio {ε : ℝ} (hε : 0 < ε) (n m : ℕ) :
    weight ε n m / weight ε (n + 1) m ≤ 80 := by
  exact (div_le_iff₀ (weight_pos hε (n + 1) m)).2 (weight_radial_shift hε n m)


-- @@ L275-289 verbatim
/-- Assigning the output radial shift to a parameter-differentiated factor. -/
theorem weight_parameter_radial_shift {ε : ℝ} (hε : 0 < ε) (i k : ℕ) :
    weight ε i (k + 1) ≤ (80 / ε) * ((i : ℝ) + 1) * weight ε (i + 1) k := by
  have hc : 0 ≤ (20 / ε) * ((i : ℝ) + 1) * coreWeight ε (i + 1) k := by
    have hcpos := coreWeight_pos hε (i + 1) k
    positivity
  have hd := mul_le_mul (squareDecay_le_four_succ i) (squareDecay_succ_le k)
    (squareDecay_pos (k + 1)).le (mul_nonneg (by norm_num) (squareDecay_pos (i + 1)).le)
  rw [weight_eq_core_decay, coreWeight_parameter_shift hε, weight_eq_core_decay]
  calc
    _ = ((20 / ε) * ((i : ℝ) + 1) * coreWeight ε (i + 1) k) *
        (squareDecay i * squareDecay (k + 1)) := by ring
    _ ≤ ((20 / ε) * ((i : ℝ) + 1) * coreWeight ε (i + 1) k) *
        (4 * squareDecay (i + 1) * squareDecay k) := mul_le_mul_of_nonneg_left hd hc
    _ = _ := by ring


-- @@ L291-293 verbatim
theorem weight_parameter_radial_shift_ratio {ε : ℝ} (hε : 0 < ε) (i k : ℕ) :
    weight ε i (k + 1) / weight ε (i + 1) k ≤ (80 / ε) * ((i : ℝ) + 1) := by
  exact (div_le_iff₀ (weight_pos hε (i + 1) k)).2 (weight_parameter_radial_shift hε i k)


-- @@ L295-299 verbatim
/-- The finite weight convolution associated with radial multiplication and
the parameter Leibniz rule. -/
def productWeightSum (ε : ℝ) (n m : ℕ) : ℝ :=
  ∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
    (m.choose kl.1 : ℝ) * weight ε ij.1 kl.1 * weight ε ij.2 kl.2


-- @@ L301-316 verbatim
theorem weight_product_term_le {ε : ℝ} (hε : 0 < ε) (i j k l : ℕ) :
    ((k + l).choose k : ℝ) * weight ε i k * weight ε j l ≤
      coreWeight ε (i + j) (k + l) * (squareDecay i * squareDecay j) *
        (squareDecay k * squareDecay l) := by
  have hd : 0 ≤ squareDecay i * squareDecay j * squareDecay k * squareDecay l := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (squareDecay_pos i).le
      (squareDecay_pos j).le) (squareDecay_pos k).le) (squareDecay_pos l).le
  calc
    _ = (((k + l).choose k : ℝ) * coreWeight ε i k * coreWeight ε j l) *
        (squareDecay i * squareDecay j * squareDecay k * squareDecay l) := by
      rw [weight_eq_core_decay, weight_eq_core_decay]
      ring
    _ ≤ coreWeight ε (i + j) (k + l) *
        (squareDecay i * squareDecay j * squareDecay k * squareDecay l) :=
      mul_le_mul_of_nonneg_right (coreWeight_product_le hε i j k l) hd
    _ = _ := by ring


-- @@ L318-355 verbatim
/-- The manuscript's uniform algebra constant `64`, with actual finite sums. -/
theorem productWeightSum_le {ε : ℝ} (hε : 0 < ε) (n m : ℕ) :
    productWeightSum ε n m ≤ 64 * weight ε n m := by
  have hsum : productWeightSum ε n m ≤
      ∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
        coreWeight ε n m * (squareDecay ij.1 * squareDecay ij.2) *
          (squareDecay kl.1 * squareDecay kl.2) := by
    apply Finset.sum_le_sum
    intro ij hij
    apply Finset.sum_le_sum
    intro kl hkl
    have h := weight_product_term_le hε ij.1 ij.2 kl.1 kl.2
    rw [mem_antidiagonal.mp hij, mem_antidiagonal.mp hkl] at h
    exact h
  have hfactor :
      (∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
        coreWeight ε n m * (squareDecay ij.1 * squareDecay ij.2) *
          (squareDecay kl.1 * squareDecay kl.2)) =
      coreWeight ε n m *
        (∑ ij ∈ antidiagonal n, squareDecay ij.1 * squareDecay ij.2) *
        (∑ kl ∈ antidiagonal m, squareDecay kl.1 * squareDecay kl.2) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hfactor] at hsum
  have hn0 : 0 ≤ ∑ ij ∈ antidiagonal n, squareDecay ij.1 * squareDecay ij.2 :=
    Finset.sum_nonneg (fun ij _ => mul_nonneg (squareDecay_pos _).le (squareDecay_pos _).le)
  have hm0 : 0 ≤ ∑ kl ∈ antidiagonal m, squareDecay kl.1 * squareDecay kl.2 :=
    Finset.sum_nonneg (fun kl _ => mul_nonneg (squareDecay_pos _).le (squareDecay_pos _).le)
  have hprod := mul_le_mul (squareDecay_convolution_le n) (squareDecay_convolution_le m)
    hm0 (mul_nonneg (by norm_num) (squareDecay_pos n).le)
  calc
    _ ≤ coreWeight ε n m *
        ((∑ ij ∈ antidiagonal n, squareDecay ij.1 * squareDecay ij.2) *
        (∑ kl ∈ antidiagonal m, squareDecay kl.1 * squareDecay kl.2)) := by
      simpa only [mul_assoc] using hsum
    _ ≤ coreWeight ε n m * ((8 * squareDecay n) * (8 * squareDecay m)) :=
      mul_le_mul_of_nonneg_left hprod (coreWeight_pos hε n m).le
    _ = _ := by rw [weight_eq_core_decay]; ring


-- @@ L357-360 verbatim
/-- Actual radial convolution with the parameter Leibniz coefficients. -/
def jetProduct (f g : ℕ → ℕ → ℝ) (n m : ℕ) : ℝ :=
  ∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
    (m.choose kl.1 : ℝ) * f ij.1 kl.1 * g ij.2 kl.2


-- @@ L362-371 verbatim
theorem abs_bilinear_term_le (a x y wx wy F G : ℝ)
    (ha : 0 ≤ a) (hF : 0 ≤ F) (_hG : 0 ≤ G) (hwx : 0 ≤ wx) (_hwy : 0 ≤ wy)
    (hx : |x| ≤ F * wx) (hy : |y| ≤ G * wy) :
    |a * x * y| ≤ (F * G) * (a * wx * wy) := by
  rw [abs_mul, abs_mul, abs_of_nonneg ha]
  calc
    a * |x| * |y| = a * (|x| * |y|) := by ring
    _ ≤ a * ((F * wx) * (G * wy)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hx hy (abs_nonneg y) (mul_nonneg hF hwx)) ha
    _ = _ := by ring


-- @@ L373-381 verbatim
theorem abs_double_sum_le {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (f M : ι → κ → ℝ) (h : ∀ i ∈ s, ∀ k ∈ t, |f i k| ≤ M i k) :
    |∑ i ∈ s, ∑ k ∈ t, f i k| ≤ ∑ i ∈ s, ∑ k ∈ t, M i k := by
  calc
    _ ≤ ∑ i ∈ s, |∑ k ∈ t, f i k| := abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      exact (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (h i hi))


-- @@ L383-407 verbatim
/-- Uniform coefficient product bound, requiring only the actual coefficient
bounds on the two input arrays. -/
theorem jetProduct_bound {ε F G : ℝ} (hε : 0 < ε) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (f g : ℕ → ℕ → ℝ)
    (hf : ∀ n m, |f n m| ≤ F * weight ε n m)
    (hg : ∀ n m, |g n m| ≤ G * weight ε n m) (n m : ℕ) :
    |jetProduct f g n m| ≤ 64 * F * G * weight ε n m := by
  have hsum : |jetProduct f g n m| ≤
      ∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
        (F * G) * ((m.choose kl.1 : ℝ) * weight ε ij.1 kl.1 * weight ε ij.2 kl.2) := by
    apply abs_double_sum_le
    intro ij hij kl hkl
    exact abs_bilinear_term_le _ _ _ _ _ _ _ (Nat.cast_nonneg _) hF hG
      (weight_pos hε _ _).le (weight_pos hε _ _).le (hf _ _) (hg _ _)
  have hfactor :
      (∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
        (F * G) * ((m.choose kl.1 : ℝ) * weight ε ij.1 kl.1 * weight ε ij.2 kl.2)) =
      (F * G) * productWeightSum ε n m := by
    simp only [productWeightSum, Finset.mul_sum]
  rw [hfactor] at hsum
  calc
    _ ≤ (F * G) * productWeightSum ε n m := hsum
    _ ≤ (F * G) * (64 * weight ε n m) :=
      mul_le_mul_of_nonneg_left (productWeightSum_le hε n m) (mul_nonneg hF hG)
    _ = _ := by ring


-- @@ L409-410 verbatim
/-- Radial divisor, given by `((n : ℝ) + 1) * ((n : ℝ) + r)`. -/
def radialDivisor (r n : ℕ) : ℝ := ((n : ℝ) + 1) * ((n : ℝ) + r)


-- @@ L412-415 verbatim
theorem radialDivisor_pos {r : ℕ} (hr : 1 ≤ r) (n : ℕ) : 0 < radialDivisor r n := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  unfold radialDivisor
  positivity


-- @@ L417-423 verbatim
/-- The extra parameter and dot factors fit inside the regular radial divisor. -/
theorem mixed_factors_le_divisor {r n i j : ℕ} (hr : 1 ≤ r) (hij : i + j = n) :
    ((i : ℝ) + 1) * (j : ℝ) ≤ radialDivisor r n := by
  have hi : i + 1 ≤ n + 1 := by omega
  have hj : j ≤ n + r := by omega
  unfold radialDivisor
  exact_mod_cast Nat.mul_le_mul hi hj


-- @@ L425-429 verbatim
/-- Shifted product weight sum, given by `∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
(m.choose kl.1 : ℝ) * weight ε (ij.1 + 1) kl.1 * weight ε ij.2 kl.2`. -/
def shiftedProductWeightSum (ε : ℝ) (n m : ℕ) : ℝ :=
  ∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
    (m.choose kl.1 : ℝ) * weight ε (ij.1 + 1) kl.1 * weight ε ij.2 kl.2


-- @@ L431-442 verbatim
theorem shiftedProductWeightSum_le {ε : ℝ} (hε : 0 < ε) (n m : ℕ) :
    shiftedProductWeightSum ε n m ≤ 64 * weight ε (n + 1) m := by
  have hsub : shiftedProductWeightSum ε n m ≤ productWeightSum ε (n + 1) m := by
    unfold productWeightSum
    rw [sum_antidiagonal_succ]
    change shiftedProductWeightSum ε n m ≤ _ + shiftedProductWeightSum ε n m
    apply le_add_of_nonneg_left
    apply Finset.sum_nonneg
    intro kl hkl
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (weight_pos hε _ _).le)
      (weight_pos hε _ _).le
  exact hsub.trans (productWeightSum_le hε (n + 1) m)


-- @@ L444-468 verbatim
/-- A single mixed term after applying the inverse radial divisor. -/
theorem mixed_weight_term_le {ε : ℝ} (hε : 0 < ε) {r n i j : ℕ}
    (hr : 1 ≤ r) (hij : i + j = n) (m k l : ℕ) :
    (((m.choose k : ℝ) * j) / radialDivisor r n) * weight ε i (k + 1) * weight ε j l ≤
      (80 / ε) * ((m.choose k : ℝ) * weight ε (i + 1) k * weight ε j l) := by
  have hD := radialDivisor_pos hr n
  have hcoef : 0 ≤ ((m.choose k : ℝ) * j) / radialDivisor r n := by positivity
  have hfactor : (((i : ℝ) + 1) * j) / radialDivisor r n ≤ 1 := by
    apply (div_le_iff₀ hD).2
    simpa only [one_mul] using mixed_factors_le_divisor hr hij
  have hnonneg : 0 ≤ (80 / ε) *
      ((m.choose k : ℝ) * weight ε (i + 1) k * weight ε j l) := by
    exact mul_nonneg (by positivity)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (weight_pos hε _ _).le) (weight_pos hε _ _).le)
  calc
    _ ≤ (((m.choose k : ℝ) * j) / radialDivisor r n) *
        ((80 / ε) * ((i : ℝ) + 1) * weight ε (i + 1) k) * weight ε j l := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (weight_parameter_radial_shift hε i k) hcoef)
        (weight_pos hε _ _).le
    _ = ((80 / ε) * ((m.choose k : ℝ) * weight ε (i + 1) k * weight ε j l)) *
        ((((i : ℝ) + 1) * j) / radialDivisor r n) := by ring
    _ ≤ ((80 / ε) * ((m.choose k : ℝ) * weight ε (i + 1) k * weight ε j l)) * 1 :=
      mul_le_mul_of_nonneg_left hfactor hnonneg
    _ = _ := mul_one _


-- @@ L470-474 verbatim
/-- Mixed weight sum, choosing the witness provided by `kl.1`. -/
def mixedWeightSum (ε : ℝ) (r n m : ℕ) : ℝ :=
  ∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
    (((m.choose kl.1 : ℝ) * ij.2) / radialDivisor r n) *
      weight ε ij.1 (kl.1 + 1) * weight ε ij.2 kl.2


-- @@ L476-496 verbatim
theorem mixedWeightSum_le {ε : ℝ} (hε : 0 < ε) {r : ℕ} (hr : 1 ≤ r) (n m : ℕ) :
    mixedWeightSum ε r n m ≤ (5120 / ε) * weight ε (n + 1) m := by
  have hsum : mixedWeightSum ε r n m ≤
      ∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
        (80 / ε) * ((m.choose kl.1 : ℝ) * weight ε (ij.1 + 1) kl.1 * weight ε ij.2 kl.2) := by
    apply Finset.sum_le_sum
    intro ij hij
    apply Finset.sum_le_sum
    intro kl hkl
    exact mixed_weight_term_le hε hr (mem_antidiagonal.mp hij) m kl.1 kl.2
  have hfactor :
      (∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
        (80 / ε) * ((m.choose kl.1 : ℝ) * weight ε (ij.1 + 1) kl.1 * weight ε ij.2 kl.2)) =
      (80 / ε) * shiftedProductWeightSum ε n m := by
    simp only [shiftedProductWeightSum, Finset.mul_sum]
  rw [hfactor] at hsum
  calc
    _ ≤ (80 / ε) * shiftedProductWeightSum ε n m := hsum
    _ ≤ (80 / ε) * (64 * weight ε (n + 1) m) :=
      mul_le_mul_of_nonneg_left (shiftedProductWeightSum_le hε n m) (by positivity)
    _ = _ := by ring


-- @@ L498-503 verbatim
/-- The coefficient at radial degree n+1 of J_r((∂η f) D_Y g).
The radial divisor is distributed over its finite convolution sum. -/
def inverseMixedJet (r : ℕ) (f g : ℕ → ℕ → ℝ) (n m : ℕ) : ℝ :=
  ∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
    (((m.choose kl.1 : ℝ) * ij.2) / radialDivisor r n) *
      f ij.1 (kl.1 + 1) * g ij.2 kl.2


-- @@ L505-532 verbatim
/-- The mixed derivative is bounded after radial inversion, with explicit
constant 5120/ε. Neither individual derivative is assumed bounded. -/
theorem inverseMixedJet_bound {ε F G : ℝ} (hε : 0 < ε) (hF : 0 ≤ F) (hG : 0 ≤ G)
    {r : ℕ} (hr : 1 ≤ r) (f g : ℕ → ℕ → ℝ)
    (hf : ∀ n m, |f n m| ≤ F * weight ε n m)
    (hg : ∀ n m, |g n m| ≤ G * weight ε n m) (n m : ℕ) :
    |inverseMixedJet r f g n m| ≤ (5120 / ε) * F * G * weight ε (n + 1) m := by
  have hD := radialDivisor_pos hr n
  have hsum : |inverseMixedJet r f g n m| ≤
      ∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
        (F * G) * ((((m.choose kl.1 : ℝ) * ij.2) / radialDivisor r n) *
          weight ε ij.1 (kl.1 + 1) * weight ε ij.2 kl.2) := by
    apply abs_double_sum_le
    intro ij hij kl hkl
    exact abs_bilinear_term_le _ _ _ _ _ _ _ (by positivity) hF hG
      (weight_pos hε _ _).le (weight_pos hε _ _).le (hf _ _) (hg _ _)
  have hfactor :
      (∑ ij ∈ antidiagonal n, ∑ kl ∈ antidiagonal m,
        (F * G) * ((((m.choose kl.1 : ℝ) * ij.2) / radialDivisor r n) *
          weight ε ij.1 (kl.1 + 1) * weight ε ij.2 kl.2)) =
      (F * G) * mixedWeightSum ε r n m := by
    simp only [mixedWeightSum, Finset.mul_sum]
  rw [hfactor] at hsum
  calc
    _ ≤ (F * G) * mixedWeightSum ε r n m := hsum
    _ ≤ (F * G) * ((5120 / ε) * weight ε (n + 1) m) :=
      mul_le_mul_of_nonneg_left (mixedWeightSum_le hε hr n m) (mul_nonneg hF hG)
    _ = _ := by ring


-- @@ L534-535 verbatim
/-- Coefficients of the radial averaging operator `Bf(Y)=∫₀¹ f(tY)dt`. -/
def averageJet (f : ℕ → ℕ → ℝ) (n m : ℕ) : ℝ := f n m / ((n : ℝ) + 1)


-- @@ L537-540 verbatim
/-- Coefficients of the zero-datum primitive. -/
def primitiveJet (f : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | n + 1, m => f n m / ((n : ℝ) + 1)


-- @@ L542-545 verbatim
/-- Coefficients of the regular zero-datum inverse of `Y f'' + r f'`. -/
def regularInverseJet (r : ℕ) (f : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | n + 1, m => f n m / radialDivisor r n


-- @@ L547-550 verbatim
/-- The primitive is applied together with the parameter derivative. -/
def parameterPrimitiveJet (f : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | n + 1, m => f n (m + 1) / ((n : ℝ) + 1)


-- @@ L552-559 verbatim
theorem averageJet_bound {ε F : ℝ} (_hε : 0 < ε) (_hF : 0 ≤ F)
    (f : ℕ → ℕ → ℝ) (hf : ∀ n m, |f n m| ≤ F * weight ε n m) (n m : ℕ) :
    |averageJet f n m| ≤ F * weight ε n m := by
  unfold averageJet
  rw [abs_div, abs_of_pos (by positivity : 0 < (n : ℝ) + 1)]
  exact (div_le_self (abs_nonneg _) (by
    have hn : (0 : ℝ) ≤ n := by positivity
    linarith)).trans (hf n m)


-- @@ L561-574 verbatim
theorem primitiveJet_bound {ε F : ℝ} (hε : 0 < ε) (hF : 0 ≤ F)
    (f : ℕ → ℕ → ℝ) (hf : ∀ n m, |f n m| ≤ F * weight ε n m) (n m : ℕ) :
    |primitiveJet f n m| ≤ 80 * F * weight ε n m := by
  cases n with
  | zero =>
      simpa only [primitiveJet, abs_zero] using
        (mul_nonneg (mul_nonneg (by norm_num) hF) (weight_pos hε 0 m).le)
  | succ n =>
      calc
        |primitiveJet f (n + 1) m| = |averageJet f n m| := rfl
        _ ≤ F * weight ε n m := averageJet_bound hε hF f hf n m
        _ ≤ F * (80 * weight ε (n + 1) m) :=
          mul_le_mul_of_nonneg_left (weight_radial_shift hε n m) hF
        _ = _ := by ring


-- @@ L576-582 verbatim
theorem radialDivisor_ge_one {r : ℕ} (hr : 1 ≤ r) (n : ℕ) : 1 ≤ radialDivisor r n := by
  have hn : (0 : ℝ) ≤ n := by positivity
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have ha : (1 : ℝ) ≤ n + 1 := by linarith
  have hb : (1 : ℝ) ≤ n + r := by linarith
  simpa only [one_mul, radialDivisor] using
    (mul_le_mul ha hb (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ (n : ℝ) + 1))


-- @@ L584-600 verbatim
theorem regularInverseJet_bound {ε F : ℝ} (hε : 0 < ε) (hF : 0 ≤ F)
    {r : ℕ} (hr : 1 ≤ r) (f : ℕ → ℕ → ℝ)
    (hf : ∀ n m, |f n m| ≤ F * weight ε n m) (n m : ℕ) :
    |regularInverseJet r f n m| ≤ 80 * F * weight ε n m := by
  cases n with
  | zero =>
      simpa only [regularInverseJet, abs_zero] using
        (mul_nonneg (mul_nonneg (by norm_num) hF) (weight_pos hε 0 m).le)
  | succ n =>
      rw [regularInverseJet, abs_div, abs_of_pos (radialDivisor_pos hr n)]
      calc
        |f n m| / radialDivisor r n ≤ |f n m| :=
          div_le_self (abs_nonneg _) (radialDivisor_ge_one hr n)
        _ ≤ F * weight ε n m := hf n m
        _ ≤ F * (80 * weight ε (n + 1) m) :=
          mul_le_mul_of_nonneg_left (weight_radial_shift hε n m) hF
        _ = _ := by ring


-- @@ L602-616 verbatim
theorem parameterPrimitiveJet_bound {ε F : ℝ} (hε : 0 < ε) (hF : 0 ≤ F)
    (f : ℕ → ℕ → ℝ) (hf : ∀ n m, |f n m| ≤ F * weight ε n m) (n m : ℕ) :
    |parameterPrimitiveJet f n m| ≤ (80 / ε) * F * weight ε n m := by
  cases n with
  | zero =>
      simpa only [parameterPrimitiveJet, abs_zero] using
        (mul_nonneg (mul_nonneg (show 0 ≤ 80 / ε by positivity) hF) (weight_pos hε 0 m).le)
  | succ n =>
      rw [parameterPrimitiveJet, abs_div, abs_of_pos (by positivity : 0 < (n : ℝ) + 1)]
      apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).2
      calc
        |f n (m + 1)| ≤ F * weight ε n (m + 1) := hf n (m + 1)
        _ ≤ F * ((80 / ε) * ((n : ℝ) + 1) * weight ε (n + 1) m) :=
          mul_le_mul_of_nonneg_left (weight_parameter_radial_shift hε n m) hF
        _ = _ := by ring


-- @@ L618-621 verbatim
/-- Put the already estimated mixed coefficient in its output radial degree. -/
def regularInverseMixedJet (r : ℕ) (f g : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | n + 1, m => inverseMixedJet r f g n m


-- @@ L623-634 verbatim
theorem regularInverseMixedJet_bound {ε F G : ℝ}
    (hε : 0 < ε) (hF : 0 ≤ F) (hG : 0 ≤ G) {r : ℕ} (hr : 1 ≤ r)
    (f g : ℕ → ℕ → ℝ)
    (hf : ∀ n m, |f n m| ≤ F * weight ε n m)
    (hg : ∀ n m, |g n m| ≤ G * weight ε n m) (n m : ℕ) :
    |regularInverseMixedJet r f g n m| ≤ (5120 / ε) * F * G * weight ε n m := by
  cases n with
  | zero =>
      simpa only [regularInverseMixedJet, abs_zero] using
        (mul_nonneg (mul_nonneg (mul_nonneg (show 0 ≤ 5120 / ε by positivity) hF) hG)
          (weight_pos hε 0 m).le)
  | succ n => exact inverseMixedJet_bound hε hF hG hr f g hf hg n m


-- @@ L636-636 verbatim
end


-- @@ L638-638 verbatim
end NavierStokes.AxisWeightEstimates


-- @@ L640-640 verbatim
end


-- @@ L642-642 verbatim
end


-- @@ L644-644 verbatim
@[expose] public section


-- @@ L646-646 verbatim
noncomputable section


-- @@ L648-648 verbatim
namespace NavierStokes.AxisCoefficientSpace


-- @@ L650-650 verbatim
open Set MeasureTheory

-- @@ L651-651 verbatim
open scoped Topology BoundedContinuousFunction ContDiff


-- @@ L653-659 verbatim
/-- A fixed nondegenerate compact real parameter interval. -/
structure Window where
  /-- Left of `Window`, of type `ℝ`. -/
  left : ℝ
  /-- Right of `Window`, of type `ℝ`. -/
  right : ℝ
  nondegenerate : left < right


-- @@ L661-662 verbatim
/-- Interval, given by `Icc I.left I.right`. -/
def Window.interval (I : Window) : Set ℝ := Icc I.left I.right


-- @@ L664-667 verbatim
/-- The continuous clamping map is only an extension device. Smoothness is
proved on the original closed interval, including its one-sided endpoint jets. -/
def Window.project (I : Window) : ℝ → I.interval :=
  projIcc I.left I.right I.nondegenerate.le


-- @@ L669-670 verbatim
theorem Window.continuous_project (I : Window) : Continuous I.project :=
  continuous_projIcc


-- @@ L672-674 verbatim
theorem Window.project_of_mem (I : Window) {x : ℝ} (hx : x ∈ I.interval) :
    I.project x = ⟨x, hx⟩ :=
  projIcc_of_mem I.nondegenerate.le hx


-- @@ L676-678 verbatim
/-- Ambient normalized jets with the supremum norm over both indices and
the compact parameter interval. -/
abbrev RawJets (I : Window) := ((ℕ × ℕ) × I.interval) →ᵇ ℝ


-- @@ L680-682 verbatim
/-- Unnormalized, continuously extended `m`-th jet of coefficient `n`. -/
def jet (I : Window) (w : ℕ → ℕ → ℝ) (A : RawJets I) (n m : ℕ) (x : ℝ) : ℝ :=
  w n m * A ((n, m), I.project x)


-- @@ L684-687 verbatim
theorem continuous_jet (I : Window) (w : ℕ → ℕ → ℝ) (A : RawJets I) (n m : ℕ) :
    Continuous (jet I w A n m) := by
  exact continuous_const.mul
    (A.continuous.comp (continuous_const.prodMk I.continuous_project))


-- @@ L689-691 verbatim
theorem continuous_jet_parameter (I : Window) (w : ℕ → ℕ → ℝ) (n m : ℕ) (x : ℝ) :
    Continuous (fun A : RawJets I => jet I w A n m x) := by
  exact continuous_const.mul (continuous_eval_const _)


-- @@ L693-698 verbatim
theorem continuous_jet_joint (I : Window) (w : ℕ → ℕ → ℝ) (n m : ℕ) :
    Continuous (fun p : RawJets I × ℝ => jet I w p.1 n m p.2) := by
  exact continuous_const.mul
    (continuous_eval.comp
      (continuous_fst.prodMk
        (continuous_const.prodMk (I.continuous_project.comp continuous_snd))))


-- @@ L700-701 verbatim
@[simp] theorem jet_zero (I : Window) (w : ℕ → ℕ → ℝ) (n m : ℕ) (x : ℝ) :
    jet I w 0 n m x = 0 := by simp [jet]


-- @@ L703-706 verbatim
@[simp] theorem jet_add (I : Window) (w : ℕ → ℕ → ℝ) (A B : RawJets I)
    (n m : ℕ) (x : ℝ) :
    jet I w (A + B) n m x = jet I w A n m x + jet I w B n m x := by
  simp [jet, mul_add]


-- @@ L708-711 verbatim
@[simp] theorem jet_sub (I : Window) (w : ℕ → ℕ → ℝ) (A B : RawJets I)
    (n m : ℕ) (x : ℝ) :
    jet I w (A - B) n m x = jet I w A n m x - jet I w B n m x := by
  simp [jet, mul_sub]


-- @@ L713-717 verbatim
@[simp] theorem jet_smul (I : Window) (w : ℕ → ℕ → ℝ) (c : ℝ) (A : RawJets I)
    (n m : ℕ) (x : ℝ) :
    jet I w (c • A) n m x = c * jet I w A n m x := by
  simp [jet]
  ring


-- @@ L719-724 verbatim
/-- Compatibility is an actual FTC identity for every successive pair of
jets, throughout the full interval. -/
def Compatible (I : Window) (w : ℕ → ℕ → ℝ) (A : RawJets I) : Prop :=
  ∀ n m x, x ∈ I.interval →
    jet I w A n m x = jet I w A n m I.left +
      ∫ t in I.left..x, jet I w A n (m + 1) t


-- @@ L726-744 verbatim
/-- The compatible arrays form a linear subspace of the ambient Banach space. -/
def compatibleSubmodule (I : Window) (w : ℕ → ℕ → ℝ) : Submodule ℝ (RawJets I) where
  carrier := {A | Compatible I w A}
  zero_mem' := by
    intro n m x hx
    simp
  add_mem' := by
    intro A B hA hB n m x hx
    simp only [jet_add]
    rw [intervalIntegral.integral_add
      ((continuous_jet I w A n (m + 1)).intervalIntegrable I.left x)
      ((continuous_jet I w B n (m + 1)).intervalIntegrable I.left x),
      hA n m x hx, hB n m x hx]
    ring
  smul_mem' := by
    intro c A hA n m x hx
    simp only [jet_smul, intervalIntegral.integral_const_mul]
    rw [hA n m x hx]
    ring


-- @@ L746-756 verbatim
/-- Closedness follows from continuous evaluation and continuous interval
integration. This is the completeness-critical compatibility argument. -/
theorem isClosed_compatible (I : Window) (w : ℕ → ℕ → ℝ) :
    IsClosed {A : RawJets I | Compatible I w A} := by
  simp only [Compatible, ofPred_forall]
  refine isClosed_iInter fun n => isClosed_iInter fun m =>
    isClosed_iInter fun x => isClosed_iInter fun hx => ?_
  exact isClosed_eq (continuous_jet_parameter I w n m x)
    ((continuous_jet_parameter I w n m I.left).add
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (continuous_jet_joint I w n (m + 1)) I.left x))


-- @@ L758-759 verbatim
/-- The coefficient space, retaining the inherited genuine norm and linear structure. -/
abbrev CoefficientSpace (I : Window) (w : ℕ → ℕ → ℝ) := compatibleSubmodule I w


-- @@ L761-763 verbatim
instance coefficientSpace_complete (I : Window) (w : ℕ → ℕ → ℝ) :
    CompleteSpace (CoefficientSpace I w) :=
  (isClosed_compatible I w).completeSpace_coe


-- @@ L765-767 verbatim
/-- A coefficient is the zeroth actual jet. -/
def coefficient (I : Window) (w : ℕ → ℕ → ℝ) (A : CoefficientSpace I w) (n : ℕ) : ℝ → ℝ :=
  jet I w A.1 n 0


-- @@ L769-777 verbatim
/-- FTC compatibility identifies the derivative within the closed interval;
this includes the corresponding one-sided endpoint derivatives. -/
theorem hasDerivWithinAt_jet (I : Window) (w : ℕ → ℕ → ℝ)
    (A : CoefficientSpace I w) (n m : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    HasDerivWithinAt (jet I w A.1 n m) (jet I w A.1 n (m + 1) x) I.interval x := by
  have h := ((continuous_jet I w A.1 n (m + 1)).integral_hasStrictDerivAt I.left
      x).hasDerivAt.const_add
    (jet I w A.1 n m I.left)
  exact h.hasDerivWithinAt.congr_of_mem (fun y hy => A.2 n m y hy) hx


-- @@ L779-783 verbatim
theorem derivWithin_jet (I : Window) (w : ℕ → ℕ → ℝ)
    (A : CoefficientSpace I w) (n m : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    derivWithin (jet I w A.1 n m) I.interval x = jet I w A.1 n (m + 1) x :=
  (hasDerivWithinAt_jet I w A n m hx).derivWithin
    (uniqueDiffOn_Icc I.nondegenerate x hx)


-- @@ L785-791 verbatim
/-- At every interior point these are the ordinary real derivatives. -/
theorem hasDerivAt_jet_interior (I : Window) (w : ℕ → ℕ → ℝ)
    (A : CoefficientSpace I w) (n m : ℕ) {x : ℝ}
    (hx : x ∈ Ioo I.left I.right) :
    HasDerivAt (jet I w A.1 n m) (jet I w A.1 n (m + 1) x) x :=
  (hasDerivWithinAt_jet I w A n m ⟨hx.1.le, hx.2.le⟩).hasDerivAt
    (Icc_mem_nhds hx.1 hx.2)


-- @@ L793-802 verbatim
/-- Every stored jet is the corresponding iterated derivative of the actual function. -/
theorem iteratedDerivWithin_jet (I : Window) (w : ℕ → ℕ → ℝ)
    (A : CoefficientSpace I w) (n q m : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    iteratedDerivWithin m (jet I w A.1 n q) I.interval x = jet I w A.1 n (q + m) x := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    rw [iteratedDerivWithin_succ,
      derivWithin_congr (fun y hy => ih hy) (ih hx), derivWithin_jet I w A n (q + m) hx]
    simp only [Nat.add_assoc]


-- @@ L804-807 verbatim
theorem iteratedDerivWithin_coefficient (I : Window) (w : ℕ → ℕ → ℝ)
    (A : CoefficientSpace I w) (n m : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    iteratedDerivWithin m (coefficient I w A n) I.interval x = jet I w A.1 n m x := by
  simpa only [coefficient, Nat.zero_add] using iteratedDerivWithin_jet I w A n 0 m hx


-- @@ L809-816 verbatim
/-- Genuine infinite smoothness on the full compact interval. -/
theorem contDiffOn_jet (I : Window) (w : ℕ → ℕ → ℝ)
    (A : CoefficientSpace I w) (n q : ℕ) :
    ContDiffOn ℝ ∞ (jet I w A.1 n q) I.interval := by
  apply contDiffOn_of_differentiableOn_deriv
  intro m hm x hx
  exact ((hasDerivWithinAt_jet I w A n (q + m) hx).congr_of_mem
    (fun y hy => iteratedDerivWithin_jet I w A n q m hy) hx).differentiableWithinAt


-- @@ L818-821 verbatim
theorem contDiffOn_coefficient (I : Window) (w : ℕ → ℕ → ℝ)
    (A : CoefficientSpace I w) (n : ℕ) :
    ContDiffOn ℝ ∞ (coefficient I w A n) I.interval :=
  contDiffOn_jet I w A n 0


-- @@ L823-830 verbatim
/-- On the interior these are ordinary smooth real functions on an open
neighborhood, so an original interval may be placed inside this enlarged one. -/
theorem contDiffAt_coefficient_interior (I : Window) (w : ℕ → ℕ → ℝ)
    (A : CoefficientSpace I w) (n : ℕ) {x : ℝ}
    (hx : x ∈ Ioo I.left I.right) :
    ContDiffAt ℝ ∞ (coefficient I w A n) x :=
  ((contDiffOn_coefficient I w A n) x ⟨hx.1.le, hx.2.le⟩).contDiffAt
    (Icc_mem_nhds hx.1 hx.2)


-- @@ L832-838 verbatim
/-- The inherited norm controls every actual parameter derivative with its weight. -/
theorem abs_jet_le (I : Window) (w : ℕ → ℕ → ℝ) (A : CoefficientSpace I w)
    (n m : ℕ) (x : ℝ) :
    |jet I w A.1 n m x| ≤ |w n m| * ‖A‖ := by
  rw [jet, abs_mul]
  exact mul_le_mul_of_nonneg_left
    (A.1.norm_coe_le_norm ((n, m), I.project x)) (abs_nonneg _)


-- @@ L840-844 verbatim
theorem abs_iteratedDerivWithin_coefficient_le (I : Window) (w : ℕ → ℕ → ℝ)
    (A : CoefficientSpace I w) (n m : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    |iteratedDerivWithin m (coefficient I w A n) I.interval x| ≤ |w n m| * ‖A‖ := by
  rw [iteratedDerivWithin_coefficient I w A n m hx]
  exact abs_jet_le I w A n m x


-- @@ L846-850 verbatim
/-- Norm convergence controls every derivative uniformly in the parameter. -/
theorem abs_jet_sub_le (I : Window) (w : ℕ → ℕ → ℝ) (A B : CoefficientSpace I w)
    (n m : ℕ) (x : ℝ) :
    |jet I w A.1 n m x - jet I w B.1 n m x| ≤ |w n m| * ‖A - B‖ := by
  simpa only [Submodule.coe_sub, jet_sub] using abs_jet_le I w (A - B) n m x


-- @@ L852-861 verbatim
/-- For nonzero weights, the normalized actual derivative recovers exactly
the stored bounded-continuous coordinate. -/
theorem normalized_derivative (I : Window) (w : ℕ → ℕ → ℝ)
    (hw : ∀ n m, w n m ≠ 0) (A : CoefficientSpace I w)
    (n m : ℕ) (x : I.interval) :
    iteratedDerivWithin m (coefficient I w A n) I.interval x / w n m =
      A.1 ((n, m), x) := by
  rw [iteratedDerivWithin_coefficient I w A n m x.property,
    jet, I.project_of_mem x.property]
  exact mul_div_cancel_left₀ _ (hw n m)


-- @@ L863-871 verbatim
theorem quotient_abs_derivative (I : Window) (w : ℕ → ℕ → ℝ)
    (hw : ∀ n m, 0 < w n m) (A : CoefficientSpace I w)
    (n m : ℕ) (x : I.interval) :
    |iteratedDerivWithin m (coefficient I w A n) I.interval x| / w n m =
      |A.1 ((n, m), x)| := by
  calc
    _ = |iteratedDerivWithin m (coefficient I w A n) I.interval x / w n m| := by
      rw [abs_div, abs_of_pos (hw n m)]
    _ = _ := by rw [normalized_derivative I w (fun n m => (hw n m).ne') A n m x]


-- @@ L873-889 verbatim
/-- This is precisely the supremum quotient norm in the manuscript,
expressed by its universal upper-bound characterization. -/
theorem norm_le_iff_derivative_bound (I : Window) (w : ℕ → ℕ → ℝ)
    (hw : ∀ n m, 0 < w n m) (A : CoefficientSpace I w) (C : ℝ) (hC : 0 ≤ C) :
    ‖A‖ ≤ C ↔ ∀ (n m : ℕ) (x : I.interval),
      |iteratedDerivWithin m (coefficient I w A n) I.interval x| / w n m ≤ C := by
  change ‖A.1‖ ≤ C ↔ _
  rw [BoundedContinuousFunction.norm_le hC]
  constructor
  · intro h n m x
    rw [quotient_abs_derivative I w hw A n m x]
    exact h ((n, m), x)
  · intro h p
    rcases p with ⟨⟨n, m⟩, x⟩
    have hx := h n m x
    rw [quotient_abs_derivative I w hw A n m x] at hx
    exact hx


-- @@ L891-903 verbatim
/-- Positive weights leave no independent or invisible jet coordinates:
equality of the actual coefficient functions forces equality in the space. -/
theorem coefficient_ext (I : Window) (w : ℕ → ℕ → ℝ)
    (hw : ∀ n m, w n m ≠ 0) (A B : CoefficientSpace I w)
    (h : ∀ n x, x ∈ I.interval → coefficient I w A n x = coefficient I w B n x) :
    A = B := by
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  rintro ⟨⟨n, m⟩, x⟩
  rw [← normalized_derivative I w hw A n m x,
    ← normalized_derivative I w hw B n m x]
  congr 1
  exact iteratedDerivWithin_congr (fun y hy => h n y hy) x.property


-- @@ L905-916 verbatim
/-- Normalize an actual continuous jet family with a uniform weighted bound. -/
def rawOfJetFamily (I : Window) (w : ℕ → ℕ → ℝ) (hw : ∀ n m, 0 < w n m)
    (J : ℕ → ℕ → ℝ → ℝ) (hcont : ∀ n m, ContinuousOn (J n m) I.interval)
    (C : ℝ) (hbound : ∀ n m x, x ∈ I.interval → |J n m x| ≤ C * w n m) : RawJets I :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p : (ℕ × ℕ) × I.interval => J p.1.1 p.1.2 p.2 / w p.1.1 p.1.2)
    (continuous_prod_of_discrete_left.mpr
      (fun p => (hcont p.1 p.2).domRestrict.div_const (w p.1 p.2))) C
    (by
      rintro ⟨⟨n, m⟩, x⟩
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (hw n m)]
      exact (div_le_iff₀ (hw n m)).mpr (hbound n m x x.property))


-- @@ L918-925 verbatim
theorem jet_rawOfJetFamily (I : Window) (w : ℕ → ℕ → ℝ) (hw : ∀ n m, 0 < w n m)
    (J : ℕ → ℕ → ℝ → ℝ) (hcont : ∀ n m, ContinuousOn (J n m) I.interval)
    (C : ℝ) (hbound : ∀ n m x, x ∈ I.interval → |J n m x| ≤ C * w n m)
    (n m : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    jet I w (rawOfJetFamily I w hw J hcont C hbound) n m x = J n m x := by
  change w n m * (J n m (I.project x) / w n m) = J n m x
  rw [I.project_of_mem hx]
  exact mul_div_cancel₀ _ (hw n m).ne'


-- @@ L927-955 verbatim
/-- Actual derivative compatibility implies the closed FTC compatibility
required by the Banach-space representation. -/
theorem compatible_rawOfJetFamily (I : Window) (w : ℕ → ℕ → ℝ) (hw : ∀ n m, 0 < w n m)
    (J : ℕ → ℕ → ℝ → ℝ) (hcont : ∀ n m, ContinuousOn (J n m) I.interval)
    (hderiv : ∀ n m x, x ∈ I.interval →
      HasDerivWithinAt (J n m) (J n (m + 1) x) I.interval x)
    (C : ℝ) (hbound : ∀ n m x, x ∈ I.interval → |J n m x| ≤ C * w n m) :
    Compatible I w (rawOfJetFamily I w hw J hcont C hbound) := by
  intro n m x hx
  have hleft : I.left ∈ I.interval := ⟨le_rfl, I.nondegenerate.le⟩
  have hsub : Icc I.left x ⊆ I.interval := fun y hy => ⟨hy.1, hy.2.trans hx.2⟩
  have hint : IntervalIntegrable (J n (m + 1)) volume I.left x :=
    ContinuousOn.intervalIntegrable_of_Icc hx.1 ((hcont n (m + 1)).mono hsub)
  have hFTC : (∫ t in I.left..x, J n (m + 1) t) = J n m x - J n m I.left := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
      ((hcont n m).mono hsub) _ hint
    intro y hy
    exact (hderiv n m y (hsub ⟨hy.1.le, hy.2.le⟩)).hasDerivAt
      (Icc_mem_nhds hy.1 (hy.2.trans_le hx.2))
  have hintEq : (∫ t in I.left..x,
      jet I w (rawOfJetFamily I w hw J hcont C hbound) n (m + 1) t) =
      ∫ t in I.left..x, J n (m + 1) t := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hx.1] at hy
    exact jet_rawOfJetFamily I w hw J hcont C hbound n (m + 1) (hsub hy)
  rw [jet_rawOfJetFamily I w hw J hcont C hbound n m hx,
    jet_rawOfJetFamily I w hw J hcont C hbound n m hleft, hintEq, hFTC]
  ring


-- @@ L957-967 verbatim
/-- Reverse constructor used by genuine products and radial operators:
a continuous family with actual adjacent derivatives and the weighted bound
becomes an element of the complete coefficient space. -/
def ofJetFamily (I : Window) (w : ℕ → ℕ → ℝ) (hw : ∀ n m, 0 < w n m)
    (J : ℕ → ℕ → ℝ → ℝ) (hcont : ∀ n m, ContinuousOn (J n m) I.interval)
    (hderiv : ∀ n m x, x ∈ I.interval →
      HasDerivWithinAt (J n m) (J n (m + 1) x) I.interval x)
    (C : ℝ) (_hC : 0 ≤ C)
    (hbound : ∀ n m x, x ∈ I.interval → |J n m x| ≤ C * w n m) : CoefficientSpace I w :=
  ⟨rawOfJetFamily I w hw J hcont C hbound,
    compatible_rawOfJetFamily I w hw J hcont hderiv C hbound⟩


-- @@ L969-977 verbatim
theorem jet_ofJetFamily (I : Window) (w : ℕ → ℕ → ℝ) (hw : ∀ n m, 0 < w n m)
    (J : ℕ → ℕ → ℝ → ℝ) (hcont : ∀ n m, ContinuousOn (J n m) I.interval)
    (hderiv : ∀ n m x, x ∈ I.interval →
      HasDerivWithinAt (J n m) (J n (m + 1) x) I.interval x)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n m x, x ∈ I.interval → |J n m x| ≤ C * w n m)
    (n m : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    jet I w (ofJetFamily I w hw J hcont hderiv C hC hbound).1 n m x = J n m x :=
  jet_rawOfJetFamily I w hw J hcont C hbound n m hx


-- @@ L979-987 verbatim
theorem coefficient_ofJetFamily (I : Window) (w : ℕ → ℕ → ℝ) (hw : ∀ n m, 0 < w n m)
    (J : ℕ → ℕ → ℝ → ℝ) (hcont : ∀ n m, ContinuousOn (J n m) I.interval)
    (hderiv : ∀ n m x, x ∈ I.interval →
      HasDerivWithinAt (J n m) (J n (m + 1) x) I.interval x)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n m x, x ∈ I.interval → |J n m x| ≤ C * w n m)
    (n : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    coefficient I w (ofJetFamily I w hw J hcont hderiv C hC hbound) n x = J n 0 x :=
  jet_ofJetFamily I w hw J hcont hderiv C hC hbound n 0 hx


-- @@ L989-1000 verbatim
theorem norm_ofJetFamily_le (I : Window) (w : ℕ → ℕ → ℝ) (hw : ∀ n m, 0 < w n m)
    (J : ℕ → ℕ → ℝ → ℝ) (hcont : ∀ n m, ContinuousOn (J n m) I.interval)
    (hderiv : ∀ n m x, x ∈ I.interval →
      HasDerivWithinAt (J n m) (J n (m + 1) x) I.interval x)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n m x, x ∈ I.interval → |J n m x| ≤ C * w n m) :
    ‖ofJetFamily I w hw J hcont hderiv C hC hbound‖ ≤ C := by
  apply (norm_le_iff_derivative_bound I w hw _ C hC).mpr
  intro n m x
  rw [iteratedDerivWithin_coefficient I w _ n m x.property,
    jet_ofJetFamily I w hw J hcont hderiv C hC hbound n m x.property]
  exact (div_le_iff₀ (hw n m)).mpr (hbound n m x x.property)


-- @@ L1002-1013 verbatim
/-- A smooth coefficient family's genuine iterated derivatives form the
adjacent derivative chain required by `ofJetFamily`. -/
theorem hasDerivWithinAt_iterated_smooth (I : Window) (F : ℕ → ℝ → ℝ)
    (hF : ∀ n, ContDiffOn ℝ ∞ (F n) I.interval) (n m : ℕ)
    {x : ℝ} (hx : x ∈ I.interval) :
    HasDerivWithinAt (iteratedDerivWithin m (F n) I.interval)
      (iteratedDerivWithin (m + 1) (F n) I.interval x) I.interval x := by
  have hd : DifferentiableWithinAt ℝ (iteratedDerivWithin m (F n) I.interval) I.interval x :=
    (hF n).differentiableOn_iteratedDerivWithin (m := m)
      (by exact_mod_cast (ENat.natCast_lt_top m))
      (uniqueDiffOn_Icc I.nondegenerate) x hx
  simpa only [iteratedDerivWithin_succ] using hd.hasDerivWithinAt


-- @@ L1015-1026 verbatim
/-- Reverse constructor from actual smooth coefficient functions with
uniform bounds on all their parameter derivatives. -/
def ofSmoothFamily (I : Window) (w : ℕ → ℕ → ℝ) (hw : ∀ n m, 0 < w n m)
    (F : ℕ → ℝ → ℝ) (hF : ∀ n, ContDiffOn ℝ ∞ (F n) I.interval)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n m x, x ∈ I.interval →
      |iteratedDerivWithin m (F n) I.interval x| ≤ C * w n m) : CoefficientSpace I w :=
  ofJetFamily I w hw (fun n m => iteratedDerivWithin m (F n) I.interval)
    (fun n m => (hF n).continuousOn_iteratedDerivWithin (m := m)
      (by exact_mod_cast (ENat.natCast_lt_top m).le)
      (uniqueDiffOn_Icc I.nondegenerate))
    (fun n m _ hx => hasDerivWithinAt_iterated_smooth I F hF n m hx) C hC hbound


-- @@ L1028-1037 verbatim
theorem jet_ofSmoothFamily (I : Window) (w : ℕ → ℕ → ℝ) (hw : ∀ n m, 0 < w n m)
    (F : ℕ → ℝ → ℝ) (hF : ∀ n, ContDiffOn ℝ ∞ (F n) I.interval)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n m x, x ∈ I.interval →
      |iteratedDerivWithin m (F n) I.interval x| ≤ C * w n m)
    (n m : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    jet I w (ofSmoothFamily I w hw F hF C hC hbound).1 n m x =
      iteratedDerivWithin m (F n) I.interval x := by
  unfold ofSmoothFamily
  exact jet_ofJetFamily I w hw _ _ _ C hC hbound n m hx


-- @@ L1039-1047 verbatim
theorem coefficient_ofSmoothFamily (I : Window) (w : ℕ → ℕ → ℝ) (hw : ∀ n m, 0 < w n m)
    (F : ℕ → ℝ → ℝ) (hF : ∀ n, ContDiffOn ℝ ∞ (F n) I.interval)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n m x, x ∈ I.interval →
      |iteratedDerivWithin m (F n) I.interval x| ≤ C * w n m)
    (n : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    coefficient I w (ofSmoothFamily I w hw F hF C hC hbound) n x = F n x := by
  simpa only [coefficient, iteratedDerivWithin_zero] using
    jet_ofSmoothFamily I w hw F hF C hC hbound n 0 hx


-- @@ L1049-1056 verbatim
theorem norm_ofSmoothFamily_le (I : Window) (w : ℕ → ℕ → ℝ) (hw : ∀ n m, 0 < w n m)
    (F : ℕ → ℝ → ℝ) (hF : ∀ n, ContDiffOn ℝ ∞ (F n) I.interval)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n m x, x ∈ I.interval →
      |iteratedDerivWithin m (F n) I.interval x| ≤ C * w n m) :
    ‖ofSmoothFamily I w hw F hF C hC hbound‖ ≤ C := by
  unfold ofSmoothFamily
  exact norm_ofJetFamily_le I w hw _ _ _ C hC hbound


-- @@ L1058-1061 verbatim
/-- The specific space in GAX.2, with the manuscript's exact positive weights
when `ε>0`. Completeness and normed vector-space structures are inherited. -/
abbrev AxisSpace (I : Window) (ε : ℝ) :=
  CoefficientSpace I (AxisWeightEstimates.weight ε)


-- @@ L1063-1065 verbatim
/-- The concrete space is a complete normed space of actual smooth functions. -/
theorem axisSpace_complete (I : Window) (ε : ℝ) : CompleteSpace (AxisSpace I ε) :=
  inferInstance


-- @@ L1067-1069 verbatim
theorem axisSpace_smooth (I : Window) (ε : ℝ) (A : AxisSpace I ε) (n : ℕ) :
    ContDiffOn ℝ ∞ (coefficient I (AxisWeightEstimates.weight ε) A n) I.interval :=
  contDiffOn_coefficient I (AxisWeightEstimates.weight ε) A n


-- @@ L1071-1077 verbatim
/-- Each actual derivative is controlled by exactly the printed weight. -/
theorem axisSpace_derivative_bound (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (n m : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    |iteratedDerivWithin m (coefficient I (AxisWeightEstimates.weight ε) A n) I.interval x| ≤
      AxisWeightEstimates.weight ε n m * ‖A‖ := by
  simpa only [abs_of_pos (AxisWeightEstimates.weight_pos hε n m)] using
    abs_iteratedDerivWithin_coefficient_le I (AxisWeightEstimates.weight ε) A n m hx


-- @@ L1079-1086 verbatim
/-- The exact manuscript norm, with actual derivatives in its quotient. -/
theorem axisSpace_norm_le_iff (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (C : ℝ) (hC : 0 ≤ C) :
    ‖A‖ ≤ C ↔ ∀ (n m : ℕ) (x : I.interval),
      |iteratedDerivWithin m (coefficient I (AxisWeightEstimates.weight ε) A n) I.interval x| /
        AxisWeightEstimates.weight ε n m ≤ C :=
  norm_le_iff_derivative_bound I (AxisWeightEstimates.weight ε)
    (AxisWeightEstimates.weight_pos hε) A C hC


-- @@ L1088-1088 verbatim
end NavierStokes.AxisCoefficientSpace


-- @@ L1090-1090 verbatim
end
