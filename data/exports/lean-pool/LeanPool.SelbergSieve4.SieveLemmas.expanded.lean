/-
Copyright (c) 2026 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import LeanPool.SelbergSieve4.UpperBoundSieve
import LeanPool.SelbergSieve4.AuxResults
import LeanPool.SelbergSieve4.ForMathlib.Basic
import LeanPool.SelbergSieve4.Tactic.AesopDiv
import LeanPool.SelbergSieve4.Tactic.AesopInit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.Positivity.Finset


-- @@ L19-21 verbatim
/-!
# LeanPool.SelbergSieve4.SieveLemmas
-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
open scoped BigOperators ArithmeticFunction.zeta ArithmeticFunction.Moebius ArithmeticFunction.omega


-- @@ L29-29 verbatim
open Finset Real Nat Aux


-- @@ L31-31 verbatim
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)


-- @@ L33-49 verbatim
/-- Data for a finite weighted sieve problem. -/
structure Sieve where mk ::
  /-- Finite support of integers being sifted. -/
  support : Finset ℕ
  /-- Product of the primes used by the sieve. -/
  prodPrimes : ℕ
  prodPrimes_squarefree : Squarefree prodPrimes
  /-- Nonnegative weights on the support. -/
  weights : ℕ → ℝ
  weights_nonneg : ∀ n : ℕ, 0 ≤ weights n
  /-- Main term for the weighted support. -/
  totalMass : ℝ
  /-- Local density arithmetic function. -/
  nu : ArithmeticFunction ℝ
  nu_mult : nu.IsMultiplicative
  nu_pos_of_prime : ∀ p : ℕ, p.Prime → p ∣ prodPrimes → 0 < nu p
  nu_lt_one_of_prime : ∀ p : ℕ, p.Prime → p ∣ prodPrimes → nu p < 1


-- @@ L51-51 verbatim
attribute [aesop safe (rule_sets := [Divisibility])] Sieve.prodPrimes_squarefree

-- @@ L52-52 verbatim
attribute [arith_mult] Sieve.nu_mult


-- @@ L54-54 verbatim
namespace Sieve


-- @@ L56-56 verbatim
variable (s : Sieve)

-- @@ L57-57 verbatim
local notation3 "ν" => Sieve.nu s

-- @@ L58-58 verbatim
local notation3 "P" => Sieve.prodPrimes s

-- @@ L59-59 verbatim
local notation3 "a" => Sieve.weights s

-- @@ L60-60 verbatim
local notation3 "X" => Sieve.totalMass s

-- @@ L61-61 verbatim
local notation3 "A" => Sieve.support s


-- @@ L63-66 verbatim
/-- Weighted count of support elements divisible by `d`. -/
@[simp]
def multSum (d : ℕ) : ℝ :=
  ∑ n ∈ A, if d ∣ n then a n else 0


-- @@ L68-70 verbatim
local notation3 "𝒜" => Sieve.multSum s

-- A_d = ν (d)/d X + R_d

-- @@ L71-74 verbatim
/-- Remainder term after subtracting the expected main term from `multSum`. -/
@[simp]
def rem (d : ℕ) : ℝ :=
  𝒜 d - ν d * X


-- @@ L76-76 verbatim
local notation3 "R" => Sieve.rem s


-- @@ L78-80 verbatim
/-- Weighted count of support elements coprime to the sieve modulus. -/
def siftedSum : ℝ :=
  ∑ d ∈ A, if Coprime P d then a d else 0


-- @@ L82-82 verbatim
open scoped ArithmeticFunction

-- @@ L83-85 verbatim
/-- Selberg local factor product used in the simple upper-bound sieve. -/
def selbergTerms : ArithmeticFunction ℝ :=
  s.nu.pmul (.prodPrimeFactors fun p =>  1 / (1 - ν p))


-- @@ L87-87 verbatim
local notation3 "g" => Sieve.selbergTerms s


-- @@ L89-95 verbatim
/-- Expands `selbergTerms` as a product over the prime factors of `d`. -/
theorem selbergTerms_apply (d : ℕ) :
    g d = ν d * ∏ p ∈ d.primeFactors, 1/(1 - ν p) := by
  unfold selbergTerms
  by_cases h : d=0
  · rw [h]; simp
  rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.prodPrimeFactors_apply h]



-- @@ L98-100 verbatim
/-- Main contribution of an upper-bound sieve weight. -/
def mainSum (μPlus : ℕ → ℝ) : ℝ :=
  ∑ d ∈ divisors P, μPlus d * ν d


-- @@ L102-104 verbatim
/-- Error contribution of an upper-bound sieve weight. -/
def errSum (μPlus : ℕ → ℝ) : ℝ :=
  ∑ d ∈ divisors P, |μPlus d| * |R d|


-- @@ L106-106 verbatim
section SieveLemmas


-- @@ L108-110 verbatim
@[aesop forward safe (rule_sets := [Divisibility])]
theorem prodPrimes_ne_zero : P ≠ 0 :=
  Squarefree.ne_zero s.prodPrimes_squarefree


-- @@ L112-113 verbatim
theorem squarefree_of_dvd_prodPrimes {d : ℕ} (hd : d ∣ P) : Squarefree d :=
  Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree


-- @@ L115-117 verbatim
theorem squarefree_of_mem_divisors_prodPrimes {d : ℕ} (hd : d ∈ divisors P) : Squarefree d := by
  simp only [Nat.mem_divisors] at hd
  exact Squarefree.squarefree_of_dvd hd.left s.prodPrimes_squarefree


-- @@ L119-128 verbatim
theorem nu_pos_of_dvd_prodPrimes {d : ℕ} (hd : d ∣ P) : 0 < ν d := by
  calc
    0 < ∏ p ∈ d.primeFactors, ν p := by
      apply prod_pos
      intro p hpd
      have hp_prime : p.Prime := by exact prime_of_mem_primeFactors hpd
      have hp_dvd : p ∣ P := (dvd_of_mem_primeFactors hpd).trans hd
      exact s.nu_pos_of_prime p hp_prime hp_dvd
    _ = ν d := prod_factors_of_mult ν s.nu_mult
      (Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree)


-- @@ L130-132 verbatim
theorem nu_ne_zero {d : ℕ} (hd : d ∣ P) : ν d ≠ 0 := by
  apply _root_.ne_of_gt
  exact nu_pos_of_dvd_prodPrimes s hd


-- @@ L134-137 verbatim
theorem nu_ne_zero_of_mem_divisors_prodPrimes {d : ℕ} (hd : d ∈ divisors P) : ν d ≠ 0 := by
  apply _root_.ne_of_gt
  rw [mem_divisors] at hd
  apply s.nu_pos_of_dvd_prodPrimes hd.left


-- @@ L139-140 verbatim
theorem multSum_eq_main_err (d : ℕ) : s.multSum d = ν d * X + R d := by
  simp_all


-- @@ L142-143 verbatim
/-- Kronecker delta at `1`, valued in the reals. -/
def delta (n : ℕ) : ℝ := if n=1 then 1 else 0


-- @@ L145-145 verbatim
local notation "δ" => delta


-- @@ L147-155 verbatim
theorem siftedSum_as_delta : s.siftedSum = ∑ d ∈ s.support, a d * δ (Nat.gcd P d) :=
  by
  dsimp only [siftedSum]
  apply sum_congr rfl
  intro d _
  dsimp only [Nat.Coprime, delta] at *
  simp_all

-- Unused ?

-- @@ L156-174 expanded
theorem nu_lt_self_of_dvd_prodPrimes : ∀ d : ℕ, d ∣ P → d ≠ 1 → ν d < 1 :=
  by
  intro d hdP hd_ne_one
  have hd_sq : Squarefree d := Squarefree.squarefree_of_dvd hdP s.prodPrimes_squarefree
  calc
    ν d = ∏ p ∈ d.primeFactors, ν p := eq_comm.mp (prod_factors_of_mult ν s.nu_mult hd_sq)
    _ < ∏ p ∈ d.primeFactors, 1 :=
      by
      have hd_ne_zero : d ≠ 0 := by
        aesop  (config := { enableSimp := false })  (rule_sets := [Divisibility])
      apply prod_lt_prod_of_nonempty₀
      · intro p hp
        simp only [mem_primeFactors] at hp
        apply
          s.nu_pos_of_prime p (by aesop)
            (by aesop  (config := { enableSimp := false })  (rule_sets := [Divisibility]))
      · intro p hpd; rw [mem_primeFactors_of_ne_zero hd_ne_zero] at hpd
        apply
          s.nu_lt_one_of_prime p hpd.left
            (by aesop  (config := { enableSimp := false })  (rule_sets := [Divisibility]))
      · apply primeDivisors_nonempty _ <| (two_le_iff d).mpr ⟨hd_ne_zero, hd_ne_one⟩
    _ = 1 := by
      simp
        -- Facts about g


-- @@ L175-185 verbatim
@[aesop safe]
theorem selbergTerms_pos (l : ℕ) (hl : l ∣ P) : 0 < g l := by
  rw [selbergTerms_apply]
  apply mul_pos
  · exact s.nu_pos_of_dvd_prodPrimes hl
  · apply prod_pos
    intro p hp
    rw [one_div_pos]
    have hp_prime : p.Prime := prime_of_mem_primeFactors hp
    have hp_dvd : p ∣ P := (Nat.dvd_of_mem_primeFactors hp).trans hl
    linarith only [s.nu_lt_one_of_prime p hp_prime hp_dvd]


-- @@ L187-189 verbatim
theorem selbergTerms_mult : ArithmeticFunction.IsMultiplicative g := by
  unfold selbergTerms
  arith_mult


-- @@ L191-206 verbatim
theorem one_div_selbergTerms_eq_conv_moebius_nu (l : ℕ) (hl : Squarefree l)
    (hnu_nonzero : ν l ≠ 0) : 1 / g l = ∑ d ∈ l.divisors, (μ <| l / d) * (ν d)⁻¹ :=
  by
  rw [selbergTerms_apply]
  simp only [one_div, mul_inv, inv_inv, Finset.prod_inv_distrib]
  rw [(s.nu_mult).prodPrimeFactors_one_sub_of_squarefree _ hl]
  rw [mul_sum]
  apply symm
  rw [← Nat.sum_divisorsAntidiagonal' fun d e : ℕ => ↑(μ d) * (ν e)⁻¹]
  rw [Nat.sum_divisorsAntidiagonal fun d e : ℕ => ↑(μ d) * (ν e)⁻¹]
  apply sum_congr rfl; intro d hd
  have hd_dvd : d ∣ l := dvd_of_mem_divisors hd
  rw [←div_mult_of_dvd_squarefree ν s.nu_mult l d (dvd_of_mem_divisors hd) hl, inv_div]
  · ring
  · revert hnu_nonzero; contrapose!
    exact multiplicative_zero_of_zero_dvd ν s.nu_mult hl hd_dvd


-- @@ L208-221 verbatim
theorem nu_eq_conv_one_div_selbergTerms (d : ℕ) (hdP : d ∣ P) :
    (ν d)⁻¹ = ∑ l ∈ divisors P, if l ∣ d then 1 / g l else 0 := by
  apply symm
  rw [←sum_filter, Nat.divisors_filter_dvd_of_dvd s.prodPrimes_ne_zero hdP]
  have hd_pos : 0 < d :=
    Nat.pos_of_ne_zero <| ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hdP
  revert hdP; revert d
  apply (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on _ (fun _ _ => Nat.dvd_trans)).mpr
  intro l _ hlP
  rw [sum_divisorsAntidiagonal' (f:=fun x y => (μ <| x) * (ν y)⁻¹) (n:=l)]
  apply symm
  exact s.one_div_selbergTerms_eq_conv_moebius_nu l
    (Squarefree.squarefree_of_dvd hlP s.prodPrimes_squarefree)
    (_root_.ne_of_gt <| s.nu_pos_of_dvd_prodPrimes hlP)


-- @@ L223-245 verbatim
theorem conv_selbergTerms_eq_selbergTerms_mul_nu {d : ℕ} (hd : d ∣ P) :
    (∑ l ∈ divisors P, if l ∣ d then g l else 0) = g d * (ν d)⁻¹ := by
  calc
    (∑ l ∈ divisors P, if l ∣ d then g l else 0) =
        ∑ l ∈ divisors P, if l ∣ d then g (d / l) else 0 := by
      rw [← sum_over_dvd_ite s.prodPrimes_ne_zero hd]
      rw [← Nat.sum_divisorsAntidiagonal fun x _ => g x]
      rw [Nat.sum_divisorsAntidiagonal' fun x _ => g x]
      rw [sum_over_dvd_ite s.prodPrimes_ne_zero hd]
    _ = g d * ∑ l ∈ divisors P, if l ∣ d then 1 / g l else 0 := by
      rw [mul_sum]; apply sum_congr rfl; intro l hl
      rw [mul_ite_zero]
      apply if_ctx_congr Iff.rfl _ (fun _ => rfl)
      intro h
      rw [← div_mult_of_dvd_squarefree g s.selbergTerms_mult d l]
      · ring
      · exact h
      · apply Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree
      · apply _root_.ne_of_gt
        rw [mem_divisors] at hl
        apply selbergTerms_pos
        exact hl.left
    _ = g d * (ν d)⁻¹ := by rw [← s.nu_eq_conv_one_div_selbergTerms d hd]


-- @@ L247-264 verbatim
theorem upper_bound_of_UpperBoundSieve (μPlus : UpperBoundSieve) :
    s.siftedSum ≤ ∑ d ∈ divisors P, μPlus d * s.multSum d := by
  have hμ : ∀ n, δ n ≤ ∑ d ∈ n.divisors, μPlus d := μPlus.hμPlus
  rw [siftedSum_as_delta]
  trans (∑ n ∈ s.support, a n * ∑ d ∈ (Nat.gcd P n).divisors, μPlus d)
  · apply Finset.sum_le_sum; intro n _
    exact mul_le_mul_of_nonneg_left (hμ (Nat.gcd P n)) (s.weights_nonneg n)
  apply le_of_eq
  trans (∑ n ∈ s.support, ∑ d ∈ divisors P, if d ∣ n then a n * μPlus d else 0)
  · apply sum_congr rfl; intro n _
    rw [mul_sum, sum_over_dvd_ite s.prodPrimes_ne_zero (Nat.gcd_dvd_left _ _),
      sum_congr rfl]; intro d hd
    apply if_congr _ rfl rfl
    rw [Nat.dvd_gcd_iff, and_iff_right (dvd_of_mem_divisors hd)]
  rw [sum_comm, sum_congr rfl]; intro d _
  dsimp only [multSum]
  rw [mul_sum, sum_congr rfl]; intro n _
  rw [←ite_zero_mul, mul_comm]


-- @@ L266-279 verbatim
theorem siftedSum_le_mainSum_errSum_of_UpperBoundSieve (μPlus : UpperBoundSieve) :
    s.siftedSum ≤ X * s.mainSum μPlus + s.errSum μPlus := by
  dsimp only [mainSum, errSum]
  trans (∑ d ∈ divisors P, μPlus d * s.multSum d)
  · apply upper_bound_of_UpperBoundSieve
  trans ( X * ∑ d ∈ divisors P, μPlus d * ν d + ∑ d ∈ divisors P, μPlus d * R d )
  · apply le_of_eq
    rw [mul_sum, ←sum_add_distrib]
    apply sum_congr rfl; intro d _
    dsimp only [rem]; ring
  apply _root_.add_le_add (le_rfl)
  apply sum_le_sum; intro d _
  rw [←abs_mul]
  exact le_abs_self (UpperBoundSieve.μPlus μPlus d * rem s d)


-- @@ L281-281 verbatim
end SieveLemmas


-- @@ L283-283 verbatim
section LambdaSquared


-- @@ L285-287 verbatim
/-- Lambda-squared upper-bound weights generated from a function on divisors. -/
def _root_.Sieve.lambdaSquared (weights : ℕ → ℝ) : ℕ → ℝ := fun d =>
  ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then weights d1 * weights d2 else 0


-- @@ L289-303 verbatim
private theorem lambdaSquared_eq_zero_of_support_wlog {w : ℕ → ℝ} {y : ℝ}
    (hw : ∀ (d : ℕ), ¬↑(d ^ 2) ≤ y → w d = 0)
    {d : ℕ} (hd : ¬↑d ≤ y) (d1 : ℕ) (d2 : ℕ) (h : d = Nat.lcm d1 d2)
    (hle : d1 ≤ d2) :
    w d1 * w d2 = 0 := by
  rw [hw d2]
  · ring
  by_contra hyp
  apply hd
  apply le_trans _ hyp
  norm_cast
  calc _ ≤ (d1.lcm d2) := by rw [h]
      _ ≤ (d1*d2) := Nat.div_le_self _ _
      _ ≤ _       := ?_
  · rw [sq]; gcongr

-- @@ L304-323 verbatim
theorem _root_.Sieve.lambdaSquared_eq_zero_of_support (w : ℕ → ℝ) (y : ℝ)
    (hw : ∀ d : ℕ, ¬d ^ 2 ≤ y → w d = 0) (d : ℕ) (hd : ¬d ≤ y) :
    lambdaSquared w d = 0 := by
  dsimp only [lambdaSquared]
  by_cases hy : 0 ≤ y
  swap
  · push Not at hd hy
    have : ∀ d' : ℕ, w d' = 0 := by
      intro d'; apply hw
      have : (0:ℝ) ≤ (d') ^ 2 := by norm_num
      linarith
    simp_all
  apply sum_eq_zero; intro d1 _; apply sum_eq_zero; intro d2 _
  split_ifs with h
  swap
  · rfl
  rcases Nat.le_or_le d1 d2 with hle | hle
  · apply lambdaSquared_eq_zero_of_support_wlog hw hd d1 d2 h hle
  · rw[mul_comm]
    apply lambdaSquared_eq_zero_of_support_wlog hw hd d2 d1 (Nat.lcm_comm d1 d2 ▸ h) hle


-- @@ L325-351 verbatim
theorem _root_.Sieve.upperMoebius_of_lambda_sq (weights : ℕ → ℝ) (hw : weights 1 = 1) :
    UpperMoebius <| lambdaSquared weights := by
  dsimp [UpperMoebius, lambdaSquared]
  intro n
  have h_sq :
    (∑ d ∈ n.divisors, ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
      if d = Nat.lcm d1 d2 then weights d1 * weights d2 else 0) =
      (∑ d ∈ n.divisors, weights d) ^ 2 := by
    rw [sq, mul_sum, conv_lambda_sq_larger_sum _ n, sum_comm]
    apply sum_congr rfl; intro d1 hd1
    rw [sum_mul, sum_comm]
    apply sum_congr rfl; intro d2 hd2
    rw [←Aux.sum_intro]
    · ring
    · rw [mem_divisors, Nat.lcm_dvd_iff]
      exact ⟨⟨dvd_of_mem_divisors hd1, dvd_of_mem_divisors hd2⟩, (mem_divisors.mp hd1).2⟩
  rw [h_sq]
  split_ifs with hn
  · rw [hn]; simp [hw]
  · apply sq_nonneg

-- local notation3 "ν" => Sieve.nu s
-- local notation3 "P" => Sieve.prodPrimes s
-- local notation3 "a" => Sieve.weights s
-- local notation3 "X" => Sieve.totalMass s
-- local notation3 "R" => Sieve.rem s
-- local notation3 "g" => Sieve.selbergTerms s


-- @@ L353-375 verbatim
theorem _root_.Sieve.lambdaSquared_mainSum_eq_quad_form (w : ℕ → ℝ) :
    s.mainSum (lambdaSquared w) =
      ∑ d1 ∈ divisors P, ∑ d2 ∈ divisors P,
        ν d1 * w d1 * ν d2 * w d2 * (ν (d1.gcd d2))⁻¹ := by
  dsimp only [mainSum, lambdaSquared]
  trans (∑ d ∈ divisors P, ∑ d1 ∈ divisors d, ∑ d2 ∈ divisors d,
          if d = d1.lcm d2 then w d1 * w d2 * ν d else 0)
  · rw [sum_congr rfl]; intro d _
    rw [sum_mul, sum_congr rfl]; intro d1 _
    rw [sum_mul, sum_congr rfl]; simp_all
  trans (∑ d ∈ divisors P, ∑ d1 ∈ divisors P, ∑ d2 ∈ divisors P,
          if d = d1.lcm d2 then w d1 * w d2 * ν d else 0)
  · apply conv_lambda_sq_larger_sum
  rw [sum_comm, sum_congr rfl]; intro d1 hd1
  rw [sum_comm, sum_congr rfl]; intro d2 hd2
  have h : d1.lcm d2 ∣ P := Nat.lcm_dvd_iff.mpr ⟨dvd_of_mem_divisors hd1, dvd_of_mem_divisors hd2⟩
  rw [←sum_intro (divisors P) (d1.lcm d2) (mem_divisors.mpr ⟨h, s.prodPrimes_ne_zero⟩ )]
  rw [mult_lcm_eq_of_ne_zero ν s.nu_mult _ _ _]
  · ring
  · refine _root_.ne_of_gt (s.nu_pos_of_dvd_prodPrimes ?_)
    trans d1
    · exact Nat.gcd_dvd_left d1 d2
    · exact dvd_of_mem_divisors hd1


-- @@ L377-399 verbatim
theorem _root_.Sieve.lambdaSquared_mainSum_eq_diag_quad_form (w : ℕ → ℝ) :
    s.mainSum (lambdaSquared w) =
      ∑ l ∈ divisors P,
        1 / g l * (∑ d ∈ divisors P, if l ∣ d then ν d * w d else 0) ^ 2 :=
  by
  rw [s.lambdaSquared_mainSum_eq_quad_form w]
  trans (∑ d1 ∈ divisors P, ∑ d2 ∈ divisors P, (∑ l ∈ divisors P,
          if l ∣ d1.gcd d2 then 1 / g l * (ν d1 * w d1) * (ν d2 * w d2) else 0))
  · apply sum_congr rfl; intro d1 hd1; apply sum_congr rfl; intro d2 _
    have hgcd_dvd: d1.gcd d2 ∣ P := Trans.trans (Nat.gcd_dvd_left d1 d2) (dvd_of_mem_divisors hd1)
    rw [s.nu_eq_conv_one_div_selbergTerms _ hgcd_dvd, mul_sum]
    apply sum_congr rfl; intro l _
    rw [mul_ite_zero]; apply if_congr Iff.rfl _ rfl
    ring
  trans (∑ l ∈ divisors P, ∑ d1 ∈ divisors P, ∑ d2 ∈ divisors P,
        if l ∣ Nat.gcd d1 d2 then 1 / selbergTerms s l * (ν d1 * w d1) * (ν d2 * w d2) else 0)
  · apply symm; rw [sum_comm, sum_congr rfl]; intro d1 _; rw[sum_comm];
  apply sum_congr rfl; intro l _
  rw [sq, sum_mul, mul_sum, sum_congr rfl]; intro d1 _
  rw [mul_sum, mul_sum, sum_congr rfl]; intro d2 _
  rw [ite_zero_mul_ite_zero, mul_ite_zero]
  apply if_congr (Nat.dvd_gcd_iff) _ rfl;
  ring


-- @@ L401-401 verbatim
end LambdaSquared


-- @@ L403-403 verbatim
end Sieve
