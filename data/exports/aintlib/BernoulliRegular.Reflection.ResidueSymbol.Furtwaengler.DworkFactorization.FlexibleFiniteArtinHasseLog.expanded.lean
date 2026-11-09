module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FlexibleFiniteLogLocalized


-- @@ L5-14 verbatim
/-!
# Finite Artin-Hasse logarithm sums

This file defines the finite Artin-Hasse logarithm side

`AH_N(x) = sum_{0 <= r <= N} x^(ell^r) / ell^r`

in `𝓞 R' / Q^(N+1)` for `x ∈ Q`.  Division by `ell^r` uses the same
localized natural-denominator evaluator as the finite logarithm.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-20 verbatim
open scoped NumberField


-- @@ L22-22 verbatim
namespace Nat


-- @@ L24-35 verbatim
/-- For a base at least two, `r * a <= a^r`. -/
theorem mul_le_pow_self_of_two_le {a r : ℕ} (ha : 2 ≤ a) :
    r * a ≤ a ^ r := by
  cases r with
  | zero =>
      simp
  | succ r =>
      have hs : r + 1 ≤ a ^ r := by
        have htwo : r + 1 ≤ 2 ^ r := Nat.succ_le_of_lt r.lt_two_pow_self
        exact htwo.trans (Nat.pow_le_pow_left ha r)
      have hmul := Nat.mul_le_mul_right a hs
      simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul


-- @@ L37-49 verbatim
/-- The Artin-Hasse denominator cancellation leaves at least the index order. -/
theorem le_pow_sub_mul_pred_of_two_le {a r : ℕ} (ha : 2 ≤ a) :
    r ≤ a ^ r - r * (a - 1) := by
  have hmul := Nat.mul_le_pow_self_of_two_le (a := a) (r := r) ha
  have ha1 : 1 ≤ a := by omega
  have hadd : r + r * (a - 1) ≤ a ^ r := by
    calc
      r + r * (a - 1) = r * (1 + (a - 1)) := by
        rw [Nat.mul_add, mul_one]
      _ = r * a := by
        rw [Nat.add_comm 1 (a - 1), Nat.sub_add_cancel ha1]
      _ ≤ a ^ r := hmul
  exact Nat.le_sub_of_add_le hadd


-- @@ L51-51 verbatim
end Nat


-- @@ L53-53 verbatim
namespace BernoulliRegular


-- @@ L55-55 verbatim
namespace Furtwaengler


-- @@ L57-57 verbatim
universe u v w


-- @@ L59-59 verbatim
namespace ConductorFlexibleFullTeichStickelbergerSetup


-- @@ L61-61 verbatim
variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]

-- @@ L62-62 verbatim
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]

-- @@ L63-63 verbatim
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

-- @@ L64-64 verbatim
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']


-- @@ L66-66 verbatim
variable (F : ConductorFlexibleFullTeichStickelbergerSetup ℓ p k K R')


-- @@ L68-71 verbatim
/-- Forced `Q`-adic order of the Artin-Hasse log term
`x^(ell^r) / ell^r` for `x ∈ Q`. -/
def finiteArtinHasseLogTermOrder (r : ℕ) : ℕ :=
  ℓ ^ r - r * (ℓ - 1)


-- @@ L73-76 verbatim
theorem finiteArtinHasseLog_den_le (r : ℕ) :
    r * (ℓ - 1) ≤ ℓ ^ r := by
  have h := Nat.mul_pred_le_pow_sub_one ℓ r (Fact.out : Nat.Prime ℓ).pos
  exact h.trans (Nat.sub_le (ℓ ^ r) 1)


-- @@ L78-84 verbatim
theorem factorization_mul_pred_add_finiteArtinHasseLogTermOrder (r : ℕ) :
    (ℓ ^ r).factorization ℓ * (ℓ - 1) +
        finiteArtinHasseLogTermOrder (ℓ := ℓ) r =
      ℓ ^ r := by
  have hden := finiteArtinHasseLog_den_le (ℓ := ℓ) r
  rw [Nat.factorization_pow_self (p := ℓ) (n := r) (Fact.out : Nat.Prime ℓ)]
  exact Nat.add_sub_cancel' hden


-- @@ L86-92 verbatim
theorem pow_factorization_mul_pred_add_finiteArtinHasseLogTermOrder (r : ℕ) :
    r * ℓ.factorization ℓ * (ℓ - 1) +
        finiteArtinHasseLogTermOrder (ℓ := ℓ) r =
      ℓ ^ r := by
  have hden := finiteArtinHasseLog_den_le (ℓ := ℓ) r
  rw [Nat.Prime.factorization_self (Fact.out : Nat.Prime ℓ)]
  simpa [finiteArtinHasseLogTermOrder, Nat.mul_assoc] using Nat.add_sub_cancel' hden


-- @@ L94-98 verbatim
theorem le_finiteArtinHasseLogTermOrder (r : ℕ) :
    r ≤ finiteArtinHasseLogTermOrder (ℓ := ℓ) r := by
  simpa [finiteArtinHasseLogTermOrder] using
    Nat.le_pow_sub_mul_pred_of_two_le (a := ℓ) (r := r)
      (Fact.out : Nat.Prime ℓ).two_le


-- @@ L100-107 verbatim
theorem one_le_finiteArtinHasseLogTermOrder (r : ℕ) :
    1 ≤ finiteArtinHasseLogTermOrder (ℓ := ℓ) r := by
  cases r with
  | zero =>
      simp [finiteArtinHasseLogTermOrder]
  | succ r =>
      exact (Nat.succ_pos r).trans_le
        (le_finiteArtinHasseLogTermOrder (ℓ := ℓ) (r + 1))


-- @@ L109-116 verbatim
/-- The `r`-th term `x^(ell^r) / ell^r` of the finite Artin-Hasse logarithm,
valued in `𝓞 R' / Q^(N+1)`. -/
noncomputable def finiteArtinHasseLogTerm (N r : ℕ)
    (x : 𝓞 R') (hx : x ∈ F.Q) : 𝓞 R' ⧸ F.Q ^ (N + 1) :=
  F.finiteLogNatDivEval N (ℓ ^ r) (finiteArtinHasseLogTermOrder (ℓ := ℓ) r)
    (pow_ne_zero r (Fact.out : Nat.Prime ℓ).ne_zero) (x ^ (ℓ ^ r)) (by
      simpa [pow_factorization_mul_pred_add_finiteArtinHasseLogTermOrder (ℓ := ℓ) r]
        using Ideal.pow_mem_pow hx (ℓ ^ r))


-- @@ L118-127 verbatim
/-- Multiplying the `r`-th Artin-Hasse logarithm term by `ell^r` recovers
`x^(ell^r)` in the quotient. -/
theorem finiteArtinHasseLogTerm_natCast_mul_eq_mk (N r : ℕ)
    {x : 𝓞 R'} (hx : x ∈ F.Q) :
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (((ℓ ^ r : ℕ) : 𝓞 R')) *
        F.finiteArtinHasseLogTerm N r x hx =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (x ^ (ℓ ^ r)) := by
  rw [finiteArtinHasseLogTerm]
  exact F.finiteLogNatDivEval_natCast_mul_eq_mk
    (pow_ne_zero r (Fact.out : Nat.Prime ℓ).ne_zero) _


-- @@ L129-136 verbatim
theorem finiteArtinHasseLogTerm_mem_map_Q_pow (N r : ℕ)
    {x : 𝓞 R'} (hx : x ∈ F.Q) :
    F.finiteArtinHasseLogTerm N r x hx ∈
      Ideal.map (Ideal.Quotient.mk (F.Q ^ (N + 1)))
        (F.Q ^ finiteArtinHasseLogTermOrder (ℓ := ℓ) r) := by
  rw [finiteArtinHasseLogTerm]
  exact F.finiteLogNatDivEval_mem_map_Q_pow
    (pow_ne_zero r (Fact.out : Nat.Prime ℓ).ne_zero) _


-- @@ L138-148 verbatim
theorem finiteArtinHasseLogTerm_mem_map_Q (N r : ℕ)
    {x : 𝓞 R'} (hx : x ∈ F.Q) :
    F.finiteArtinHasseLogTerm N r x hx ∈
      Ideal.map (Ideal.Quotient.mk (F.Q ^ (N + 1))) F.Q := by
  have hterm := F.finiteArtinHasseLogTerm_mem_map_Q_pow N r hx
  have hle :
      F.Q ^ finiteArtinHasseLogTermOrder (ℓ := ℓ) r ≤ F.Q := by
    simpa using
      (Ideal.pow_le_pow_right (one_le_finiteArtinHasseLogTermOrder (ℓ := ℓ) r) :
        F.Q ^ finiteArtinHasseLogTermOrder (ℓ := ℓ) r ≤ F.Q ^ 1)
  exact Ideal.map_mono hle hterm


-- @@ L150-156 verbatim
theorem finiteArtinHasseLogTerm_eq_zero_of_succ_le {N r : ℕ}
    {x : 𝓞 R'} (hx : x ∈ F.Q)
    (horder : N + 1 ≤ finiteArtinHasseLogTermOrder (ℓ := ℓ) r) :
    F.finiteArtinHasseLogTerm N r x hx = 0 := by
  rw [finiteArtinHasseLogTerm]
  exact F.finiteLogNatDivEval_eq_zero_of_succ_le
    (pow_ne_zero r (Fact.out : Nat.Prime ℓ).ne_zero) _ horder


-- @@ L158-162 verbatim
theorem finiteArtinHasseLogTerm_eq_zero_of_succ_le_index {N r : ℕ}
    {x : 𝓞 R'} (hx : x ∈ F.Q) (hr : N + 1 ≤ r) :
    F.finiteArtinHasseLogTerm N r x hx = 0 :=
  F.finiteArtinHasseLogTerm_eq_zero_of_succ_le hx
    (hr.trans (le_finiteArtinHasseLogTermOrder (ℓ := ℓ) r))


-- @@ L164-167 verbatim
/-- Finite Artin-Hasse logarithm sum in `𝓞 R' / Q^(N+1)`. -/
noncomputable def finiteArtinHasseLog (N : ℕ)
    (x : 𝓞 R') (hx : x ∈ F.Q) : 𝓞 R' ⧸ F.Q ^ (N + 1) :=
  ∑ r ∈ Finset.range (N + 1), F.finiteArtinHasseLogTerm N r x hx


-- @@ L169-174 verbatim
theorem finiteArtinHasseLog_mem_map_Q (N : ℕ)
    {x : 𝓞 R'} (hx : x ∈ F.Q) :
    F.finiteArtinHasseLog N x hx ∈
      Ideal.map (Ideal.Quotient.mk (F.Q ^ (N + 1))) F.Q := by
  rw [finiteArtinHasseLog]
  exact Ideal.sum_mem _ fun r _hr => F.finiteArtinHasseLogTerm_mem_map_Q N r hx


-- @@ L176-186 verbatim
/-- Extending the Artin-Hasse log sum past `N` does not change its value
modulo `Q^(N+1)`. -/
theorem finiteArtinHasseLog_eq_sum_range_of_le {N M : ℕ} (hNM : N ≤ M)
    {x : 𝓞 R'} (hx : x ∈ F.Q) :
    F.finiteArtinHasseLog N x hx =
      ∑ r ∈ Finset.range (M + 1), F.finiteArtinHasseLogTerm N r x hx := by
  rw [finiteArtinHasseLog]
  refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hNM)) ?_
  intro r _hrM hrN
  have hNr : N + 1 ≤ r := Nat.le_of_not_gt (by simpa using hrN)
  exact F.finiteArtinHasseLogTerm_eq_zero_of_succ_le_index hx hNr


-- @@ L188-188 verbatim
end ConductorFlexibleFullTeichStickelbergerSetup


-- @@ L190-190 verbatim
end Furtwaengler


-- @@ L192-192 verbatim
end BernoulliRegular


-- @@ L194-194 verbatim
end
