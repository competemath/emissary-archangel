/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.DedekindZeta.IdealPrimeFactorization
public import LeanPool.Odlyzko.DedekindZeta.Coefficients
import LeanPool.Odlyzko.DedekindZeta.Convergence
import LeanPool.Odlyzko.DedekindZeta.FiniteFiberSeries
import LeanPool.Odlyzko.DedekindZeta.PrimeIdealSummability
import Mathlib.Tactic.ArithMult.Init


-- @@ L15-15 verbatim
/-! TODO: Add doc-string. -/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
section


-- @@ L23-23 verbatim
open Complex Nat


-- @@ L25-25 verbatim
namespace NumberField.Odlyzko


-- @@ L27-27 verbatim
variable (K : Type*) [Field K] [NumberField K]


-- @@ L29-31 verbatim
/-- A dedekind zeta summand used in the Odlyzko-bound argument. -/
noncomputable def dedekindZetaSummand (s : ℂ) (n : ℕ) : ℂ :=
  LSeries.term (fun m ↦ (idealNormCount K m : ℂ)) s n


-- @@ L33-35 verbatim
@[simp] lemma dedekindZetaSummand_zero (s : ℂ) :
    dedekindZetaSummand K s 0 = 0 := by
  simp [dedekindZetaSummand]


-- @@ L37-37 verbatim
end NumberField.Odlyzko


-- @@ L39-39 verbatim
end


-- @@ L41-41 verbatim
section


-- @@ L43-43 verbatim
open Ideal IsDedekindDomain


-- @@ L45-45 verbatim
namespace NumberField.Odlyzko


-- @@ L47-47 verbatim
variable (K : Type*) [Field K] [NumberField K]


-- @@ L49-51 verbatim
/-- An ideal inverse norm power used in the Odlyzko-bound argument. -/
noncomputable def idealInverseNormPower (s : ℂ) (I : Ideal (𝓞 K)) : ℂ :=
  if I = 0 then 0 else ((absNorm I : ℂ) ^ (-s))


-- @@ L53-55 verbatim
lemma idealInverseNormPower_zero (s : ℂ) :
    idealInverseNormPower K s 0 = 0 := by
  simp [idealInverseNormPower]


-- @@ L57-61 verbatim
lemma idealInverseNormPower_of_ne_zero (s : ℂ) {I : Ideal (𝓞 K)}
    (hI : I ≠ 0) :
    idealInverseNormPower K s I = ((absNorm I : ℂ) ^ (-s)) := by
  unfold idealInverseNormPower
  simp_all


-- @@ L63-75 verbatim
theorem summable_norm_idealInverseNormPower {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I : Ideal (𝓞 K) ↦ ‖idealInverseNormPower K s I‖) := by
  apply (summable_ideal_absNorm_rpow K hs).congr
  intro I
  by_cases hI : I = 0
  · subst I
    simp [idealInverseNormPower, ne_of_gt (zero_lt_one.trans hs)]
  · rw [idealInverseNormPower_of_ne_zero K s hI,
      show ((absNorm I : ℂ) ^ (-s)) =
        inverseNormPower (absNorm I) s by rfl,
      norm_inverseNormPower]
    exact Nat.pos_of_ne_zero (by
      simpa [Ideal.absNorm_eq_zero_iff] using hI)


-- @@ L77-79 verbatim
theorem summable_idealInverseNormPower {s : ℂ} (hs : 1 < s.re) :
    Summable (idealInverseNormPower K s) :=
  (summable_norm_idealInverseNormPower K hs).of_norm


-- @@ L81-114 verbatim
lemma hasSum_idealInverseNormPower_fiber (s : ℂ) (n : ℕ) :
    HasSum
      (fun I : {I : Ideal (𝓞 K) // absNorm I = n} ↦
        idealInverseNormPower K s I)
      (dedekindZetaSummand K s n) := by
  let : Fintype {I : Ideal (𝓞 K) // absNorm I = n} :=
    (Ideal.finite_setOfPred_absNorm_eq n).fintype
  have hf := hasSum_fintype
    (fun I : {I : Ideal (𝓞 K) // absNorm I = n} ↦
      idealInverseNormPower K s I)
  convert hf using 1
  by_cases hn : n = 0
  · subst n
    rw [dedekindZetaSummand_zero]
    symm
    apply Finset.sum_eq_zero
    intro I _
    rw [show (I : Ideal (𝓞 K)) = 0 from
      Ideal.absNorm_eq_zero_iff.mp I.2,
      idealInverseNormPower_zero]
  · simp only [dedekindZetaSummand, LSeries.term_of_ne_zero hn,
      idealNormCount]
    have hconst :
        (fun I : {I : Ideal (𝓞 K) // absNorm I = n} ↦
          idealInverseNormPower K s I) =
        fun _ ↦ inverseNormPower n s := by
      funext I
      rw [idealInverseNormPower_of_ne_zero K s]
      · rw [I.2]
        rfl
      · grind
    rw [hconst, Finset.sum_const, nsmul_eq_mul, inverseNormPower,
      Complex.cpow_neg, div_eq_mul_inv]
    simp


-- @@ L116-122 verbatim
private lemma summable_idealInverseNormPower_fiber (s : ℂ) (n : ℕ) :
    Summable
      (fun I : {I : Ideal (𝓞 K) // absNorm I = n} ↦
        idealInverseNormPower K s I) := by
  let : Fintype {I : Ideal (𝓞 K) // absNorm I = n} :=
    (Ideal.finite_setOfPred_absNorm_eq n).fintype
  exact Summable.of_finite


-- @@ L124-150 verbatim
theorem hasSum_idealInverseNormPower {s : ℂ} (hs : 1 < s.re) :
    HasSum (idealInverseNormPower K s) (NumberField.dedekindZeta K s) := by
  let e := Equiv.sigmaFiberEquiv (absNorm : Ideal (𝓞 K) → ℕ)
  apply e.hasSum_iff.mp
  have hsum :
      Summable (fun x : Σ n, {I : Ideal (𝓞 K) // absNorm I = n} ↦
        idealInverseNormPower K s x.2) :=
    (summable_idealInverseNormPower K hs).comp_injective e.injective
  have heq :
      (∑' x : Σ n, {I : Ideal (𝓞 K) // absNorm I = n},
        idealInverseNormPower K s x.2) =
        NumberField.dedekindZeta K s := by
    calc
      _ = ∑' n, ∑' I : {I : Ideal (𝓞 K) // absNorm I = n},
          idealInverseNormPower K s I :=
        tsum_sigma_of_summable
          (fun x : Σ n, {I : Ideal (𝓞 K) // absNorm I = n} ↦
            idealInverseNormPower K s x.2)
          (summable_idealInverseNormPower_fiber K s)
          hsum
      _ = ∑' n, dedekindZetaSummand K s n := by
        apply tsum_congr
        intro n
        exact (hasSum_idealInverseNormPower_fiber K s n).tsum_eq
      _ = NumberField.dedekindZeta K s :=
        (hasSum_dedekindZeta K hs).tsum_eq
  exact heq ▸ hsum.hasSum


-- @@ L152-173 verbatim
theorem hasSum_nonzeroIdeal_inverseNormPower {s : ℂ} (hs : 1 < s.re) :
    HasSum
      (fun I : NonzeroIdeal K ↦
        ((absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s)))
      (NumberField.dedekindZeta K s) := by
  have h := hasSum_idealInverseNormPower K hs
  let f := fun I : NonzeroIdeal K ↦
    ((absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s))
  have hext :
      idealInverseNormPower K s =
        Function.extend (Subtype.val : NonzeroIdeal K → Ideal (𝓞 K)) f 0 := by
    funext I
    by_cases hI : I = 0
    · subst I
      rw [idealInverseNormPower_zero]
      simp
    · rw [idealInverseNormPower_of_ne_zero K s hI]
      let J : NonzeroIdeal K := ⟨I, hI⟩
      simpa [f, J] using
        (Subtype.val_injective.extend_apply f 0 J).symm
  rw [hext] at h
  exact (hasSum_extend_zero Subtype.val_injective).1 h


-- @@ L175-175 verbatim
end NumberField.Odlyzko


-- @@ L177-177 verbatim
end
