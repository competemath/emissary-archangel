/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import BernoulliRegular.BernoulliFast.Tactic
import BernoulliRegular.Main
import FltRegular.FltRegular


-- @@ L10-15 verbatim
/-!
# The prime `23`

This file certifies the Bernoulli-number side of regularity for `23`, and
packages regularity and FLT for exponent `23`.
-/


-- @@ L17-17 verbatim
namespace BernoulliRegular


-- @@ L19-19 verbatim
universe v


-- @@ L21-21 verbatim
open NumberField


-- @@ L23-24 verbatim
instance fact_prime_twentythree : Fact (Nat.Prime 23) :=
  ⟨by norm_num⟩


-- @@ L26-28 verbatim
instance cyclotomicField_twentythree_isCyclotomicExtension :
    IsCyclotomicExtension {23} ℚ (CyclotomicField 23 ℚ) :=
  CyclotomicField.isCyclotomicExtension 23 ℚ


-- @@ L30-33 verbatim
instance cyclotomicField_twentythree_isCMField :
    IsCMField (CyclotomicField 23 ℚ) :=
  isCMField_of_cyclotomic
    (p := 23) (hp_odd := by norm_num) (K := CyclotomicField 23 ℚ)


-- @@ L35-39 verbatim
theorem not_dvd_bernoulli_twentythree :
    ∀ k, 1 ≤ k → 2 * k ≤ 23 - 3 → ¬ (23 : ℤ) ∣ (bernoulli (2 * k)).num := by
  intro k hk hk_range
  have hk_upper : k ≤ 10 := by omega
  interval_cases k <;> bernoulli_decide


-- @@ L41-44 verbatim
/-- Regularity of `23` from the certified Bernoulli checks. -/
theorem isRegularPrime_twentythree :
    IsRegularPrime 23 :=
  (kummer_criterion (p := 23) (by norm_num)).2 not_dvd_bernoulli_twentythree


-- @@ L46-49 verbatim
/-- FLT for exponent `23`. -/
theorem fermatLastTheoremFor_twentythree :
    FermatLastTheoremFor 23 :=
  flt_regular isRegularPrime_twentythree (by norm_num)


-- @@ L51-51 verbatim
end BernoulliRegular
