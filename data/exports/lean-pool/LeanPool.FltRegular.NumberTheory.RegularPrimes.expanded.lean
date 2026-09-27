/-
Copyright (c) 2026 FltRegular contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FltRegular contributors
-/

module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID


-- @@ L13-21 verbatim
/-!
# Regular primes

## Main definitions

* `IsRegularNumber`: a natural number `n` is regular if `n` is coprime with the cardinal of the
  class group.

-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
open Nat Polynomial NumberField


-- @@ L29-29 verbatim
open scoped NumberField


-- @@ L31-31 verbatim
variable (n p : ℕ)


-- @@ L33-35 verbatim
/-- A natural number `n` is regular if `n` is coprime with the cardinal of the class group. -/
def IsRegularNumber : Prop :=
  n.Coprime <| Fintype.card <| ClassGroup (𝓞 <| CyclotomicField n ℚ)


-- @@ L37-39 verbatim
/-- The definition of regular primes. -/
def IsRegularPrime : Prop :=
  IsRegularNumber p


-- @@ L41-41 verbatim
section TwoRegular


-- @@ L43-43 verbatim
variable (K : Type*) [Field K]


-- @@ L45-45 verbatim
variable (L : Type*) [Field L] [Algebra K L]


-- @@ L47-55 verbatim
/-- The second cyclotomic field is equivalent to the base field. -/
def cyclotomicFieldTwoEquiv [IsCyclotomicExtension {2} K L] : L ≃ₐ[K] K := by
  suffices IsSplittingField K K (cyclotomic 2 K) by
    have : IsSplittingField K L (cyclotomic 2 K) :=
      IsCyclotomicExtension.splitting_field_cyclotomic 2 K L
    exact (IsSplittingField.algEquiv L (cyclotomic 2 K)).trans
      (IsSplittingField.algEquiv K <| cyclotomic 2 K).symm
  exact ⟨by simpa using Splits.X_sub_C (-1 : K),
    by simp [eq_iff_true_of_subsingleton]⟩


-- @@ L57-62 verbatim
instance IsPrincipalIdealRing_of_IsCyclotomicExtension_two
    (L : Type*) [Field L] [CharZero L] [IsCyclotomicExtension {2} ℚ L] :
    IsPrincipalIdealRing (𝓞 L) :=
  let F : 𝓞 L ≃+* ℤ := (RingOfIntegers.mapRingEquiv
    (cyclotomicFieldTwoEquiv ℚ L).toRingEquiv).trans Rat.ringOfIntegersEquiv
  IsPrincipalIdealRing.of_surjective F.symm.toRingHom F.symm.surjective


-- @@ L64-65 verbatim
instance : IsCyclotomicExtension {2} ℚ (CyclotomicField 2 ℚ) :=
  CyclotomicField.isCyclotomicExtension 2 ℚ


-- @@ L67-68 verbatim
instance : IsPrincipalIdealRing (𝓞 (CyclotomicField 2 ℚ)) :=
  IsPrincipalIdealRing_of_IsCyclotomicExtension_two _


-- @@ L70-73 verbatim
theorem isRegularPrime_two : IsRegularPrime 2 := by
  rw [IsRegularPrime, IsRegularNumber]
  convert coprime_one_right _
  exact (card_classGroup_eq_one_iff (R := 𝓞 (CyclotomicField 2 ℚ))).2 inferInstance


-- @@ L75-83 verbatim
theorem isRegularPrime_three :
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    IsRegularPrime 3 := by
  let _ : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  rw [IsRegularPrime, IsRegularNumber]
  convert coprime_one_right _
  exact classNumber_eq_one_iff.2
    (IsCyclotomicExtension.Rat.three_pid (CyclotomicField _ ℚ))


-- @@ L85-85 verbatim
end TwoRegular
