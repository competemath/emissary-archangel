module

public import BernoulliRegular.CyclotomicUnits.UnitsReflection
public import FltRegular.NumberTheory.RegularPrimes


-- @@ L6-10 verbatim
/-!
# Kummer's criterion

This file exposes the final public theorem of the project.
-/


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
open NumberField


-- @@ L16-16 verbatim
namespace BernoulliRegular


-- @@ L18-37 verbatim
/-- **Kummer's criterion.**

An odd prime `p` is regular iff `p` does not divide the numerator of any
Bernoulli number `B_2, B_4, ..., B_{p-3}`. -/
theorem kummer_criterion {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2) :
    IsRegularPrime p ↔
      ∀ k, 1 ≤ k → 2 * k ≤ p - 3 → ¬ (p : ℤ) ∣ (bernoulli (2 * k)).num := by
  letI : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  letI : IsCMField (CyclotomicField p ℚ) :=
    isCMField_of_cyclotomic (p := p) (hp_odd := hp_odd) (K := CyclotomicField p ℚ)
  have hiff : (p : ℕ) ∣ h (CyclotomicField p ℚ) ↔
      ∃ k, 1 ≤ k ∧ 2 * k ≤ p - 3 ∧ (p : ℤ) ∣ (bernoulli (2 * k)).num :=
    dvd_h_iff_exists_dvd_bernoulli_units
      (p := p) (K := CyclotomicField p ℚ) hp_odd
  rw [IsRegularPrime, IsRegularNumber, hp.out.coprime_iff_not_dvd]
  change ¬ (p : ℕ) ∣ h (CyclotomicField p ℚ) ↔ _
  rw [hiff]
  push Not
  rfl


-- @@ L39-39 verbatim
end BernoulliRegular
