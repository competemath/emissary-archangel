module

public import BernoulliRegular.CyclotomicUnits.HMinusCriterion


-- @@ L5-10 verbatim
/-!
# Class-number algebra for the cyclotomic-unit route

This file isolates the class-number step needed to plug a cyclotomic-unit proof
of `p ∣ h⁺ → p ∣ h⁻` into Kummer's criterion.
-/


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
noncomputable section


-- @@ L16-16 verbatim
open NumberField


-- @@ L18-18 verbatim
namespace BernoulliRegular


-- @@ L20-43 verbatim
/-- If the cyclotomic-unit route proves `p ∣ hPlus K → p ∣ hMinus K`, then
the total class-number divisibility condition is equivalent to relative
class-number divisibility.

The canonical class-number API used here is:
* `h K` from `BernoulliRegular/TotallyRealSubfield/Basic.lean`;
* `hPlus K` from `BernoulliRegular/TotallyRealSubfield/Basic.lean`;
* `hMinus K` from `BernoulliRegular/TotallyRealSubfield/ClassGroup.lean`;
* `h_eq_hPlus_mul_hMinus` from
  `BernoulliRegular/TotallyRealSubfield/ClassGroup.lean`.
-/
theorem dvd_h_iff_dvd_hMinus_of_dvd_hPlus_imp
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [IsCMField K]
    (hplus_to_hminus : (p : ℕ) ∣ hPlus K → (p : ℕ) ∣ hMinus K) :
    (p : ℕ) ∣ h K ↔ (p : ℕ) ∣ hMinus K := by
  constructor
  · intro hpH
    rw [h_eq_hPlus_mul_hMinus p hp_odd K] at hpH
    exact (hp.out.dvd_mul.mp hpH).elim hplus_to_hminus id
  · intro hminus
    rw [h_eq_hPlus_mul_hMinus p hp_odd K]
    exact dvd_mul_of_dvd_right hminus (hPlus K)


-- @@ L45-45 verbatim
end BernoulliRegular


-- @@ L47-47 verbatim
end
