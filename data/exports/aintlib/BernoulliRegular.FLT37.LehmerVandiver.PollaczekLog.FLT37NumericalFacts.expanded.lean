/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.FLT37.LehmerVandiver.Certificate


-- @@ L10-27 verbatim
/-!
# FLT37-specific numerical residue facts

For the FLT37 certificate tuple `(p, i, ℓ, t, k) = (37, 32, 149, 2, 4)`, this file
provides the two numerical facts in `ZMod 149` used to prove the Pollaczek unit is
not a `p`-th power.

## Main results

* `lehmerVandiverProduct_thirtyseven_ne_one`: the FLT37 Lehmer--Vandiver product is
  not one.
* `one_sub_two_pow_four_pow_kS_eq_one`: the denominator power in the FLT37 residue
  calculation is one.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Section 8.3.
-/


-- @@ L29-29 verbatim
@[expose] public section


-- @@ L31-31 verbatim
namespace BernoulliRegular


-- @@ L33-33 verbatim
namespace FLT37


-- @@ L35-35 verbatim
namespace LehmerVandiver


-- @@ L37-37 verbatim
section FLT37NumericalFacts


-- @@ L39-39 verbatim
set_option maxRecDepth 2000


-- @@ L41-45 verbatim
/-- The FLT37 Lehmer--Vandiver product is not one in `ZMod 149`. -/
theorem lehmerVandiverProduct_thirtyseven_ne_one :
    lehmerVandiverProduct 37 32 149 2 4 ≠ 1 := by
  simp only [lehmerVandiverProduct]
  decide


-- @@ L47-51 verbatim
/-- The denominator power in the FLT37 residue calculation is one in `ZMod 149`. -/
theorem one_sub_two_pow_four_pow_kS_eq_one :
    ((1 : ZMod 149) - 2 ^ 4) ^ (4 * 432345) = 1 := by
  have h148 : ((1 : ZMod 149) - 2 ^ 4) ^ 148 = 1 := by decide
  rw [show (4 * 432345 : ℕ) = 148 * 11685 by decide, pow_mul, h148, one_pow]


-- @@ L53-53 verbatim
end FLT37NumericalFacts


-- @@ L55-55 verbatim
end LehmerVandiver


-- @@ L57-57 verbatim
end FLT37


-- @@ L59-59 verbatim
end BernoulliRegular


-- @@ L61-61 verbatim
end
