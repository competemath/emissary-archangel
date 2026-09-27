/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/
module

public import LeanPool.LocalComplexGeometry.Nullstellensatz.RadicalReduction
import LeanPool.LocalComplexGeometry.Germs.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset


-- @@ L15-21 verbatim
/-!
# The zero-dimensional prime case

The analytic Nullstellensatz induction starts in complex dimension zero.  The
germ ring there is canonically `ℂ`, so its only prime ideal is zero; the zero
ideal has the full neighborhood as its zero-set germ.
-/


-- @@ L23-23 verbatim
@[expose] public section



-- @@ L26-26 verbatim
namespace LocalComplexGeometry


-- @@ L28-28 verbatim
noncomputable section


-- @@ L30-45 verbatim
/-- Every prime ideal of the zero-dimensional holomorphic germ ring is zero. -/
theorem holomorphicGerm_zero_prime_eq_bot
    (P : Ideal (HolomorphicGerm 0)) (hP : P.IsPrime) :
    P = ⊥ := by
  apply le_antisymm
  · intro f hf
    by_contra hf0
    have he0 : holomorphicGermZeroEquiv f ≠ 0 :=
      fun h ↦ hf0 (holomorphicGermZeroEquiv.injective (h.trans (map_zero _).symm))
    have heunit : IsUnit (holomorphicGermZeroEquiv f) :=
      isUnit_iff_ne_zero.mpr he0
    have hfunit : IsUnit f :=
      (MulEquiv.isUnit_map holomorphicGermZeroEquiv).mp heunit
    let : P.IsPrime := hP
    exact (Ideal.notMem_of_isUnit P hfunit) hf
  · exact bot_le


-- @@ L47-51 verbatim
/-- The prime zero-set theorem in complex dimension zero. -/
theorem primeZeroSetProperty_zero : PrimeZeroSetProperty 0 := by
  intro P hP
  rw [holomorphicGerm_zero_prime_eq_bot P hP,
    idealZeroSetGerm_bot, vanishingIdeal_top]


-- @@ L53-53 verbatim
end


-- @@ L55-55 verbatim
end LocalComplexGeometry
