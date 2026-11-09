module

public import BernoulliRegular.FLT37.PrimaryConj
public import BernoulliRegular.FLT37.PrimaryUnits.RealCyclotomicUnitsAndTaylorExpansions
public import BernoulliRegular.HMinus.KplusPrimeArithmetic
public import BernoulliRegular.TotallyRealSubfield.ZetaPrime
public import FltRegular.NumberTheory.Cyclotomic.MoreLemmas
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits


-- @@ L10-34 verbatim
/-!
# Real cyclotomic units in `𝓞 K⁺`

The real cyclotomic combination in `𝓞 K` is invariant under complex conjugation, so it descends
to the ring of integers of the maximal real subfield. This file chooses such a descent and develops
its natural-number and `ZMod p`-indexed API.

## Main definitions

* `realCyclotomicUnitPlus`: the chosen descent to `𝓞 K⁺`.
* `realCyclotomicUnitZMod` and `realCyclotomicUnitPlusZMod`: residue-indexed wrappers.
* `realCyclotomicUnitPlusUnit`: the descended element packaged as a unit.

## Main results

* `algebraMap_realCyclotomicUnitPlus`: the chosen descent maps to the K-side combination.
* `isUnit_realCyclotomicUnitPlus`: a coprime-indexed descent is a unit.
* `realCyclotomicUnitPlus_norm_int_sq_eq_one`: its integer norm has square one.

## References

* Washington, *Introduction to Cyclotomic Fields*, §6.4.
* Vandiver 1929, *Fermat's Last Theorem and the Second Factor in the
  Cyclotomic Class Number*.
-/


-- @@ L36-36 verbatim
@[expose] public section


-- @@ L38-38 verbatim
noncomputable section


-- @@ L40-40 verbatim
open NumberField NumberField.IsCMField IsCyclotomicExtension

-- @@ L41-41 verbatim
open scoped NumberField


-- @@ L43-43 verbatim
namespace BernoulliRegular


-- @@ L45-45 verbatim
namespace FLT37


-- @@ L47-47 verbatim
section RealCyclotomicUnits


-- @@ L49-50 verbatim
variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]


-- @@ L52-59 verbatim
/-- The real cyclotomic combination descends to `𝓞 K⁺`: there exists
`y ∈ 𝓞 K⁺` with `algebraMap y = realCyclotomicUnit p K k`. -/
theorem exists_realCyclotomicUnit_descent [IsCMField K] (k : ℕ) :
    ∃ y : 𝓞 (NumberField.maximalRealSubfield K),
      algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) y =
      realCyclotomicUnit p K k :=
  (ringOfIntegersComplexConj_eq_self_iff K (realCyclotomicUnit p K k)).mp
    (realCyclotomicUnit_complexConj p K k)


-- @@ L61-65 verbatim
/-- The K⁺-side real cyclotomic unit: a chosen lift of
`realCyclotomicUnit p K k` to `𝓞 K⁺`. -/
noncomputable def realCyclotomicUnitPlus [IsCMField K] (k : ℕ) :
    𝓞 (NumberField.maximalRealSubfield K) :=
  (exists_realCyclotomicUnit_descent p K k).choose


-- @@ L67-72 verbatim
/-- `algebraMap (realCyclotomicUnitPlus p K k) = realCyclotomicUnit p K k`. -/
theorem algebraMap_realCyclotomicUnitPlus [IsCMField K] (k : ℕ) :
    algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
        (realCyclotomicUnitPlus p K k) =
      realCyclotomicUnit p K k :=
  (exists_realCyclotomicUnit_descent p K k).choose_spec


-- @@ L74-79 verbatim
/-- `realCyclotomicUnitPlus p K 1 = 1` in `𝓞 K⁺`. -/
theorem realCyclotomicUnitPlus_one [IsCMField K] :
    realCyclotomicUnitPlus p K 1 = 1 := by
  apply FaithfulSMul.algebraMap_injective
    (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
  rw [algebraMap_realCyclotomicUnitPlus, realCyclotomicUnit_one, map_one]


-- @@ L81-86 verbatim
/-- `realCyclotomicUnitPlus p K (p - 1) = 1` in `𝓞 K⁺`. -/
theorem realCyclotomicUnitPlus_p_sub_one [IsCMField K] :
    realCyclotomicUnitPlus p K (p - 1) = 1 := by
  apply FaithfulSMul.algebraMap_injective
    (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
  rw [algebraMap_realCyclotomicUnitPlus, realCyclotomicUnit_p_sub_one, map_one]


-- @@ L88-93 verbatim
/-- `realCyclotomicUnitPlus p K p = 0` in `𝓞 K⁺`. -/
theorem realCyclotomicUnitPlus_p_eq_zero [IsCMField K] :
    realCyclotomicUnitPlus p K p = 0 := by
  apply FaithfulSMul.algebraMap_injective
    (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
  rw [algebraMap_realCyclotomicUnitPlus, realCyclotomicUnit_p_eq_zero, map_zero]


-- @@ L95-100 verbatim
/-- `realCyclotomicUnitPlus p K (p + 1) = 1` in `𝓞 K⁺`. -/
theorem realCyclotomicUnitPlus_p_add_one [IsCMField K] :
    realCyclotomicUnitPlus p K (p + 1) = 1 := by
  apply FaithfulSMul.algebraMap_injective
    (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
  rw [algebraMap_realCyclotomicUnitPlus, realCyclotomicUnit_p_add_one, map_one]


-- @@ L102-108 verbatim
/-- Iterated periodicity for the K⁺-side cyclotomic unit. -/
theorem realCyclotomicUnitPlus_add_mul_p [IsCMField K] (a m : ℕ) :
    realCyclotomicUnitPlus p K (a + m * p) = realCyclotomicUnitPlus p K a := by
  apply FaithfulSMul.algebraMap_injective
    (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
  rw [algebraMap_realCyclotomicUnitPlus, algebraMap_realCyclotomicUnitPlus,
    realCyclotomicUnit_add_mul_p]


-- @@ L110-116 verbatim
/-- `realCyclotomicUnitPlus p K k` only depends on `k mod p`. -/
theorem realCyclotomicUnitPlus_mod_p [IsCMField K] (k : ℕ) :
    realCyclotomicUnitPlus p K k = realCyclotomicUnitPlus p K (k % p) := by
  apply FaithfulSMul.algebraMap_injective
    (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
  rw [algebraMap_realCyclotomicUnitPlus, algebraMap_realCyclotomicUnitPlus,
    realCyclotomicUnit_mod_p]


-- @@ L118-120 verbatim
/-- ZMod-indexed wrapper for `realCyclotomicUnit`. -/
noncomputable def realCyclotomicUnitZMod [IsCMField K] (k : ZMod p) : 𝓞 K :=
  realCyclotomicUnit p K k.val


-- @@ L122-126 verbatim
/-- The ZMod-indexed real cyclotomic combination is invariant under complex conjugation. -/
theorem realCyclotomicUnitZMod_complexConj [IsCMField K] (k : ZMod p) :
    ringOfIntegersComplexConj K (realCyclotomicUnitZMod p K k) =
      realCyclotomicUnitZMod p K k :=
  realCyclotomicUnit_complexConj p K k.val


-- @@ L128-134 verbatim
/-- ZMod-indexed value at `k = 2` (for `p ≥ 3`). -/
theorem realCyclotomicUnitZMod_two [IsCMField K] (hp_three : 3 ≤ p) :
    realCyclotomicUnitZMod p K (2 : ZMod p) = realCyclotomicUnit p K 2 := by
  haveI : NeZero p := ⟨hp.1.ne_zero⟩
  simp only [realCyclotomicUnitZMod]
  congr 1
  exact ZMod.val_natCast_of_lt (n := p) (a := 2) (by omega)


-- @@ L136-142 verbatim
/-- ZMod-indexed value at `k = 3` (for `p ≥ 5`). -/
theorem realCyclotomicUnitZMod_three [IsCMField K] (hp_five : 5 ≤ p) :
    realCyclotomicUnitZMod p K (3 : ZMod p) = realCyclotomicUnit p K 3 := by
  haveI : NeZero p := ⟨hp.1.ne_zero⟩
  simp only [realCyclotomicUnitZMod]
  congr 1
  exact ZMod.val_natCast_of_lt (n := p) (a := 3) (by omega)


-- @@ L144-149 verbatim
/-- ZMod-indexed residue-field congruence: `realCyclotomicUnitZMod k ≡ k.val²
(mod ζ - 1)` in `𝓞 K`. -/
theorem zetaSubOne_dvd_realCyclotomicUnitZMod_sub_sq [IsCMField K] (k : ZMod p) :
    ((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1 ∣
      realCyclotomicUnitZMod p K k - (k.val : 𝓞 K) ^ 2 :=
  zetaSubOne_dvd_realCyclotomicUnit_sub_sq p K k.val


-- @@ L151-155 verbatim
/-- Casting a natural index to `ZMod p` does not change the real cyclotomic combination. -/
theorem realCyclotomicUnitZMod_natCast [IsCMField K] (k : ℕ) [NeZero p] :
    realCyclotomicUnitZMod p K (k : ZMod p) = realCyclotomicUnit p K k := by
  simp only [realCyclotomicUnitZMod]
  rw [ZMod.val_natCast, ← realCyclotomicUnit_mod_p]


-- @@ L157-161 verbatim
/-- The ZMod-indexed real cyclotomic combination vanishes at zero. -/
theorem realCyclotomicUnitZMod_zero [IsCMField K] [NeZero p] :
    realCyclotomicUnitZMod p K (0 : ZMod p) = 0 := by
  simp only [realCyclotomicUnitZMod]
  rw [ZMod.val_zero, realCyclotomicUnit_zero]


-- @@ L163-168 verbatim
/-- The ZMod-indexed real cyclotomic combination equals one at one. -/
theorem realCyclotomicUnitZMod_one [IsCMField K] :
    realCyclotomicUnitZMod p K (1 : ZMod p) = 1 := by
  haveI : NeZero p := ⟨hp.1.ne_zero⟩
  simp only [realCyclotomicUnitZMod]
  rw [ZMod.val_one, realCyclotomicUnit_one]


-- @@ L170-176 verbatim
/-- `realCyclotomicUnitZMod p K k = 0 ↔ k = 0`. -/
theorem realCyclotomicUnitZMod_eq_zero_iff [IsCMField K] (k : ZMod p) :
    realCyclotomicUnitZMod p K k = 0 ↔ k = 0 := by
  haveI : NeZero p := ⟨hp.1.ne_zero⟩
  simp only [realCyclotomicUnitZMod]
  rw [realCyclotomicUnit_eq_zero_iff, ← ZMod.natCast_eq_zero_iff,
    ZMod.natCast_zmod_val]


-- @@ L178-185 verbatim
/-- For `k : (ZMod p)ˣ`, `realCyclotomicUnitZMod p K (k : ZMod p)` is a unit. -/
theorem isUnit_realCyclotomicUnitZMod_of_units [IsCMField K] (k : (ZMod p)ˣ)
    (hp_two : 2 ≤ p) :
    IsUnit (realCyclotomicUnitZMod p K (k : ZMod p)) := by
  haveI : NeZero p := ⟨hp.1.ne_zero⟩
  simp only [realCyclotomicUnitZMod]
  exact isUnit_realCyclotomicUnit p K (k : ZMod p).val
    (ZMod.val_coe_unit_coprime k) hp_two


-- @@ L187-198 verbatim
/-- `IsUnit (realCyclotomicUnitZMod p K k) ↔ k ≠ 0`. -/
theorem isUnit_realCyclotomicUnitZMod_iff [IsCMField K] (k : ZMod p) :
    IsUnit (realCyclotomicUnitZMod p K k) ↔ k ≠ 0 := by
  haveI : NeZero p := ⟨hp.1.ne_zero⟩
  refine ⟨fun h hk ↦ ?_, fun h ↦ ?_⟩
  · subst hk
    rw [realCyclotomicUnitZMod_zero] at h
    exact not_isUnit_zero h
  · have h_unit : IsUnit k := isUnit_iff_ne_zero.mpr h
    obtain ⟨u, hu⟩ := h_unit
    rw [← hu]
    exact isUnit_realCyclotomicUnitZMod_of_units p K u hp.1.two_le


-- @@ L200-204 verbatim
/-- The ZMod-indexed K-side cyclotomic unit vanishes exactly when `p` divides the representative. -/
theorem cyclotomicUnitZMod_eq_iff_val_dvd (k : ZMod p) :
    cyclotomicUnitZMod p K k = 0 ↔ p ∣ k.val := by
  simp only [cyclotomicUnitZMod]
  rw [cyclotomicUnit_eq_zero_iff]


-- @@ L206-208 verbatim
/-- Unfolding the ZMod-indexed cyclotomic unit at a unit-class element. -/
theorem cyclotomicUnitZMod_units_val (k : (ZMod p)ˣ) :
    cyclotomicUnitZMod p K (k : ZMod p) = cyclotomicUnit p K (k : ZMod p).val := rfl


-- @@ L210-216 verbatim
/-- ZMod-indexed cyclotomic unit value at `k = 2` (for `p ≥ 3`). -/
theorem cyclotomicUnitZMod_two (hp_three : 3 ≤ p) :
    cyclotomicUnitZMod p K (2 : ZMod p) = cyclotomicUnit p K 2 := by
  haveI : NeZero p := ⟨hp.1.ne_zero⟩
  simp only [cyclotomicUnitZMod]
  congr 1
  exact ZMod.val_natCast_of_lt (n := p) (a := 2) (by omega)


-- @@ L218-224 verbatim
/-- ZMod-indexed cyclotomic unit value at `k = 3` (for `p ≥ 5`). -/
theorem cyclotomicUnitZMod_three (hp_five : 5 ≤ p) :
    cyclotomicUnitZMod p K (3 : ZMod p) = cyclotomicUnit p K 3 := by
  haveI : NeZero p := ⟨hp.1.ne_zero⟩
  simp only [cyclotomicUnitZMod]
  congr 1
  exact ZMod.val_natCast_of_lt (n := p) (a := 3) (by omega)


-- @@ L226-231 verbatim
/-- ZMod-indexed residue-field congruence: `cyclotomicUnitZMod k ≡ k.val
(mod ζ - 1)` in `𝓞 K`. -/
theorem zetaSubOne_dvd_cyclotomicUnitZMod_sub_natCast (k : ZMod p) :
    ((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1 ∣
      cyclotomicUnitZMod p K k - (k.val : 𝓞 K) :=
  zetaSubOne_dvd_cyclotomicUnit_sub_natCast p K k.val


-- @@ L233-236 verbatim
/-- ZMod-indexed wrapper for the K⁺-side cyclotomic unit. -/
noncomputable def realCyclotomicUnitPlusZMod [IsCMField K] (k : ZMod p) :
    𝓞 (NumberField.maximalRealSubfield K) :=
  realCyclotomicUnitPlus p K k.val


-- @@ L238-242 verbatim
/-- Casting a natural index to `ZMod p` does not change the descended cyclotomic unit. -/
theorem realCyclotomicUnitPlusZMod_natCast [IsCMField K] (k : ℕ) [NeZero p] :
    realCyclotomicUnitPlusZMod p K (k : ZMod p) = realCyclotomicUnitPlus p K k := by
  simp only [realCyclotomicUnitPlusZMod]
  rw [ZMod.val_natCast, ← realCyclotomicUnitPlus_mod_p]


-- @@ L244-249 verbatim
/-- The descended ZMod-indexed unit maps to the corresponding K-side combination. -/
theorem algebraMap_realCyclotomicUnitPlusZMod [IsCMField K] (k : ZMod p) :
    algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
        (realCyclotomicUnitPlusZMod p K k) =
      realCyclotomicUnitZMod p K k :=
  algebraMap_realCyclotomicUnitPlus p K k.val


-- @@ L251-256 verbatim
/-- The descended ZMod-indexed cyclotomic unit vanishes at zero. -/
theorem realCyclotomicUnitPlusZMod_zero [IsCMField K] [NeZero p] :
    realCyclotomicUnitPlusZMod p K (0 : ZMod p) = 0 := by
  apply FaithfulSMul.algebraMap_injective
    (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
  rw [algebraMap_realCyclotomicUnitPlusZMod, realCyclotomicUnitZMod_zero, map_zero]


-- @@ L258-263 verbatim
/-- The descended ZMod-indexed cyclotomic unit equals one at one. -/
theorem realCyclotomicUnitPlusZMod_one [IsCMField K] :
    realCyclotomicUnitPlusZMod p K (1 : ZMod p) = 1 := by
  apply FaithfulSMul.algebraMap_injective
    (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
  rw [algebraMap_realCyclotomicUnitPlusZMod, realCyclotomicUnitZMod_one, map_one]


-- @@ L265-271 verbatim
/-- The descended ZMod-indexed cyclotomic unit vanishes exactly at the zero index. -/
theorem realCyclotomicUnitPlusZMod_eq_zero_iff [IsCMField K] (k : ZMod p) :
    realCyclotomicUnitPlusZMod p K k = 0 ↔ k = 0 := by
  rw [← (FaithfulSMul.algebraMap_injective
      (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)).eq_iff,
    map_zero, algebraMap_realCyclotomicUnitPlusZMod,
    realCyclotomicUnitZMod_eq_zero_iff]


-- @@ L273-279 verbatim
/-- K⁺-side ZMod-indexed value at `k = 2` (for `p ≥ 3`). -/
theorem realCyclotomicUnitPlusZMod_two [IsCMField K] (hp_three : 3 ≤ p) :
    realCyclotomicUnitPlusZMod p K (2 : ZMod p) = realCyclotomicUnitPlus p K 2 := by
  haveI : NeZero p := ⟨hp.1.ne_zero⟩
  simp only [realCyclotomicUnitPlusZMod]
  congr 1
  exact ZMod.val_natCast_of_lt (n := p) (a := 2) (by omega)


-- @@ L281-287 verbatim
/-- K⁺-side ZMod-indexed value at `k = 3` (for `p ≥ 5`). -/
theorem realCyclotomicUnitPlusZMod_three [IsCMField K] (hp_five : 5 ≤ p) :
    realCyclotomicUnitPlusZMod p K (3 : ZMod p) = realCyclotomicUnitPlus p K 3 := by
  haveI : NeZero p := ⟨hp.1.ne_zero⟩
  simp only [realCyclotomicUnitPlusZMod]
  congr 1
  exact ZMod.val_natCast_of_lt (n := p) (a := 3) (by omega)


-- @@ L289-299 verbatim
/-- The K⁺-side real cyclotomic unit is itself a unit when `k` is coprime
to `p`. Uses the norm characterization of units in `𝓞 K⁺`. -/
theorem isUnit_realCyclotomicUnitPlus [IsCMField K] (k : ℕ)
    (hk : k.Coprime p) (hp_two : 2 ≤ p) :
    IsUnit (realCyclotomicUnitPlus p K k) := by
  have h_unit : IsUnit (realCyclotomicUnit p K k) :=
    isUnit_realCyclotomicUnit p K k hk hp_two
  rw [← algebraMap_realCyclotomicUnitPlus p K k] at h_unit
  rw [← (RingOfIntegers.isUnit_norm (K := NumberField.maximalRealSubfield K)),
    RingOfIntegers.norm_algebraMap] at h_unit
  exact (isUnit_pow_iff Module.finrank_pos.ne').mp h_unit


-- @@ L301-306 verbatim
/-- The K⁺-side real cyclotomic unit, packaged as an element of
`(𝓞 K⁺)ˣ` when `k` is coprime to `p`. -/
noncomputable def realCyclotomicUnitPlusUnit [IsCMField K] (k : ℕ)
    (hk : k.Coprime p) (hp_two : 2 ≤ p) :
    (𝓞 (NumberField.maximalRealSubfield K))ˣ :=
  (isUnit_realCyclotomicUnitPlus p K k hk hp_two).unit


-- @@ L308-314 verbatim
/-- The value of the packaged K⁺-side unit is the chosen descended cyclotomic unit. -/
@[simp]
theorem realCyclotomicUnitPlusUnit_val [IsCMField K] (k : ℕ)
    (hk : k.Coprime p) (hp_two : 2 ≤ p) :
    (realCyclotomicUnitPlusUnit p K k hk hp_two : 𝓞 (NumberField.maximalRealSubfield K)) =
      realCyclotomicUnitPlus p K k :=
  IsUnit.unit_spec _


-- @@ L316-323 verbatim
/-- The K⁺-side cyclotomic unit lift, viewed in `(𝓞 K)ˣ` via the unit
map of `algebraMap`, equals `realCyclotomicUnitUnit`. -/
theorem algebraMap_realCyclotomicUnitPlusUnit_val [IsCMField K] (k : ℕ)
    (hk : k.Coprime p) (hp_two : 2 ≤ p) :
    algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
        (realCyclotomicUnitPlusUnit p K k hk hp_two) =
      realCyclotomicUnit p K k := by
  rw [realCyclotomicUnitPlusUnit_val, algebraMap_realCyclotomicUnitPlus]


-- @@ L325-332 verbatim
/-- For `k : (ZMod p)ˣ`, `realCyclotomicUnitPlusZMod p K (k : ZMod p)` is a unit. -/
theorem isUnit_realCyclotomicUnitPlusZMod_of_units [IsCMField K] (k : (ZMod p)ˣ)
    (hp_two : 2 ≤ p) :
    IsUnit (realCyclotomicUnitPlusZMod p K (k : ZMod p)) := by
  haveI : NeZero p := ⟨hp.1.ne_zero⟩
  simp only [realCyclotomicUnitPlusZMod]
  exact isUnit_realCyclotomicUnitPlus p K (k : ZMod p).val
    (ZMod.val_coe_unit_coprime k) hp_two


-- @@ L334-345 verbatim
/-- `IsUnit (realCyclotomicUnitPlusZMod p K k) ↔ k ≠ 0`. -/
theorem isUnit_realCyclotomicUnitPlusZMod_iff [IsCMField K] (k : ZMod p) :
    IsUnit (realCyclotomicUnitPlusZMod p K k) ↔ k ≠ 0 := by
  haveI : NeZero p := ⟨hp.1.ne_zero⟩
  refine ⟨fun h hk ↦ ?_, fun h ↦ ?_⟩
  · subst hk
    rw [realCyclotomicUnitPlusZMod_zero] at h
    exact not_isUnit_zero h
  · have h_unit : IsUnit k := isUnit_iff_ne_zero.mpr h
    obtain ⟨u, hu⟩ := h_unit
    rw [← hu]
    exact isUnit_realCyclotomicUnitPlusZMod_of_units p K u hp.1.two_le


-- @@ L347-351 verbatim
/-- The integer norm of a K⁺-side cyclotomic unit with coprime index is a unit in `ℤ`. -/
theorem realCyclotomicUnitPlus_norm_int_isUnit [IsCMField K]
    (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p) :
    IsUnit (Algebra.norm ℤ (realCyclotomicUnitPlus p K k)) :=
  (isUnit_realCyclotomicUnitPlus p K k hk hp_two).map _


-- @@ L353-357 verbatim
/-- The squared integer norm of a K⁺-side cyclotomic unit with coprime index is one. -/
theorem realCyclotomicUnitPlus_norm_int_sq_eq_one [IsCMField K]
    (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p) :
    (Algebra.norm ℤ (realCyclotomicUnitPlus p K k)) ^ 2 = (1 : ℤ) :=
  Int.isUnit_sq (realCyclotomicUnitPlus_norm_int_isUnit p K k hk hp_two)


-- @@ L359-359 verbatim
end RealCyclotomicUnits


-- @@ L361-361 verbatim
end FLT37


-- @@ L363-363 verbatim
end BernoulliRegular


-- @@ L365-365 verbatim
end
