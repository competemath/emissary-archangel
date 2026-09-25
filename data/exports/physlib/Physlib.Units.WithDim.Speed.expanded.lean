/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Units.WithDim.Basic

-- @@ L9-16 verbatim
/-!

# Speed

In this module we define the dimensionful type corresponding to an speed.
We define specific instances of speed, such as miles per hour, kilometers per hour, etc.

-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
open Dimension

-- @@ L21-21 verbatim
open NNReal


-- @@ L23-24 verbatim
/-- The type of speeds in the absence of a choice of unit. -/
abbrev DimSpeed : Type := Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ≥0)


-- @@ L26-26 verbatim
namespace DimSpeed


-- @@ L28-28 verbatim
open LTMCTUnitChoices


-- @@ L30-34 verbatim
/-!

## Basic speeds

-/

-- @@ L35-35 verbatim
open Dimensionful

-- @@ L36-36 verbatim
open LTMCTUnitChoices CarriesDimension

-- @@ L37-38 verbatim
/-- The dimensional speed corresponding to 1 meter per second. -/
noncomputable def oneMeterPerSecond : DimSpeed := toDimensionful SI ⟨1⟩


-- @@ L40-42 verbatim
/-- The dimensional speed corresponding to 1 mile per hour. -/
noncomputable def oneMilePerHour : DimSpeed := toDimensionful ({SI with
  length := LengthUnit.miles, time := TimeUnit.hours} : LTMCTUnitChoices) ⟨1⟩


-- @@ L44-46 verbatim
/-- The dimensional speed corresponding to 1 kilometer per hour. -/
noncomputable def oneKilometerPerHour : DimSpeed := toDimensionful ({SI with
  length := LengthUnit.kilometers, time := TimeUnit.hours} : LTMCTUnitChoices) ⟨1⟩


-- @@ L48-50 verbatim
/-- The dimensional speed corresponding to 1 knot, aka, one nautical mile per hour. -/
noncomputable def oneKnot : DimSpeed := toDimensionful ({SI with
  length := LengthUnit.nauticalMiles, time := TimeUnit.hours} : LTMCTUnitChoices) ⟨1⟩


-- @@ L52-54 verbatim
/-- The dimensionful speed of light corresponding to 299792458 meters per second. -/
noncomputable def speedOfLight : Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ) :=
  toDimensionful SI ⟨299792458⟩


-- @@ L56-60 verbatim
/-!

## Speed in SI units

-/


-- @@ L62-64 verbatim
@[simp]
lemma oneMeterPerSecond_in_SI : oneMeterPerSecond SI = ⟨1⟩ := by
  simp [oneMeterPerSecond, toDimensionful_apply_apply]


-- @@ L66-72 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma oneMilePerHour_in_SI : oneMilePerHour SI = ⟨0.44704⟩ := by
  simp [oneMilePerHour, dimScale, LengthUnit.miles, TimeUnit.hours, toDimensionful_apply_apply]
  ext
  simp [NNReal.coe_ofScientific]
  norm_num [toReal]


-- @@ L74-83 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma oneKilometerPerHour_in_SI :
    oneKilometerPerHour SI = ⟨5/18⟩ := by
  simp [oneKilometerPerHour, dimScale,
    LengthUnit.kilometers, TimeUnit.hours, toDimensionful_apply_apply]
  ext
  simp only [WithDim.smul_val, smul_eq_mul, mul_one, NNReal.coe_mul, coe_rpow, NNReal.coe_div,
    NNReal.coe_ofNat]
  norm_num [toReal]


-- @@ L85-92 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma oneKnot_in_SI : oneKnot SI = ⟨463/900⟩ := by
  simp [oneKnot, dimScale, LengthUnit.nauticalMiles, TimeUnit.hours, toDimensionful_apply_apply]
  ext
  simp only [WithDim.smul_val, smul_eq_mul, mul_one, NNReal.coe_mul, coe_rpow, NNReal.coe_div,
    NNReal.coe_ofNat]
  norm_num [toReal]


-- @@ L94-96 verbatim
@[simp]
lemma speedOfLight_in_SI : speedOfLight SI = ⟨299792458⟩ := by
  simp [speedOfLight, toDimensionful_apply_apply]


-- @@ L98-102 verbatim
/-!

## Relations between speeds

-/


-- @@ L104-109 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma oneKnot_eq_mul_oneKilometerPerHour :
    oneKnot = (1.852 : ℝ≥0) • oneKilometerPerHour := by
  apply (toDimensionful SI).symm.injective
  ext
  norm_num [toDimensionful]


-- @@ L111-116 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma oneKilometerPerHour_eq_mul_oneKnot:
    oneKilometerPerHour = (250/463 : ℝ≥0) • oneKnot := by
  apply (toDimensionful SI).symm.injective
  ext
  norm_num [toDimensionful]


-- @@ L118-123 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma oneMeterPerSecond_eq_mul_oneMilePerHour :
    oneMeterPerSecond = (3125/1397 : ℝ≥0) • oneMilePerHour := by
  apply (toDimensionful SI).symm.injective
  ext
  norm_num [toDimensionful]


-- @@ L125-125 verbatim
end DimSpeed
