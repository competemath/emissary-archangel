/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Units.WithDim.Basic

-- @@ L9-16 verbatim
/-!

# Area

In this module we define the dimensionful type corresponding to an area.
We define specific instances of areas, such as square meters, square feet, etc.

-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
open Dimension

-- @@ L21-21 verbatim
open NNReal


-- @@ L23-24 verbatim
/-- The type of areas in the absence of a choice of unit. -/
abbrev DimArea : Type := Dimensionful (WithDim (L𝓭 * L𝓭) ℝ≥0)


-- @@ L26-26 verbatim
namespace DimArea


-- @@ L28-28 verbatim
open LTMCTUnitChoices


-- @@ L30-34 verbatim
/-!

## Basic areas

-/


-- @@ L36-36 verbatim
open Dimensionful CarriesDimension


-- @@ L38-39 verbatim
/-- The dimensional area corresponding to 1 square meter. -/
noncomputable def squareMeter : DimArea := toDimensionful SI ⟨1⟩


-- @@ L41-43 verbatim
/-- The dimensional area corresponding to 1 square foot. -/
noncomputable def squareFoot : DimArea := toDimensionful ({SI with
  length := LengthUnit.feet} : LTMCTUnitChoices) ⟨1⟩


-- @@ L45-47 verbatim
/-- The dimensional area corresponding to 1 square mile. -/
noncomputable def squareMile : DimArea := toDimensionful ({SI with
  length := LengthUnit.miles} : LTMCTUnitChoices) ⟨1⟩


-- @@ L49-50 verbatim
/-- The dimensional area corresponding to 1 are (100 square meters). -/
noncomputable def are : DimArea := toDimensionful SI ⟨100⟩


-- @@ L52-53 verbatim
/-- The dimensional area corresponding to 1 hectare (10,000 square meters). -/
noncomputable def hectare : DimArea := toDimensionful SI ⟨10000⟩


-- @@ L55-57 verbatim
/-- The dimensional area corresponding to 1 acre (1/640 square miles). -/
noncomputable def acre : DimArea := toDimensionful ({SI with
  length := LengthUnit.miles} : LTMCTUnitChoices) ⟨(1/640)⟩


-- @@ L59-63 verbatim
/-!

## Area in SI units

-/


-- @@ L65-67 verbatim
@[simp]
lemma squareMeter_in_SI : squareMeter.1 SI = ⟨1⟩ := by
  simp [squareMeter, toDimensionful_apply_apply]


-- @@ L69-75 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma squareFoot_in_SI : squareFoot.1 SI = ⟨0.09290304⟩ := by
  simp [squareFoot, dimScale, LengthUnit.feet, toDimensionful_apply_apply]
  ext
  simp [NNReal.coe_ofScientific]
  norm_num [toReal]


-- @@ L77-83 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma squareMile_in_SI : squareMile.1 SI = ⟨2589988.110336⟩ := by
  simp [squareMile, dimScale, LengthUnit.miles, toDimensionful_apply_apply]
  ext
  simp [NNReal.coe_ofScientific]
  norm_num [toReal]


-- @@ L85-87 verbatim
@[simp]
lemma are_in_SI : are.1 SI = ⟨100⟩ := by
  simp [are, toDimensionful_apply_apply]


-- @@ L89-91 verbatim
@[simp]
lemma hectare_in_SI : hectare.1 SI = ⟨10000⟩ := by
  simp [hectare, toDimensionful_apply_apply]


-- @@ L93-99 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma acre_in_SI : acre.1 SI = ⟨4046.8564224⟩ := by
  simp [acre, dimScale, LengthUnit.miles, toDimensionful_apply_apply]
  ext
  simp [NNReal.coe_ofScientific]
  norm_num [toReal]


-- @@ L101-105 verbatim
/-!

## Relations between areas

-/


-- @@ L107-112 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- One acre is exactly `43560` square feet. -/
lemma acre_eq_mul_squareFeet : acre = (43560 : ℝ≥0) • squareFoot := by
  apply (toDimensionful SI).symm.injective
  ext
  norm_num [toDimensionful]


-- @@ L114-114 verbatim
end DimArea
