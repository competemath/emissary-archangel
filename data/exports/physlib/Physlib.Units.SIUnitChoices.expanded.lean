/-
Copyright (c) 2026 Nicolas Rouquette. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette
-/
module

public import Physlib.Units.UnitSystem
public import Physlib.Units.ISQDimensionBase

-- @@ L10-36 verbatim
/-!

# A typed unit choice over the ISQ base quantities (the SI units)

`LTMCTUnitChoices` is the typed unit choice over PhysLib's default dimension basis
`LTMCTDimensionBase`. This module gives the *second* typed unit choice — over the
seven ISQ base quantities `ISQDimensionBase` — realised through the basis-generic
`UnitMagnitudeCatalog` / `UnitSystem` machinery of `Physlib.Units.UnitSystem`. It is the concrete
payoff of parametrising the unit side: the same generic layer produces a fully *typed*
unit choice over a different basis, and the scaling homomorphism comes for free from
`UnitScale.dimScale` — nothing is re-proved by hand.

The ISQ base quantities are length, mass, time, electric current, thermodynamic
temperature, amount of substance and luminous intensity. Four of the corresponding typed
unit types already exist (`LengthUnit`, `MassUnit`, `TimeUnit`, `TemperatureUnit`); the
remaining three — `CurrentUnit`, `AmountUnit`, `LuminousIntensityUnit` — are introduced
here. They follow the `LengthUnit` convention of a positive-real magnitude and support
rescaling; the remaining unit-ratio relation API can be filled in later and, following
PhysLib's layout, they would ultimately live under the relevant physics directories.

`SIUnitChoices := UnitSystem ISQDimensionBase` is then the typed SI unit choice, and
`SIUnitChoices.SI` is the coherent SI choice (metre, kilogram, second, ampere, kelvin,
mole, candela). Contrast `SIUnitChoices` (current-based, seven typed slots) with
`LTMCTUnitChoices` (charge-based, five typed slots): the machinery supports both, and the
`Dimension.ltmctToISQ` / `Dimension.isqToLTMCT` bridge relates their bases.

-/


-- @@ L38-38 verbatim
@[expose] public section


-- @@ L40-40 verbatim
open NNReal

-- @@ L41-41 verbatim
open scoped BigOperators


-- @@ L43-47 verbatim
/-!

## Typed unit types for the ISQ base quantities not already present

-/


-- @@ L49-54 verbatim
/-- A unit of electric current — a choice of positive-real magnitude. The SI coherent
  choice is the ampere. -/
structure CurrentUnit where
  /-- The underlying scale of the unit. -/
  val : ℝ
  property : 0 < val


-- @@ L56-56 verbatim
namespace CurrentUnit


-- @@ L58-59 verbatim
@[simp]
lemma val_ne_zero (x : CurrentUnit) : x.val ≠ 0 := Ne.symm (ne_of_lt x.property)


-- @@ L61-61 verbatim
lemma val_pos (x : CurrentUnit) : 0 < x.val := x.property


-- @@ L63-64 verbatim
instance : Inhabited CurrentUnit where
  default := ⟨1, by norm_num⟩


-- @@ L66-67 verbatim
noncomputable instance : HDiv CurrentUnit CurrentUnit ℝ≥0 where
  hDiv x t := ⟨x.val / t.val, div_nonneg x.val_pos.le t.val_pos.le⟩


-- @@ L69-70 verbatim
lemma div_eq_val (x y : CurrentUnit) :
    x / y = (⟨x.val / y.val, div_nonneg x.val_pos.le y.val_pos.le⟩ : ℝ≥0) := rfl


-- @@ L72-74 verbatim
/-- Scale a unit of electric current by a positive real factor. -/
def scale (r : ℝ) (x : CurrentUnit) (hr : 0 < r := by norm_num) : CurrentUnit :=
  ⟨r * x.val, mul_pos hr x.val_pos⟩


-- @@ L76-80 verbatim
@[simp]
lemma scale_div_self (x : CurrentUnit) (r : ℝ) (hr : 0 < r) :
    scale r x hr / x = (⟨r, le_of_lt hr⟩ : ℝ≥0) := by
  simp [scale, div_eq_val]
  rfl


-- @@ L82-87 verbatim
@[simp]
lemma self_div_scale (x : CurrentUnit) (r : ℝ) (hr : 0 < r) :
    x / scale r x hr =
      (⟨1 / r, _root_.div_nonneg (by simp) (le_of_lt hr)⟩ : ℝ≥0) := by
  simp [scale, div_eq_val]
  field_simp


-- @@ L89-91 verbatim
@[simp]
lemma scale_one (x : CurrentUnit) : scale 1 x = x := by
  simp [scale]


-- @@ L93-100 verbatim
@[simp]
lemma scale_div_scale
    (x1 x2 : CurrentUnit) {r1 r2 : ℝ} (hr1 : 0 < r1) (hr2 : 0 < r2) :
    scale r1 x1 hr1 / scale r2 x2 hr2 =
      (⟨r1, le_of_lt hr1⟩ / ⟨r2, le_of_lt hr2⟩) * (x1 / x2) := by
  refine NNReal.eq ?_
  show r1 * x1.val / (r2 * x2.val) = r1 / r2 * (x1.val / x2.val)
  rw [div_mul_div_comm]


-- @@ L102-107 verbatim
@[simp]
lemma scale_scale (x : CurrentUnit) (r1 r2 : ℝ) (hr1 : 0 < r1) (hr2 : 0 < r2) :
    scale r1 (scale r2 x hr2) hr1 =
      scale (r1 * r2) x (mul_pos hr1 hr2) := by
  simp [scale]
  ring


-- @@ L109-110 verbatim
/-- The SI coherent unit of electric current, the ampere. -/
def amperes : CurrentUnit := ⟨1, by norm_num⟩


-- @@ L112-114 verbatim
/-- One milliampere, equal to `10⁻³` amperes. -/
noncomputable def milliamperes : CurrentUnit :=
  scale ((1 / 10) ^ 3) amperes


-- @@ L116-116 verbatim
end CurrentUnit


-- @@ L118-123 verbatim
/-- A unit of amount of substance — a choice of positive-real magnitude. The SI coherent
  choice is the mole. -/
structure AmountUnit where
  /-- The underlying scale of the unit. -/
  val : ℝ
  property : 0 < val


-- @@ L125-125 verbatim
namespace AmountUnit


-- @@ L127-128 verbatim
@[simp]
lemma val_ne_zero (x : AmountUnit) : x.val ≠ 0 := Ne.symm (ne_of_lt x.property)


-- @@ L130-130 verbatim
lemma val_pos (x : AmountUnit) : 0 < x.val := x.property


-- @@ L132-133 verbatim
instance : Inhabited AmountUnit where
  default := ⟨1, by norm_num⟩


-- @@ L135-136 verbatim
noncomputable instance : HDiv AmountUnit AmountUnit ℝ≥0 where
  hDiv x t := ⟨x.val / t.val, div_nonneg x.val_pos.le t.val_pos.le⟩


-- @@ L138-139 verbatim
lemma div_eq_val (x y : AmountUnit) :
    x / y = (⟨x.val / y.val, div_nonneg x.val_pos.le y.val_pos.le⟩ : ℝ≥0) := rfl


-- @@ L141-143 verbatim
/-- Scale a unit of amount of substance by a positive real factor. -/
def scale (r : ℝ) (x : AmountUnit) (hr : 0 < r := by norm_num) : AmountUnit :=
  ⟨r * x.val, mul_pos hr x.val_pos⟩


-- @@ L145-149 verbatim
@[simp]
lemma scale_div_self (x : AmountUnit) (r : ℝ) (hr : 0 < r) :
    scale r x hr / x = (⟨r, le_of_lt hr⟩ : ℝ≥0) := by
  simp [scale, div_eq_val]
  rfl


-- @@ L151-156 verbatim
@[simp]
lemma self_div_scale (x : AmountUnit) (r : ℝ) (hr : 0 < r) :
    x / scale r x hr =
      (⟨1 / r, _root_.div_nonneg (by simp) (le_of_lt hr)⟩ : ℝ≥0) := by
  simp [scale, div_eq_val]
  field_simp


-- @@ L158-160 verbatim
@[simp]
lemma scale_one (x : AmountUnit) : scale 1 x = x := by
  simp [scale]


-- @@ L162-169 verbatim
@[simp]
lemma scale_div_scale
    (x1 x2 : AmountUnit) {r1 r2 : ℝ} (hr1 : 0 < r1) (hr2 : 0 < r2) :
    scale r1 x1 hr1 / scale r2 x2 hr2 =
      (⟨r1, le_of_lt hr1⟩ / ⟨r2, le_of_lt hr2⟩) * (x1 / x2) := by
  refine NNReal.eq ?_
  show r1 * x1.val / (r2 * x2.val) = r1 / r2 * (x1.val / x2.val)
  rw [div_mul_div_comm]


-- @@ L171-176 verbatim
@[simp]
lemma scale_scale (x : AmountUnit) (r1 r2 : ℝ) (hr1 : 0 < r1) (hr2 : 0 < r2) :
    scale r1 (scale r2 x hr2) hr1 =
      scale (r1 * r2) x (mul_pos hr1 hr2) := by
  simp [scale]
  ring


-- @@ L178-179 verbatim
/-- The SI coherent unit of amount of substance, the mole. -/
def moles : AmountUnit := ⟨1, by norm_num⟩


-- @@ L181-181 verbatim
end AmountUnit


-- @@ L183-188 verbatim
/-- A unit of luminous intensity — a choice of positive-real magnitude. The SI coherent
  choice is the candela. -/
structure LuminousIntensityUnit where
  /-- The underlying scale of the unit. -/
  val : ℝ
  property : 0 < val


-- @@ L190-190 verbatim
namespace LuminousIntensityUnit


-- @@ L192-193 verbatim
@[simp]
lemma val_ne_zero (x : LuminousIntensityUnit) : x.val ≠ 0 := Ne.symm (ne_of_lt x.property)


-- @@ L195-195 verbatim
lemma val_pos (x : LuminousIntensityUnit) : 0 < x.val := x.property


-- @@ L197-198 verbatim
instance : Inhabited LuminousIntensityUnit where
  default := ⟨1, by norm_num⟩


-- @@ L200-201 verbatim
noncomputable instance : HDiv LuminousIntensityUnit LuminousIntensityUnit ℝ≥0 where
  hDiv x t := ⟨x.val / t.val, div_nonneg x.val_pos.le t.val_pos.le⟩


-- @@ L203-204 verbatim
lemma div_eq_val (x y : LuminousIntensityUnit) :
    x / y = (⟨x.val / y.val, div_nonneg x.val_pos.le y.val_pos.le⟩ : ℝ≥0) := rfl


-- @@ L206-210 verbatim
/-- Scale a unit of luminous intensity by a positive real factor. -/
def scale
    (r : ℝ) (x : LuminousIntensityUnit) (hr : 0 < r := by norm_num) :
    LuminousIntensityUnit :=
  ⟨r * x.val, mul_pos hr x.val_pos⟩


-- @@ L212-216 verbatim
@[simp]
lemma scale_div_self (x : LuminousIntensityUnit) (r : ℝ) (hr : 0 < r) :
    scale r x hr / x = (⟨r, le_of_lt hr⟩ : ℝ≥0) := by
  simp [scale, div_eq_val]
  rfl


-- @@ L218-223 verbatim
@[simp]
lemma self_div_scale (x : LuminousIntensityUnit) (r : ℝ) (hr : 0 < r) :
    x / scale r x hr =
      (⟨1 / r, _root_.div_nonneg (by simp) (le_of_lt hr)⟩ : ℝ≥0) := by
  simp [scale, div_eq_val]
  field_simp


-- @@ L225-227 verbatim
@[simp]
lemma scale_one (x : LuminousIntensityUnit) : scale 1 x = x := by
  simp [scale]


-- @@ L229-238 verbatim
@[simp]
lemma scale_div_scale
    (x1 x2 : LuminousIntensityUnit)
    {r1 r2 : ℝ}
    (hr1 : 0 < r1) (hr2 : 0 < r2) :
    scale r1 x1 hr1 / scale r2 x2 hr2 =
      (⟨r1, le_of_lt hr1⟩ / ⟨r2, le_of_lt hr2⟩) * (x1 / x2) := by
  refine NNReal.eq ?_
  show r1 * x1.val / (r2 * x2.val) = r1 / r2 * (x1.val / x2.val)
  rw [div_mul_div_comm]


-- @@ L240-248 verbatim
@[simp]
lemma scale_scale
    (x : LuminousIntensityUnit)
    (r1 r2 : ℝ)
    (hr1 : 0 < r1) (hr2 : 0 < r2) :
    scale r1 (scale r2 x hr2) hr1 =
      scale (r1 * r2) x (mul_pos hr1 hr2) := by
  simp [scale]
  ring


-- @@ L250-251 verbatim
/-- The SI coherent unit of luminous intensity, the candela. -/
def candelas : LuminousIntensityUnit := ⟨1, by norm_num⟩


-- @@ L253-253 verbatim
end LuminousIntensityUnit


-- @@ L255-262 verbatim
/-!

## The ISQ `UnitMagnitudeCatalog` instance

Each ISQ base quantity is assigned its typed unit type; the magnitude layer is the
positive-real `val`, exactly as for the `LTMCTDimensionBase` instance.

-/


-- @@ L264-280 verbatim
noncomputable instance : UnitMagnitudeCatalog ISQDimensionBase where
  Unit
    | .length => LengthUnit
    | .mass => MassUnit
    | .time => TimeUnit
    | .current => CurrentUnit
    | .temperature => TemperatureUnit
    | .amount => AmountUnit
    | .luminousIntensity => LuminousIntensityUnit
  mag {b} :=
    match b with
    | .length | .mass | .time | .current | .temperature | .amount | .luminousIntensity =>
        fun u => ⟨u.val, u.val_pos.le⟩
  mag_pos {b} :=
    match b with
    | .length | .mass | .time | .current | .temperature | .amount | .luminousIntensity =>
        fun u => NNReal.coe_pos.mp u.val_pos


-- @@ L282-286 verbatim
/-!

## Folding over the ISQ base quantities

-/


-- @@ L288-300 verbatim
open Finset in
/-- The product over the seven ISQ base quantities, in canonical enumeration order — the
  `ISQDimensionBase` companion to `prod_univ_LTMCTDimensionBase`, a reusable fact about the
  `Fintype` enumeration for folding `Finset.prod` over the ISQ basis. -/
lemma prod_univ_ISQDimensionBase {M : Type} [CommMonoid M] (f : ISQDimensionBase → M) :
    ∏ b, f b = f .length * f .mass * f .time * f .current * f .temperature
      * f .amount * f .luminousIntensity := by
  rw [show (univ : Finset ISQDimensionBase) =
        {.length, .mass, .time, .current, .temperature, .amount, .luminousIntensity} from by
      decide]
  rw [prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
    prod_insert (by decide), prod_insert (by decide), prod_insert (by decide), prod_singleton,
    ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc]


-- @@ L302-306 verbatim
/-!

## `SIUnitChoices`

-/


-- @@ L308-311 verbatim
/-- A **typed SI unit choice**: a typed unit at every ISQ base quantity. This is the
  seven-slot, current-based sibling of the five-slot, charge-based `LTMCTUnitChoices`,
  produced by the same basis-generic `UnitSystem` / `UnitMagnitudeCatalog` machinery. -/
abbrev SIUnitChoices := UnitSystem ISQDimensionBase


-- @@ L313-313 verbatim
namespace SIUnitChoices


-- @@ L315-323 verbatim
/-- The coherent SI unit choice: metre, kilogram, second, ampere, kelvin, mole, candela. -/
noncomputable def SI : SIUnitChoices := fun
  | .length => LengthUnit.meters
  | .mass => MassUnit.kilograms
  | .time => TimeUnit.seconds
  | .current => CurrentUnit.amperes
  | .temperature => TemperatureUnit.kelvin
  | .amount => AmountUnit.moles
  | .luminousIntensity => LuminousIntensityUnit.candelas


-- @@ L325-328 verbatim
/-- The dimension-scaling homomorphism over the ISQ basis, obtained *for free* from the
  generic `UnitScale.dimScale` fold — no per-basis hand-rolling. -/
noncomputable def dimScale (u1 u2 : SIUnitChoices) : Dimension ISQDimensionBase →* ℝ≥0 :=
  UnitScale.dimScale u1.toScale u2.toScale


-- @@ L330-332 verbatim
/-- Type-safety check: the current slot of a typed SI unit choice is a `CurrentUnit` —
  a `MassUnit` cannot be placed there. -/
example (u : SIUnitChoices) : CurrentUnit := u .current


-- @@ L334-336 verbatim
/-- A quantity of ISQ dimension does not rescale between a unit choice and itself. -/
lemma dimScale_self (u : SIUnitChoices) (d : Dimension ISQDimensionBase) :
    dimScale u u d = 1 := UnitScale.dimScale_self _ d


-- @@ L338-338 verbatim
end SIUnitChoices
