/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.RCLike.Basic

-- @@ L9-27 verbatim
/-!

# Units on Temperature

A unit of temperature corresponds to a choice of translationally-invariant
metric on the temperature manifold (to be defined diffeomorphic to `ℝ≥0`).
Such a choice is (non-canonically) equivalent to a
choice of positive real number. We define the type `TemperatureUnit` to be equivalent to the
positive reals.

On `TemperatureUnit` there is an instance of division giving a real number, corresponding to the
ratio of the two scales of temperature unit.

To define specific temperature units, we first state the existence of a
a given temperature unit, and then construct all other temperature units from it.
We choose to state the
existence of the temperature unit of kelvin, and construct all other temperature units from that.

-/


-- @@ L29-29 verbatim
@[expose] public section


-- @@ L31-31 verbatim
open NNReal


-- @@ L33-38 verbatim
/-- The choices of translationally-invariant metrics on the temperature-manifold.
  Such a choice corresponds to a choice of units for temperature. -/
structure TemperatureUnit where
  /-- The underlying scale of the unit. -/
  val : ℝ
  property : 0 < val


-- @@ L40-40 verbatim
namespace TemperatureUnit


-- @@ L42-44 verbatim
@[simp]
lemma val_ne_zero (x : TemperatureUnit) : x.val ≠ 0 := by
  exact Ne.symm (ne_of_lt x.property)


-- @@ L46-46 verbatim
lemma val_pos (x : TemperatureUnit) : 0 < x.val := x.property


-- @@ L48-49 verbatim
instance : Inhabited TemperatureUnit where
  default := ⟨1, by norm_num⟩


-- @@ L51-55 verbatim
/-!

## Division of TemperatureUnit

-/


-- @@ L57-58 verbatim
noncomputable instance : HDiv TemperatureUnit TemperatureUnit ℝ≥0 where
  hDiv x t := ⟨x.val / t.val, div_nonneg (le_of_lt x.val_pos) (le_of_lt t.val_pos)⟩


-- @@ L60-61 verbatim
lemma div_eq_val (x y : TemperatureUnit) :
    x / y = (⟨x.val / y.val, div_nonneg (le_of_lt x.val_pos) (le_of_lt y.val_pos)⟩ : ℝ≥0) := rfl


-- @@ L63-67 verbatim
@[simp]
lemma div_ne_zero (x y : TemperatureUnit) : ¬ x / y = (0 : ℝ≥0) := by
  rw [div_eq_val]
  refine coe_ne_zero.mp ?_
  simp [toReal]


-- @@ L69-73 verbatim
@[simp]
lemma div_pos (x y : TemperatureUnit) : (0 : ℝ≥0) < x/ y := by
  apply lt_of_le_of_ne
  · exact zero_le
  · exact Ne.symm (div_ne_zero x y)


-- @@ L75-79 verbatim
@[simp]
lemma div_self (x : TemperatureUnit) :
    x / x = (1 : ℝ≥0) := by
  simp [div_eq_val, x.val_ne_zero]
  rfl


-- @@ L81-84 verbatim
lemma div_symm (x y : TemperatureUnit) :
    x / y = (y / x)⁻¹ := NNReal.eq <| by
  show x.val / y.val = (y.val / x.val)⁻¹
  rw [inv_div]


-- @@ L86-89 verbatim
/-- The unit-ratio cocycle at `ℝ≥0` (the un-coerced form of `div_mul_div_coe`). -/
lemma div_mul_div (x y z : TemperatureUnit) : (x / y) * (y / z) = x / z := NNReal.eq <| by
  show x.val / y.val * (y.val / z.val) = x.val / z.val
  rw [div_mul_div_comm, mul_comm x.val y.val, mul_div_mul_left _ _ y.val_ne_zero]


-- @@ L91-95 verbatim
@[simp]
lemma div_mul_div_coe (x y z : TemperatureUnit) :
    (x / y : ℝ) * (y /z : ℝ) = x /z := by
  simp [div_eq_val, toReal]
  field_simp


-- @@ L97-101 verbatim
/-!

## The scaling of a temperature unit

-/


-- @@ L103-105 verbatim
/-- The scaling of a temperature unit by a positive real. -/
def scale (r : ℝ) (x : TemperatureUnit) (hr : 0 < r := by norm_num) : TemperatureUnit :=
  ⟨r * x.val, mul_pos hr x.val_pos⟩


-- @@ L107-111 verbatim
@[simp]
lemma scale_div_self (x : TemperatureUnit) (r : ℝ) (hr : 0 < r) :
    scale r x hr / x = (⟨r, le_of_lt hr⟩ : ℝ≥0) := by
  simp [scale, div_eq_val]
  rfl


-- @@ L113-118 verbatim
@[simp]
lemma self_div_scale (x : TemperatureUnit) (r : ℝ) (hr : 0 < r) :
    x / scale r x hr = (⟨1/r, _root_.div_nonneg (by simp) (le_of_lt hr)⟩ : ℝ≥0) := by
  simp [scale, div_eq_val]
  ext
  field_simp


-- @@ L120-122 verbatim
@[simp]
lemma scale_one (x : TemperatureUnit) : scale 1 x = x := by
  simp [scale]


-- @@ L124-129 verbatim
@[simp]
lemma scale_div_scale (x1 x2 : TemperatureUnit) {r1 r2 : ℝ} (hr1 : 0 < r1) (hr2 : 0 < r2) :
    scale r1 x1 hr1 / scale r2 x2 hr2 = (⟨r1, le_of_lt hr1⟩ / ⟨r2, le_of_lt hr2⟩) * (x1 / x2) := by
  refine NNReal.eq ?_
  show r1 * x1.val / (r2 * x2.val) = r1 / r2 * (x1.val / x2.val)
  rw [div_mul_div_comm]


-- @@ L131-135 verbatim
@[simp]
lemma scale_scale (x : TemperatureUnit) (r1 r2 : ℝ) (hr1 : 0 < r1) (hr2 : 0 < r2) :
    scale r1 (scale r2 x hr2) hr1 = scale (r1 * r2) x (mul_pos hr1 hr2) := by
  simp [scale]
  ring


-- @@ L137-148 verbatim
/-!

## Specific choices of temperature units

To define a specific temperature units.
We first define the notion of a kelvin to correspond to the temperature unit with underlying value
equal to `1`. This is really down to a choice in the isomorphism between the set of metrics
on the temperature manifold and the positive reals.

Once we have defined kelvin, we can define other temperature units by scaling kelvin.

-/


-- @@ L150-151 verbatim
/-- The definition of a temperature unit of kelvin. -/
def kelvin : TemperatureUnit := ⟨1, by norm_num⟩


-- @@ L153-154 verbatim
/-- The temperature unit of degrees nanokelvin (10^(-9) kelvin). -/
noncomputable def nanokelvin : TemperatureUnit := scale (1e-9) kelvin


-- @@ L156-157 verbatim
/-- The temperature unit of degrees microkelvin (10^(-6) kelvin). -/
noncomputable def microkelvin : TemperatureUnit := scale (1e-6) kelvin


-- @@ L159-160 verbatim
/-- The temperature unit of degrees millikelvin (10^(-3) kelvin). -/
noncomputable def millikelvin : TemperatureUnit := scale (1e-3) kelvin


-- @@ L162-164 verbatim
/-- The temperature unit of degrees fahrenheit ((5/9) of a kelvin).
  Note, this is fahrenheit starting at `0` absolute temperature. -/
noncomputable def absoluteFahrenheit : TemperatureUnit := scale (5 / 9) kelvin


-- @@ L166-166 verbatim
end TemperatureUnit
