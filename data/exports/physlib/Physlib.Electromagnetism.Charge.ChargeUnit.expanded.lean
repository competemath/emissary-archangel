/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.RCLike.Basic

-- @@ L9-30 verbatim
/-!

# The units of charge

A unit of charge corresponding to a choice of translationally-invariant
metric on the charge manifold (to be defined diffeomorphic to `ℝ`).
Such a choice is (non-canonically) equivalent to a
choice of positive real number. We define the type `ChargeUnit` to be equivalent to the
positive reals.

We assume that the charge manifold is already defined with an orientation, with the
electron being in the negative direction.

On `ChargeUnit` there is an instance of division giving a real number, corresponding to the
ratio of the two scales of temperature unit.

To define specific charge units, we first state the existence of a
a given charge unit, and then construct all other charge units from it.
We choose to state the
existence of the charge unit of the coulomb, and construct all other charge units from that.

-/


-- @@ L32-32 verbatim
@[expose] public section


-- @@ L34-34 verbatim
open NNReal


-- @@ L36-42 verbatim
/-- The choices of translationally-invariant metrics on the charge-manifold.
  Such a choice corresponds to a choice of units for charge.
  This assumes that an orientation has already being picked on the charge manifold. -/
structure ChargeUnit where
  /-- The underlying scale of the unit. -/
  val : ℝ
  property : 0 < val


-- @@ L44-44 verbatim
namespace ChargeUnit


-- @@ L46-48 verbatim
@[simp]
lemma val_ne_zero (x : ChargeUnit) : x.val ≠ 0 := by
  exact Ne.symm (ne_of_lt x.property)


-- @@ L50-50 verbatim
lemma val_pos (x : ChargeUnit) : 0 < x.val := x.property


-- @@ L52-53 verbatim
instance : Inhabited ChargeUnit where
  default := ⟨1, by norm_num⟩


-- @@ L55-59 verbatim
/-!

## Division of ChargeUnit

-/


-- @@ L61-62 verbatim
noncomputable instance : HDiv ChargeUnit ChargeUnit ℝ≥0 where
  hDiv x t := ⟨x.val / t.val, div_nonneg (le_of_lt x.val_pos) (le_of_lt t.val_pos)⟩


-- @@ L64-65 verbatim
lemma div_eq_val (x y : ChargeUnit) :
    x / y = (⟨x.val / y.val, div_nonneg (le_of_lt x.val_pos) (le_of_lt y.val_pos)⟩ : ℝ≥0) := rfl


-- @@ L67-71 verbatim
@[simp]
lemma div_ne_zero (x y : ChargeUnit) : ¬ x / y = (0 : ℝ≥0) := by
  rw [div_eq_val]
  refine coe_ne_zero.mp ?_
  simp [toReal]


-- @@ L73-77 verbatim
@[simp]
lemma div_pos (x y : ChargeUnit) : (0 : ℝ≥0) < x/ y := by
  apply lt_of_le_of_ne
  · exact zero_le
  · exact Ne.symm (div_ne_zero x y)


-- @@ L79-83 verbatim
@[simp]
lemma div_self (x : ChargeUnit) :
    x / x = (1 : ℝ≥0) := by
  simp [div_eq_val, x.val_ne_zero]
  rfl


-- @@ L85-88 verbatim
lemma div_symm (x y : ChargeUnit) :
    x / y = (y / x)⁻¹ := NNReal.eq <| by
  show x.val / y.val = (y.val / x.val)⁻¹
  rw [inv_div]


-- @@ L90-93 verbatim
/-- The unit-ratio cocycle at `ℝ≥0` (the un-coerced form of `div_mul_div_coe`). -/
lemma div_mul_div (x y z : ChargeUnit) : (x / y) * (y / z) = x / z := NNReal.eq <| by
  show x.val / y.val * (y.val / z.val) = x.val / z.val
  rw [div_mul_div_comm, mul_comm x.val y.val, mul_div_mul_left _ _ y.val_ne_zero]


-- @@ L95-99 verbatim
@[simp]
lemma div_mul_div_coe (x y z : ChargeUnit) :
    (x / y : ℝ) * (y / z : ℝ) = x / z := by
  simp [div_eq_val, toReal]
  field_simp


-- @@ L101-105 verbatim
/-!

## The scaling of a charge unit

-/


-- @@ L107-109 verbatim
/-- The scaling of a charge unit by a positive real. -/
def scale (r : ℝ) (x : ChargeUnit) (hr : 0 < r := by norm_num) : ChargeUnit :=
  ⟨r * x.val, mul_pos hr x.val_pos⟩


-- @@ L111-115 verbatim
@[simp]
lemma scale_div_self (x : ChargeUnit) (r : ℝ) (hr : 0 < r) :
    scale r x hr / x = (⟨r, le_of_lt hr⟩ : ℝ≥0) := by
  simp [scale, div_eq_val]
  rfl


-- @@ L117-121 verbatim
@[simp]
lemma self_div_scale (x : ChargeUnit) (r : ℝ) (hr : 0 < r) :
    x / scale r x hr = (⟨1/r, _root_.div_nonneg (by simp) (le_of_lt hr)⟩ : ℝ≥0) := by
  simp [scale, div_eq_val]
  field_simp


-- @@ L123-125 verbatim
@[simp]
lemma scale_one (x : ChargeUnit) : scale 1 x = x := by
  simp [scale]


-- @@ L127-132 verbatim
@[simp]
lemma scale_div_scale (x1 x2 : ChargeUnit) {r1 r2 : ℝ} (hr1 : 0 < r1) (hr2 : 0 < r2) :
    scale r1 x1 hr1 / scale r2 x2 hr2 = (⟨r1, le_of_lt hr1⟩ / ⟨r2, le_of_lt hr2⟩) * (x1 / x2) := by
  refine NNReal.eq ?_
  show r1 * x1.val / (r2 * x2.val) = r1 / r2 * (x1.val / x2.val)
  rw [div_mul_div_comm]


-- @@ L134-138 verbatim
@[simp]
lemma scale_scale (x : ChargeUnit) (r1 r2 : ℝ) (hr1 : 0 < r1) (hr2 : 0 < r2) :
    scale r1 (scale r2 x hr2) hr1 = scale (r1 * r2) x (mul_pos hr1 hr2) := by
  simp [scale]
  ring


-- @@ L140-149 verbatim
/-!

## Specific choices of charge units

We define specific choices of charge units.
We first define the notion of a columb to correspond to the charge unit with underlying value
equal to `1`. This is really down to a choice in the isomorphism between the set of metrics
on the charge manifold and the positive reals.

-/


-- @@ L151-152 verbatim
/-- The definition of a charge unit of coulomb. -/
def coulombs : ChargeUnit := ⟨1, by norm_num⟩


-- @@ L154-155 verbatim
/-- The charge unit of a elementryCharge (1.602176634×10−19 coulomb). -/
noncomputable def elementaryCharge : ChargeUnit := scale (1.602176634e-19) coulombs


-- @@ L157-157 verbatim
end ChargeUnit
