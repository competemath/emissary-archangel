/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

public import LeanPool.RiemannRochFunctionFields.CoordinateFree.EllipticCurve

public import LeanPool.RiemannRochFunctionFields.EllipticCurve.Instances
import Mathlib.Analysis.SpecialFunctions.Pow.Real


-- @@ L15-34 verbatim
/-!
# Concrete regression for the elliptic-curve development

This file is an end-to-end smoke test: it instantiates the generic elliptic-curve theorems on a
*concrete* Weierstrass curve over a *concrete* algebraically closed field, so that instance
synthesis for the whole hypothesis pack is exercised for real.

* The base field is `k := AlgebraicClosure ℚ` (characteristic zero, `IsAlgClosed`).
* The curve is `y² = x³ - x`, i.e. `curve : WeierstrassCurve.Affine k := ⟨0, 0, 0, -1, 0⟩`,
  whose discriminant is `Δ = 64 ≠ 0`, so it is elliptic.
* The fraction field `K` of `curve.CoordinateRing` is kept **abstract** (exactly as the general
  theorems are stated); a concrete `FractionRing` would reintroduce a `Semiring` instance diamond.

We assemble the full `k[X]` / `k⟮X⟯` algebra tower via the constructors in
`RiemannRoch.EllipticCurve.Instances`, and then check that the public targets
`genus_eq_one`, `picTorsor`, and `picTorsor_compat_groupLaw` elaborate on this concrete input.

All declarations live in the `RiemannRochTest.EllipticCurve` namespace so that the generic names
`k`, `curve`, … do not leak into the root environment.
-/


-- @@ L36-36 verbatim
@[expose] public section


-- @@ L38-38 verbatim
open FunctionField


-- @@ L40-40 verbatim
open scoped Polynomial RatFunc


-- @@ L42-42 verbatim
namespace RiemannRochTest.EllipticCurve


-- @@ L44-44 verbatim
noncomputable section


-- @@ L46-47 verbatim
/-- The concrete algebraically closed base field: the algebraic closure of `ℚ`. -/
abbrev k : Type := AlgebraicClosure ℚ


-- @@ L49-50 verbatim
/-- The concrete Weierstrass curve `y² = x³ - x` over `k = AlgebraicClosure ℚ`. -/
def curve : WeierstrassCurve.Affine k := ⟨0, 0, 0, -1, 0⟩


-- @@ L52-56 verbatim
/-- The discriminant of `curve` is `64`. -/
theorem curve_Δ : curve.Δ = 64 := by
  simp only [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring


-- @@ L58-63 verbatim
/-- `curve` is an elliptic curve: its discriminant `64` is a unit over a field of characteristic
zero. -/
instance : curve.IsElliptic := by
  refine ⟨?_⟩
  rw [curve_Δ]
  exact isUnit_iff_ne_zero.mpr (by norm_num)


-- @@ L65-65 verbatim
open WeierstrassCurve.Affine


-- @@ L67-71 verbatim
/-- The affine point `(0, 0)` is a nonsingular point of `curve`
(here `a₆ = 0` and `a₄ = -1 ≠ 0`). -/
theorem curve_nonsingular : curve.Nonsingular (0 : k) (0 : k) := by
  rw [nonsingular_zero]
  exact ⟨rfl, Or.inr (by norm_num [curve])⟩


-- @@ L73-73 verbatim
section Tower


-- @@ L75-76 verbatim
variable (K : Type*) [Field K] [Algebra curve.CoordinateRing K]
  [IsFractionRing curve.CoordinateRing K]


-- @@ L78-81 verbatim
/-! ## The instance tower on the abstract fraction field `K`

Each `local instance` is a constructor from `RiemannRoch.EllipticCurve.Instances`, introduced in
strict dependency order so that the next one can synthesise the ones already in scope. -/


-- @@ L83-84 verbatim
/-- Item 1: the `k[X]`-algebra structure on `K` (`X ↦ x`). -/
local instance instAlgPoly : Algebra k[X] K := curve.algebraPolynomial K


-- @@ L86-88 verbatim
/-- Item 1: compatibility of the `k[X]`-algebra with the coordinate-ring inclusion. -/
local instance instTowerPoly : IsScalarTower k[X] curve.CoordinateRing K :=
  curve.algebraPolynomial_isScalarTower K


-- @@ L90-91 verbatim
/-- Item 2: the `k⟮X⟯`-algebra structure on `K`. -/
local instance instAlgRat : Algebra k⟮X⟯ K := curve.algebraRatFunc K


-- @@ L93-95 verbatim
/-- Item 2: the `k[X] → k⟮X⟯ → K` scalar tower. -/
local instance instTowerRat : IsScalarTower k[X] k⟮X⟯ K :=
  curve.algebraRatFunc_isScalarTower K


-- @@ L97-98 verbatim
/-- Item 3: `K` is a function field over `k`. -/
local instance instFunctionField : _root_.FunctionField k K := curve.functionField K


-- @@ L100-101 verbatim
/-- Item 4: `K` is separable over `k⟮X⟯`. -/
local instance instSeparable : Algebra.IsSeparable k⟮X⟯ K := curve.isSeparable K


-- @@ L103-104 verbatim
/-- Constant field: the `k`-algebra structure on `K` through `k[X]`. -/
local instance instAlgConst : Algebra k K := FunctionField.algebraConstants k K


-- @@ L106-108 verbatim
/-- Constant field: the `k → k[X] → K` scalar tower. -/
local instance instTowerConst : IsScalarTower k k[X] K :=
  FunctionField.algebraConstants_isScalarTower k K


-- @@ L110-112 verbatim
/-- Item 5: over an algebraically closed base, the constant field is full. -/
local instance instFullConstant : FunctionField.IsFullConstantField k K :=
  FunctionField.isFullConstantField_of_isAlgClosed k K


-- @@ L114-114 verbatim
/-! ## The headline targets, elaborated on the concrete input -/


-- @@ L116-117 verbatim
/-- The genus of the concrete curve is `1`. -/
example : genus k K = 1 := genus_eq_one curve K


-- @@ L119-121 verbatim
/-- The degree-one Picard torsor is the coordinate-ring class group. -/
example : {v : Place k K // v.degree = 1} ≃ ClassGroup curve.CoordinateRing :=
  picTorsor curve K


-- @@ L123-129 verbatim
/-- Group-law compatibility at the nonsingular point `(0, 0)`: the torsor map agrees with
Angdinata's ideal-class construction. -/
example :
    picTorsor curve K ⟨placeOfPoint curve K (.some 0 0 curve_nonsingular),
        placeOfPoint_deg_one curve K (.some 0 0 curve_nonsingular)⟩ =
      ClassGroup.mk curve.FunctionField (CoordinateRing.XYIdeal' curve_nonsingular) :=
  picTorsor_compat_groupLaw curve K curve_nonsingular


-- @@ L131-131 verbatim
end Tower


-- @@ L133-133 verbatim
end


-- @@ L135-135 verbatim
end RiemannRochTest.EllipticCurve


-- @@ L137-137 verbatim
end
