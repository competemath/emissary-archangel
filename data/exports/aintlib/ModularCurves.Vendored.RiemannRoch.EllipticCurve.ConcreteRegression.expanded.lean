/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import ModularCurves.Vendored.RiemannRoch.CoordinateFree.EllipticCurve
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure


-- @@ L11-30 verbatim
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


-- @@ L32-32 verbatim
@[expose] public section


-- @@ L34-34 verbatim
open FunctionField


-- @@ L36-36 verbatim
open scoped Polynomial RatFunc


-- @@ L38-38 verbatim
namespace RiemannRochTest.EllipticCurve


-- @@ L40-40 verbatim
noncomputable section


-- @@ L42-43 verbatim
/-- The concrete algebraically closed base field: the algebraic closure of `ℚ`. -/
abbrev k : Type := AlgebraicClosure ℚ


-- @@ L45-46 verbatim
/-- The concrete Weierstrass curve `y² = x³ - x` over `k = AlgebraicClosure ℚ`. -/
def curve : WeierstrassCurve.Affine k := ⟨0, 0, 0, -1, 0⟩


-- @@ L48-52 verbatim
/-- The discriminant of `curve` is `64`. -/
theorem curve_Δ : curve.Δ = 64 := by
  simp only [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring


-- @@ L54-59 verbatim
/-- `curve` is an elliptic curve: its discriminant `64` is a unit over a field of characteristic
zero. -/
instance : curve.IsElliptic := by
  refine ⟨?_⟩
  rw [curve_Δ]
  exact isUnit_iff_ne_zero.mpr (by norm_num)


-- @@ L61-61 verbatim
open WeierstrassCurve.Affine


-- @@ L63-67 verbatim
/-- The affine point `(0, 0)` is a nonsingular point of `curve`
(here `a₆ = 0` and `a₄ = -1 ≠ 0`). -/
theorem curve_nonsingular : curve.Nonsingular (0 : k) (0 : k) := by
  rw [nonsingular_zero]
  exact ⟨rfl, Or.inr (by norm_num [curve])⟩


-- @@ L69-69 verbatim
section Tower


-- @@ L71-72 verbatim
variable (K : Type*) [Field K] [Algebra curve.CoordinateRing K]
  [IsFractionRing curve.CoordinateRing K]


-- @@ L74-77 verbatim
/-! ## The instance tower on the abstract fraction field `K`

Each `local instance` is a constructor from `RiemannRoch.EllipticCurve.Instances`, introduced in
strict dependency order so that the next one can synthesise the ones already in scope. -/


-- @@ L79-80 verbatim
/-- Item 1: the `k[X]`-algebra structure on `K` (`X ↦ x`). -/
local instance instAlgPoly : Algebra k[X] K := curve.algebraPolynomial K


-- @@ L82-84 verbatim
/-- Item 1: compatibility of the `k[X]`-algebra with the coordinate-ring inclusion. -/
local instance instTowerPoly : IsScalarTower k[X] curve.CoordinateRing K :=
  curve.algebraPolynomial_isScalarTower K


-- @@ L86-87 verbatim
/-- Item 2: the `k⟮X⟯`-algebra structure on `K`. -/
local instance instAlgRat : Algebra k⟮X⟯ K := curve.algebraRatFunc K


-- @@ L89-91 verbatim
/-- Item 2: the `k[X] → k⟮X⟯ → K` scalar tower. -/
local instance instTowerRat : IsScalarTower k[X] k⟮X⟯ K :=
  curve.algebraRatFunc_isScalarTower K


-- @@ L93-94 verbatim
/-- Item 3: `K` is a function field over `k`. -/
local instance instFunctionField : _root_.FunctionField k K := curve.functionField K


-- @@ L96-97 verbatim
/-- Item 4: `K` is separable over `k⟮X⟯`. -/
local instance instSeparable : Algebra.IsSeparable k⟮X⟯ K := curve.isSeparable K


-- @@ L99-100 verbatim
/-- Constant field: the `k`-algebra structure on `K` through `k[X]`. -/
local instance instAlgConst : Algebra k K := FunctionField.algebraConstants k K


-- @@ L102-104 verbatim
/-- Constant field: the `k → k[X] → K` scalar tower. -/
local instance instTowerConst : IsScalarTower k k[X] K :=
  FunctionField.algebraConstants_isScalarTower k K


-- @@ L106-108 verbatim
/-- Item 5: over an algebraically closed base, the constant field is full. -/
local instance instFullConstant : FunctionField.IsFullConstantField k K :=
  FunctionField.isFullConstantField_of_isAlgClosed k K


-- @@ L110-110 verbatim
/-! ## The headline targets, elaborated on the concrete input -/


-- @@ L112-113 verbatim
/-- The genus of the concrete curve is `1`. -/
example : genus k K = 1 := genus_eq_one curve K


-- @@ L115-117 verbatim
/-- The degree-one Picard torsor is the coordinate-ring class group. -/
example : {v : Place k K // v.degree = 1} ≃ ClassGroup curve.CoordinateRing :=
  picTorsor curve K


-- @@ L119-125 verbatim
/-- Group-law compatibility at the nonsingular point `(0, 0)`: the torsor map agrees with
Angdinata's ideal-class construction. -/
example :
    picTorsor curve K ⟨placeOfPoint curve K (.some 0 0 curve_nonsingular),
        placeOfPoint_deg_one curve K (.some 0 0 curve_nonsingular)⟩ =
      ClassGroup.mk curve.FunctionField (CoordinateRing.XYIdeal' curve_nonsingular) :=
  picTorsor_compat_groupLaw curve K curve_nonsingular


-- @@ L127-127 verbatim
end Tower


-- @@ L129-129 verbatim
end


-- @@ L131-131 verbatim
end RiemannRochTest.EllipticCurve


-- @@ L133-133 verbatim
end
