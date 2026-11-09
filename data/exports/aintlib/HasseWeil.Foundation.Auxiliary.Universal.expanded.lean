/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point


-- @@ L8-35 verbatim
/-!
# Additions to Affine.Point and the universal elliptic curve

This file provides lemmas needed for the division polynomial / ZSMul development:
- `algebraMap_poly_injective` and `algebraMap_injective'` (injectivity of `algebraMap` into
  the coordinate ring)
- `some_eq_some_iff` (point equality for nonsingular affine points)

It also defines the universal Weierstrass curve (`Universal.curve`) over the
polynomial ring `ℤ[A₁,A₂,A₃,A₄,A₆]`, and the universal pointed elliptic curve
(`Universal.pointedCurve`) over the field of fractions (`Universal.Field`) of
`Universal.Ring = Universal.Poly/⟨P⟩ = ℤ[A₁,A₂,A₃,A₄,A₆,X,Y]/⟨P⟩` (where `P` is the Weierstrass
polynomial) with distinguished point `(X,Y)`.

Given a Weierstrass curve `W` over a commutative ring `R`, we define the specialization
homomorphism `W.specialize : ℤ[A₁,A₂,A₃,A₄,A₆] →+* R`. If `(x,y)` is a point on the affine plane,
we define `W.polyEval x y : Universal.Poly →+* R`, which factors through
`W.ringEval x y : Universal.Ring →+* R` if `(x,y)` is on `W`.

We also introduce the cusp curve `Y² = X³`, on which lies the rational point `(1,1)`, with
the nice property that `ψₙ(1,1) = n`, making it easy to prove nonvanishing of the universal `ψₙ`
when `n ≠ 0` by specializing to the cusp curve, which shows that `(X,Y)` is a point of infinite
order on the universal pointed elliptic curve.

## References

Ported from the LutzNagell project (`LutzNagell/Universal.lean`).
-/


-- @@ L37-37 verbatim
noncomputable section


-- @@ L39-39 verbatim
/-! ## Point.lean additions -/


-- @@ L41-41 verbatim
namespace WeierstrassCurve.Affine.CoordinateRing


-- @@ L43-43 verbatim
open Polynomial


-- @@ L45-45 verbatim
variable {R : Type*} [CommRing R] {W' : WeierstrassCurve.Affine R}


-- @@ L47-50 verbatim
lemma algebraMap_poly_injective : Function.Injective (algebraMap R[X] W'.CoordinateRing) :=
  (injective_iff_map_eq_zero _).mpr fun p hp ↦ And.left <|
    smul_basis_eq_zero (W' := W') (q := 0) <| by
      rwa [Algebra.smul_def, mul_one, zero_smul, add_zero]


-- @@ L52-53 verbatim
lemma algebraMap_injective' : Function.Injective (algebraMap R W'.CoordinateRing) :=
  (CoordinateRing.algebraMap_poly_injective (W' := W')).comp C_injective


-- @@ L55-55 verbatim
end WeierstrassCurve.Affine.CoordinateRing


-- @@ L57-57 verbatim
namespace WeierstrassCurve.Affine.Point


-- @@ L59-59 verbatim
variable {R : Type*} [CommRing R] {W' : WeierstrassCurve.Affine R}


-- @@ L61-63 verbatim
lemma some_eq_some_iff {x₁ x₂ y₁ y₂ : R} (h₁ : W'.Nonsingular x₁ y₁)
    (h₂ : W'.Nonsingular x₂ y₂) : some x₁ y₁ h₁ = some x₂ y₂ h₂ ↔ x₁ = x₂ ∧ y₁ = y₂ :=
  ⟨by rintro (_ | _); trivial, by rintro ⟨rfl, rfl⟩; rfl⟩


-- @@ L65-65 verbatim
end WeierstrassCurve.Affine.Point


-- @@ L67-67 verbatim
/-! ## The universal elliptic curve -/


-- @@ L69-69 verbatim
namespace WeierstrassCurve


-- @@ L71-73 verbatim
/-- A type whose elements represent the five coefficients `a₁`, `a₂`, `a₃`, `a₄` and `a₆`
of the Weierstrass polynomial. -/
inductive Coeff : Type | A₁ : Coeff | A₂ : Coeff | A₃ : Coeff | A₄ : Coeff | A₆ : Coeff


-- @@ L75-75 verbatim
namespace Universal


-- @@ L77-77 verbatim
open scoped Polynomial Polynomial.Bivariate

-- @@ L78-78 verbatim
open Coeff


-- @@ L80-85 verbatim
open MvPolynomial (X) in
/-- The universal Weierstrass curve over the polynomial ring in five variables
(the **universal polynomial ring** for Weierstrass curves),
corresponding to the five coefficients of the Weierstrass polynomial. -/
def curve : Affine (MvPolynomial Coeff ℤ) :=
  { a₁ := X A₁, a₂ := X A₂, a₃ := X A₃, a₄ := X A₄, a₆ := X A₆ }


-- @@ L87-90 verbatim
lemma Δ_curve_ne_zero : curve.Δ ≠ 0 := fun h ↦ by
  simp_rw [Δ, b₂, b₄, b₆, b₈, curve] at h
  apply_fun MvPolynomial.eval (Coeff.rec 0 0 0 0 1) at h
  simp at h


-- @@ L92-94 verbatim
/-- The polynomial ring over ℤ in the variables `A₁`, `A₂`, `A₃`, `A₄`, `A₆`, `X` and `Y`,
which is the polynomial ring in two variables over the universal polynomial ring. -/
abbrev Poly : Type := (MvPolynomial Coeff ℤ)[X][Y]

-- @@ L95-96 verbatim
/-- The universal ring for **pointed** Weierstrass curves. -/
protected abbrev Ring : Type := curve.CoordinateRing

-- @@ L97-99 verbatim
/-- The universal field for pointed Weierstrass curves is
the field of fractions of the universal ring. -/
protected abbrev Field : Type := FractionRing Universal.Ring


-- @@ L101-103 verbatim
lemma Poly.two_ne_zero : (2 : Poly) ≠ 0 :=
  Polynomial.C_ne_zero.mpr <| Polynomial.C_ne_zero.mpr fun h ↦ two_ne_zero' (α := ℤ) <|
    MvPolynomial.C_injective _ _ <| by rwa [← MvPolynomial.C_0] at h


-- @@ L105-106 verbatim
/-- The obvious ring homomorphism from the polynomial ring in 7 variables to the universal field. -/
def polyToField : Poly →+* Universal.Field := (algebraMap Universal.Ring _).comp <| AdjoinRoot.mk _


-- @@ L108-109 verbatim
lemma polyToField_apply (p : Poly) :
    polyToField p = algebraMap Universal.Ring _ (AdjoinRoot.mk _ p) := rfl


-- @@ L111-112 verbatim
lemma algebraMap_field_eq_comp :
    algebraMap (MvPolynomial Coeff ℤ) Universal.Field = polyToField.comp (algebraMap _ _) := rfl


-- @@ L114-116 verbatim
lemma algebraMap_ring_eq_comp :
    algebraMap (MvPolynomial Coeff ℤ) Universal.Ring = (AdjoinRoot.mk _).comp (algebraMap _ _) :=
  rfl


-- @@ L118-119 verbatim
@[simp] lemma polyToField_polynomial : polyToField curve.polynomial = 0 := by
  rw [polyToField_apply, AdjoinRoot.mk_self, map_zero]


-- @@ L121-124 verbatim
lemma algebraMap_field_injective :
    Function.Injective (algebraMap (MvPolynomial Coeff ℤ) Universal.Field) :=
  (IsFractionRing.injective Universal.Ring Universal.Field).comp
    (Affine.CoordinateRing.algebraMap_injective' (W' := curve))


-- @@ L126-128 verbatim
/-- The universal pointed Weierstrass curve is an elliptic curve
when base-changed to the universal field. -/
abbrev pointedCurve : WeierstrassCurve Universal.Field := baseChange curve Universal.Field


-- @@ L130-133 verbatim
instance : pointedCurve.IsElliptic where
  isUnit := by
    rw [show pointedCurve.Δ = _ from map_Δ curve (algebraMap _ Universal.Field)]
    exact ((map_ne_zero_iff _ algebraMap_field_injective).mpr Δ_curve_ne_zero).isUnit


-- @@ L135-145 verbatim
open Polynomial in
lemma equation_point : pointedCurve.toAffine.Equation (polyToField (C X)) (polyToField Y) := by
  change evalEval (polyToField (C X)) (polyToField Y)
    ((curve.map (algebraMap _ Universal.Field)).toAffine.polynomial) = 0
  have h : (evalEvalRingHom (polyToField (C X)) (polyToField Y)).comp
      (mapRingHom <| mapRingHom (algebraMap _ Universal.Field)) = polyToField := by
    ext <;> simp [polyToField, algebraMap_field_eq_comp]
  have : ∀ p, evalEval (polyToField (C X)) (polyToField Y)
      (p.map (mapRingHom (algebraMap _ Universal.Field))) = polyToField p :=
    fun p ↦ congr($h p)
  rw [Affine.map_polynomial, this, polyToField_polynomial]


-- @@ L147-150 verbatim
open Polynomial Affine in
/-- The distinguished point on the universal pointed Weierstrass curve. -/
def Affine.point : (curve.baseChange Universal.Field).Point :=
  .mk equation_point


-- @@ L152-154 verbatim
/-- The distinguished point on the universal curve in Jacobian coordinates. -/
def Jacobian.point : Jacobian.Point (curve.baseChange Universal.Field) :=
  Jacobian.Point.fromAffine Affine.point


-- @@ L156-156 verbatim
open Polynomial (CC)


-- @@ L158-158 verbatim
@[simp] lemma pointedCurve_a₁ : pointedCurve.a₁ = polyToField (CC curve.a₁) := rfl

-- @@ L159-159 verbatim
@[simp] lemma pointedCurve_a₂ : pointedCurve.a₂ = polyToField (CC curve.a₂) := rfl

-- @@ L160-160 verbatim
@[simp] lemma pointedCurve_a₃ : pointedCurve.a₃ = polyToField (CC curve.a₃) := rfl

-- @@ L161-161 verbatim
@[simp] lemma pointedCurve_a₄ : pointedCurve.a₄ = polyToField (CC curve.a₄) := rfl

-- @@ L162-162 verbatim
@[simp] lemma pointedCurve_a₆ : pointedCurve.a₆ = polyToField (CC curve.a₆) := rfl


-- @@ L164-165 verbatim
/-- The base change of the universal curve from `ℤ[A₁,⋯,A₆]` to `ℤ[A₁,⋯,A₆,X,Y]`. -/
abbrev curvePoly : WeierstrassCurve Poly := curve.baseChange Poly

-- @@ L166-168 verbatim
/-- The base change of the universal curve from `ℤ[A₁,⋯,A₆]` to `ℤ[A₁,⋯,A₆,X,Y]/⟨P⟩`
(the universal ring), where `P` is the Weierstrass polynomial. -/
abbrev curveRing : WeierstrassCurve Universal.Ring := curve.baseChange Universal.Ring

-- @@ L169-171 verbatim
/-- The base change of the universal curve from `ℤ[A₁,⋯,A₆]` to `Frac(ℤ[A₁,⋯,A₆,X,Y]/⟨P⟩)`
(the universal field), where `P` is the Weierstrass polynomial. -/
abbrev curveField : WeierstrassCurve Universal.Field := curve.baseChange Universal.Field


-- @@ L173-173 verbatim
lemma curveField_eq : curveField = pointedCurve := rfl


-- @@ L175-175 verbatim
end Universal


-- @@ L177-178 verbatim
/-- The cusp curve $Y^2 = X^3$ over ℤ. -/
def cusp : Affine ℤ := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 0 }


-- @@ L180-181 verbatim
lemma cusp_equation_one_one : cusp.Equation 1 1 := by
  simp [Affine.Equation, Affine.polynomial, cusp, Polynomial.evalEval]


-- @@ L183-183 verbatim
open Universal

-- @@ L184-184 verbatim
variable {R} [CommRing R] (W : WeierstrassCurve R)


-- @@ L186-189 verbatim
/-- The specialization homomorphism from `ℤ[A₁, ⋯, A₆]`
to the ring of definition of the Weierstrass curve. -/
def specialize : MvPolynomial Coeff ℤ →+* R :=
  (MvPolynomial.aeval <| Coeff.rec W.a₁ W.a₂ W.a₃ W.a₄ W.a₆).toRingHom


-- @@ L191-192 verbatim
/-- Every Weierstrass curve is a specialization of the universal Weierstrass curve. -/
lemma map_specialize : Universal.curve.map W.specialize = W := by simp [specialize, curve, map]


-- @@ L194-194 verbatim
namespace Universal


-- @@ L196-196 verbatim
variable (x y : R)


-- @@ L198-201 verbatim
open Polynomial (eval₂RingHom) in
/-- A point in the affine plane over `R` induces an evaluation homomorphism
from `ℤ[A₁, ⋯, A₆, X, Y]` to `R`. -/
def polyEval : Poly →+* R := eval₂RingHom (eval₂RingHom W.specialize x) y


-- @@ L203-206 verbatim
open Polynomial in
lemma polyEval_apply (p : Poly) :
    polyEval W x y p = (p.map <| mapRingHom W.specialize).evalEval x y :=
  eval₂_eval₂RingHom_apply _ _ _ _


-- @@ L208-208 verbatim
variable {W x y} (eqn : Affine.Equation W x y)


-- @@ L210-216 verbatim
open Polynomial in
/-- A point on a Weierstrass curve over `R` induces a specialization homomorphism
from the universal ring to `R`. -/
def ringEval : Universal.Ring →+* R :=
  AdjoinRoot.lift (eval₂RingHom W.specialize x) y <| by
    simp_rw [← coe_eval₂RingHom, eval₂RingHom_eval₂RingHom, RingHom.comp_apply, coe_mapRingHom]
    rwa [← Affine.map_polynomial, map_specialize]


-- @@ L218-219 verbatim
lemma ringEval_mk (p : Poly) : ringEval eqn (AdjoinRoot.mk _ p) = polyEval W x y p :=
  AdjoinRoot.lift_mk _ p


-- @@ L221-222 verbatim
lemma ringEval_comp_mk : (ringEval eqn).comp (AdjoinRoot.mk _) = polyEval W x y :=
  RingHom.ext (ringEval_mk eqn)


-- @@ L224-225 verbatim
lemma polyEval_comp_eq_specialize : (polyEval W x y).comp (algebraMap _ _) = W.specialize := by
  ext <;> simp [polyEval]


-- @@ L227-228 verbatim
lemma ringEval_comp_eq_specialize : (ringEval eqn).comp (algebraMap _ _) = W.specialize := by
  rw [algebraMap_ring_eq_comp, ← RingHom.comp_assoc, ringEval_comp_mk, polyEval_comp_eq_specialize]


-- @@ L230-233 verbatim
protected lemma Field.two_ne_zero : (2 : Universal.Field) ≠ 0 := by
  rw [← map_ofNat (algebraMap Universal.Ring _), map_ne_zero_iff _ (IsFractionRing.injective _ _)]
  intro h; replace h := congr(ringEval cusp_equation_one_one $h)
  rw [map_ofNat, map_zero] at h; cases h


-- @@ L235-237 verbatim
lemma curveRing_map_ringEval : curveRing.map (ringEval eqn) = W :=
  (map_map curve (algebraMap _ _) (ringEval eqn)).symm ▸
    (ringEval_comp_eq_specialize eqn) ▸ map_specialize W


-- @@ L239-239 verbatim
end Universal


-- @@ L241-241 verbatim
end WeierstrassCurve
