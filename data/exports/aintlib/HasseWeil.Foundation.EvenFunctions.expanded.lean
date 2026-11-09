/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point


-- @@ L8-30 verbatim
/-!
# Even functions on Weierstrass curves

This file proves that a function in the coordinate ring of a Weierstrass curve is fixed by the
negation involution if and only if it lies in the image of `R[X]` (i.e., it depends only on `x`,
not on `y`). This is the algebraic content of Silverman III.2.3.1.

## Main definitions

* `WeierstrassCurve.Affine.negInvolution`: the negation involution on the coordinate ring,
  defined via `AdjoinRoot.lift` sending `Y` to `negPolynomial`.

## Main results

* `WeierstrassCurve.Affine.eval₂_polynomial_negPolynomial`: the polynomial identity
  `W.polynomial.eval₂ C W.negPolynomial = W.polynomial`.
* `WeierstrassCurve.Affine.negInvolution_involutive`: the negation involution is involutive.
* `WeierstrassCurve.Affine.negInvolution_eq_iff`: characterization of fixed points.

## References

* [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.2.3.1
-/


-- @@ L32-32 verbatim
open Polynomial


-- @@ L34-34 verbatim
open scoped Polynomial.Bivariate


-- @@ L36-36 verbatim
namespace WeierstrassCurve.Affine


-- @@ L38-38 verbatim
variable {R : Type*} [CommRing R] (W : WeierstrassCurve.Affine R)


-- @@ L40-40 verbatim
section NegInvolution


-- @@ L42-48 verbatim
/-- The polynomial identity: evaluating `W.polynomial` at `W.negPolynomial` via `eval₂` gives
`W.polynomial` back. This is the key identity ensuring the negation involution is well-defined. -/
lemma eval₂_polynomial_negPolynomial :
    W.polynomial.eval₂ (C : R[X] →+* R[X][Y]) W.negPolynomial = W.polynomial := by
  simp only [polynomial, negPolynomial, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X,
    eval₂_C]
  ring


-- @@ L50-56 verbatim
private lemma negInvolution_aux :
    W.polynomial.eval₂ (AdjoinRoot.of W.polynomial)
      (AdjoinRoot.mk W.polynomial W.negPolynomial) = 0 := by
  rw [show AdjoinRoot.of W.polynomial =
    (AdjoinRoot.mk W.polynomial).comp (C : R[X] →+* R[X][Y]) from rfl,
    ← hom_eval₂ W.polynomial C (AdjoinRoot.mk W.polynomial) W.negPolynomial,
    eval₂_polynomial_negPolynomial, AdjoinRoot.mk_self]


-- @@ L58-62 verbatim
/-- The negation involution on the coordinate ring, sending the class of `Y` to the class of
`negPolynomial`. -/
noncomputable def negInvolution : W.CoordinateRing →+* W.CoordinateRing :=
  AdjoinRoot.lift (AdjoinRoot.of W.polynomial)
    (AdjoinRoot.mk W.polynomial W.negPolynomial) (negInvolution_aux W)


-- @@ L64-68 verbatim
@[simp]
lemma negInvolution_root :
    W.negInvolution (AdjoinRoot.root W.polynomial) =
      AdjoinRoot.mk W.polynomial W.negPolynomial :=
  AdjoinRoot.lift_root (negInvolution_aux W)


-- @@ L70-74 verbatim
@[simp]
lemma negInvolution_of (p : R[X]) :
    W.negInvolution (AdjoinRoot.of W.polynomial p) =
      AdjoinRoot.of W.polynomial p :=
  AdjoinRoot.lift_of (negInvolution_aux W)


-- @@ L76-80 verbatim
@[simp]
lemma negInvolution_mk_C (p : R[X]) :
    W.negInvolution (AdjoinRoot.mk W.polynomial (C p)) =
      AdjoinRoot.mk W.polynomial (C p) :=
  negInvolution_of W p


-- @@ L82-88 verbatim
/-- The negation involution applied to `mk Y` gives `mk negPolynomial`. -/
@[simp]
lemma negInvolution_mk_Y :
    W.negInvolution (CoordinateRing.mk W Y) =
      CoordinateRing.mk W W.negPolynomial := by
  change W.negInvolution (AdjoinRoot.root W.polynomial) = _
  rw [negInvolution_root]


-- @@ L90-100 verbatim
/-- Applying negInvolution to `mk negPolynomial` gives `mk Y` (= root). -/
lemma negInvolution_mk_negPolynomial :
    W.negInvolution (AdjoinRoot.mk W.polynomial W.negPolynomial) =
      AdjoinRoot.root W.polynomial := by
  have hmk : AdjoinRoot.mk W.polynomial W.negPolynomial =
    -AdjoinRoot.root W.polynomial -
      AdjoinRoot.of W.polynomial (C W.a₁ * X + C W.a₃) := by
    simp only [negPolynomial, map_sub, map_neg, map_add, map_mul, AdjoinRoot.mk_X]
    rfl
  rw [hmk, map_sub, map_neg, negInvolution_root, negInvolution_of, hmk]
  ring


-- @@ L102-112 verbatim
/-- The negation involution is involutive: applying it twice is the identity. -/
lemma negInvolution_involutive : Function.Involutive W.negInvolution := by
  intro x
  have h : W.negInvolution.comp W.negInvolution = RingHom.id _ := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro p
      simp only [RingHom.comp_apply, negInvolution_of, RingHomCompTriple.comp_eq]
    · simp only [RingHom.comp_apply, negInvolution_root, negInvolution_mk_negPolynomial,
        RingHom.id_apply]
  exact RingHom.congr_fun h x


-- @@ L114-117 verbatim
/-- The negation involution applied to a scalar-multiplied element. -/
lemma negInvolution_smul (p : R[X]) (f : W.CoordinateRing) :
    W.negInvolution (p • f) = p • W.negInvolution f := by
  rw [CoordinateRing.smul, map_mul, negInvolution_mk_C, ← CoordinateRing.smul]


-- @@ L119-119 verbatim
end NegInvolution


-- @@ L121-121 verbatim
section FixedPoints


-- @@ L123-123 verbatim
variable {F : Type*} [Field F] {W : WeierstrassCurve.Affine F}


-- @@ L125-142 verbatim
/-- If `p₁ • 1 + q₁ • Y = p₂ • 1 + q₂ • Y` in the coordinate ring, then `p₁ = p₂` and
`q₁ = q₂` (linear independence of the basis `{1, Y}`). -/
private lemma smul_basis_eq_of_eq {p₁ q₁ p₂ q₂ : F[X]}
    (h : p₁ • (1 : W.CoordinateRing) + q₁ • CoordinateRing.mk W (Y : F[X][Y]) =
         p₂ • (1 : W.CoordinateRing) + q₂ • CoordinateRing.mk W (Y : F[X][Y])) :
    p₁ = p₂ ∧ q₁ = q₂ := by
  have key : (p₁ - p₂) • (1 : W.CoordinateRing) +
      (q₁ - q₂) • CoordinateRing.mk W (Y : F[X][Y]) = 0 := by
    have h' := sub_eq_zero.mpr h
    rw [show p₁ • (1 : W.CoordinateRing) + q₁ • CoordinateRing.mk W (Y : F[X][Y]) -
      (p₂ • (1 : W.CoordinateRing) + q₂ • CoordinateRing.mk W (Y : F[X][Y])) =
      (p₁ - p₂) • (1 : W.CoordinateRing) +
        (q₁ - q₂) • CoordinateRing.mk W (Y : F[X][Y]) from by
        simp only [CoordinateRing.smul, map_sub, sub_mul]
        ring] at h'
    exact h'
  exact ⟨sub_eq_zero.mp (CoordinateRing.smul_basis_eq_zero key).1,
         sub_eq_zero.mp (CoordinateRing.smul_basis_eq_zero key).2⟩


-- @@ L144-144 verbatim
open CoordinateRing


-- @@ L146-153 verbatim
/-- The negation involution applied to `p • 1 + q • Y` in the coordinate ring. -/
lemma negInvolution_smul_basis (p q : F[X]) :
    W.negInvolution (p • (1 : W.CoordinateRing) + q • CoordinateRing.mk W (Y : F[X][Y])) =
      (p - q * (C W.a₁ * X + C W.a₃)) • (1 : W.CoordinateRing) +
        (-q) • CoordinateRing.mk W (Y : F[X][Y]) := by
  rw [map_add, negInvolution_smul, negInvolution_smul, map_one, negInvolution_mk_Y]
  simp only [CoordinateRing.smul, mul_one, negPolynomial, map_sub, map_neg, map_add, map_mul]
  ring


-- @@ L155-175 verbatim
/-- In a field of characteristic not 2, the negation involution fixes `f` iff `f` lies in the
image of `F[X]` (i.e., `f` only depends on `x`, not `y`). -/
lemma negInvolution_eq_iff [NeZero (2 : F)] (f : W.CoordinateRing) :
    W.negInvolution f = f ↔ ∃ p : F[X], f = p • (1 : W.CoordinateRing) := by
  constructor
  · intro h
    obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq f
    rw [negInvolution_smul_basis] at h
    have hq : q = 0 := by
      have hcomp := (smul_basis_eq_of_eq h).2
      have h2q : q + q = 0 := by linear_combination -hcomp
      ext n
      have h2coeff : q.coeff n + q.coeff n = 0 := by
        have := congr_arg (fun p ↦ p.coeff n) h2q
        simpa [Polynomial.coeff_add] using this
      have : 2 * q.coeff n = 0 := by linear_combination h2coeff
      exact (mul_eq_zero.mp this).resolve_left (NeZero.ne 2)
    refine ⟨p, ?_⟩
    simp only [hq, CoordinateRing.smul, map_zero, zero_mul, add_zero]
  · rintro ⟨p, rfl⟩
    rw [negInvolution_smul, map_one]


-- @@ L177-177 verbatim
end FixedPoints


-- @@ L179-179 verbatim
end WeierstrassCurve.Affine
