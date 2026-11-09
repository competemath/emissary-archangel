/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, David Kurniadi Angdinata
-/
import LutzNagell.DivisionPolynomial


-- @@ L8-21 verbatim
/-!
# The omega division polynomials and related definitions

This file extends the division polynomial development from mathlib with the `ω` family of
division polynomials, the complement `ψc`, and the invariant `invar`, which are needed for
the `ZSMul` proof.

## Main definitions

 * `WeierstrassCurve.invar`: the "invariant" polynomial.
 * `WeierstrassCurve.ψc`: the complement of `ψ(n)` in `ψ(2n)`.
 * `WeierstrassCurve.ω`: the bivariate polynomials `ωₙ`.
 * `WeierstrassCurve.isEllSequence_ψ`: the `ψ` family forms an elliptic sequence.
-/


-- @@ L23-23 verbatim
open Polynomial

-- @@ L24-24 verbatim
open scoped Polynomial.Bivariate


-- @@ L26-27 verbatim
local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])


-- @@ L29-33 verbatim
local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow, map_div₀,
    Polynomial.map_ofNat, Polynomial.map_one, map_C, map_X, Polynomial.map_neg, Polynomial.map_add,
    Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_div, coe_mapRingHom,
    apply_ite <| mapRingHom _, WeierstrassCurve.map])


-- @@ L35-35 verbatim
namespace WeierstrassCurve


-- @@ L37-37 verbatim
variable {R : Type*} {S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R)


-- @@ L39-39 verbatim
noncomputable section


-- @@ L41-41 verbatim
open Affine (polynomial polynomialX polynomialY negPolynomial)

-- @@ L42-42 verbatim
open EllSequence

-- @@ L43-43 verbatim
open WeierstrassCurve (ψ₂ ψ φ)


-- @@ L45-48 verbatim
/-- The "invariant" that is equal to the quotient
`(ψ(n-1)²ψ(n+2)+ψ(n-2)ψ(n+1)²+ψ₂²ψ(n)³)/ψ(n+1)ψ(n)ψ(n-1)` for arbitrary `n`
modulo the Weierstrass polynomial. -/
def invar : R[X] := 6 * X ^ 2 + C W.b₂ * X + C W.b₄


-- @@ L50-51 verbatim
/-- The complement of ψ(n) in ψ(2n). -/
def ψc : ℤ → R[X][Y] := compl₂EDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄)


-- @@ L53-53 verbatim
lemma isEllSequence_ψ : IsEllSequence W.ψ := IsEllSequence.normEDS


-- @@ L55-58 expanded
lemma C_Ψ₃_eq :
    C W.Ψ₃ =
      (3 * C X + CC W.a₂) * C W.Ψ₂Sq - polynomialX W ^ 2 + CC W.a₁ * W.ψ₂ * polynomialX W -
        CC W.a₁ ^ 2 * polynomial W :=
  by simp_rw [Ψ₃, Ψ₂Sq, polynomial, polynomialX, ψ₂, polynomialY, b₂, b₄, b₆, b₈, CC];
  simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow]; ring


-- @@ L60-62 expanded
lemma preΨ₄_add_Ψ₂Sq_sq : W.preΨ₄ + W.Ψ₂Sq ^ 2 = W.invar * W.Ψ₃ :=
  by
  rw [preΨ₄, Ψ₂Sq, invar, Ψ₃]
  linear_combination (norm :=
    (simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow]; ring_nf))
    congr(C $W.b_relation) * (@X R _) ^ 2


-- @@ L64-67 expanded
lemma preΨ₄_add_ψ₂_pow_four :
    C W.preΨ₄ + W.ψ₂ ^ 4 = C (W.invar * W.Ψ₃) + 8 * polynomial W * (2 * polynomial W + C W.Ψ₂Sq) :=
  by
  simp_rw [show 4 = 2 * 2 by rfl, pow_mul, ψ₂_sq, add_sq, ← add_assoc, ← C_pow, ← C_add,
    preΨ₄_add_Ψ₂Sq_sq];
  simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow]; ring


-- @@ L69-70 verbatim
lemma φ_mul_ψ (n : ℤ) : W.φ n * W.ψ n = C X * W.ψ n ^ 3 - invarDenom W.ψ 1 n := by
  rw [φ, invarDenom]; ring


-- @@ L72-78 verbatim
/-- The `ω` family of division polynomials: `ω n` gives the second (`Y`) coordinate in
Jacobian coordinates of the scalar multiplication by `n`. -/
protected def ω (n : ℤ) : R[X][Y] :=
  redInvarDenom W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n *
    ((CC W.a₁ * polynomialY W - polynomialX W) * C W.Ψ₃
      + 4 * polynomial W * (2 * polynomial W + C W.Ψ₂Sq))
  - compl₂EDSAux W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n + negPolynomial W * W.ψ n ^ 3


-- @@ L80-80 verbatim
open WeierstrassCurve (ω)


-- @@ L82-87 expanded
lemma ω_spec (n : ℤ) : 2 * W.ω n + CC W.a₁ * W.φ n * W.ψ n + CC W.a₃ * W.ψ n ^ 3 = W.ψc n :=
  by
  rw [ψc, compl₂EDS_eq_redInvarNum_sub, redInvar_normEDS, preΨ₄_add_ψ₂_pow_four, mul_assoc (C _),
    φ_mul_ψ, ψ, invarDenom_eq_redInvarDenom_mul, ω, ← ψ, invar, b₂, b₄, ψ₂, polynomialY,
    polynomialX, negPolynomial]
  simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow]; ring


-- @@ L89-91 verbatim
lemma two_mul_ω (n : ℤ) :
    2 * W.ω n = W.ψc n - CC W.a₁ * W.φ n * W.ψ n - CC W.a₃ * W.ψ n ^ 3 := by
  rw [← ω_spec]; abel


-- @@ L93-93 verbatim
lemma ψc_spec (n : ℤ) : W.ψ n * W.ψc n = W.ψ (2 * n) := normEDS_mul_compl₂EDS _ _ _ _


-- @@ L95-95 verbatim
@[simp] lemma ω_zero : W.ω 0 = 1 := by simp [ω]

-- @@ L96-96 verbatim
@[simp] lemma ω_one : W.ω 1 = Y := by simp [ω, ψ₂, ← Affine.Y_sub_polynomialY]

-- @@ L97-97 verbatim
@[simp] lemma ψc_neg (n : ℤ) : W.ψc (-n) = W.ψc n := by simp [ψc]


-- @@ L99-99 verbatim
end


-- @@ L101-101 verbatim
section Map


-- @@ L103-103 verbatim
/-! ### Maps across ring homomorphisms -/


-- @@ L105-105 verbatim
open WeierstrassCurve (Ψ Φ ψ φ ω)


-- @@ L107-107 verbatim
variable (f : R →+* S)


-- @@ L109-114 verbatim
open Affine EllSequence in
@[simp]
lemma map_ω (n : ℤ) : (W.map f).ω n = (W.ω n).map (mapRingHom f) := by
  simp_rw [ω, ← coe_mapRingHom, map_add, map_sub, map_mul, map_redInvarDenom, map_compl₂EDSAux,
    map_polynomial, map_polynomialX, map_polynomialY, map_negPolynomial, map_ψ₂, map_Ψ₃, map_preΨ₄,
    map_Ψ₂Sq, map_ψ]; simp


-- @@ L116-120 verbatim
private lemma universal_ω_neg (n : ℤ) : letI W := Universal.curve
    W.ω (-n) = W.ω n + CC W.a₁ * W.φ n * W.ψ n + CC W.a₃ * W.ψ n ^ 3 := by
  rw [← mul_cancel_left_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero Universal.Poly.two_ne_zero)]
  simp_rw [left_distrib, two_mul_ω, ψc_neg, ψ_neg, φ_neg]; ring


-- @@ L122-123 verbatim
lemma ω_neg (n : ℤ) : W.ω (-n) = W.ω n + CC W.a₁ * W.φ n * W.ψ n + CC W.a₃ * W.ψ n ^ 3 := by
  rw [← W.map_specialize, map_ω, universal_ω_neg, map_φ, map_ω, map_ψ]; simp


-- @@ L125-125 verbatim
end Map


-- @@ L127-127 verbatim
end WeierstrassCurve
