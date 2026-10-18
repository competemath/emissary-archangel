/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.MulByTwoPullback
import EllipticCurves.FunctionField.TranslationEndomorphism
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree


-- @@ L10-61 verbatim
/-!
# The multiplication-by-`2` endomorphism of the function field

Let `W` be a Weierstrass curve over a field `F` of characteristic `≠ 2`, with affine coordinate ring
`F[W] = AdjoinRoot W.polynomial` and function field `F(W) = Frac F[W]`. Building on
`EllipticCurves/FunctionField/MulByTwoPullback.lean` — which constructs the *coordinate-ring half*
`mulByTwoCoordHom : F[W] →+* F(W)` of the multiplication-by-`2` pullback `[2]∗` — this file promotes
it to the full endomorphism of the function field:

* `WeierstrassCurve.Affine.CoordinateRing.mulByTwoEndo h2 : F(W) →+* F(W)`.

The missing ingredient is that `mulByTwoCoordHom` is **injective** (the duplication map `[2]` is
dominant), after which `IsFractionRing.lift` produces the endomorphism. This is the multiplication-
by-`n` analogue (for `n = 2`) of the translation endomorphism `translateEndo`, and a substrate for a
divisor-theoretic Weil pairing.

## The dominance argument

Unlike translation — whose dominance used the inverse morphism `· + (-T)` and the point group law —
the multiplication-by-`2` map has no inverse morphism, so a different (and slightly simpler)
argument is used: the `x`-coordinate image is a *nonconstant rational function* of the generic
`x`-coordinate.

* `transcendental_genX` (from `TranslationEndomorphism`): the generic `x`-coordinate `genX = x(P)`
  is transcendental over `F`.
* `isAlgebraic_genX_of_two`: if the `x`-coordinate `x(2 • P) = Φ₂(genX)/Ψ₂Sq(genX)` of the *doubled*
  generic point is algebraic over `F`, then so is `genX = x(P)`. Indeed `genX` is then a root of the
  polynomial `Φ₂ - x(2 • P) · Ψ₂Sq`, which is nonzero because `Φ₂` has degree `4` while `Ψ₂Sq` has
  degree `≤ 3` (`Mathlib`'s `natDegree_Φ` / `natDegree_Ψ₂Sq_le`), so its degree-`4` coefficient is
  `1`; as its coefficients lie in the relative algebraic closure `K := algebraicClosure F F(W)`,
  `genX` is algebraic over `K` and hence over `F`.
* If `mulByTwoCoordHom h2` were not injective, its kernel would be a nonzero prime of the
  one-dimensional domain `F[W]` (Krull dimension `≤ 1` is `EllipticCurves.Torsion`'s
  `CoordinateRingDedekind`), hence maximal; by Zariski's lemma (`isAlgebraic_of_ker_maximal`) the
  residue field is algebraic over `F`, so the image `x(2 • P)` would be algebraic — forcing `genX`
  algebraic, contradicting `transcendental_genX`.

Note in particular that this argument needs neither `[W.IsElliptic]` nor `[DecidableEq F]` (no group
law, no `slope`), only `(2 : F) ≠ 0`.

## Main definitions and statements

* `WeierstrassCurve.Affine.CoordinateRing.isAlgebraic_genX_of_two`.
* `WeierstrassCurve.Affine.CoordinateRing.mulByTwoCoordHom_injective`.
* `WeierstrassCurve.Affine.CoordinateRing.mulByTwoEndo`: the endomorphism `F(W) →+* F(W)`, with
  `mulByTwoEndo_algebraMap` (its value on `F[W]`) and the generator images `mulByTwoEndo_genX` and
  `mulByTwoEndo_genY`.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.6, III.8.
-/


-- @@ L63-63 verbatim
open Polynomial


-- @@ L65-65 verbatim
namespace WeierstrassCurve.Affine

-- @@ L66-66 verbatim
namespace CoordinateRing


-- @@ L68-68 verbatim
open scoped Polynomial.Bivariate


-- @@ L70-70 verbatim
variable {F : Type*} [Field F] {W : Affine F}


-- @@ L72-73 verbatim
/-- The relative algebraic closure of `F` in the function field `F(W)`. -/
local notation "K" => algebraicClosure F W.FunctionField


-- @@ L75-82 verbatim
/-- `mulByTwoCoordHom` is an `F`-algebra homomorphism: it fixes the image of `F`. -/
lemma mulByTwoCoordHom_algebraMap (h2 : (2 : F) ≠ 0) (c : F) :
    mulByTwoCoordHom h2 (algebraMap F W.CoordinateRing c) = algebraMap F W.FunctionField c := by
  have h1 : (algebraMap F W.CoordinateRing c) = mk W (C (C c)) := by
    rw [IsScalarTower.algebraMap_apply F F[X] W.CoordinateRing, AdjoinRoot.algebraMap_eq,
      ← Polynomial.C_eq_algebraMap]; rfl
  rw [h1, show mk W (C (C c)) = AdjoinRoot.of W.polynomial (C c) from rfl, mulByTwoCoordHom,
    AdjoinRoot.lift_of, coe_eval₂RingHom, eval₂_C]


-- @@ L84-88 verbatim
/-- `mulByTwoCoordHom` packaged as an `F`-algebra homomorphism. -/
noncomputable def mulByTwoAlgHom (h2 : (2 : F) ≠ 0) :
    W.CoordinateRing →ₐ[F] W.FunctionField where
  toRingHom := mulByTwoCoordHom h2
  commutes' := mulByTwoCoordHom_algebraMap h2


-- @@ L90-91 verbatim
@[simp] lemma mulByTwoAlgHom_apply (h2 : (2 : F) ≠ 0) (a : W.CoordinateRing) :
    mulByTwoAlgHom h2 a = mulByTwoCoordHom h2 a := rfl


-- @@ L93-139 verbatim
/-- **Dominance of `[2]`, key step.** If the `x`-coordinate of the doubled generic point
`x(2 • P) = Φ₂(genX)/Ψ₂Sq(genX)` (= `mulByTwoCoordHom h2 (mk W (C X))`) is algebraic over `F`, then
so is the generic `x`-coordinate `genX = x(P)`. -/
lemma isAlgebraic_genX_of_two (h2 : (2 : F) ≠ 0)
    (hu : IsAlgebraic F (mulByTwoCoordHom h2 (mk W (C X)))) :
    IsAlgebraic F (genX W) := by
  rw [mulByTwoCoordHom_X] at hu
  set L := W.FunctionField
  set φ := algebraMap F L with hφ
  -- the denominator does not vanish at the generic point
  have hden : ((W.map φ).Ψ₂Sq).eval (genX W) ≠ 0 := by
    have hsq := ψ_sq_evalEval (W := W.map φ) equation_gen 2
    rw [ΨSq_two] at hsq
    rw [← hsq]
    exact pow_ne_zero 2 (psiTwo_gen_ne h2)
  -- so `x(2 • P) · Ψ₂Sq(genX) = Φ₂(genX)`
  set u := ((W.map φ).Φ 2).eval (genX W) / ((W.map φ).Ψ₂Sq).eval (genX W) with hu_def
  have hrel : u * ((W.map φ).Ψ₂Sq).eval (genX W) = ((W.map φ).Φ 2).eval (genX W) :=
    div_mul_cancel₀ _ hden
  -- `u` lies in the relative algebraic closure `K`
  have hu_mem : u ∈ K := mem_algebraicClosure_iff.mpr hu
  set uK : K := ⟨u, hu_mem⟩ with huK
  -- the candidate annihilating polynomial of `genX`, over `K`
  set q : K[X] := (W.Φ 2).map (algebraMap F K) - C uK * (W.Ψ₂Sq).map (algebraMap F K) with hq
  have hjK : (algebraMap (↥K) L).comp (algebraMap F (↥K)) = φ := by
    rw [hφ, IsScalarTower.algebraMap_eq F (↥K) L]
  have hqmap : q.map (algebraMap (↥K) L) = (W.map φ).Φ 2 - C u * (W.map φ).Ψ₂Sq := by
    rw [hq, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map,
      Polynomial.map_map, hjK, ← map_Φ, ← map_Ψ₂Sq]
    congr 2
  -- `q` is nonzero: its degree-4 coefficient is `1`
  have hqne : q ≠ 0 := by
    intro h0
    have hcoeff : (q.map (algebraMap (↥K) L)).coeff 4 = 1 := by
      rw [hqmap, coeff_sub, coeff_C_mul,
        show (4 : ℕ) = (2 : ℤ).natAbs ^ 2 by decide, (W.map φ).coeff_Φ 2,
        coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (W.map φ).natDegree_Ψ₂Sq_le (by norm_num)),
        mul_zero, sub_zero]
    rw [h0, Polynomial.map_zero, coeff_zero] at hcoeff
    exact zero_ne_one hcoeff
  -- `genX` is a root of `q`
  have hroot : (aeval (genX W)) q = 0 := by
    rw [aeval_def, ← eval_map, hqmap, eval_sub, eval_mul, eval_C]
    rw [hrel, sub_self]
  -- hence `genX` is algebraic over `K`, therefore over `F`
  have halgK : IsAlgebraic (↥K) (genX W) := ⟨q, hqne, hroot⟩
  exact halgK.restrictScalars F


-- @@ L141-159 verbatim
/-- **Multiplication-by-`2` is dominant: `mulByTwoCoordHom h2` is injective.** If it were not, its
kernel would be a nonzero prime — hence maximal, as `F[W]` has Krull dimension `≤ 1` — so the
residue field would be algebraic over `F` (Zariski), forcing the generic `x`-coordinate `x(2 • P)`
to be algebraic and, via `isAlgebraic_genX_of_two`, `genX` itself to be algebraic, contradicting
`transcendental_genX`. -/
lemma mulByTwoCoordHom_injective (h2 : (2 : F) ≠ 0) :
    Function.Injective (mulByTwoCoordHom (W := W) h2) := by
  set g := mulByTwoAlgHom (W := W) h2 with hg
  have key : Function.Injective g := by
    by_contra hni
    have hne : RingHom.ker g ≠ ⊥ := fun h =>
      hni ((RingHom.injective_iff_ker_eq_bot _).mpr h)
    haveI hprime : (RingHom.ker g).IsPrime := RingHom.ker_isPrime _
    have hmax : (RingHom.ker g).IsMaximal := hprime.isMaximal hne
    have hu : IsAlgebraic F (g (mk W (C X))) :=
      isAlgebraic_of_ker_maximal g hmax (mk W (C X))
    rw [hg, mulByTwoAlgHom_apply] at hu
    exact transcendental_genX (isAlgebraic_genX_of_two h2 hu)
  exact key


-- @@ L161-166 verbatim
/-- **The multiplication-by-`2` endomorphism of the function field.** The ring endomorphism
`F(W) →+* F(W)` realising `h ↦ h ∘ [2]`, obtained from the injective coordinate-ring pullback
`mulByTwoCoordHom h2` by the universal property of the fraction field. -/
noncomputable def mulByTwoEndo (h2 : (2 : F) ≠ 0) :
    W.FunctionField →+* W.FunctionField :=
  IsFractionRing.lift (mulByTwoCoordHom_injective (W := W) h2)


-- @@ L168-171 verbatim
/-- On the image of `F[W]`, `mulByTwoEndo` agrees with the coordinate-ring pullback. -/
@[simp] lemma mulByTwoEndo_algebraMap (h2 : (2 : F) ≠ 0) (a : W.CoordinateRing) :
    mulByTwoEndo h2 (algebraMap W.CoordinateRing W.FunctionField a) = mulByTwoCoordHom h2 a :=
  IsFractionRing.lift_algebraMap (mulByTwoCoordHom_injective (W := W) h2) a


-- @@ L173-179 verbatim
/-- The image of the generic `x`-coordinate: the `x`-coordinate of `2 • P`. -/
lemma mulByTwoEndo_genX (h2 : (2 : F) ≠ 0) :
    mulByTwoEndo h2 (genX W) =
      ((W.map (algebraMap F W.FunctionField)).Φ 2).eval (genX W) /
        (W.map (algebraMap F W.FunctionField)).Ψ₂Sq.eval (genX W) := by
  conv_lhs => rw [genX, genPsi]
  rw [mulByTwoEndo_algebraMap, mulByTwoCoordHom_X]


-- @@ L181-192 verbatim
/-- The image of the generic `y`-coordinate: the `y`-coordinate of `2 • P`. -/
lemma mulByTwoEndo_genY (h2 : (2 : F) ≠ 0) :
    mulByTwoEndo h2 (genY W) =
      ((W.map (algebraMap F W.FunctionField)).preΨ₄.eval (genX W) -
          ((W.map (algebraMap F W.FunctionField)).ψ 2).evalEval (genX W) (genY W) *
            ((W.map (algebraMap F W.FunctionField)).a₁ *
                ((W.map (algebraMap F W.FunctionField)).Φ 2).eval (genX W) +
              (W.map (algebraMap F W.FunctionField)).a₃ *
                (W.map (algebraMap F W.FunctionField)).Ψ₂Sq.eval (genX W))) /
        (2 * ((W.map (algebraMap F W.FunctionField)).ψ 2).evalEval (genX W) (genY W) ^ 3) := by
  conv_lhs => rw [genY]
  rw [mulByTwoEndo_algebraMap, mulByTwoCoordHom_root]


-- @@ L194-194 verbatim
end CoordinateRing

-- @@ L195-195 verbatim
end WeierstrassCurve.Affine
