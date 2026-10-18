/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.MulByTwoPullback
import EllipticCurves.FunctionField.TranslationEndomorphism
import EllipticCurves.Torsion.OmegaThree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree


-- @@ L11-77 verbatim
/-!
# The multiplication-by-`3` endomorphism of the function field

Let `W` be a Weierstrass curve over a field `F` of characteristic `≠ 2, 3`, with affine coordinate
ring `F[W] = AdjoinRoot W.polynomial` and function field `F(W) = Frac F[W]`. The tripling map
`P ↦ 3 • P` is a morphism of the curve, and pulling back rational functions along it gives a ring
endomorphism `[3]∗` of `F(W)`. This file is the concrete `n = 3` instance of the
multiplication-by-`n` pullback `[n]∗`, mirroring the merged `n = 2` files `MulByTwoPullback` /
`MulByTwoEndomorphism`; it
delivers both halves:

* `WeierstrassCurve.Affine.CoordinateRing.mulByThreeCoordHom h2 h3 : F[W] →+* F(W)` — the
  coordinate-ring half, sending the generic point `P = (x, y)` to `3 • P`, i.e. realising on the
  coordinate generators the classical division-polynomial tripling coordinates
  `x ↦ Φ₃(x) / ΨSq₃(x)` and `y ↦ ω₃(x, y) / (2 ψ₃(x, y)³)` with
  `ω₃(x, y) = (2y + a₁x + a₃)(preΨ₅(x) − preΨ₄(x)²) − a₁ Φ₃(x) ψ₃(x, y) − a₃ ψ₃(x, y)³`;
* `WeierstrassCurve.Affine.CoordinateRing.mulByThreeEndo h2 h3 : F(W) →+* F(W)` — the full
  endomorphism.

Because the merged `EllipticCurves/Torsion/OmegaThree.lean` supplies the on-curve identity for the
tripling point (`WeierstrassCurve.Affine.tripling_equation`), this construction sidesteps the
general-`n` on-curve identity crux (#404, since closed) entirely: it is a clean clone of the `[2]∗`
construction
with `2 ↦ 3`.

## The construction

The coordinate-ring half is `AdjoinRoot.lift` of the tripling coordinates, whose well-definedness
obligation `W.polynomial.eval₂ _ _ = 0` is exactly that `3 • P` lies on the curve, discharged by
`tripling_equation` over the base-changed curve `W ⁄ F(W)` at the generic point (`equation_gen`),
using the **genericity** `psiThree_gen_ne` — that `ψ₃` does not vanish at the generic point.

## The dominance argument

Exactly as for `[2]∗` (and unlike translation, which used the inverse morphism `· + (-T)`): the
`x`-coordinate image `x(3 • P) = Φ₃(genX)/ΨSq₃(genX)` is a *nonconstant rational function* of the
generic `x`-coordinate. If it were algebraic over `F`, then `genX` is a root of the polynomial
`Φ₃ − x(3 • P) · ΨSq₃`, nonzero because `Φ₃` has degree `9 = 3²` while `ΨSq₃` has degree `≤ 8`
(`Mathlib`'s `coeff_Φ` / `natDegree_ΨSq_le`), so its degree-`9` coefficient is `1`; hence `genX` is
algebraic over `K := algebraicClosure F F(W)` and thus over `F`, contradicting
`transcendental_genX`.
Injectivity of `mulByThreeCoordHom` then follows (nonzero prime kernel → maximal, `F[W]` having
Krull dimension `≤ 1` → Zariski), and `IsFractionRing.lift` produces the endomorphism. This needs
neither `[W.IsElliptic]` nor `[DecidableEq F]`, only `(2 : F) ≠ 0` and `(3 : F) ≠ 0`.

## Main definitions and statements

* `WeierstrassCurve.Affine.CoordinateRing.psiThree_gen_ne`.
* `WeierstrassCurve.Affine.CoordinateRing.tripling_equation_gen`.
* `WeierstrassCurve.Affine.CoordinateRing.mulByThreeCoordHom`, with `mulByThreeCoordHom_X` and
  `mulByThreeCoordHom_root`.
* `WeierstrassCurve.Affine.CoordinateRing.mulByThreeCoordHom_injective`.
* `WeierstrassCurve.Affine.CoordinateRing.mulByThreeEndo`, with `mulByThreeEndo_algebraMap`,
  `mulByThreeEndo_genX`, and `mulByThreeEndo_genY`.

## ⚠️ One `@[simp]` attribute was removed here, and the lemma kept (`#1278`)

`mulByThreeCoordHom_X` carried `@[simp]` and **could never fire**: its LHS is `mk W (C X)`, and
`AdjoinRoot.mk_C` — itself `@[simp]` — rewrites that to `AdjoinRoot.of W.polynomial X` before the
pattern is tried. Measured with Mathlib's `simpNF` environment linter, which had never been run on
this tree. The lemma is unchanged and has thirteen named consumers across three other files; only
the attribute went.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.6, III.8.
-/


-- @@ L79-79 verbatim
open Polynomial

-- @@ L80-80 verbatim
open scoped Polynomial.Bivariate


-- @@ L82-82 verbatim
namespace WeierstrassCurve.Affine

-- @@ L83-83 verbatim
namespace CoordinateRing


-- @@ L85-85 verbatim
variable {F : Type*} [Field F] {W : Affine F}


-- @@ L87-88 verbatim
/-- The relative algebraic closure of `F` in the function field `F(W)`. -/
local notation "K" => algebraicClosure F W.FunctionField


-- @@ L90-106 verbatim
/-- **Genericity of `ψ₃`.** Over a field of characteristic `≠ 3`, the `3`-division polynomial `ψ₃`
does not vanish at the generic point `(genX, genY)` of the base-changed curve `W ⁄ F(W)`; i.e. the
generic point is not `3`-torsion. -/
lemma psiThree_gen_ne (h3 : (3 : F) ≠ 0) :
    ((W.map (algebraMap F W.FunctionField)).ψ 3).evalEval (genX W) (genY W) ≠ 0 := by
  rw [map_ψ, ← genPsi_mk_map_evalEval]
  intro hz
  have hmk : mk W (W.ψ 3) = 0 :=
    (injective_iff_map_eq_zero _).mp
      (IsFractionRing.injective W.CoordinateRing W.FunctionField) _ hz
  have h0 : W.ψ 3 ≠ 0 := by
    rw [ψ_three]
    exact C_ne_zero.mpr fun hΨ => W.coeff_Ψ₃_ne_zero h3 (by rw [hΨ, coeff_zero])
  have hdeg : (W.ψ 3).natDegree < W.polynomial.natDegree := by
    rw [natDegree_polynomial, ψ_three, natDegree_C]
    norm_num
  exact AdjoinRoot.mk_ne_zero_of_natDegree_lt monic_polynomial h0 hdeg hmk


-- @@ L108-112 verbatim
/-- The scalar `2` is nonzero in the function field when it is nonzero in the base field. -/
private lemma two_ne_zero_functionField (h2 : (2 : F) ≠ 0) : (2 : W.FunctionField) ≠ 0 := by
  have hinj := (algebraMap F W.FunctionField).injective
  intro h
  exact h2 (hinj (by rw [map_ofNat, map_zero]; exact h))


-- @@ L114-133 verbatim
/-- **The tripled generic point lies on the curve.** Applying the division-polynomial tripling
identity `tripling_equation` over the base-changed curve `W ⁄ F(W)` to the generic point
`(genX, genY)` (which lies on the curve by `equation_gen` and is not `3`-torsion by
`psiThree_gen_ne`), the classical tripling coordinates satisfy the Weierstrass equation. This is the
element-level `F(W)`-identity consumed by the multiplication-by-`3` pullback. -/
theorem tripling_equation_gen (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    (W.map (algebraMap F W.FunctionField)).Equation
      (((W.map (algebraMap F W.FunctionField)).Φ 3).eval (genX W) /
        ((W.map (algebraMap F W.FunctionField)).ΨSq 3).eval (genX W))
      (((2 * genY W + (W.map (algebraMap F W.FunctionField)).a₁ * genX W +
              (W.map (algebraMap F W.FunctionField)).a₃) *
            (((W.map (algebraMap F W.FunctionField)).preΨ 5).eval (genX W) -
              (W.map (algebraMap F W.FunctionField)).preΨ₄.eval (genX W) ^ 2) -
          (W.map (algebraMap F W.FunctionField)).a₁ *
              ((W.map (algebraMap F W.FunctionField)).Φ 3).eval (genX W) *
              ((W.map (algebraMap F W.FunctionField)).ψ 3).evalEval (genX W) (genY W) -
          (W.map (algebraMap F W.FunctionField)).a₃ *
              ((W.map (algebraMap F W.FunctionField)).ψ 3).evalEval (genX W) (genY W) ^ 3) /
        (2 * ((W.map (algebraMap F W.FunctionField)).ψ 3).evalEval (genX W) (genY W) ^ 3)) :=
  tripling_equation equation_gen (two_ne_zero_functionField h2) (psiThree_gen_ne h3)


-- @@ L135-158 verbatim
/-- **The multiplication-by-`3` pullback (coordinate-ring half).** The ring homomorphism
`F[W] →+* F(W)` sending the generic point `P = (x, y)` to the tripled point `3 • P`. It is
`AdjoinRoot.lift` of the division-polynomial tripling coordinates, whose well-definedness obligation
`W.polynomial.eval₂ _ _ = 0` is exactly that `3 • P` lies on the curve, discharged by
`tripling_equation_gen`. -/
noncomputable def mulByThreeCoordHom (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    W.CoordinateRing →+* W.FunctionField :=
  AdjoinRoot.lift
    (eval₂RingHom (algebraMap F W.FunctionField)
      (((W.map (algebraMap F W.FunctionField)).Φ 3).eval (genX W) /
        ((W.map (algebraMap F W.FunctionField)).ΨSq 3).eval (genX W)))
    (((2 * genY W + (W.map (algebraMap F W.FunctionField)).a₁ * genX W +
            (W.map (algebraMap F W.FunctionField)).a₃) *
          (((W.map (algebraMap F W.FunctionField)).preΨ 5).eval (genX W) -
            (W.map (algebraMap F W.FunctionField)).preΨ₄.eval (genX W) ^ 2) -
        (W.map (algebraMap F W.FunctionField)).a₁ *
            ((W.map (algebraMap F W.FunctionField)).Φ 3).eval (genX W) *
            ((W.map (algebraMap F W.FunctionField)).ψ 3).evalEval (genX W) (genY W) -
        (W.map (algebraMap F W.FunctionField)).a₃ *
            ((W.map (algebraMap F W.FunctionField)).ψ 3).evalEval (genX W) (genY W) ^ 3) /
      (2 * ((W.map (algebraMap F W.FunctionField)).ψ 3).evalEval (genX W) (genY W) ^ 3))
    (by
      rw [eval₂_eval₂RingHom_apply, ← map_polynomial]
      exact tripling_equation_gen h2 h3)


-- @@ L160-168 verbatim
/-- Image of the `x`-generator under the multiplication-by-`3` pullback: the `x`-coordinate of
`3 • P`. -/
lemma mulByThreeCoordHom_X (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    mulByThreeCoordHom h2 h3 (mk W (C X)) =
      ((W.map (algebraMap F W.FunctionField)).Φ 3).eval (genX W) /
        ((W.map (algebraMap F W.FunctionField)).ΨSq 3).eval (genX W) := by
  rw [mulByThreeCoordHom,
    show mk W (C X) = AdjoinRoot.of W.polynomial X from rfl,
    AdjoinRoot.lift_of, coe_eval₂RingHom, eval₂_X]


-- @@ L170-184 verbatim
/-- Image of the `y`-generator (the root) under the multiplication-by-`3` pullback: the
`y`-coordinate of `3 • P`. -/
@[simp] lemma mulByThreeCoordHom_root (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    mulByThreeCoordHom h2 h3 (AdjoinRoot.root W.polynomial) =
      (((2 * genY W + (W.map (algebraMap F W.FunctionField)).a₁ * genX W +
              (W.map (algebraMap F W.FunctionField)).a₃) *
            (((W.map (algebraMap F W.FunctionField)).preΨ 5).eval (genX W) -
              (W.map (algebraMap F W.FunctionField)).preΨ₄.eval (genX W) ^ 2) -
          (W.map (algebraMap F W.FunctionField)).a₁ *
              ((W.map (algebraMap F W.FunctionField)).Φ 3).eval (genX W) *
              ((W.map (algebraMap F W.FunctionField)).ψ 3).evalEval (genX W) (genY W) -
          (W.map (algebraMap F W.FunctionField)).a₃ *
              ((W.map (algebraMap F W.FunctionField)).ψ 3).evalEval (genX W) (genY W) ^ 3) /
        (2 * ((W.map (algebraMap F W.FunctionField)).ψ 3).evalEval (genX W) (genY W) ^ 3)) := by
  rw [mulByThreeCoordHom, AdjoinRoot.lift_root]


-- @@ L186-194 verbatim
/-- `mulByThreeCoordHom` fixes the image of `F`. -/
lemma mulByThreeCoordHom_algebraMap (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (c : F) :
    mulByThreeCoordHom h2 h3 (algebraMap F W.CoordinateRing c) =
      algebraMap F W.FunctionField c := by
  have h1 : (algebraMap F W.CoordinateRing c) = mk W (C (C c)) := by
    rw [IsScalarTower.algebraMap_apply F F[X] W.CoordinateRing, AdjoinRoot.algebraMap_eq,
      ← Polynomial.C_eq_algebraMap]; rfl
  rw [h1, show mk W (C (C c)) = AdjoinRoot.of W.polynomial (C c) from rfl, mulByThreeCoordHom,
    AdjoinRoot.lift_of, coe_eval₂RingHom, eval₂_C]


-- @@ L196-200 verbatim
/-- `mulByThreeCoordHom` packaged as an `F`-algebra homomorphism. -/
noncomputable def mulByThreeAlgHom (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    W.CoordinateRing →ₐ[F] W.FunctionField where
  toRingHom := mulByThreeCoordHom h2 h3
  commutes' := mulByThreeCoordHom_algebraMap h2 h3


-- @@ L202-203 verbatim
@[simp] lemma mulByThreeAlgHom_apply (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (a : W.CoordinateRing) :
    mulByThreeAlgHom h2 h3 a = mulByThreeCoordHom h2 h3 a := rfl


-- @@ L205-250 verbatim
/-- **Dominance of `[3]`, key step.** If the `x`-coordinate of the tripled generic point
`x(3 • P) = Φ₃(genX)/ΨSq₃(genX)` (= `mulByThreeCoordHom h2 h3 (mk W (C X))`) is algebraic over `F`,
then so is the generic `x`-coordinate `genX = x(P)`. -/
lemma isAlgebraic_genX_of_three (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hu : IsAlgebraic F (mulByThreeCoordHom h2 h3 (mk W (C X)))) :
    IsAlgebraic F (genX W) := by
  rw [mulByThreeCoordHom_X] at hu
  set L := W.FunctionField
  set φ := algebraMap F L with hφ
  -- the denominator does not vanish at the generic point
  have hden : ((W.map φ).ΨSq 3).eval (genX W) ≠ 0 := by
    have hsq := ψ_sq_evalEval (W := W.map φ) equation_gen 3
    rw [← hsq]
    exact pow_ne_zero 2 (psiThree_gen_ne h3)
  -- so `x(3 • P) · ΨSq₃(genX) = Φ₃(genX)`
  set u := ((W.map φ).Φ 3).eval (genX W) / ((W.map φ).ΨSq 3).eval (genX W) with hu_def
  have hrel : u * ((W.map φ).ΨSq 3).eval (genX W) = ((W.map φ).Φ 3).eval (genX W) :=
    div_mul_cancel₀ _ hden
  -- `u` lies in the relative algebraic closure `K`
  have hu_mem : u ∈ K := mem_algebraicClosure_iff.mpr hu
  set uK : K := ⟨u, hu_mem⟩ with huK
  -- the candidate annihilating polynomial of `genX`, over `K`
  set q : K[X] := (W.Φ 3).map (algebraMap F K) - C uK * (W.ΨSq 3).map (algebraMap F K) with hq
  have hjK : (algebraMap (↥K) L).comp (algebraMap F (↥K)) = φ := by
    rw [hφ, IsScalarTower.algebraMap_eq F (↥K) L]
  have hqmap : q.map (algebraMap (↥K) L) = (W.map φ).Φ 3 - C u * (W.map φ).ΨSq 3 := by
    rw [hq, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map,
      Polynomial.map_map, hjK, ← map_Φ, ← map_ΨSq]
    congr 2
  -- `q` is nonzero: its degree-9 coefficient is `1`
  have hqne : q ≠ 0 := by
    intro h0
    have hcoeff : (q.map (algebraMap (↥K) L)).coeff 9 = 1 := by
      rw [hqmap, coeff_sub, coeff_C_mul,
        show (9 : ℕ) = (3 : ℤ).natAbs ^ 2 by decide, (W.map φ).coeff_Φ 3,
        coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt ((W.map φ).natDegree_ΨSq_le 3) (by decide)),
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


-- @@ L252-269 verbatim
/-- **Multiplication-by-`3` is dominant: `mulByThreeCoordHom h2 h3` is injective.** If it were not,
its kernel would be a nonzero prime — hence maximal, as `F[W]` has Krull dimension `≤ 1` — so the
residue field would be algebraic over `F` (Zariski), forcing `x(3 • P)` to be algebraic and, via
`isAlgebraic_genX_of_three`, `genX` itself to be algebraic, contradicting `transcendental_genX`. -/
lemma mulByThreeCoordHom_injective (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Function.Injective (mulByThreeCoordHom (W := W) h2 h3) := by
  set g := mulByThreeAlgHom (W := W) h2 h3 with hg
  have key : Function.Injective g := by
    by_contra hni
    have hne : RingHom.ker g ≠ ⊥ := fun h =>
      hni ((RingHom.injective_iff_ker_eq_bot _).mpr h)
    haveI hprime : (RingHom.ker g).IsPrime := RingHom.ker_isPrime _
    have hmax : (RingHom.ker g).IsMaximal := hprime.isMaximal hne
    have hu : IsAlgebraic F (g (mk W (C X))) :=
      isAlgebraic_of_ker_maximal g hmax (mk W (C X))
    rw [hg, mulByThreeAlgHom_apply] at hu
    exact transcendental_genX (isAlgebraic_genX_of_three h2 h3 hu)
  exact key


-- @@ L271-276 verbatim
/-- **The multiplication-by-`3` endomorphism of the function field.** The ring endomorphism
`F(W) →+* F(W)` realising `h ↦ h ∘ [3]`, obtained from the injective coordinate-ring pullback
`mulByThreeCoordHom h2 h3` by the universal property of the fraction field. -/
noncomputable def mulByThreeEndo (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    W.FunctionField →+* W.FunctionField :=
  IsFractionRing.lift (mulByThreeCoordHom_injective (W := W) h2 h3)


-- @@ L278-283 verbatim
/-- On the image of `F[W]`, `mulByThreeEndo` agrees with the coordinate-ring pullback. -/
@[simp] lemma mulByThreeEndo_algebraMap (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (a : W.CoordinateRing) :
    mulByThreeEndo h2 h3 (algebraMap W.CoordinateRing W.FunctionField a) =
      mulByThreeCoordHom h2 h3 a :=
  IsFractionRing.lift_algebraMap (mulByThreeCoordHom_injective (W := W) h2 h3) a


-- @@ L285-291 verbatim
/-- The image of the generic `x`-coordinate: the `x`-coordinate of `3 • P`. -/
lemma mulByThreeEndo_genX (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    mulByThreeEndo h2 h3 (genX W) =
      ((W.map (algebraMap F W.FunctionField)).Φ 3).eval (genX W) /
        ((W.map (algebraMap F W.FunctionField)).ΨSq 3).eval (genX W) := by
  conv_lhs => rw [genX, genPsi]
  rw [mulByThreeEndo_algebraMap, mulByThreeCoordHom_X]


-- @@ L293-307 verbatim
/-- The image of the generic `y`-coordinate: the `y`-coordinate of `3 • P`. -/
lemma mulByThreeEndo_genY (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    mulByThreeEndo h2 h3 (genY W) =
      (((2 * genY W + (W.map (algebraMap F W.FunctionField)).a₁ * genX W +
              (W.map (algebraMap F W.FunctionField)).a₃) *
            (((W.map (algebraMap F W.FunctionField)).preΨ 5).eval (genX W) -
              (W.map (algebraMap F W.FunctionField)).preΨ₄.eval (genX W) ^ 2) -
          (W.map (algebraMap F W.FunctionField)).a₁ *
              ((W.map (algebraMap F W.FunctionField)).Φ 3).eval (genX W) *
              ((W.map (algebraMap F W.FunctionField)).ψ 3).evalEval (genX W) (genY W) -
          (W.map (algebraMap F W.FunctionField)).a₃ *
              ((W.map (algebraMap F W.FunctionField)).ψ 3).evalEval (genX W) (genY W) ^ 3) /
        (2 * ((W.map (algebraMap F W.FunctionField)).ψ 3).evalEval (genX W) (genY W) ^ 3)) := by
  conv_lhs => rw [genY]
  rw [mulByThreeEndo_algebraMap, mulByThreeCoordHom_root]


-- @@ L309-309 verbatim
end CoordinateRing

-- @@ L310-310 verbatim
end WeierstrassCurve.Affine
