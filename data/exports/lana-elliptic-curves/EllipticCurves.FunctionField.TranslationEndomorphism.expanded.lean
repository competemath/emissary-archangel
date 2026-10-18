/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import EllipticCurves.FunctionField.TranslationPullback
import EllipticCurves.Torsion.CoordinateRingDedekind
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.RingTheory.Jacobson.Ring


-- @@ L11-64 verbatim
/-!
# The translation-by-a-point endomorphism of the function field

Let `W` be an elliptic curve over a field `F`, with affine coordinate ring
`F[W] = AdjoinRoot W.polynomial` and function field `F(W) = Frac F[W]`. Building on
`EllipticCurves/FunctionField/TranslationPullback.lean` — which constructs the *coordinate-ring
half* `translateCoordHom : F[W] →+* F(W)` of the translation-by-`T` pullback — this file promotes it
to the full endomorphism of the function field:

* `WeierstrassCurve.Affine.CoordinateRing.translateEndo h₂ : F(W) →+* F(W)`.

The missing ingredient is that `translateCoordHom` is **injective** (translation is a dominant map),
after which `IsFractionRing.lift` produces the endomorphism. Injectivity is the *dominance* of
translation, proved here as follows.

## The dominance argument

* `transcendental_genX`: the generic `x`-coordinate `genX = x(P)` is transcendental over `F`
  (it is the image of the polynomial variable `X` under the injective map `F[X] → F(W)`).
* `genX_mem_algebraicClosure_of`: if the coordinates `x(P + T)`, `y(P + T)` of the *translated*
  generic point are algebraic over `F`, then so is `genX = x(P)`. This is the group-law cancellation
  `(P + T) + (-T) = P`, evaluated at the generic point `P = (genX, genY)` of `W ⁄ F(W)`, together
  with the fact that the affine addition/slope/negation formulae preserve the relative algebraic
  closure `algebraicClosure F F(W)`.
  ⚠️ **This bullet named a lemma that is not in this file, from the first commit until `#1049`,
  and a mechanical rename then made the wrong name *resolve*.**  As written on 2026-08-09 it said
  `isAlgebraic_genX_of`, while the lemma it describes has always been
  `genX_mem_algebraicClosure_of`, and no declaration of that name existed anywhere — the reference
  simply dangled.  One hour later `EllipticCurves.FunctionField.MulByTwoEndomorphism` was created
  and declared `isAlgebraic_genX_of` for the *doubling* statement
  (`x(2 • P) = Φ₂(genX)/Ψ₂Sq(genX)` algebraic ⇒ `genX` algebraic), a different hypothesis reached
  by a different argument — that file's own dominance section opens by saying so — and the
  dangling reference silently became a reference to the wrong lemma.  The `_two` rename sweep
  (`#360`) then rewrote the token here as though it were an occurrence of the declaration it had
  renamed, which it was not.
* If `translateCoordHom h₂` were not injective, its kernel would be a nonzero prime of the
  one-dimensional domain `F[W]` (Krull dimension `≤ 1` is `EllipticCurves.Torsion`'s
  `CoordinateRingDedekind`), hence maximal; by Zariski's lemma
  (`finite_of_finite_type_of_isJacobsonRing`) the residue field is algebraic over `F`, so the
  images `x(P + T)`, `y(P + T)` would be algebraic — forcing `genX` algebraic, contradicting
  `transcendental_genX`.

## Main definitions and statements

* `WeierstrassCurve.Affine.CoordinateRing.transcendental_genX`.
* `WeierstrassCurve.Affine.CoordinateRing.translateCoordHom_injective`.
* `WeierstrassCurve.Affine.CoordinateRing.translateEndo`: the endomorphism `F(W) →+* F(W)`, with
  `translateEndo_algebraMap` (its value on `F[W]`) and the generator images `translateEndo_genX`
  and `translateEndo_genY`.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.2, III.8.
-/


-- @@ L66-66 verbatim
open Polynomial


-- @@ L68-87 verbatim
/-- **Zariski's lemma, image form.** An `F`-algebra homomorphism from a finite-type `F`-algebra to a
field, whose kernel is a maximal ideal, has algebraic image: every value `g b` is algebraic over the
base field `F`. (The residue field `A ⧸ ker g` is then a field of finite type over `F`, hence finite
over `F` by Zariski's lemma, so integral; the value `g b` is the image of the integral element
`b mod ker g` under the injective factor map.) -/
lemma isAlgebraic_of_ker_maximal {F A L : Type*} [Field F] [CommRing A] [Field L]
    [Algebra F A] [Algebra F L] [Algebra.FiniteType F A]
    (g : A →ₐ[F] L) (hmax : (RingHom.ker g).IsMaximal) (b : A) :
    IsAlgebraic F (g b) := by
  letI : Field (A ⧸ RingHom.ker g) := Ideal.Quotient.field _
  haveI : Algebra.FiniteType F (A ⧸ RingHom.ker g) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F _) (Ideal.Quotient.mkₐ_surjective F _)
  haveI := finite_of_finite_type_of_isJacobsonRing F (A ⧸ RingHom.ker g)
  let ψ : (A ⧸ RingHom.ker g) →ₐ[F] L := Ideal.Quotient.liftₐ (RingHom.ker g) g (fun _ hx => hx)
  have hint : IsIntegral F (Ideal.Quotient.mk (RingHom.ker g) b) := IsIntegral.of_finite F _
  have hint2 : IsIntegral F (ψ (Ideal.Quotient.mk (RingHom.ker g) b)) := hint.map ψ
  have heq : ψ (Ideal.Quotient.mk (RingHom.ker g) b) = g b := by
    simp only [ψ, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]; rfl
  rw [heq] at hint2
  exact hint2.isAlgebraic


-- @@ L89-89 verbatim
namespace WeierstrassCurve.Affine

-- @@ L90-90 verbatim
namespace CoordinateRing


-- @@ L92-92 verbatim
open scoped Polynomial.Bivariate


-- @@ L94-94 verbatim
variable {F : Type*} [Field F] {W : Affine F}


-- @@ L96-96 verbatim
/-! ### The generic `x`-coordinate is transcendental -/


-- @@ L98-100 verbatim
/-- The polynomial `W.polynomial` has nonzero degree (it is monic of degree `2`). -/
private lemma polynomial_degree_ne_zero : W.polynomial.degree ≠ 0 := by
  rw [Polynomial.degree_eq_natDegree W.monic_polynomial.ne_zero, W.natDegree_polynomial]; decide


-- @@ L102-109 verbatim
/-- The structural map `F[X] → F(W)` is injective (it factors as the injective coordinate-ring
inclusion `AdjoinRoot.of` followed by the fraction-field embedding). -/
lemma algebraMap_polynomial_funcField_injective :
    Function.Injective (algebraMap F[X] W.FunctionField) := by
  rw [IsScalarTower.algebraMap_eq F[X] W.CoordinateRing W.FunctionField, RingHom.coe_comp]
  refine (IsFractionRing.injective W.CoordinateRing W.FunctionField).comp ?_
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.of.injective_of_degree_ne_zero polynomial_degree_ne_zero


-- @@ L111-123 verbatim
/-- **The generic `x`-coordinate is transcendental over `F`.** Indeed `genX` is the image of the
polynomial variable `X` under the injective map `F[X] → F(W)`. -/
lemma transcendental_genX : Transcendental F (genX W) := by
  have hgenX : genX W = algebraMap F[X] W.FunctionField X := by
    rw [genX, genPsi, show mk W (C X) = AdjoinRoot.of W.polynomial X from rfl,
      ← AdjoinRoot.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply F[X] W.CoordinateRing W.FunctionField]
  rw [hgenX]
  refine (Polynomial.transcendental_X (R := F)).ringHom_of_comp_eq (RingHom.id F)
    (algebraMap F[X] W.FunctionField) Function.surjective_id
    algebraMap_polynomial_funcField_injective ?_
  ext c
  simp [IsScalarTower.algebraMap_apply F F[X] W.FunctionField]


-- @@ L125-129 verbatim
/-! ### The relative algebraic closure is preserved by the addition formulae

Throughout, `K := algebraicClosure F W.FunctionField` is the relative algebraic closure of `F` in
`F(W)` — the intermediate field of elements algebraic over `F`. The affine coordinate operations of
the base-changed curve `W ⁄ F(W)` map `K`-tuples into `K`. -/


-- @@ L131-131 verbatim
local notation "K" => algebraicClosure F W.FunctionField


-- @@ L133-134 verbatim
private lemma map_a₁_mem : (W.map (algebraMap F W.FunctionField)).a₁ ∈ K := by
  rw [WeierstrassCurve.map_a₁]; exact (algebraicClosure F W.FunctionField).algebraMap_mem W.a₁


-- @@ L136-137 verbatim
private lemma map_a₂_mem : (W.map (algebraMap F W.FunctionField)).a₂ ∈ K := by
  rw [WeierstrassCurve.map_a₂]; exact (algebraicClosure F W.FunctionField).algebraMap_mem W.a₂


-- @@ L139-140 verbatim
private lemma map_a₃_mem : (W.map (algebraMap F W.FunctionField)).a₃ ∈ K := by
  rw [WeierstrassCurve.map_a₃]; exact (algebraicClosure F W.FunctionField).algebraMap_mem W.a₃


-- @@ L142-143 verbatim
private lemma map_a₄_mem : (W.map (algebraMap F W.FunctionField)).a₄ ∈ K := by
  rw [WeierstrassCurve.map_a₄]; exact (algebraicClosure F W.FunctionField).algebraMap_mem W.a₄


-- @@ L145-147 verbatim
private lemma negY_mem {x y : W.FunctionField} (hx : x ∈ K) (hy : y ∈ K) :
    (W.map (algebraMap F W.FunctionField)).negY x y ∈ K :=
  sub_mem (sub_mem (neg_mem hy) (mul_mem map_a₁_mem hx)) map_a₃_mem


-- @@ L149-153 verbatim
private lemma addX_mem {x₁ x₂ ℓ : W.FunctionField} (h1 : x₁ ∈ K) (h2 : x₂ ∈ K) (hℓ : ℓ ∈ K) :
    (W.map (algebraMap F W.FunctionField)).addX x₁ x₂ ℓ ∈ K := by
  rw [addX]
  exact sub_mem (sub_mem (sub_mem (add_mem (pow_mem hℓ 2) (mul_mem map_a₁_mem hℓ)) map_a₂_mem) h1)
    h2


-- @@ L155-165 verbatim
open Classical in
private lemma slope_mem {x₁ x₂ y₁ y₂ : W.FunctionField}
    (h1 : x₁ ∈ K) (h2 : x₂ ∈ K) (hy1 : y₁ ∈ K) (hy2 : y₂ ∈ K) :
    (W.map (algebraMap F W.FunctionField)).slope x₁ x₂ y₁ y₂ ∈ K := by
  rw [slope]
  split_ifs
  · exact zero_mem _
  · refine div_mem ?_ (sub_mem hy1 (negY_mem h1 hy1))
    refine sub_mem (add_mem (add_mem (mul_mem (ofNat_mem _ 3) (pow_mem h1 2))
      (mul_mem (mul_mem (ofNat_mem _ 2) map_a₂_mem) h1)) map_a₄_mem) (mul_mem map_a₁_mem hy1)
  · exact div_mem (sub_mem hy1 hy2) (sub_mem h1 h2)


-- @@ L167-174 verbatim
/-- `translateCoordHom` is an `F`-algebra homomorphism: it fixes the image of `F`. -/
lemma translateCoordHom_algebraMap {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) (c : F) :
    translateCoordHom h₂ (algebraMap F W.CoordinateRing c) = algebraMap F W.FunctionField c := by
  have h1 : (algebraMap F W.CoordinateRing c) = mk W (C (C c)) := by
    rw [IsScalarTower.algebraMap_apply F F[X] W.CoordinateRing, AdjoinRoot.algebraMap_eq,
      ← Polynomial.C_eq_algebraMap]; rfl
  rw [h1, show mk W (C (C c)) = AdjoinRoot.of W.polynomial (C c) from rfl, translateCoordHom,
    AdjoinRoot.lift_of, coe_eval₂RingHom, eval₂_C]


-- @@ L176-180 verbatim
/-- `translateCoordHom` packaged as an `F`-algebra homomorphism. -/
noncomputable def translateAlgHom {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) :
    W.CoordinateRing →ₐ[F] W.FunctionField where
  toRingHom := translateCoordHom h₂
  commutes' := translateCoordHom_algebraMap h₂


-- @@ L182-183 verbatim
@[simp] lemma translateAlgHom_apply {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) (a : W.CoordinateRing) :
    translateAlgHom h₂ a = translateCoordHom h₂ a := rfl


-- @@ L185-200 verbatim
/-- The `F`-algebra structure on `F[W]` is finitely generated: `F[W]` is module-finite over the
polynomial ring `F[X]`, which is finite type over `F`.

⚠️ **Named rather than anonymous** (`#1277`).  An anonymous `instance` whose elaborated type
mentions no constant of this project gets `moduleToSuffix` appended by
`Lean.Elab.NameGen.mkBaseNameWithSuffix` — here `_ellipticCurves`, the lake library name — so the
auto-generated name was ``…CoordinateRing.instFiniteType_ellipticCurves``.  That is not a
collision (the unsuffixed name exists nowhere); it is the library name leaking into the API, and it
would change if the library were renamed.  The name below is Lean's own generated name with the
suffix removed, so nothing else moves.

⚠️ The `defsWithUnderscore` linter does **not** report this one, because `Algebra.FiniteType` is a
`Prop` and the linter skips proofs.  It is in the census all the same. -/
instance instFiniteType : Algebra.FiniteType F W.CoordinateRing :=
  Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType F F[X])
    (Module.Finite.finiteType (R := F[X]) W.CoordinateRing)


-- @@ L202-202 verbatim
/-! ### Dominance of translation, and the endomorphism -/


-- @@ L204-204 verbatim
variable [W.IsElliptic]


-- @@ L206-247 verbatim
open Classical in
/-- **Group-law cancellation `(P + T) + (-T) = P` at the generic point.** If the coordinates of the
translated generic point `P + T` — i.e. the images of the `F[W]`-generators under
`translateCoordHom` — are algebraic over `F`, then the generic `x`-coordinate `genX = x(P)` is
algebraic over `F`. -/
lemma genX_mem_algebraicClosure_of {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂)
    (hu : translateCoordHom h₂ (mk W (C X)) ∈ K)
    (hv : translateCoordHom h₂ (AdjoinRoot.root W.polynomial) ∈ K) :
    genX W ∈ K := by
  have hP : (W.map (algebraMap F W.FunctionField)).Nonsingular (genX W) (genY W) :=
    equation_iff_nonsingular.mp equation_gen
  have hT : (W.map (algebraMap F W.FunctionField)).Nonsingular
      (algebraMap F W.FunctionField x₂) (algebraMap F W.FunctionField y₂) :=
    equation_iff_nonsingular.mp (h₂.map (algebraMap F W.FunctionField))
  have hxne : genX W ≠ algebraMap F W.FunctionField x₂ := genX_ne x₂
  have hPQ : (Point.some _ _ hP) + (Point.some _ _ hT)
      = Point.some _ _ (nonsingular_add hP hT (fun h => hxne h.1)) := Point.add_of_X_ne hxne
  rw [translateCoordHom_X] at hu
  rw [translateCoordHom_root] at hv
  set u := (W.map (algebraMap F W.FunctionField)).addX (genX W)
    (algebraMap F W.FunctionField x₂) ((W.map (algebraMap F W.FunctionField)).slope (genX W)
      (algebraMap F W.FunctionField x₂) (genY W) (algebraMap F W.FunctionField y₂)) with hu_def
  set v := (W.map (algebraMap F W.FunctionField)).addY (genX W)
    (algebraMap F W.FunctionField x₂) (genY W) ((W.map (algebraMap F W.FunctionField)).slope
      (genX W) (algebraMap F W.FunctionField x₂) (genY W) (algebraMap F W.FunctionField y₂))
      with hv_def
  have hcancel : (Point.some _ _ hP + Point.some _ _ hT) + (-(Point.some _ _ hT))
      = Point.some _ _ hP := by rw [add_assoc, add_neg_cancel, add_zero]
  rw [hPQ, Point.neg_some] at hcancel
  have hx₂K : algebraMap F W.FunctionField x₂ ∈ K :=
    (algebraicClosure F W.FunctionField).algebraMap_mem x₂
  have hy₂K : algebraMap F W.FunctionField y₂ ∈ K :=
    (algebraicClosure F W.FunctionField).algebraMap_mem y₂
  by_cases hc : u = algebraMap F W.FunctionField x₂ ∧
      v = (W.map (algebraMap F W.FunctionField)).negY (algebraMap F W.FunctionField x₂)
        ((W.map (algebraMap F W.FunctionField)).negY (algebraMap F W.FunctionField x₂)
          (algebraMap F W.FunctionField y₂))
  · rw [Point.add_of_Y_eq hc.1 hc.2] at hcancel
    exact absurd hcancel.symm (Point.some_ne_zero _)
  · rw [Point.add_some hc, Point.some.injEq] at hcancel
    rw [hcancel.1.symm]
    exact addX_mem hu hx₂K (slope_mem hu hx₂K hv (negY_mem hx₂K hy₂K))


-- @@ L249-273 verbatim
set_option maxHeartbeats 400000 in
-- The proof specialises Zariski's lemma (`isAlgebraic_of_ker_maximal`) to `F[W]` and then unfolds
-- the large `AdjoinRoot.lift` term defining `translateCoordHom` to identify its values with the
-- addition-law coordinates; this defeq check needs a little over the default heartbeat budget.
/-- **Translation is dominant: `translateCoordHom h₂` is injective.** If it were not, its kernel
would be a nonzero prime — hence maximal, as `F[W]` has Krull dimension `≤ 1` — so the residue field
would be algebraic over `F` (Zariski), forcing the generic `x`-coordinate to be algebraic and
contradicting `transcendental_genX`. -/
lemma translateCoordHom_injective {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) :
    Function.Injective (translateCoordHom h₂) := by
  have key : Function.Injective (translateAlgHom h₂) := by
    by_contra hni
    have hne : RingHom.ker (translateAlgHom h₂) ≠ ⊥ := fun h =>
      hni ((RingHom.injective_iff_ker_eq_bot _).mpr h)
    haveI hprime : (RingHom.ker (translateAlgHom h₂)).IsPrime := RingHom.ker_isPrime _
    have hmax : (RingHom.ker (translateAlgHom h₂)).IsMaximal := hprime.isMaximal hne
    have hu : IsAlgebraic F (translateAlgHom h₂ (mk W (C X))) :=
      isAlgebraic_of_ker_maximal (translateAlgHom h₂) hmax (mk W (C X))
    have hv : IsAlgebraic F (translateAlgHom h₂ (AdjoinRoot.root W.polynomial)) :=
      isAlgebraic_of_ker_maximal (translateAlgHom h₂) hmax (AdjoinRoot.root W.polynomial)
    rw [translateAlgHom_apply] at hu hv
    have hgen : genX W ∈ K := genX_mem_algebraicClosure_of h₂
      (mem_algebraicClosure_iff.mpr hu) (mem_algebraicClosure_iff.mpr hv)
    exact transcendental_genX (mem_algebraicClosure_iff.mp hgen)
  exact key


-- @@ L275-280 verbatim
/-- **The translation-by-`T` endomorphism of the function field.** The ring endomorphism
`F(W) →+* F(W)` realising `h ↦ h ∘ (· + T)`, obtained from the injective coordinate-ring pullback
`translateCoordHom h₂` by the universal property of the fraction field. -/
noncomputable def translateEndo {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) :
    W.FunctionField →+* W.FunctionField :=
  IsFractionRing.lift (translateCoordHom_injective h₂)


-- @@ L282-285 verbatim
/-- On the image of `F[W]`, `translateEndo` agrees with the coordinate-ring pullback. -/
@[simp] lemma translateEndo_algebraMap {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) (a : W.CoordinateRing) :
    translateEndo h₂ (algebraMap W.CoordinateRing W.FunctionField a) = translateCoordHom h₂ a :=
  IsFractionRing.lift_algebraMap (translateCoordHom_injective h₂) a


-- @@ L287-295 verbatim
open Classical in
/-- The image of the generic `x`-coordinate: the `x`-coordinate of `P + T`. -/
lemma translateEndo_genX {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) :
    translateEndo h₂ (genX W) =
      (W.map (algebraMap F W.FunctionField)).addX (genX W) (algebraMap F W.FunctionField x₂)
        ((W.map (algebraMap F W.FunctionField)).slope (genX W) (algebraMap F W.FunctionField x₂)
          (genY W) (algebraMap F W.FunctionField y₂)) := by
  conv_lhs => rw [genX, genPsi]
  rw [translateEndo_algebraMap, translateCoordHom_X]


-- @@ L297-305 verbatim
open Classical in
/-- The image of the generic `y`-coordinate: the `y`-coordinate of `P + T`. -/
lemma translateEndo_genY {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) :
    translateEndo h₂ (genY W) =
      (W.map (algebraMap F W.FunctionField)).addY (genX W) (algebraMap F W.FunctionField x₂)
        (genY W) ((W.map (algebraMap F W.FunctionField)).slope (genX W)
          (algebraMap F W.FunctionField x₂) (genY W) (algebraMap F W.FunctionField y₂)) := by
  conv_lhs => rw [genY]
  rw [translateEndo_algebraMap, translateCoordHom_root]


-- @@ L307-307 verbatim
end CoordinateRing

-- @@ L308-308 verbatim
end WeierstrassCurve.Affine
