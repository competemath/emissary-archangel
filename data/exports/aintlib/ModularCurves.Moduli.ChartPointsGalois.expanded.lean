/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PointsDictionaryGalois
import ModularCurves.Moduli.E3DatumAssembly


-- @@ L9-38 verbatim
/-!
# Galois naturality of the chart point dictionaries (DS4 M1c, nodes B–D)

`chartAffinePointEquiv` (`WeilPairing/FibrePointDict.lean`) is the composite

```
E.Point (t ≫ chartρ V)  --chartPointsEquiv-->  (modelEllipticCurve Pr.W).Point t
                        --modelPointAddEquiv-->  (Pr.W.baseChange K).toAffine.Point
```

and this file shows both factors carry the scheme-level Galois action `P ↦ Spec σ ≫ P`
to mathlib's coordinatewise `Affine.Point.map σ`.

Following the review advice, every statement takes its hypothesis and states its
conclusion **on underlying morphisms** rather than on typed points: the base point of a
restricted point is `a ≫ t`, which is only propositionally the original one, and
threading that through dependent types is what makes these arguments expensive. With the
morphism-level formulation there are no casts at all.

`modelPointAddEquiv` is `Equiv.subtypeEquivProp rfl` composed with the field-points
dictionary, so node B is `Subtype.ext` plus
`projModelPointsEquiv_specMapCompPoint` (node A). `chartPointsEquiv` is built from
`Point.baseChangeEquiv⁻¹` and `pointAddEquiv`; the second is postcomposition (pure
associativity), the first is `pullback.lift` and needs the universal property.
-/

-- v4.33 bump: component types coming from semireducible `baseChange*`/`pullback`/`resLE`
-- defs are defeq only after delta, which `rw`/`simp` will not do at `implicit`
-- transparency; and the `Scheme` category instance is likewise no longer transparent
-- enough for the `≫`-associativity rewrites.

-- @@ L39-39 verbatim
set_option backward.defeqAttrib.useBackward true

-- @@ L40-40 verbatim
set_option backward.isDefEq.respectTransparency false

-- @@ L41-41 verbatim
set_option backward.isDefEq.respectTransparency.types false


-- @@ L43-43 verbatim
universe u


-- @@ L45-45 verbatim
open CategoryTheory AlgebraicGeometry Limits


-- @@ L47-47 verbatim
namespace ModularCurves


-- @@ L49-49 verbatim
/-! ## Node B — `modelPointAddEquiv` -/


-- @@ L51-51 verbatim
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]


-- @@ L53-72 verbatim
/-- **(B)** The model-points dictionary carries precomposition with `Spec σ` to mathlib's
`Affine.Point.map σ`. The hypothesis is stated on the underlying morphisms, so the caller
never has to transport along `Spec σ ≫ t = t`. -/
theorem modelPointAddEquiv_of_coe_eq {K : Type u} [Field K] [DecidableEq K] [Algebra R K]
    (σ : K ≃ₐ[R] K)
    (P Q : (modelEllipticCurve W).Point
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (h : (Q.1 : Spec (CommRingCat.of K) ⟶ (modelEllipticCurve W).E) =
      Spec.map (CommRingCat.ofHom (σ : K →+* K)) ≫
        (P.1 : Spec (CommRingCat.of K) ⟶ (modelEllipticCurve W).E)) :
    modelPointAddEquiv W Q =
      WeierstrassCurve.Affine.Point.map (W' := W) (F := K) (K := K)
        (σ : K →ₐ[R] K) (modelPointAddEquiv W P) := by
  have hpt : (⟨Q.1, Q.2⟩ : SpecPoints (projModel W) (projModelπ W) K) =
      specMapCompPoint W σ ⟨P.1, P.2⟩ := Subtype.ext h
  show projModelPointsEquiv W K ⟨Q.1, Q.2⟩ =
    WeierstrassCurve.Affine.Point.map (W' := W) (F := K) (K := K) (σ : K →ₐ[R] K)
      (projModelPointsEquiv W K ⟨P.1, P.2⟩)
  rw [hpt]
  exact projModelPointsEquiv_specMapCompPoint W σ ⟨P.1, P.2⟩


-- @@ L74-74 verbatim
/-! ## Node C — `chartPointsEquiv` -/


-- @@ L76-76 verbatim
section Chart


-- @@ L78-78 verbatim
open LocalPresentation


-- @@ L80-81 verbatim
variable {S : Scheme.{u}} {E : EllipticCurve S} {V : S.affineOpens}
  (Pr : LocalPresentation E.toEllipticCurveGeom V)


-- @@ L83-90 verbatim
/-- The underlying morphism of `chartPointsEquiv`: the pullback lift, followed by the
chart comparison. Definitional, but recorded so that no later proof has to unfold the
two equivalences it is built from. -/
theorem chartPointsEquiv_coe {T : Scheme.{u}} (tV : T ⟶ Spec Γ(S, V.1))
    (P : letI := Pr.elliptic; E.Point (tV ≫ chartρ V)) :
    letI := Pr.elliptic
    ((chartPointsEquiv Pr tV P).1 : T ⟶ (modelEllipticCurve Pr.W).E) =
      pullback.lift (P.1 : T ⟶ E.E) tV P.2 ≫ (chartRecordIso Pr).hom.left := rfl


-- @@ L92-111 verbatim
/-- **(C)** `chartPointsEquiv` commutes with restriction along any `a : T' ⟶ T`.
Stated on underlying morphisms: the hypothesis says `Q` restricts `P`, the conclusion
says the same downstairs. The `pullback.lift` in the inverse of `Point.baseChangeEquiv`
is handled by `pullback.hom_ext` — it is *not* pure associativity. -/
theorem chartPointsEquiv_restrict_coe {T T' : Scheme.{u}} (tV : T ⟶ Spec Γ(S, V.1))
    (a : T' ⟶ T)
    (P : letI := Pr.elliptic; E.Point (tV ≫ chartρ V))
    (Q : letI := Pr.elliptic; E.Point ((a ≫ tV) ≫ chartρ V))
    (hQ : (Q.1 : T' ⟶ E.E) = a ≫ (P.1 : T ⟶ E.E)) :
    letI := Pr.elliptic
    ((chartPointsEquiv Pr (a ≫ tV) Q).1 : T' ⟶ (modelEllipticCurve Pr.W).E) =
      a ≫ ((chartPointsEquiv Pr tV P).1 : T ⟶ (modelEllipticCurve Pr.W).E) := by
  letI := Pr.elliptic
  have hlift : pullback.lift (Q.1 : T' ⟶ E.E) (a ≫ tV) Q.2 =
      a ≫ pullback.lift (P.1 : T ⟶ E.E) tV P.2 := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, hQ, Category.assoc, pullback.lift_fst]
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd]
  rw [chartPointsEquiv_coe Pr (a ≫ tV) Q, chartPointsEquiv_coe Pr tV P, hlift,
    Category.assoc]


-- @@ L113-130 verbatim
/-- `chartPointsEquiv` only depends on the base point through its value: two points with
the same underlying morphism over equal base points have the same image. This is the
transport that lets node C (stated with the base point *moving*) be used at a base point
that is *fixed* by `σ`. -/
theorem chartPointsEquiv_congr_base {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec Γ(S, V.1)}
    (h : t₁ = t₂)
    (P₁ : letI := Pr.elliptic; E.Point (t₁ ≫ chartρ V))
    (P₂ : letI := Pr.elliptic; E.Point (t₂ ≫ chartρ V))
    (hP : (P₁.1 : T ⟶ E.E) = (P₂.1 : T ⟶ E.E)) :
    letI := Pr.elliptic
    ((chartPointsEquiv Pr t₁ P₁).1 : T ⟶ (modelEllipticCurve Pr.W).E) =
      ((chartPointsEquiv Pr t₂ P₂).1 : T ⟶ (modelEllipticCurve Pr.W).E) := by
  letI := Pr.elliptic
  subst h
  rw [chartPointsEquiv_coe Pr t₁ P₁, chartPointsEquiv_coe Pr t₁ P₂]
  congr 1
  exact pullback.hom_ext (by rw [pullback.lift_fst, pullback.lift_fst]; exact hP)
    (by rw [pullback.lift_snd, pullback.lift_snd])


-- @@ L132-132 verbatim
end Chart


-- @@ L134-134 verbatim
end ModularCurves
