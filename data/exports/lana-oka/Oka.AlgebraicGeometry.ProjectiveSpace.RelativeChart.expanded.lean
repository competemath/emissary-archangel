/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.AlgebraicGeometry.ProjectiveSpace.BaseChange


-- @@ L8-27 verbatim
/-!
# Charts of `Y ×_K ℙⁿ_K` over affine opens of `Y`

Let `y : Y ⟶ Spec K` be a scheme over a ring `K` and `P = Y ×_K ℙ(n; K)`. For an affine open
`V ⊆ Y` with ring `A = Γ(Y, V)`, the preimage of `V` in `P` is `ℙ(n; A)`: the morphism
`ProjectiveSpace.affineChart y hV : ℙ(n; A) ⟶ P`, with components `ℙ(n; A) ⟶ Spec A ⟶ Y` and
`ProjectiveSpace.map : ℙ(n; A) ⟶ ℙ(n; K)`, is an open immersion
(`ProjectiveSpace.isOpenImmersion_affineChart`) with range `pr₁⁻¹ V`
(`ProjectiveSpace.opensRange_affineChart`), since the square

```
ℙ(n; A) --affineChart--> P
   |                      | pr₁
 Spec A ----fromSpec----> Y
```

is a pullback square (`ProjectiveSpace.isPullback_affineChart`), by base change of `ℙ(n; K)`
along `K → A` (`ProjectiveSpace.isPullback_map`). The preimage of a basic open `D(g)`, `g ∈ A`,
is the basic open of `g` on `ℙ(n; A)` (`ProjectiveSpace.affineChart_preimage_basicOpen`).
-/


-- @@ L29-29 verbatim
open CategoryTheory Limits


-- @@ L31-31 verbatim
universe u


-- @@ L33-33 verbatim
namespace AlgebraicGeometry.ProjectiveSpace


-- @@ L35-36 verbatim
variable {n : ℕ} {K : Type u} [CommRing K] {Y : Scheme.{u}} (y : Y ⟶ Spec (.of K))
  {V : Y.Opens} (hV : IsAffineOpen V)


-- @@ L38-40 verbatim
/-- The ring map `K → Γ(Y, V)` of the structure morphism, for an affine open `V`. -/
noncomputable def structureRingHom : K →+* Γ(Y, V) :=
  (Spec.preimage (hV.fromSpec ≫ y)).hom


-- @@ L42-44 verbatim
lemma SpecMap_structureRingHom :
    Spec.map (CommRingCat.ofHom (structureRingHom y hV)) = hV.fromSpec ≫ y :=
  Spec.map_preimage _


-- @@ L46-50 verbatim
variable (n) in
/-- The chart `ℙ(n; Γ(Y, V)) ⟶ Y ×_K ℙ(n; K)` over the affine open `V`. -/
noncomputable def affineChart : ℙ(n; Γ(Y, V)) ⟶ pullback y (toSpec n K) :=
  pullback.lift (toSpec n _ ≫ hV.fromSpec) (map (structureRingHom y hV)) (by
    rw [map_toSpec, Category.assoc, SpecMap_structureRingHom])


-- @@ L52-55 verbatim
@[reassoc (attr := simp)]
lemma affineChart_fst :
    affineChart n y hV ≫ pullback.fst _ _ = toSpec n _ ≫ hV.fromSpec :=
  pullback.lift_fst _ _ _


-- @@ L57-60 verbatim
@[reassoc (attr := simp)]
lemma affineChart_snd :
    affineChart n y hV ≫ pullback.snd _ _ = map (structureRingHom y hV) :=
  pullback.lift_snd _ _ _


-- @@ L62-67 verbatim
/-- The chart square over the affine open `V` is a pullback square. -/
theorem isPullback_affineChart :
    IsPullback (affineChart n y hV) (toSpec n _) (pullback.fst y (toSpec n K)) hV.fromSpec := by
  refine IsPullback.of_right ?_ (affineChart_fst y hV) (IsPullback.of_hasPullback _ _).flip
  rw [affineChart_snd, ← SpecMap_structureRingHom]
  exact isPullback_map _


-- @@ L69-71 verbatim
instance isOpenImmersion_affineChart : IsOpenImmersion (affineChart n y hV) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_affineChart y hV).flip
    inferInstance


-- @@ L73-78 verbatim
lemma range_affineChart :
    Set.range (affineChart n y hV) = pullback.fst y (toSpec n K) ⁻¹' (V : Set Y) := by
  have h := (isPullback_affineChart (n := n) y hV).flip
  rw [← h.isoPullback_hom_snd, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    (Set.range_eq_univ (f := h.isoPullback.hom)).2 h.isoPullback.hom.surjective, Set.image_univ,
    Scheme.Pullback.range_snd, hV.range_fromSpec]


-- @@ L80-82 verbatim
lemma opensRange_affineChart :
    (affineChart n y hV).opensRange = pullback.fst y (toSpec n K) ⁻¹ᵁ V :=
  TopologicalSpace.Opens.ext (range_affineChart y hV)


-- @@ L84-90 verbatim
/-- The preimage under the chart of the preimage of a basic open `D(g) ⊆ V` is the basic open of
`g` on `ℙ(n; Γ(Y, V))`. -/
lemma affineChart_preimage_basicOpen (g : Γ(Y, V)) :
    affineChart n y hV ⁻¹ᵁ (pullback.fst y (toSpec n K) ⁻¹ᵁ Y.basicOpen g) =
      ℙ(n; Γ(Y, V)).basicOpen ((toSpec n _).appTop ((Scheme.ΓSpecIso Γ(Y, V)).inv g)) := by
  rw [← Scheme.Hom.comp_preimage, affineChart_fst, Scheme.Hom.comp_preimage,
    hV.fromSpec_preimage_basicOpen', Scheme.preimage_basicOpen_top]


-- @@ L92-92 verbatim
end AlgebraicGeometry.ProjectiveSpace
