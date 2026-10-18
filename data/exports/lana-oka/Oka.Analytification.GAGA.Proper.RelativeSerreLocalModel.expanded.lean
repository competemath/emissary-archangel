/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.AlgebraicGeometry.ProjectiveSpace.RelativeSerreFinite
import Oka.Analytification.GAGA.Proper.RelativeBaseChangeIso
import Oka.Analytification.GAGA.Proper.RelativeSerre


-- @@ L10-30 verbatim
/-!
# Local models for projective morphisms over `ℂ`

Let `Y` be a scheme locally of finite type over `ℂ`. We package the schemes and morphisms which
describe a projective morphism `π : Y' ⟶ Y` with `(π, j) : Y' ⟶ Y ×_ℂ ℙᴺ` a closed immersion
locally over an affine open `V ⊆ Y` with ring `A = Γ(Y, V)`, as schemes locally of finite type over
`ℂ`:

* `Y ×_ℂ ℙᴺ` with its projections (`ComplexAnalytic.SchemeLFTℂ.relProj`,
  `SchemeLFTℂ.relProjFst`, `SchemeLFTℂ.relProjSnd`) and the morphism `(π, j)`
  (`SchemeLFTℂ.relProjLift`);
* `Spec A` with its open immersion into `Y` (`SchemeLFTℂ.affineSpec`, `SchemeLFTℂ.affineSpecι`),
  and `ℙ(N; A)` with its structure morphism to `Spec A` and its open immersion into
  `Y ×_ℂ ℙᴺ` onto the preimage of `V` (`SchemeLFTℂ.affineProj`, `SchemeLFTℂ.affineProjToSpec`,
  `SchemeLFTℂ.affineProjChart`);
* for a presentation `s : ℂ[y₀, …, y_{r-1}] → A` (which exists,
  `SchemeLFTℂ.exists_presentation`), the closed immersions `Spec A ⟶ 𝔸ʳ` and
  `ℙ(N; A) ⟶ ℙ(N; ℂ[y₀, …, y_{r-1}])` over it (`SchemeLFTℂ.affineSpecEmb`,
  `SchemeLFTℂ.affineProjEmb`, `SchemeLFTℂ.isClosedImmersion_affineSpecEmb`,
  `SchemeLFTℂ.isClosedImmersion_affineProjEmb`).
-/


-- @@ L32-32 verbatim
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace


-- @@ L34-34 verbatim
universe u


-- @@ L36-36 verbatim
noncomputable section


-- @@ L38-38 verbatim
namespace ComplexAnalytic


-- @@ L40-40 verbatim
open ProjectiveSpace


-- @@ L42-42 verbatim
variable (Y : SchemeLFTℂ.{u}) (N : ℕ)


-- @@ L44-50 verbatim
/-- `Y ×_ℂ ℙᴺ`, as a scheme locally of finite type over `ℂ`. -/
def SchemeLFTℂ.relProj : SchemeLFTℂ.{u} :=
  ⟨Over.mk (pullback.fst Y.obj.hom (toSpec N (ULift.{u} ℂ)) ≫ Y.obj.hom), by
    haveI : LocallyOfFiniteType Y.obj.hom := Y.property
    haveI : LocallyOfFiniteType (toSpec N (ULift.{u} ℂ)) := IsProper.toLocallyOfFiniteType
    change LocallyOfFiniteType (pullback.fst Y.obj.hom (toSpec N (ULift.{u} ℂ)) ≫ Y.obj.hom)
    infer_instance⟩


-- @@ L52-54 verbatim
/-- The projection `Y ×_ℂ ℙᴺ ⟶ Y`. -/
def SchemeLFTℂ.relProjFst : Y.relProj N ⟶ Y :=
  ObjectProperty.homMk (Over.homMk (pullback.fst Y.obj.hom (toSpec N (ULift.{u} ℂ))) rfl)


-- @@ L56-59 verbatim
/-- The projection `Y ×_ℂ ℙᴺ ⟶ ℙᴺ`. -/
def SchemeLFTℂ.relProjSnd : Y.relProj N ⟶ projectiveSpace.{u} N :=
  ObjectProperty.homMk (Over.homMk (pullback.snd Y.obj.hom (toSpec N (ULift.{u} ℂ)))
    pullback.condition.symm)


-- @@ L61-61 verbatim
variable {Y N} {Y' : SchemeLFTℂ.{u}} (π : Y' ⟶ Y) (j : Y' ⟶ projectiveSpace.{u} N)


-- @@ L63-69 verbatim
/-- The morphism `(π, j) : Y' ⟶ Y ×_ℂ ℙᴺ`. -/
def SchemeLFTℂ.relProjLift : Y' ⟶ Y.relProj N :=
  ObjectProperty.homMk (Over.homMk (pullback.lift π.hom.left j.hom.left
    (hom_left_comp_obj_hom_eq π j)) (by
      change pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ Y.obj.hom = Y'.obj.hom
      rw [pullback.lift_fst_assoc]
      exact Over.w π.hom))


-- @@ L71-73 verbatim
lemma SchemeLFTℂ.relProjLift_fst : Y.relProjLift π j ≫ Y.relProjFst N = π := by
  ext1
  exact Over.OverMorphism.ext (pullback.lift_fst _ _ _)


-- @@ L75-77 verbatim
lemma SchemeLFTℂ.relProjLift_snd : Y.relProjLift π j ≫ Y.relProjSnd N = j := by
  ext1
  exact Over.OverMorphism.ext (pullback.lift_snd _ _ _)



-- @@ L80-80 verbatim
section Affine


-- @@ L82-82 verbatim
variable {V : Y.obj.left.Opens} (hV : IsAffineOpen V)


-- @@ L84-89 verbatim
/-- An affine open `V` of `Y`, as the spectrum `Spec Γ(Y, V)` over `ℂ`. -/
def SchemeLFTℂ.affineSpec : SchemeLFTℂ.{u} :=
  ⟨Over.mk (hV.fromSpec ≫ Y.obj.hom), by
    haveI : LocallyOfFiniteType Y.obj.hom := Y.property
    change LocallyOfFiniteType (hV.fromSpec ≫ Y.obj.hom)
    infer_instance⟩


-- @@ L91-93 verbatim
/-- The open immersion `Spec Γ(Y, V) ⟶ Y`. -/
def SchemeLFTℂ.affineSpecι : Y.affineSpec hV ⟶ Y :=
  ObjectProperty.homMk (Over.homMk hV.fromSpec rfl)


-- @@ L95-96 verbatim
instance : IsOpenImmersion (Y.affineSpecι hV).hom.left :=
  inferInstanceAs (IsOpenImmersion hV.fromSpec)


-- @@ L98-105 verbatim
variable (N) in
/-- `ℙ(N; Γ(Y, V))`, over `ℂ`. -/
def SchemeLFTℂ.affineProj : SchemeLFTℂ.{u} :=
  ⟨Over.mk (toSpec N Γ(Y.obj.left, V) ≫ hV.fromSpec ≫ Y.obj.hom), by
    haveI : LocallyOfFiniteType Y.obj.hom := Y.property
    haveI : LocallyOfFiniteType (toSpec N Γ(Y.obj.left, V)) := IsProper.toLocallyOfFiniteType
    change LocallyOfFiniteType (toSpec N Γ(Y.obj.left, V) ≫ hV.fromSpec ≫ Y.obj.hom)
    infer_instance⟩


-- @@ L107-110 verbatim
variable (N) in
/-- The structure morphism `ℙ(N; Γ(Y, V)) ⟶ Spec Γ(Y, V)`. -/
def SchemeLFTℂ.affineProjToSpec : Y.affineProj N hV ⟶ Y.affineSpec hV :=
  ObjectProperty.homMk (Over.homMk (toSpec N Γ(Y.obj.left, V)) rfl)


-- @@ L112-118 verbatim
variable (N) in
/-- The open immersion `ℙ(N; Γ(Y, V)) ⟶ Y ×_ℂ ℙᴺ` over `V`. -/
def SchemeLFTℂ.affineProjChart : Y.affineProj N hV ⟶ Y.relProj N :=
  ObjectProperty.homMk (Over.homMk (affineChart N Y.obj.hom hV) (by
    change affineChart N Y.obj.hom hV ≫ pullback.fst _ _ ≫ Y.obj.hom = _
    rw [affineChart_fst_assoc]
    rfl))


-- @@ L120-121 verbatim
instance : IsOpenImmersion (Y.affineProjChart N hV).hom.left :=
  inferInstanceAs (IsOpenImmersion (affineChart N Y.obj.hom hV))


-- @@ L123-126 verbatim
lemma SchemeLFTℂ.affineProjToSpec_comp_affineSpecι :
    Y.affineProjToSpec N hV ≫ Y.affineSpecι hV = Y.affineProjChart N hV ≫ Y.relProjFst N := by
  ext1
  exact Over.OverMorphism.ext (affineChart_fst Y.obj.hom hV).symm


-- @@ L128-135 verbatim
lemma SchemeLFTℂ.mem_range_affineProjChart (z : (Y.relProj N).obj.left)
    (hz : (Y.relProjFst N).hom.left.base z ∈ Set.range (Y.affineSpecι hV).hom.left.base) :
    z ∈ Set.range (Y.affineProjChart N hV).hom.left.base := by
  change z ∈ Set.range (affineChart N Y.obj.hom hV).base
  rw [range_affineChart]
  change (pullback.fst Y.obj.hom (toSpec N (ULift.{u} ℂ))).base z ∈ Set.range hV.fromSpec.base
    at hz
  rwa [hV.range_fromSpec] at hz



-- @@ L138-152 verbatim
/-- **Presentations of affine opens**: the ring `Γ(Y, V)` of an affine open is a quotient of a
polynomial ring `ℂ[y₀, …, y_{r-1}]`, compatibly with the structure maps from `ℂ`. -/
lemma SchemeLFTℂ.exists_presentation :
    ∃ (r : ℕ) (s : RelBase.{u} r →+* Γ(Y.obj.left, V)), Function.Surjective s ∧
      s.comp MvPolynomial.C = structureRingHom Y.obj.hom hV := by
  haveI : LocallyOfFiniteType Y.obj.hom := Y.property
  have hft : (structureRingHom Y.obj.hom hV).FiniteType := by
    have h := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
      (φ := CommRingCat.ofHom (structureRingHom Y.obj.hom hV))).1
        (by rw [SpecMap_structureRingHom]; infer_instance)
    exact h
  letI := (structureRingHom Y.obj.hom hV).toAlgebra
  haveI : Algebra.FiniteType (ULift.{u} ℂ) Γ(Y.obj.left, V) := hft
  obtain ⟨r, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 this
  exact ⟨r, f.toRingHom, hf, f.comp_algebraMap⟩


-- @@ L154-155 verbatim
variable {r : ℕ} {s : RelBase.{u} r →+* Γ(Y.obj.left, V)}
  (hs : s.comp MvPolynomial.C = structureRingHom Y.obj.hom hV)


-- @@ L157-161 verbatim
include hs in
lemma SchemeLFTℂ.specMap_presentation :
    Spec.map (CommRingCat.ofHom s) ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) =
      hV.fromSpec ≫ Y.obj.hom := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hs, SpecMap_structureRingHom]


-- @@ L163-166 verbatim
/-- The embedding `Spec Γ(Y, V) ⟶ 𝔸ʳ` given by a presentation. -/
def SchemeLFTℂ.affineSpecEmb : Y.affineSpec hV ⟶ affineSpace.{u} r :=
  ObjectProperty.homMk (Over.homMk (Spec.map (CommRingCat.ofHom s))
    (SchemeLFTℂ.specMap_presentation hV hs))


-- @@ L168-174 verbatim
variable (N) in
/-- The embedding `ℙ(N; Γ(Y, V)) ⟶ ℙ(N; ℂ[y₀, …, y_{r-1}])` given by a presentation. -/
def SchemeLFTℂ.affineProjEmb : Y.affineProj N hV ⟶ relProjectiveSpace.{u} r N :=
  ObjectProperty.homMk (Over.homMk (ProjectiveSpace.map s) (by
    change map s ≫ toSpec N _ ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) = _
    rw [map_toSpec_assoc, SchemeLFTℂ.specMap_presentation hV hs]
    rfl))


-- @@ L176-180 verbatim
lemma SchemeLFTℂ.affineProjEmb_comp :
    Y.affineProjEmb N hV hs ≫ relProjectiveSpaceToAffine r N =
      Y.affineProjToSpec N hV ≫ Y.affineSpecEmb hV hs := by
  ext1
  exact Over.OverMorphism.ext (map_toSpec s)


-- @@ L182-185 verbatim
include hs in
lemma SchemeLFTℂ.isClosedImmersion_affineSpecEmb (hsurj : Function.Surjective s) :
    IsClosedImmersion (Y.affineSpecEmb hV hs).hom.left :=
  IsClosedImmersion.spec_of_surjective _ hsurj


-- @@ L187-192 verbatim
include hs in
lemma SchemeLFTℂ.isClosedImmersion_affineProjEmb (hsurj : Function.Surjective s) :
    IsClosedImmersion (Y.affineProjEmb N hV hs).hom.left := by
  haveI := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom s) hsurj
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) (isPullback_map s).flip
    inferInstance


-- @@ L194-194 verbatim
end Affine


-- @@ L196-196 verbatim
end ComplexAnalytic
