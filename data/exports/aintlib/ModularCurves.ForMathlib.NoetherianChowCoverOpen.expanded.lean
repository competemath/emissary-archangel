/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.ForMathlib.NoetherianChowCover
import ModularCurves.ForMathlib.ProperDenseOpenRestriction


-- @@ L11-17 verbatim
/-!
# The common-open isomorphism locus of a Noetherian Chow cover

The finite-proper-closure construction of a Chow cover contains the common open of the chosen
finite affine cover. This file exposes that map and proves that the Chow cover is an isomorphism
over the corresponding target open.
-/


-- @@ L19-19 verbatim
open CategoryTheory TopologicalSpace


-- @@ L21-21 verbatim
universe u


-- @@ L23-23 verbatim
namespace AlgebraicGeometry.Scheme.FiniteAffineImageCover


-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
variable {R : Type u} [CommRing R] {X : Scheme.{u}}

-- @@ L28-28 verbatim
variable (xπ : X ⟶ Spec (.of R)) {ι : Type u} [Finite ι]

-- @@ L29-29 verbatim
variable (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))

-- @@ L30-30 verbatim
variable [IsNoetherian X] [LocallyOfFinitePresentation xπ]


-- @@ L32-40 verbatim
/-- The common open of the finite affine cover, lifted into the chosen Chow source. -/
noncomputable def chowCommonOpen (i : ι) :
    (commonOpen U).toScheme ⟶ chowObj xπ U hU := by
  letI : ∀ i, IsOpenImmersion (projectiveOpen xπ U hU i) :=
    fun i ↦ projectiveOpen_isOpenImmersion xπ U hU i
  exact Scheme.FiniteProperClosure.toChartUnion
    (projectiveπ xπ U hU) (projectiveOpen xπ U hU)
    ((commonOpen U).ι ≫ xπ) (toChart U)
    (coordinates_comp_p xπ U hU) i


-- @@ L42-78 verbatim
/-- The common open is open in the chosen Chow source. -/
lemma chowCommonOpen_isOpenImmersion (i : ι) :
    IsOpenImmersion (chowCommonOpen xπ U hU i) := by
  letI : Nonempty ι := ⟨i⟩
  letI : IsNoetherian (commonOpen U).toScheme := commonOpen_isNoetherian U
  letI : QuasiCompact (commonOpen U).ι := by infer_instance
  letI : IsOpenImmersion (toImage U) := by
    change IsOpenImmersion (commonOpen U).ι.toImage
    infer_instance
  letI : ∀ i, IsOpenImmersion (toChart U i) := fun i ↦ by
    haveI : IsOpenImmersion (toChart U i ≫ (chart U i).ι) := by
      rw [toChart_chartι]
      infer_instance
    exact IsOpenImmersion.of_comp (toChart U i) (chart U i).ι
  letI : ∀ i, IsOpenImmersion (projectiveOpen xπ U hU i) :=
    fun i ↦ projectiveOpen_isOpenImmersion xπ U hU i
  letI : QuasiCompact
      (Scheme.FiniteProperClosure.diagonal
        (projectiveπ xπ U hU) ((commonOpen U).ι ≫ xπ)
        (fun i ↦ toChart U i ≫ projectiveOpen xπ U hU i)
        (coordinates_comp_p xπ U hU)) := by infer_instance
  letI : IsOpenImmersion
      (Scheme.FiniteProperClosure.toClosure
        (projectiveπ xπ U hU) ((commonOpen U).ι ≫ xπ)
        (fun i ↦ toChart U i ≫ projectiveOpen xπ U hU i)
        (coordinates_comp_p xπ U hU)) :=
    Scheme.FiniteProperClosure.toClosure_isOpenImmersion
      (projectiveπ xπ U hU) ((commonOpen U).ι ≫ xπ)
      (fun i ↦ toChart U i ≫ projectiveOpen xπ U hU i)
      (coordinates_comp_p xπ U hU) (fun i ↦ by infer_instance)
  haveI : IsOpenImmersion
      (chowCommonOpen xπ U hU i ≫ (chowOpen xπ U hU).ι) := by
    unfold chowCommonOpen chowOpen
    rw [Scheme.FiniteProperClosure.toChartUnion_ι]
    infer_instance
  exact IsOpenImmersion.of_comp (chowCommonOpen xπ U hU i)
    (chowOpen xπ U hU).ι


-- @@ L80-95 verbatim
/-- The common open is scheme-theoretically dense in the chosen Chow source. -/
lemma chowCommonOpen_isSchemeTheoreticallyDominant (i : ι) :
    IsSchemeTheoreticallyDominant (chowCommonOpen xπ U hU i) := by
  letI : ∀ i, IsOpenImmersion (projectiveOpen xπ U hU i) :=
    fun i ↦ projectiveOpen_isOpenImmersion xπ U hU i
  letI : IsNoetherian (commonOpen U).toScheme := commonOpen_isNoetherian U
  letI : QuasiCompact
      (Scheme.FiniteProperClosure.diagonal
        (projectiveπ xπ U hU) ((commonOpen U).ι ≫ xπ)
        (fun i ↦ toChart U i ≫ projectiveOpen xπ U hU i)
        (coordinates_comp_p xπ U hU)) := by infer_instance
  unfold chowCommonOpen
  exact Scheme.FiniteProperClosure.toChartUnion_isSchemeTheoreticallyDominant
    (projectiveπ xπ U hU) (projectiveOpen xπ U hU)
    ((commonOpen U).ι ≫ xπ) (toChart U)
    (coordinates_comp_p xπ U hU) i


-- @@ L97-101 verbatim
/-- The common-open lift is quasi-compact. -/
lemma chowCommonOpen_quasiCompact (i : ι) :
    QuasiCompact (chowCommonOpen xπ U hU i) := by
  letI : IsNoetherian (commonOpen U).toScheme := commonOpen_isNoetherian U
  infer_instance


-- @@ L103-125 verbatim
/-- The common-open lift followed by the Chow cover is the original open immersion. -/
@[reassoc]
lemma chowCommonOpen_comp_chowToTarget [IsSeparated xπ] (i : ι) :
    chowCommonOpen xπ U hU i ≫ chowToTarget xπ U hU =
      (commonOpen U).ι := by
  letI : ∀ i, IsOpenImmersion (projectiveOpen xπ U hU i) :=
    fun i ↦ projectiveOpen_isOpenImmersion xπ U hU i
  letI : IsNoetherian (commonOpen U).toScheme := commonOpen_isNoetherian U
  letI : QuasiCompact
      (Scheme.FiniteProperClosure.diagonal
        (projectiveπ xπ U hU) ((commonOpen U).ι ≫ xπ)
        (fun i ↦ toChart U i ≫ projectiveOpen xπ U hU i)
        (coordinates_comp_p xπ U hU)) := by infer_instance
  calc
    chowCommonOpen xπ U hU i ≫ chowToTarget xπ U hU =
        (chowCommonOpen xπ U hU i ≫ chowMap xπ U hU) ≫ inclusion U := by
      unfold chowToTarget
      rw [Category.assoc]
    _ = (toChart U i ≫ (chart U i).ι) ≫ inclusion U := by
      unfold chowCommonOpen chowMap
      rw [Scheme.FiniteProperClosure.toChartUnion_chartUnionToTarget]
    _ = toImage U ≫ inclusion U := by rw [toChart_chartι]
    _ = (commonOpen U).ι := Scheme.Hom.toImage_imageι (commonOpen U).ι


-- @@ L127-141 verbatim
/-- The chosen Chow cover is an isomorphism over the common open of the affine cover. -/
lemma chowToTarget_restrict_commonOpen_isIso [IsSeparated xπ]
    (hcover : ⨆ i, U i = ⊤) (i : ι) :
    IsIso (chowToTarget xπ U hU ∣_ (commonOpen U).ι.opensRange) := by
  letI : IsProper (chowToTarget xπ U hU) :=
    chowToTarget_isProper xπ U hU hcover
  letI : IsOpenImmersion (chowCommonOpen xπ U hU i) :=
    chowCommonOpen_isOpenImmersion xπ U hU i
  letI : IsSchemeTheoreticallyDominant (chowCommonOpen xπ U hU i) :=
    chowCommonOpen_isSchemeTheoreticallyDominant xπ U hU i
  letI : QuasiCompact (chowCommonOpen xπ U hU i) :=
    chowCommonOpen_quasiCompact xπ U hU i
  exact Scheme.Hom.isIso_morphismRestrict_opensRange_of_isProper
    (chowToTarget xπ U hU) (chowCommonOpen xπ U hU i)
    (commonOpen U).ι (chowCommonOpen_comp_chowToTarget xπ U hU i)


-- @@ L143-143 verbatim
end


-- @@ L145-145 verbatim
end AlgebraicGeometry.Scheme.FiniteAffineImageCover


-- @@ L147-147 verbatim
namespace AlgebraicGeometry


-- @@ L149-149 verbatim
noncomputable section


-- @@ L151-151 verbatim
variable {R : Type u} [CommRing R] {X : Scheme.{u}}


-- @@ L153-189 verbatim
/-- A nonempty separated locally finitely presented Noetherian scheme over an affine base admits
a proper-surjective Chow cover which is an isomorphism over a nonempty open. -/
theorem Scheme.Hom.exists_chowCover_isIso_on_nonempty_open_of_isNoetherian
    (xπ : X ⟶ Spec (.of R)) [Nonempty X] [IsNoetherian X]
    [LocallyOfFinitePresentation xπ] [IsSeparated xπ] :
    ∃ (X' Z : Scheme.{u}) (cover : X' ⟶ X) (immersion : X' ⟶ Z)
      (zπ : Z ⟶ Spec (.of R)) (V : X.Opens),
      IsProper cover ∧ Surjective cover ∧ IsOpenImmersion immersion ∧
        IsProper zπ ∧ cover ≫ xπ = immersion ≫ zπ ∧
        Nonempty V.toScheme ∧ IsIso (cover ∣_ V) := by
  obtain ⟨ι, hι, hnonempty, U, hcover, hU, hDense⟩ :=
    X.exists_nonempty_finite_affine_openCover_dense_iInf_of_isNoetherian
  letI : Finite ι := hι
  have hcover' : ⨆ i, U i = ⊤ := by
    simpa only [IsOpenCover] using hcover
  let i : ι := Classical.choice hnonempty
  have hV : Nonempty
      (Scheme.FiniteAffineImageCover.commonOpen U).ι.opensRange.toScheme := by
    rw [Scheme.Opens.opensRange_ι]
    exact hDense.nonempty.to_subtype
  letI : IsIso
      (Scheme.FiniteAffineImageCover.chowToTarget xπ U hU ∣_
        (Scheme.FiniteAffineImageCover.commonOpen U).ι.opensRange) :=
    Scheme.FiniteAffineImageCover.chowToTarget_restrict_commonOpen_isIso
      xπ U hU hcover' i
  refine ⟨Scheme.FiniteAffineImageCover.chowObj xπ U hU,
    Scheme.FiniteAffineImageCover.chowAmbient xπ U hU,
    Scheme.FiniteAffineImageCover.chowToTarget xπ U hU,
    Scheme.FiniteAffineImageCover.chowImmersion xπ U hU,
    Scheme.FiniteAffineImageCover.chowAmbientπ xπ U hU,
    (Scheme.FiniteAffineImageCover.commonOpen U).ι.opensRange, ?_⟩
  exact ⟨Scheme.FiniteAffineImageCover.chowToTarget_isProper xπ U hU hcover',
    Scheme.FiniteAffineImageCover.chowToTarget_surjective xπ U hU hcover' hDense i,
    Scheme.FiniteAffineImageCover.chowImmersion_isOpenImmersion xπ U hU,
    Scheme.FiniteAffineImageCover.chowAmbientπ_isProper xπ U hU,
    Scheme.FiniteAffineImageCover.chowToTarget_comp_xπ xπ U hU,
    hV, inferInstance⟩


-- @@ L191-191 verbatim
end


-- @@ L193-193 verbatim
end AlgebraicGeometry
