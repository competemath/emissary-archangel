/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.ForMathlib.AffineModuleBaseChange
import ModularCurves.Picard.InvertibleSheaf


-- @@ L9-15 verbatim
/-!
# Pullback of quasicoherent finite-type scheme modules

Pullback along an arbitrary scheme morphism preserves quasicoherence and finite
type. The proof refines inverse images of affine target opens by affine source
opens and uses the existing affine pullback comparison on each refinement.
-/


-- @@ L17-17 verbatim
open CategoryTheory Limits TopologicalSpace


-- @@ L19-19 verbatim
universe u


-- @@ L21-21 verbatim
namespace AlgebraicGeometry.Scheme.Modules


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
variable {X Y : Scheme.{u}}


-- @@ L27-44 verbatim
private noncomputable def pullbackRestrictIsoOfLE
    (f : Y ⟶ X) (M : X.Modules) (U : X.Opens) (V : Y.Opens)
    (hVU : V ≤ f ⁻¹ᵁ U) :
    ((pullback f).obj M).restrict V.ι ≅
      (pullback (Y.homOfLE hVU ≫ f ∣_ U)).obj
        (M.restrict U.ι) := by
  let g := Y.homOfLE hVU ≫ f ∣_ U
  have hcomp : V.ι ≫ f = g ≫ U.ι := by
    dsimp only [g]
    rw [Category.assoc, morphismRestrict_ι]
    rw [← Category.assoc, Y.homOfLE_ι]
  exact
    (restrictFunctorIsoPullback V.ι).app ((pullback f).obj M) ≪≫
      (pullbackComp V.ι f).app M ≪≫
      (pullbackCongr hcomp).app M ≪≫
      ((pullbackComp g U.ι).app M).symm ≪≫
      ((pullback g).mapIso
        ((restrictFunctorIsoPullback U.ι).app M)).symm


-- @@ L46-49 verbatim
private abbrev pullbackAffineRefinementIndex
    (f : Y ⟶ X) :=
  {x : Y.Opens × X.affineOpens //
    x.1 ∈ Y.affineOpens ∧ x.1 ≤ x.2.1.comap f.base.hom}


-- @@ L51-54 verbatim
private def pullbackAffineRefinementOpen
    (f : Y ⟶ X) :
    pullbackAffineRefinementIndex f → Y.Opens :=
  fun j => j.1.1


-- @@ L56-64 verbatim
private theorem pullbackAffineRefinementOpen_isOpenCover
    (f : Y ⟶ X) :
    IsOpenCover (pullbackAffineRefinementOpen f) := by
  change IsOpenCover
    (fun j : {x : Y.Opens × X.affineOpens //
      x.1 ∈ Y.affineOpens ∧
        x.1 ≤ x.2.1.comap f.base.hom} => j.1.1)
  exact Y.isBasis_affineOpens.isOpenCover_mem_and_le
    (X.isBasis_affineOpens.isOpenCover.comap f.base.hom)


-- @@ L66-69 verbatim
private theorem pullbackAffineRefinementOpen_le_preimage
    (f : Y ⟶ X) (j : pullbackAffineRefinementIndex f) :
    pullbackAffineRefinementOpen f j ≤ f ⁻¹ᵁ j.1.2.1 :=
  j.2.2


-- @@ L71-76 verbatim
private def pullbackAffineRefinementHom
    (f : Y ⟶ X) (j : pullbackAffineRefinementIndex f) :
    (pullbackAffineRefinementOpen f j).toScheme ⟶
      j.1.2.1.toScheme :=
  Y.homOfLE (pullbackAffineRefinementOpen_le_preimage f j) ≫
    f ∣_ j.1.2.1


-- @@ L78-100 verbatim
private theorem pullbackAffineRefinement_restrict_isQuasicoherent
    (f : Y ⟶ X) (M : X.Modules) [M.IsQuasicoherent]
    (j : pullbackAffineRefinementIndex f) :
    (((pullback f).obj M).restrict
      (pullbackAffineRefinementOpen f j).ι).IsQuasicoherent := by
  letI : IsAffine (pullbackAffineRefinementOpen f j).toScheme :=
    j.2.1
  letI : IsAffine j.1.2.1.toScheme :=
    j.1.2.2
  have hPullback :
      ((pullback (pullbackAffineRefinementHom f j)).obj
        (M.restrict j.1.2.1.ι)).IsQuasicoherent :=
    isQuasicoherent_pullback_of_isAffine
      (pullbackAffineRefinementHom f j)
      (M.restrict j.1.2.1.ι)
  let e :=
    pullbackRestrictIsoOfLE f M j.1.2.1
      (pullbackAffineRefinementOpen f j)
      (pullbackAffineRefinementOpen_le_preimage f j)
  exact
    (isQuasicoherent
      (pullbackAffineRefinementOpen f j).toScheme).prop_of_iso
        e.symm hPullback


-- @@ L102-114 verbatim
private theorem pullbackAffineRefinement_over_isQuasicoherent
    (f : Y ⟶ X) (M : X.Modules) [M.IsQuasicoherent]
    (j : pullbackAffineRefinementIndex f) :
    (((pullback f).obj M).over
      (pullbackAffineRefinementOpen f j)).IsQuasicoherent := by
  letI : IsAffine (pullbackAffineRefinementOpen f j).toScheme :=
    j.2.1
  letI :
      (((pullback f).obj M).restrict
        (pullbackAffineRefinementOpen f j).ι).IsQuasicoherent :=
    pullbackAffineRefinement_restrict_isQuasicoherent f M j
  exact isQuasicoherent_over_of_restrict_of_isAffineOpen
    ((pullback f).obj M) (pullbackAffineRefinementOpen f j)


-- @@ L116-127 verbatim
/-- Pullback along an arbitrary scheme morphism preserves quasicoherence. -/
theorem isQuasicoherent_pullback
    (f : Y ⟶ X) (M : X.Modules) [M.IsQuasicoherent] :
    ((pullback f).obj M).IsQuasicoherent := by
  have hcover : (Opens.grothendieckTopology Y).CoversTop
      (pullbackAffineRefinementOpen f) := by
    rw [Opens.coversTop_iff]
    exact pullbackAffineRefinementOpen_isOpenCover f
  exact @SheafOfModules.IsQuasicoherent.of_coversTop
    _ _ _ _ _ _ _ _ ((pullback f).obj M) _
      (pullbackAffineRefinementOpen f) hcover
      (pullbackAffineRefinement_over_isQuasicoherent f M)


-- @@ L129-135 verbatim
private noncomputable def affineRestrictGeneratingSections
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (U : X.affineOpens) :
    (M.restrict U.1.ι).GeneratingSections :=
  Classical.choose
    (exists_generatingSections_restrict_of_isFiniteType_of_isAffineOpen
      M U)


-- @@ L137-143 verbatim
private theorem affineRestrictGeneratingSections_isFiniteType
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (U : X.affineOpens) :
    (affineRestrictGeneratingSections M U).IsFiniteType :=
  Classical.choose_spec
    (exists_generatingSections_restrict_of_isFiniteType_of_isAffineOpen
      M U)


-- @@ L145-160 verbatim
private noncomputable def pullbackAffineGeneratingSections
    (f : Y ⟶ X) (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType]
    (j : pullbackAffineRefinementIndex f) :
    ((pullback (pullbackAffineRefinementHom f j)).obj
      (M.restrict j.1.2.1.ι)).GeneratingSections := by
  let hPres :
      PreservesColimitsOfSize.{u, u}
        (pullback (pullbackAffineRefinementHom f j)) := by
    infer_instance
  exact
    @SheafOfModules.GeneratingSections.map
      _ _ _ _ _ _ _ _ _ _ _ _ _
      (affineRestrictGeneratingSections M j.1.2)
      (pullback (pullbackAffineRefinementHom f j)) hPres
      (pullbackUnitIso (pullbackAffineRefinementHom f j)).symm


-- @@ L162-170 verbatim
private theorem pullbackAffineGeneratingSections_isFiniteType
    (f : Y ⟶ X) (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType]
    (j : pullbackAffineRefinementIndex f) :
    (pullbackAffineGeneratingSections f M j).IsFiniteType := by
  constructor
  change Finite (affineRestrictGeneratingSections M j.1.2).I
  exact
    (affineRestrictGeneratingSections_isFiniteType M j.1.2).finite


-- @@ L172-182 verbatim
private noncomputable def pullbackRestrictGeneratingSections
    (f : Y ⟶ X) (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType]
    (j : pullbackAffineRefinementIndex f) :
    (((pullback f).obj M).restrict
      (pullbackAffineRefinementOpen f j).ι).GeneratingSections :=
  (SheafOfModules.GeneratingSections.equivOfIso
    (pullbackRestrictIsoOfLE f M j.1.2.1
      (pullbackAffineRefinementOpen f j)
      (pullbackAffineRefinementOpen_le_preimage f j))).symm
        (pullbackAffineGeneratingSections f M j)


-- @@ L184-192 verbatim
private theorem pullbackRestrictGeneratingSections_isFiniteType
    (f : Y ⟶ X) (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType]
    (j : pullbackAffineRefinementIndex f) :
    (pullbackRestrictGeneratingSections f M j).IsFiniteType := by
  constructor
  change Finite (pullbackAffineGeneratingSections f M j).I
  exact
    (pullbackAffineGeneratingSections_isFiniteType f M j).finite


-- @@ L194-206 verbatim
private noncomputable def pullbackLocalGeneratorsData
    (f : Y ⟶ X) (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] :
    ((pullback f).obj M).LocalGeneratorsData :=
  { I := pullbackAffineRefinementIndex f
    X := pullbackAffineRefinementOpen f
    coversTop := by
      rw [Opens.coversTop_iff]
      exact pullbackAffineRefinementOpen_isOpenCover f
    generators := fun j =>
      generatingSectionsOverOfRestrict
        ((pullback f).obj M) (pullbackAffineRefinementOpen f j)
        (pullbackRestrictGeneratingSections f M j) }


-- @@ L208-219 verbatim
private theorem pullbackLocalGeneratorsData_isFiniteType
    (f : Y ⟶ X) (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] :
    (pullbackLocalGeneratorsData f M).IsFiniteType := by
  constructor
  intro j
  letI :
      (pullbackRestrictGeneratingSections f M j).IsFiniteType :=
    pullbackRestrictGeneratingSections_isFiniteType f M j
  exact generatingSectionsOverOfRestrict_isFiniteType
    ((pullback f).obj M) (pullbackAffineRefinementOpen f j)
    (pullbackRestrictGeneratingSections f M j)


-- @@ L221-236 verbatim
/-- Pullback along an arbitrary scheme morphism preserves finite type for a
quasicoherent module. -/
theorem isFiniteType_pullback
    (f : Y ⟶ X) (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] :
    ((pullback f).obj M).IsFiniteType := by
  let q := pullbackLocalGeneratorsData f M
  have hq : q.IsFiniteType :=
    pullbackLocalGeneratorsData_isFiniteType f M
  have hqShrink : q.shrink.IsFiniteType := by
    constructor
    intro j
    dsimp [SheafOfModules.LocalGeneratorsData.shrink]
    exact hq.isFiniteType j.2.choose
  refine { exists_localGeneratorsData := ?_ }
  exact ⟨q.shrink, hqShrink⟩


-- @@ L238-238 verbatim
end


-- @@ L240-240 verbatim
end AlgebraicGeometry.Scheme.Modules
