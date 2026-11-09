/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.ForMathlib.PullbackTensorGeneral
import ModularCurves.ForMathlib.SchemeModuleQuasicoherent
import ModularCurves.ForMathlib.SchemeModuleSupport


-- @@ L10-16 verbatim
/-!
# Quasicoherence after tensoring by an invertible sheaf

An invertible sheaf is trivial on an open cover. Refining that cover by affine
opens identifies the restriction of its tensor product with the restriction of
the other factor, so quasicoherence descends from the affine refinement.
-/


-- @@ L18-18 verbatim
open CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace


-- @@ L20-20 verbatim
universe u


-- @@ L22-22 verbatim
namespace AlgebraicGeometry.Scheme.Modules


-- @@ L24-24 verbatim
noncomputable section


-- @@ L26-26 verbatim
variable {X : Scheme.{u}}


-- @@ L28-30 verbatim
noncomputable local instance invertibleSheafTensorMonoidal
    (Y : Scheme.{u}) : MonoidalCategory Y.Modules :=
  monoidalCategory Y


-- @@ L32-47 verbatim
private noncomputable def tensorRestrictIso
    {M L : X.Modules} (U : X.Opens)
    (eL : L.restrict U.ι ≅ unitObj U.toScheme) :
    (M ⊗ L).restrict U.ι ≅ M.restrict U.ι := by
  letI : (Scheme.Modules.pullback U.ι).Monoidal :=
    pullbackMonoidal U.ι
  exact
    (restrictFunctorIsoPullback U.ι).app (M ⊗ L) ≪≫
      (Functor.Monoidal.μIso
        (Scheme.Modules.pullback U.ι) M L).symm ≪≫
      ((restrictFunctorIsoPullback U.ι).symm.app M ⊗ᵢ
        (restrictFunctorIsoPullback U.ι).symm.app L) ≪≫
      (Iso.refl _ ⊗ᵢ eL) ≪≫
      (Iso.refl _ ⊗ᵢ
        (sheafifyValIso (unitObj U.toScheme)).symm) ≪≫
      ρ_ (M.restrict U.ι)


-- @@ L49-78 verbatim
/-- Tensoring a zero scheme module by an invertible scheme module is zero. -/
theorem IsInvertible.tensorObj_isZero
    {M L : X.Modules} (hL : IsInvertible L) (hM : IsZero M) :
    IsZero (M ⊗ L) := by
  apply isZero_of_forall_underlyingStalk_isZero
  intro x
  obtain ⟨κ, U, hU, htriv⟩ := hL
  have hx : x ∈ ⨆ i, U i := by
    rw [hU]
    trivial
  obtain ⟨i, hxi⟩ :=
    TopologicalSpace.Opens.mem_iSup.mp hx
  let xi : (U i).toScheme := ⟨x, hxi⟩
  obtain ⟨eL⟩ := htriv i
  let eL' : L.restrict (U i).ι ≅ unitObj (U i).toScheme :=
    (restrictFunctorIsoPullback (U i).ι).app L ≪≫ eL
  let e :
      (M ⊗ L).restrict (U i).ι ≅ M.restrict (U i).ι :=
    tensorRestrictIso (M := M) (L := L) (U i) eL'
  have hM' : IsZero (M.restrict (U i).ι) :=
    (restrictFunctor (U i).ι).map_isZero hM
  have hML' : IsZero ((M ⊗ L).restrict (U i).ι) :=
    e.isZero_iff.mpr hM'
  have hStalk' :
      IsZero ((underlyingStalkFunctor xi).obj
        ((M ⊗ L).restrict (U i).ι)) :=
    (underlyingStalkFunctor xi).map_isZero hML'
  exact
    ((restrictStalkNatIso (U i).ι xi).app
      (M ⊗ L)).isZero_iff.mp hStalk'


-- @@ L80-118 verbatim
/-- Tensoring a quasicoherent scheme module by an invertible scheme module
preserves quasicoherence. -/
theorem IsInvertible.tensorObj_isQuasicoherent
    {M L : X.Modules} [M.IsQuasicoherent]
    (hL : IsInvertible L) : (M ⊗ L).IsQuasicoherent := by
  let ML : X.Modules := M ⊗ L
  change ML.IsQuasicoherent
  obtain ⟨κ, V, hV, htriv⟩ := hL
  let J := {x : X.Opens × κ //
    x.1 ∈ X.affineOpens ∧ x.1 ≤ V x.2}
  let W : J → X.Opens := fun j => j.1.1
  have hW : IsOpenCover W :=
    X.isBasis_affineOpens.isOpenCover_mem_and_le
      (show IsOpenCover V from hV)
  have hlocal (j : J) :
      (ML.over (W j)).IsQuasicoherent := by
    letI : IsAffine (W j).toScheme := j.2.1
    obtain ⟨eL⟩ := htriv j.1.2
    let eL' : L.restrict (W j).ι ≅ unitObj (W j).toScheme :=
      restrictIsoOfPullbackIso L (W j)
        (restrictTrivialization j.2.2 eL)
    let e :
        ML.restrict (W j).ι ≅ M.restrict (W j).ι :=
      tensorRestrictIso (M := M) (L := L) (W j) eL'
    have hRestrict :
        (ML.restrict (W j).ι).IsQuasicoherent :=
      (isQuasicoherent (W j).toScheme).prop_of_iso
        e.symm inferInstance
    letI : (ML.restrict (W j).ι).IsQuasicoherent :=
      hRestrict
    exact
      isQuasicoherent_over_of_restrict_of_isAffineOpen
        ML (W j)
  have hcover :
      (Opens.grothendieckTopology X).CoversTop W := by
    rw [Opens.coversTop_iff]
    exact hW
  exact @SheafOfModules.IsQuasicoherent.of_coversTop
    _ _ _ _ _ _ _ _ ML _ W hcover hlocal


-- @@ L120-172 verbatim
/-- Tensoring a finite-type quasicoherent scheme module by an invertible
scheme module preserves finite type. -/
theorem IsInvertible.tensorObj_isFiniteType
    {M L : X.Modules} [M.IsQuasicoherent] [M.IsFiniteType]
    (hL : IsInvertible L) : (M ⊗ L).IsFiniteType := by
  let ML : X.Modules := M ⊗ L
  letI : ML.IsQuasicoherent :=
    hL.tensorObj_isQuasicoherent
  obtain ⟨κ, V, hV, htriv⟩ := hL
  let J := {x : X.Opens × κ //
    x.1 ∈ X.affineOpens ∧ x.1 ≤ V x.2}
  let W : J → X.Opens := fun j => j.1.1
  have hW : IsOpenCover W :=
    X.isBasis_affineOpens.isOpenCover_mem_and_le
      (show IsOpenCover V from hV)
  choose G hG using fun j : J =>
    exists_generatingSections_restrict_of_isFiniteType_of_isAffineOpen
      M ⟨W j, j.2.1⟩
  let e (j : J) : ML.restrict (W j).ι ≅ M.restrict (W j).ι := by
    let eL := Classical.choice (htriv j.1.2)
    let eL' : L.restrict (W j).ι ≅ unitObj (W j).toScheme :=
      restrictIsoOfPullbackIso L (W j)
        (restrictTrivialization j.2.2 eL)
    exact tensorRestrictIso (M := M) (L := L) (W j) eL'
  let GML (j : J) : (ML.restrict (W j).ι).GeneratingSections :=
    (SheafOfModules.GeneratingSections.equivOfIso (e j)).symm (G j)
  have hGML (j : J) : (GML j).IsFiniteType := by
    constructor
    change Finite (G j).I
    exact (hG j).finite
  have hcover :
      (Opens.grothendieckTopology X).CoversTop W := by
    rw [Opens.coversTop_iff]
    exact hW
  let q : ML.LocalGeneratorsData :=
    { I := J
      X := W
      coversTop := hcover
      generators := fun j =>
        generatingSectionsOverOfRestrict ML (W j) (GML j) }
  have hq : q.IsFiniteType := by
    constructor
    intro j
    letI : (GML j).IsFiniteType := hGML j
    exact generatingSectionsOverOfRestrict_isFiniteType
      ML (W j) (GML j)
  have hqShrink : q.shrink.IsFiniteType := by
    constructor
    intro j
    dsimp [SheafOfModules.LocalGeneratorsData.shrink]
    exact hq.isFiniteType j.2.choose
  refine { exists_localGeneratorsData := ?_ }
  exact ⟨q.shrink, hqShrink⟩


-- @@ L174-174 verbatim
end


-- @@ L176-176 verbatim
end AlgebraicGeometry.Scheme.Modules
