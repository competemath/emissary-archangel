import OAI.CategoryTheory.Globular.FrameRealization


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u v w


-- @@ L7-7 verbatim
namespace Grothendieck

-- @@ L8-8 verbatim
open CategoryTheory CategoryTheory.Limits Opposite

-- @@ L9-9 verbatim
namespace GlobularPresheaf


-- @@ L11-16 verbatim
def homEquiv (S T : GlobularPresheaf.{v}) :
    (S ⟶ T) ≃ GlobularSet.Hom S.underlying T.underlying where
  toFun := underlyingMap
  invFun f := S.underlyingPresheafIso.inv ≫ f.presheafMap ≫ T.underlyingPresheafIso.hom
  left_inv f := by apply underlyingMap_injective; rfl
  right_inv f := by ext; rfl

-- @@ L17-17 verbatim
end GlobularPresheaf

-- @@ L18-18 verbatim
namespace GlobularFrame

-- @@ L19-19 verbatim
variable {K : Type u} [Category.{v} K] [HasColimitsOfSize.{0,v} K]

-- @@ L20-25 verbatim
noncomputable def realizationHomEquiv (B : GlobularFrame K) (S : GlobularPresheaf.{v}) (Y : K) :
    (B.realization.obj S ⟶ Y) ≃ GlobularSet.Hom S.underlying (B.homGlob Y) where
  toFun := B.realizeHom
  invFun := B.desc
  left_inv := B.desc_realizeHom
  right_inv := B.realizeHom_desc

-- @@ L26-26 verbatim
end GlobularFrame

-- @@ L27-27 verbatim
namespace GlobularTheory.Model

-- @@ L28-28 verbatim
variable {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q : ℕ)


-- @@ L30-32 verbatim
noncomputable def cutoffCellEquiv (Y : CutoffModels C q) (j : ℕ) :
    (cutoffDisk hC q j ⟶ Y) ≃ Y.obj.underlying.Cell j :=
  ((cutoffAdjunction hC q).homEquiv (disk C j) Y).trans (cellEquiv Y.obj j)


-- @@ L34-41 verbatim
@[simp] theorem cutoffCellEquiv_comp {Y Z : CutoffModels C q} (j : ℕ)
    (a : cutoffDisk hC q j ⟶ Y) (f : Y ⟶ Z) :
    cutoffCellEquiv hC q Z j (a ≫ f) =
      (underlyingMap f.hom).app j (cutoffCellEquiv hC q Y j a) := by
  unfold cutoffCellEquiv
  dsimp only [Equiv.trans_apply]
  erw [Adjunction.homEquiv_naturality_right, cellEquiv_comp]
  rfl


-- @@ L43-47 verbatim
@[simp] theorem cutoffDiskFrame_target (j : ℕ) :
    (cutoffDiskFrame hC q).diagram.target j = (cutoffFunctor hC q).map (targetDisk C j) := by
  change (cutoffFunctor hC q).map _ ≫ (cutoffFunctor hC q).map _ = _
  rw [← Functor.map_comp]
  exact congrArg (cutoffFunctor hC q).map (diskFrame_target C j)


-- @@ L49-56 verbatim
@[simp] theorem cutoffCellEquiv_source {Y : CutoffModels C q} (j : ℕ)
    (a : cutoffDisk hC q (j+1) ⟶ Y) :
    cutoffCellEquiv hC q Y j ((cutoffDiskFrame hC q).diagram.source j ≫ a) =
      Y.obj.underlying.source j (cutoffCellEquiv hC q Y (j+1) a) := by
  rw [cutoffDiskFrame_source]
  unfold cutoffCellEquiv cutoffJ
  dsimp only [Equiv.trans_apply]
  erw [Adjunction.homEquiv_naturality_left, cellEquiv_J]


-- @@ L58-65 verbatim
@[simp] theorem cutoffCellEquiv_target {Y : CutoffModels C q} (j : ℕ)
    (a : cutoffDisk hC q (j+1) ⟶ Y) :
    cutoffCellEquiv hC q Y j ((cutoffDiskFrame hC q).diagram.target j ≫ a) =
      Y.obj.underlying.target j (cutoffCellEquiv hC q Y (j+1) a) := by
  rw [cutoffDiskFrame_target]
  unfold cutoffCellEquiv
  dsimp only [Equiv.trans_apply]
  erw [Adjunction.homEquiv_naturality_left, cellEquiv_targetDisk]


-- @@ L67-71 verbatim
noncomputable def cutoffDiskEvaluation (Y : CutoffModels C q) :
    GlobularSet.Hom ((cutoffDiskFrame hC q).homGlob Y) Y.obj.underlying where
  app j := cutoffCellEquiv hC q Y j
  source_app := cutoffCellEquiv_source hC q
  target_app := cutoffCellEquiv_target hC q


-- @@ L73-81 verbatim
noncomputable def cutoffDiskCoevaluation (Y : CutoffModels C q) :
    GlobularSet.Hom Y.obj.underlying ((cutoffDiskFrame hC q).homGlob Y) where
  app j := (cutoffCellEquiv hC q Y j).symm
  source_app j x := by
    apply (cutoffCellEquiv hC q Y j).injective
    erw [Equiv.apply_symm_apply, cutoffCellEquiv_source, Equiv.apply_symm_apply]
  target_app j x := by
    apply (cutoffCellEquiv hC q Y j).injective
    erw [Equiv.apply_symm_apply, cutoffCellEquiv_target, Equiv.apply_symm_apply]


-- @@ L83-89 verbatim
noncomputable def cutoffDiskHomEquiv (S : GlobularSet.{v}) (Y : CutoffModels C q) :
    GlobularSet.Hom S ((cutoffDiskFrame hC q).homGlob Y) ≃
      GlobularSet.Hom S Y.obj.underlying where
  toFun f := f.comp (cutoffDiskEvaluation hC q Y)
  invFun f := f.comp (cutoffDiskCoevaluation hC q Y)
  left_inv f := by ext j x; exact Equiv.symm_apply_apply _ _
  right_inv f := by ext j x; exact Equiv.apply_symm_apply _ _


-- @@ L91-91 verbatim
variable [HasColimitsOfSize.{0,v} (CutoffModels C q)]

-- @@ L92-97 verbatim
noncomputable def cutoffFrameHomEquiv (S : GlobularPresheaf.{v}) (Y : CutoffModels C q) :
    ((cutoffDiskFrame hC q).realization.obj S ⟶ Y) ≃
      (S ⟶ (cutoffForgetGlobular C q).obj Y) :=
  ((cutoffDiskFrame hC q).realizationHomEquiv S Y).trans
    ((cutoffDiskHomEquiv hC q S.underlying Y).trans
      (GlobularPresheaf.homEquiv S ((cutoffForgetGlobular C q).obj Y)).symm)


-- @@ L99-108 verbatim
@[reassoc] theorem cutoffFrameHomEquiv_naturality (S : GlobularPresheaf.{v})
    {Y Z : CutoffModels C q} (a : (cutoffDiskFrame hC q).realization.obj S ⟶ Y) (b : Y ⟶ Z) :
    cutoffFrameHomEquiv hC q S Z (a ≫ b) =
      cutoffFrameHomEquiv hC q S Y a ≫ (cutoffForgetGlobular C q).map b := by
  apply GlobularPresheaf.underlyingMap_injective
  ext j x
  change cutoffCellEquiv hC q Z j ((cutoffDiskFrame hC q).cell S j x ≫ (a ≫ b)) =
    (underlyingMap b.hom).app j
      (cutoffCellEquiv hC q Y j ((cutoffDiskFrame hC q).cell S j x ≫ a))
  erw [← Category.assoc, cutoffCellEquiv_comp]


-- @@ L110-129 verbatim
noncomputable def cutoffFrameFreeIso (S : GlobularPresheaf.{v}) :
    (cutoffFreeGlobular hC q).obj S ≅ (cutoffDiskFrame hC q).realization.obj S := by
  let U := cutoffForgetGlobular C q
  let A := cutoffGlobularAdjunction hC q
  let P := (cutoffDiskFrame hC q).realization.obj S
  let E (Y : CutoffModels C q) := cutoffFrameHomEquiv hC q S Y
  let f := (A.homEquiv S P).symm (E P (𝟙 P))
  let g := (E ((cutoffFreeGlobular hC q).obj S)).symm (A.unit.app S)
  have hf : A.homEquiv S P f = E P (𝟙 P) := (A.homEquiv S P).apply_symm_apply _
  have hg : E ((cutoffFreeGlobular hC q).obj S) g = A.unit.app S := (E _).apply_symm_apply _
  refine ⟨f, g, ?_, ?_⟩
  · apply (A.homEquiv S _).injective
    erw [Adjunction.homEquiv_naturality_right, hf, Adjunction.homEquiv_id]
    change E P (𝟙 P) ≫ U.map g = _
    erw [← cutoffFrameHomEquiv_naturality, Category.id_comp]
    exact hg
  · apply (E P).injective
    change E P (g ≫ f) = E P (𝟙 P)
    erw [cutoffFrameHomEquiv_naturality, hg]
    exact hf


-- @@ L131-135 verbatim
theorem cutoffFrame_cofibrant (S : GlobularPresheaf.{v}) :
    Cofibrant hC q ((cutoffDiskFrame hC q).realization.obj S) := by
  let e := cutoffFrameFreeIso hC q S
  intro P Q p hp f
  exact Cofibrant.retract (cutoffFreeGlobular_cofibrant hC q S) e.inv e.hom e.inv_hom_id p hp f

-- @@ L136-136 verbatim
end GlobularTheory.Model

-- @@ L137-137 verbatim
end Grothendieck


-- @@ L139-139 verbatim
end OAI
