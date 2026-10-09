import OAI.CategoryTheory.Globular.FrameMaps


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u v w


-- @@ L7-7 verbatim
namespace Grothendieck

-- @@ L8-8 verbatim
open CategoryTheory CategoryTheory.Limits Opposite

-- @@ L9-9 verbatim
namespace GlobularTheory.Model

-- @@ L10-10 verbatim
variable {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q : ℕ)


-- @@ L12-16 verbatim
noncomputable def representables (C : GlobularTheory.{v}) : C.Obj ⥤ C.Model where
  obj S := freeShape C S.shape
  map f := yoneda.map f
  map_id S := yoneda.map_id S
  map_comp f g := yoneda.map_comp f g


-- @@ L18-19 verbatim
noncomputable abbrev cutoffRepresentables : C.Obj ⥤ CutoffModels C q :=
  representables C ⋙ cutoffFunctor hC q


-- @@ L21-32 verbatim
@[reassoc] theorem shapeGlobularEquiv_left {S T : Shape} (f : S ⟶ T)
    (X : C.Model) (a : freeShape C T ⟶ X) :
    shapeGlobularEquiv S X (yoneda.map (C.base f) ≫ a) =
      Shape.liftedRealization.map f ≫ shapeGlobularEquiv T X a := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro x
  change X.eval (C.base (S.cellArrow k x.down)) (yonedaEquiv (yoneda.map (C.base f) ≫ a)) =
    X.eval (C.base (T.cellArrow k (f.app k x.down))) (yonedaEquiv a)
  erw [← yonedaEquiv_naturality, Shape.cellArrow_naturality, C.base_comp, eval_comp]
  rfl


-- @@ L34-43 verbatim
@[reassoc] theorem cutoffShapeEquiv_left {S T : Shape} (f : S ⟶ T)
    (Y : CutoffModels C q) (a : (cutoffRepresentables hC q).obj ⟨T⟩ ⟶ Y) :
    cutoffShapeEquiv hC q S Y ((cutoffRepresentables hC q).map (C.base f) ≫ a) =
      Shape.liftedRealization.map f ≫ cutoffShapeEquiv hC q T Y a := by
  change shapeGlobularEquiv S Y.obj
      ((cutoffAdjunction hC q).homEquiv _ Y ((cutoffFunctor hC q).map (yoneda.map (C.base f)) ≫ a)) =
    Shape.liftedRealization.map f ≫ shapeGlobularEquiv T Y.obj
      ((cutoffAdjunction hC q).homEquiv _ Y a)
  erw [Adjunction.homEquiv_naturality_left]
  exact shapeGlobularEquiv_left f Y.obj _


-- @@ L45-45 verbatim
variable [HasColimitsOfSize.{0,v} (CutoffModels C q)]


-- @@ L47-57 verbatim
@[reassoc] theorem cutoffFrameHomEquiv_left {S T : GlobularPresheaf.{v}} (f : S ⟶ T)
    (Y : CutoffModels C q) (a : (cutoffDiskFrame hC q).realization.obj T ⟶ Y) :
    cutoffFrameHomEquiv hC q S Y ((cutoffDiskFrame hC q).realization.map f ≫ a) =
      f ≫ cutoffFrameHomEquiv hC q T Y a := by
  apply GlobularPresheaf.underlyingMap_injective
  ext j x
  change cutoffCellEquiv hC q Y j ((cutoffDiskFrame hC q).cell S j x ≫
      (cutoffDiskFrame hC q).realization.map f ≫ a) =
    cutoffCellEquiv hC q Y j ((cutoffDiskFrame hC q).cell T j (f.app _ x) ≫ a)
  erw [GlobularFrame.cell_naturality_assoc]
  rfl


-- @@ L59-75 verbatim
noncomputable def shapeFrameIso (S : Shape) :
    (cutoffRepresentables hC q).obj ⟨S⟩ ≅ (cutoffDiskFrame hC q).shapeRealization.obj S := by
  let A := (cutoffRepresentables hC q).obj ⟨S⟩
  let B := (cutoffDiskFrame hC q).shapeRealization.obj S
  let E (Y) := cutoffShapeEquiv hC q S Y
  let G (Y) := cutoffFrameHomEquiv hC q (Shape.liftedRealization.obj S) Y
  let f : A ⟶ B := (E B).symm (G B (𝟙 B))
  let g : B ⟶ A := (G A).symm (E A (𝟙 A))
  have hf : E B f = G B (𝟙 B) := (E B).apply_symm_apply _
  have hg : G A g = E A (𝟙 A) := (G A).apply_symm_apply _
  refine ⟨f,g,?_,?_⟩
  · apply (E A).injective
    erw [cutoffShapeEquiv_naturality, hf, ← cutoffFrameHomEquiv_naturality, Category.id_comp]
    exact hg
  · apply (G B).injective
    erw [cutoffFrameHomEquiv_naturality, hg, ← cutoffShapeEquiv_naturality, Category.id_comp]
    exact hf


-- @@ L77-85 verbatim
@[simp] theorem shapeFrameIso_equiv (S : Shape) {Y : CutoffModels C q}
    (a : (cutoffDiskFrame hC q).shapeRealization.obj S ⟶ Y) :
    cutoffShapeEquiv hC q S Y ((shapeFrameIso hC q S).hom ≫ a) =
      cutoffFrameHomEquiv hC q (Shape.liftedRealization.obj S) Y a := by
  change cutoffShapeEquiv hC q S Y
    ((cutoffShapeEquiv hC q S _).symm (cutoffFrameHomEquiv hC q _ _ (𝟙 _)) ≫ a) = _
  erw [cutoffShapeEquiv_naturality, Equiv.apply_symm_apply,
    ← cutoffFrameHomEquiv_naturality, Category.id_comp]
  rfl


-- @@ L87-103 verbatim
@[reassoc] theorem shapeFrameIso_naturality {S T : Shape} (f : S ⟶ T) :
    (cutoffRepresentables hC q).map (C.base f) ≫ (shapeFrameIso hC q T).hom =
      (shapeFrameIso hC q S).hom ≫ (cutoffDiskFrame hC q).shapeRealization.map f := by
  let D := cutoffDiskFrame hC q
  let Y := D.shapeRealization.obj T
  apply (cutoffShapeEquiv hC q S Y).injective
  have hh : cutoffShapeEquiv hC q T Y (shapeFrameIso hC q T).hom =
      cutoffFrameHomEquiv hC q (Shape.liftedRealization.obj T) Y (𝟙 Y) := by
    have h := shapeFrameIso_equiv hC q T (𝟙 Y)
    erw [Category.comp_id] at h
    exact h
  have hl := cutoffFrameHomEquiv_left hC q (Shape.liftedRealization.map f) Y (𝟙 Y)
  erw [Category.comp_id] at hl
  exact (cutoffShapeEquiv_left hC q f Y _).trans
    ((congrArg (fun g : Shape.liftedRealization.obj T ⟶ (cutoffForgetGlobular C q).obj Y =>
      Shape.liftedRealization.map f ≫ g) hh).trans
        (hl.symm.trans (shapeFrameIso_equiv hC q S (D.shapeRealization.map f)).symm))


-- @@ L105-112 verbatim
omit [HasColimitsOfSize.{0,v} (CutoffModels C q)] in
@[simp] theorem cutoffShapeEquiv_top (Y : CutoffModels C q) (j : ℕ)
    (a : cutoffDisk hC q j ⟶ Y) :
    (cutoffShapeEquiv hC q (Shape.globe j) Y a).app (op (Globe.mk j))
      (ULift.up (ULift.up (𝟙 (Globe.mk j)))) = cutoffCellEquiv hC q Y j a := by
  change Y.obj.eval (C.base ((Shape.globe j).cellArrow _ (ULift.up (𝟙 (Globe.mk j))))) _ = _
  erw [Shape.cellArrow_identity, C.base_id, eval_id]
  rfl


-- @@ L114-126 verbatim
@[simp] theorem shapeFrameIso_globe (j : ℕ) :
    (shapeFrameIso hC q (Shape.globe j)).hom = ((cutoffDiskFrame hC q).shapeGlobeIso j).inv := by
  apply (cutoffCellEquiv hC q _ j).injective
  have hh := shapeFrameIso_equiv hC q (Shape.globe j) (𝟙 _)
  erw [Category.comp_id] at hh
  have e := congrArg (fun f => f.app (op (Globe.mk j))
      (ULift.up (ULift.up (𝟙 (Globe.mk j))))) hh
  erw [cutoffShapeEquiv_top] at e
  change cutoffCellEquiv hC q _ j _ = cutoffCellEquiv hC q _ j
    ((cutoffDiskFrame hC q).cell (Shape.liftedRealization.obj (Shape.globe j)) j
      (ULift.up (ULift.up (𝟙 (Globe.mk j)))) ≫ 𝟙 _) at e
  erw [Category.comp_id, ← GlobularFrame.shapeGlobeIso_inv_cell] at e
  exact e


-- @@ L128-128 verbatim
end GlobularTheory.Model

-- @@ L129-129 verbatim
end Grothendieck


-- @@ L131-131 verbatim
end OAI
