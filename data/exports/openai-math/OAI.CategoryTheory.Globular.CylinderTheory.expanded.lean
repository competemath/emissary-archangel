import OAI.CategoryTheory.Globular.ShapeFrame


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u v w


-- @@ L7-7 verbatim
namespace Grothendieck

-- @@ L8-8 verbatim
open CategoryTheory CategoryTheory.Limits Opposite

-- @@ L9-9 verbatim
namespace GlobularFrame

-- @@ L10-10 verbatim
variable {K : Type u} [Category.{v} K] [HasColimitsOfSize.{0,v} K]

-- @@ L11-17 verbatim
theorem shapeRealization_sums (B : GlobularFrame K) (S : Shape) (b h : ℕ)
    (hl : b < S.1) (hr : b < h) :
    IsPushout (B.shapeRealization.map (S.seam hl))
      (B.shapeRealization.map (Shape.face hr false))
      (B.shapeRealization.map (S.inl b h hl hr))
      (B.shapeRealization.map (S.inr b h hl hr)) :=
  (Shape.liftedRealization_pushout S b h hl hr).map B.realization

-- @@ L18-18 verbatim
end GlobularFrame

-- @@ L19-19 verbatim
namespace GlobularTheory.Model

-- @@ L20-20 verbatim
variable {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q n : ℕ)

-- @@ L21-21 verbatim
variable [HasColimitsOfSize.{v,v} (CutoffModels C q)]

-- @@ L22-23 verbatim
local instance smallColimitsTheory : HasColimitsOfSize.{0,v} (CutoffModels C q) :=
  hasColimitsOfSizeShrink.{0,v} (CutoffModels C q)


-- @@ L25-27 verbatim
noncomputable def shapeFrameNatIso :
    C.toTheoryData.arity ⋙ cutoffRepresentables hC q ≅ (cutoffDiskFrame hC q).shapeRealization :=
  NatIso.ofComponents (shapeFrameIso hC q) (fun f => shapeFrameIso_naturality hC q f)


-- @@ L29-31 verbatim
noncomputable def cylinderShapeEndpoint (ε : Bool) :
    C.toTheoryData.arity ⋙ cutoffRepresentables hC q ⟶ (cylinderFrame hC q n).shapeRealization :=
  (shapeFrameNatIso hC q).hom ≫ (cylinderEndpoint hC q n ε).shapeEndpoint


-- @@ L33-39 verbatim
@[reassoc] theorem cylinderShapeEndpoint_globe (ε : Bool) (j : ℕ) :
    (cylinderShapeEndpoint hC q n ε).app (Shape.globe j) ≫
      ((cylinderFrame hC q n).shapeGlobeIso j).hom = (cylinderEndpoint hC q n ε).obj j := by
  change ((shapeFrameIso hC q (Shape.globe j)).hom ≫
    (cylinderEndpoint hC q n ε).shapeEndpoint.app _) ≫ _ = _
  erw [shapeFrameIso_globe, Category.assoc]
  exact GlobularFrame.shapeEndpoint_globe _ _


-- @@ L41-50 verbatim
theorem cutoffRepresentables_sums (S : Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h) :
    IsPushout ((cutoffRepresentables hC q).map (C.base (S.seam hl)))
      ((cutoffRepresentables hC q).map (C.base (Shape.face hr false)))
      ((cutoffRepresentables hC q).map (C.base (S.inl b h hl hr)))
      ((cutoffRepresentables hC q).map (C.base (S.inr b h hl hr))) := by
  exact ((cutoffDiskFrame hC q).shapeRealization_sums S b h hl hr).of_iso'
    (shapeFrameIso hC q (Shape.globe b)) (shapeFrameIso hC q S)
    (shapeFrameIso hC q (Shape.globe h)) (shapeFrameIso hC q (S.attach b h hl hr))
    (shapeFrameIso_naturality hC q _).symm (shapeFrameIso_naturality hC q _).symm
    (shapeFrameIso_naturality hC q _).symm (shapeFrameIso_naturality hC q _).symm


-- @@ L52-55 verbatim
noncomputable abbrev cylinderTheory : GlobularTheory.{v} :=
  representedTheory (cutoffRepresentables hC q) (cylinderFrame hC q n).shapeRealization
    (cylinderShapeEndpoint hC q n false) (cylinderShapeEndpoint hC q n true)
    (cylinderFrame hC q n).shapeRealization_sums (cutoffRepresentables_sums hC q)

-- @@ L56-59 verbatim
noncomputable abbrev cylinderProjection : Morphism (cylinderTheory hC q n) C :=
  representedProjection (cutoffRepresentables hC q) (cylinderFrame hC q n).shapeRealization
    (cylinderShapeEndpoint hC q n false) (cylinderShapeEndpoint hC q n true)
    (cylinderFrame hC q n).shapeRealization_sums (cutoffRepresentables_sums hC q)


-- @@ L61-61 verbatim
end GlobularTheory.Model

-- @@ L62-62 verbatim
end Grothendieck


-- @@ L64-64 verbatim
end OAI
