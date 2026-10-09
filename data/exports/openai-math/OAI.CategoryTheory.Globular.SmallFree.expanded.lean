import OAI.CategoryTheory.Globular.Density


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


-- @@ L11-19 verbatim
theorem smallFree_hom_ext {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    {f g : (smallFree hC q).obj S ⟶ Y}
    (h : ∀ k x, (underlyingMap f.hom).app k (smallFreeGen hC q S k x) =
      (underlyingMap g.hom).app k (smallFreeGen hC q S k x)) : f = g := by
  apply ((cutoffGlobularAdjunction hC q).homEquiv _ Y).injective
  apply GlobularPresheaf.underlyingMap_injective
  ext k x
  exact h k x.down


-- @@ L21-25 verbatim
noncomputable def smallShapeDesc {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (S : Shape) {Y : CutoffModels C q}
    (t : Y.obj.presheaf.obj (op (⟨S⟩ : C.Obj))) : (smallFree hC q).obj S.realize ⟶ Y :=
  ((cutoffGlobularAdjunction hC q).homEquiv _ Y).symm
    (shapeGlobularEquiv S Y.obj (Y.obj.tupleMap S t))


-- @@ L27-41 verbatim
@[simp] theorem smallShapeDesc_gen {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (S : Shape) {Y : CutoffModels C q}
    (t : Y.obj.presheaf.obj (op (⟨S⟩ : C.Obj))) (k : ℕ) (x : S.realize.underlying.Cell k) :
    (underlyingMap (smallShapeDesc hC q S t).hom).app k (smallFreeGen hC q S.realize k x) =
      Y.obj.eval (C.base (S.cellArrow (op (Globe.mk k)) x)) t := by
  have h := ((cutoffGlobularAdjunction hC q).homEquiv _ Y).apply_symm_apply
    (shapeGlobularEquiv S Y.obj (Y.obj.tupleMap S t))
  have e := congrFun (congrArg (fun z => (GlobularPresheaf.underlyingMap z).app k) h) (ULift.up x)
  change (underlyingMap (smallShapeDesc hC q S t).hom).app k
    (smallFreeGen hC q S.realize k x) =
    ((Y.obj.tuples.evaluation.app (op S)) (yonedaEquiv (Y.obj.tupleMap S t))).app
      (op (Globe.mk k)) (ULift.up x) at e
  have ht : yonedaEquiv (Y.obj.tupleMap S t) = t := yonedaEquiv.apply_symm_apply t
  erw [ht] at e
  exact e


-- @@ L43-55 verbatim
@[reassoc] theorem smallShapeDesc_naturality {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {S T : Shape} (f : S ⟶ T) {Y : CutoffModels C q}
    (t : Y.obj.presheaf.obj (op (⟨T⟩ : C.Obj))) :
    (smallFree hC q).map (Shape.realization.map f) ≫ smallShapeDesc hC q T t =
      smallShapeDesc hC q S (Y.obj.eval (C.base f) t) := by
  apply smallFree_hom_ext hC q
  intro k x
  change (underlyingMap (smallShapeDesc hC q T t).hom).app k
    ((underlyingMap ((smallFree hC q).map (Shape.realization.map f)).hom).app k
      (smallFreeGen hC q S.realize k x)) = _
  erw [smallFreeGen_map, smallShapeDesc_gen, smallShapeDesc_gen]
  change Y.obj.eval (C.base (T.cellArrow _ (f.app _ x))) t = _
  erw [Shape.cellArrow_naturality, C.base_comp, eval_comp]


-- @@ L57-60 verbatim
noncomputable def smallDiskDesc {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q k : ℕ) {Y : CutoffModels C q} (x : Y.obj.underlying.Cell k) :
    (smallFree hC q).obj (GlobularPresheaf.disk k) ⟶ Y :=
  smallShapeDesc hC q (Shape.globe k) x


-- @@ L62-67 verbatim
@[simp] theorem smallDiskDesc_gen {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q k : ℕ) {Y : CutoffModels C q} (x : Y.obj.underlying.Cell k) :
    (underlyingMap (smallDiskDesc hC q k x).hom).app k
      (smallFreeGen hC q (GlobularPresheaf.disk k) k (ULift.up (𝟙 (Globe.mk k)))) = x := by
  unfold smallDiskDesc
  erw [smallShapeDesc_gen, Shape.cellArrow_identity, C.base_id, eval_id]


-- @@ L69-74 verbatim
theorem smallShape_hasFillers {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (S : Shape) : ((smallFree hC q).obj S.realize).obj.underlying.HasFillers := by
  let e := smallFreeShapeIso hC q S
  apply (cutoff_freeShape_hasFillers C hC S q).retract
    (underlyingMap e.hom.hom) (underlyingMap e.inv.hom)
  exact congrArg (fun z => underlyingMap z.hom) e.hom_inv_id


-- @@ L76-83 verbatim
theorem linearFree_hasFillers {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : Shape) (hS : S.2.height ≤ n+1) :
    ((smallFree hC q).obj ((Shape.linearization n).obj S.realize)).obj.underlying.HasFillers := by
  let d := S.2.linearData n hS
  let e := (smallFree hC q).mapIso d.iso
  apply (smallShape_hasFillers hC q ⟨_,d.table⟩).retract
    (underlyingMap e.hom.hom) (underlyingMap e.inv.hom)
  exact congrArg (fun z => underlyingMap z.hom) e.hom_inv_id


-- @@ L85-85 verbatim
end GlobularTheory.Model

-- @@ L86-86 verbatim
end Grothendieck


-- @@ L88-88 verbatim
end OAI
