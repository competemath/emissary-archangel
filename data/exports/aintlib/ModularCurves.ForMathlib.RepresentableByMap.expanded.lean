/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.CategoryTheory.Yoneda


-- @@ L8-22 verbatim
/-!
# The morphism of representing objects induced by a natural transformation

`Functor.RepresentableBy F Y` packages a natural bijection `(X ⟶ Y) ≃ F.obj (op X)`.
Mathlib has `RepresentableBy.ofIso` (transport along an isomorphism of functors) and
`RepresentableBy.uniqueUpToIso` (two representing objects are isomorphic), but not the
one-directional statement: a natural transformation `α : F ⟶ G` between representable
functors induces a morphism `YF ⟶ YG` of representing objects.

That is what a level-forgetting map of moduli problems needs — `[Γ(N)] ⟶ [Γ₁(N)]` induces
`Y(N) ⟶ Y₁(N)` — so it is proved here in the general form.

`homEquiv_comp_map` is the characterising property, and the one downstream proofs use:
precomposing with the induced morphism is applying `α`.
-/


-- @@ L24-24 verbatim
universe v u


-- @@ L26-26 verbatim
namespace CategoryTheory.Functor.RepresentableBy


-- @@ L28-28 verbatim
variable {C : Type u} [Category.{v} C] {F G : Cᵒᵖ ⥤ Type v} {YF YG : C}


-- @@ L30-34 verbatim
/-- The morphism of representing objects induced by a natural transformation: apply `α` to
the tautological element and read the result back through `G`'s representation. -/
noncomputable def map (rF : F.RepresentableBy YF) (rG : G.RepresentableBy YG) (α : F ⟶ G) :
    YF ⟶ YG :=
  rG.homEquiv.symm (α.app (Opposite.op YF) (rF.homEquiv (𝟙 YF)))


-- @@ L36-45 verbatim
/-- **The characterising property.** Precomposing with the induced morphism corresponds,
under the two representations, to applying `α`. -/
theorem homEquiv_comp_map (rF : F.RepresentableBy YF) (rG : G.RepresentableBy YG)
    (α : F ⟶ G) {X : C} (f : X ⟶ YF) :
    rG.homEquiv (f ≫ rF.map rG α) = α.app (Opposite.op X) (rF.homEquiv f) := by
  rw [map, rG.comp_homEquiv_symm, Equiv.apply_symm_apply]
  have hnat := NatTrans.naturality_apply α f.op (rF.homEquiv (𝟙 YF))
  have hf : F.map f.op (rF.homEquiv (𝟙 YF)) = rF.homEquiv f := by
    rw [← rF.homEquiv_comp f (𝟙 YF), Category.comp_id]
  rw [← hnat, hf]


-- @@ L47-51 verbatim
/-- The induced morphism sends the tautological element to `α` of it. -/
@[simp] theorem homEquiv_map (rF : F.RepresentableBy YF) (rG : G.RepresentableBy YG)
    (α : F ⟶ G) :
    rG.homEquiv (rF.map rG α) = α.app (Opposite.op YF) (rF.homEquiv (𝟙 YF)) := by
  simpa using homEquiv_comp_map rF rG α (𝟙 YF)


-- @@ L53-57 verbatim
/-- The morphism induced by the identity transformation is the identity. -/
@[simp] theorem map_id (rF : F.RepresentableBy YF) : rF.map rF (𝟙 F) = 𝟙 YF := by
  refine rF.homEquiv.injective ?_
  rw [homEquiv_map]
  rfl


-- @@ L59-59 verbatim
end CategoryTheory.Functor.RepresentableBy
