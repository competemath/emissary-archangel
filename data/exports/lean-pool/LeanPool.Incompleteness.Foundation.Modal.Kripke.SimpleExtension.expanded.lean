/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Kripke.Tree
public import Mathlib.Basic.Finite.Sum


-- @@ L11-11 verbatim
/-! # SimpleExtension -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
namespace LO

-- @@ L17-17 verbatim
namespace Modal

-- @@ L18-18 verbatim
namespace Kripke


-- @@ L20-45 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Modal.Kripke.FiniteTransitiveTree.SimpleExtension (F : FiniteTransitiveTree) :
    Kripke.FiniteTransitiveTree where
  World := Unit ⊕ F.World
  Rel x
    y :=
    match x, y with
    | .inr x, .inr y => Frame.Rel' x y
    | .inl _, .inr _ => True
    | _, _ => False
  root := .inl ()
  root_rooted := by intro w;
    match w with
    | .inl _ => simp;
    | .inr x => simp []
  rel_assymetric := by intro x y hxy;
    match x, y with
    | .inl x, _ => simp;
    | .inr x, .inr y => exact F.rel_assymetric hxy;
  rel_transitive := by
    constructor
    intro x y z hxy hyz;
    match x, y, z with
    | .inl _, .inr _, .inr _ => simp;
    | .inr x, .inr y, .inr z => exact F.rel_transitive.trans _ _ _ hxy hyz;


-- @@ L46-47 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
postfix:max "↧" => FiniteTransitiveTree.SimpleExtension



-- @@ L50-50 verbatim
namespace FiniteTransitiveTree

-- @@ L51-51 verbatim
namespace SimpleExtension


-- @@ L53-53 verbatim
variable {T : FiniteTransitiveTree} {x y : T.World}


-- @@ L55-55 expanded
instance : Coe (T.World) ((FiniteTransitiveTree.SimpleExtension T).World) :=
  ⟨Sum.inr⟩


-- @@ L57-57 expanded
@[simp]
lemma root_not_original : (Sum.inr x) ≠ (FiniteTransitiveTree.SimpleExtension T).root := by
  simp [SimpleExtension]


-- @@ L59-59 expanded
lemma root_eq : (Sum.inl ()) = (FiniteTransitiveTree.SimpleExtension T).root := by
  simp [SimpleExtension];


-- @@ L61-61 expanded
lemma forth (h : Frame.Rel' x y) : (FiniteTransitiveTree.SimpleExtension T).Rel x y := by
  simpa [SimpleExtension];


-- @@ L63-70 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def pMorphism : Frame.PseudoEpimorphism T.toFrame ((FiniteTransitiveTree.SimpleExtension T).toFrame)
    where
  toFun x := x
  forth := forth
  back {x y}
    h := by
    match y with
    | .inl r => simp [Frame.Rel', SimpleExtension] at h;
    | .inr y => exact ⟨y, rfl, h⟩;


-- @@ L72-81 expanded
lemma through_original_root {x : (FiniteTransitiveTree.SimpleExtension T).World}
    (h : Frame.Rel' (FiniteTransitiveTree.SimpleExtension T).root x) :
    x = T.root ∨ (Frame.Rel' (Sum.inr T.root) x) := by
  match x with
  | .inl x => have := (FiniteTransitiveTree.SimpleExtension T).rel_irreflexive.irrefl _ h;
    contradiction;
  | .inr x =>
    by_cases h : x = T.root; · subst h; left; tauto;
    · right; exact FiniteTransitiveTree.SimpleExtension.forth <| T.root_rooted x h;


-- @@ L83-83 verbatim
end SimpleExtension

-- @@ L84-84 verbatim
end FiniteTransitiveTree



-- @@ L87-94 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.FiniteTransitiveTreeModel.SimpleExtension
    (M : FiniteTransitiveTreeModel) : Kripke.FiniteTransitiveTreeModel
    where
  toFiniteTransitiveTree := FiniteTransitiveTree.SimpleExtension M.toFiniteTransitiveTree
  Val x
    a :=
    match x with
    | .inl _ => M.Val M.root a
    | .inr x => M.Val x a


-- @@ L95-96 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
postfix:max "↧" => FiniteTransitiveTreeModel.SimpleExtension



-- @@ L99-99 verbatim
namespace FiniteTransitiveTreeModel

-- @@ L100-100 verbatim
namespace SimpleExtension


-- @@ L102-102 verbatim
variable {M : FiniteTransitiveTreeModel}


-- @@ L104-104 expanded
instance : Coe (M.World) ((FiniteTransitiveTree.SimpleExtension M).World) :=
  ⟨Sum.inr⟩


-- @@ L106-109 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def pMorphism :
    Frame.PseudoEpimorphism M.toModel ((FiniteTransitiveTree.SimpleExtension M).toModel) :=
  Model.PseudoEpimorphism.ofAtomic (FiniteTransitiveTree.SimpleExtension.pMorphism) <| by
    simp [FiniteTransitiveTree.SimpleExtension.pMorphism];


-- @@ L111-113 expanded
lemma modal_equivalence_original_world {x : M.toModel.World} :
    ModalEquivalent (M₁ := M.toModel) (M₂ := (FiniteTransitiveTree.SimpleExtension M).toModel) x
      (Sum.inr x) :=
  by apply Model.PseudoEpimorphism.modal_equivalence pMorphism;


-- @@ L115-115 verbatim
end SimpleExtension

-- @@ L116-116 verbatim
end FiniteTransitiveTreeModel



-- @@ L119-119 verbatim
end Kripke

-- @@ L120-120 verbatim
end Modal

-- @@ L121-121 verbatim
end LO
