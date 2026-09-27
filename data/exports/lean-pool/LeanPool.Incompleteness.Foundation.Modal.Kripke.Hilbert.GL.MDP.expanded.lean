/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Mathlib.Basic.Finite.Sum

public import LeanPool.Incompleteness.Foundation.Modal.Hilbert.WellKnown
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.Tree
import LeanPool.Incompleteness.Foundation.Modal.Entailment.GL
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.GL.Tree
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.GL.Unnecessitation


-- @@ L16-16 verbatim
/-! # MDP -/


-- @@ L18-18 verbatim
@[expose] public section



-- @@ L21-21 verbatim
namespace LO

-- @@ L22-22 verbatim
namespace Modal


-- @@ L24-24 verbatim
open Kripke

-- @@ L25-25 verbatim
open Entailment

-- @@ L26-26 verbatim
open Formula.Kripke


-- @@ L28-28 verbatim
namespace Hilbert

-- @@ L29-29 verbatim
namespace GL


-- @@ L31-31 verbatim
namespace Kripke


-- @@ L33-63 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev MDPCounterexampleFrame (F₁ F₂ : FiniteTransitiveTree) : FiniteTransitiveTree
    where
  World := Unit ⊕ F₁.World ⊕ F₂.World
  Rel := fun x y =>
    match x, y with
    | .inr (.inl x), .inr (.inl y) => Frame.Rel' x y
    | .inr (.inr x), .inr (.inr y) => Frame.Rel' x y
    | .inl _, .inl _ => False
    | .inl _, _ => True
    | _, _ => False
  root := .inl PUnit.unit
  root_rooted := by intro x hx;
    match x with
    | .inl x => contradiction;
    | .inr _ => simp [Frame.Rel'];
  rel_assymetric := by intro x y hxy;
    match x, y with
    | .inr (.inl x), .inr (.inl y) => apply F₁.rel_assymetric hxy;
    | .inr (.inr x), .inr (.inr y) => apply F₂.rel_assymetric hxy;
    | .inl x, .inl y => contradiction;
    | .inl x, .inr y => simp;
  rel_transitive := by
    constructor
    intro x y z hxy hyz;
    match x, y, z with
    | .inr (.inl x), .inr (.inl y), .inr (.inl z) => exact F₁.rel_transitive.trans _ _ _ hxy hyz;
    | .inr (.inr x), .inr (.inr y), .inr (.inr z) => exact F₂.rel_transitive.trans _ _ _ hxy hyz;
    | .inl _, .inr (.inr _), .inr (.inr _) => simp;
    | .inl _, .inr (.inl _), .inr (.inl _) => simp;


-- @@ L65-65 verbatim
namespace MDPCounterexampleFrame


-- @@ L67-67 verbatim
variable {F₁ F₂ : FiniteTransitiveTree}


-- @@ L69-69 expanded
instance : Coe (F₁.World) (MDPCounterexampleFrame F₁ F₂).World :=
  ⟨Sum.inr ∘ Sum.inl⟩


-- @@ L70-70 expanded
instance : Coe (F₂.World) (MDPCounterexampleFrame F₁ F₂).World :=
  ⟨Sum.inr ∘ Sum.inr⟩


-- @@ L72-78 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def pMorphism₁ : Frame.PseudoEpimorphism F₁.toFrame (MDPCounterexampleFrame F₁ F₂).toFrame
    where
  toFun x := .inr (.inl x)
  forth := by intro x y hxy; exact hxy;
  back {x y}
    h := by
    match y with
    | .inr (.inl y) => use y;


-- @@ L80-86 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def pMorphism₂ : Frame.PseudoEpimorphism F₂.toFrame (MDPCounterexampleFrame F₁ F₂).toFrame
    where
  toFun x := .inr (.inr x)
  forth := by intro x y hxy; exact hxy;
  back {x y}
    h := by
    match y with
    | .inr (.inr y) => use y;


-- @@ L88-102 expanded
lemma through_original_root {x : (MDPCounterexampleFrame F₁ F₂).World}
    (h : Frame.Rel' (MDPCounterexampleFrame F₁ F₂).root x) :
    (x = F₁.root ∨ (Frame.Rel' (Sum.inr (Sum.inl F₁.root)) x)) ∨
      (x = F₂.root ∨ (Frame.Rel' (Sum.inr (Sum.inr F₂.root)) x)) :=
  by
  match x with
  | .inl x => simp_all
  | .inr (.inl x) =>
    by_cases h : x = F₁.root; · subst h; left; tauto;
    · left; right; exact pMorphism₁.forth <| F₁.root_rooted x h;
  | .inr (.inr x) =>
    by_cases h : x = F₂.root; · subst h; right; tauto;
    · right; right; exact pMorphism₂.forth <| F₂.root_rooted x h;


-- @@ L104-104 verbatim
end MDPCounterexampleFrame


-- @@ L106-114 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev MDPCounterexampleModel (M₁ M₂ : FiniteTransitiveTreeModel) : FiniteTransitiveTreeModel where
  toFiniteTransitiveTree :=
    MDPCounterexampleFrame M₁.toFiniteTransitiveTree M₂.toFiniteTransitiveTree
  Val := fun x a =>
    match x with
    | .inr (.inl x) => M₁.Val x a
    | .inr (.inr x) => M₂.Val x a
    | .inl _ => True


-- @@ L116-116 verbatim
namespace MDPCounterexampleModel


-- @@ L118-118 verbatim
variable {M₁ M₂ : FiniteTransitiveTreeModel}


-- @@ L120-120 expanded
instance : Coe (M₁.World) (MDPCounterexampleModel M₁ M₂).World :=
  ⟨Sum.inr ∘ Sum.inl⟩


-- @@ L121-121 expanded
instance : Coe (M₂.World) (MDPCounterexampleModel M₁ M₂).World :=
  ⟨Sum.inr ∘ Sum.inr⟩


-- @@ L123-126 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def pMorphism₁ : Frame.PseudoEpimorphism M₁.toModel (MDPCounterexampleModel M₁ M₂).toModel :=
  Model.PseudoEpimorphism.ofAtomic (MDPCounterexampleFrame.pMorphism₁) <| by
    simp [MDPCounterexampleFrame.pMorphism₁];


-- @@ L128-130 verbatim
lemma modal_equivalence_original_world₁ {x : M₁.toModel.World} :
    ModalEquivalent (M₁ := M₁.toModel) (M₂ := (MDPCounterexampleModel M₁ M₂).toModel) x x := by
  apply Kripke.Model.PseudoEpimorphism.modal_equivalence pMorphism₁;


-- @@ L132-135 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def pMorphism₂ : Frame.PseudoEpimorphism M₂.toModel (MDPCounterexampleModel M₁ M₂).toModel :=
  Model.PseudoEpimorphism.ofAtomic (MDPCounterexampleFrame.pMorphism₂) <| by
    simp [MDPCounterexampleFrame.pMorphism₂];


-- @@ L137-139 verbatim
lemma modal_equivalence_original_world₂ {x : M₂.toModel.World} :
    ModalEquivalent (M₁ := M₂.toModel) (M₂ := (MDPCounterexampleModel M₁ M₂).toModel) x x := by
  apply Kripke.Model.PseudoEpimorphism.modal_equivalence pMorphism₂;


-- @@ L141-141 verbatim
end MDPCounterexampleModel


-- @@ L143-143 verbatim
end Kripke



-- @@ L146-203 expanded
lemma MDP_Aux (h : Provable Hilbert.GL (Set.box X) (Vee.vee (Box.box φ₁) (Box.box φ₂))) :
    Provable Hilbert.GL (Set.box X) (Box.box φ₁) ∨ Provable Hilbert.GL (Set.box X) (Box.box φ₂) :=
  by
  obtain ⟨Δ, sΓ, hΓ⟩ := Context.provable_iff_boxed.mp h;
  have :
    Provable Hilbert.GL
      (Arrow.arrow (List.conj₂ (List.box Δ)) (Vee.vee (Box.box φ₁) (Box.box φ₂))) :=
    FiniteContext.provable_iff.mp hΓ;
  have :
    Provable Hilbert.GL
      (Arrow.arrow (Box.box (List.conj₂ Δ)) (Vee.vee (Box.box φ₁) (Box.box φ₂))) :=
    imp_trans''! (by simp) this;
  generalize e : List.conj₂ Δ = c at this;
  have :
    Vee.vee (Provable Hilbert.GL (Arrow.arrow (boxdot c) φ₁))
      (Provable Hilbert.GL (Arrow.arrow (boxdot c) φ₂)) :=
    by
    by_contra hC;
    have ⟨h₁, h₂⟩ :
      (Unprovable Hilbert.GL (Arrow.arrow (boxdot c) φ₁)) ∧
        (Unprovable Hilbert.GL (Arrow.arrow (boxdot c) φ₂)) :=
      not_or.mp hC;
    obtain ⟨M₁, hM₁⟩ :=
      Hilbert.GL.Kripke.iff_unprovable_exists_unsatisfies_FiniteTransitiveTree.mp h₁;
    obtain ⟨M₂, hM₂⟩ :=
      Hilbert.GL.Kripke.iff_unprovable_exists_unsatisfies_FiniteTransitiveTree.mp h₂;
    replace hM₁ :=
      @Kripke.MDPCounterexampleModel.modal_equivalence_original_world₁ (M₁ := M₁) (M₂ := M₂) M₁.root
            (Wedge.wedge (boxdot c) (Tilde.tilde φ₁)) |>.mp <|
        Formula.Kripke.Satisfies.not_imp.mp hM₁;
    replace hM₂ :=
      @Kripke.MDPCounterexampleModel.modal_equivalence_original_world₂ (M₁ := M₁) (M₂ := M₂) M₂.root
            (Wedge.wedge (boxdot c) (Tilde.tilde φ₂)) |>.mp <|
        Formula.Kripke.Satisfies.not_imp.mp hM₂;
    let M := Kripke.MDPCounterexampleModel M₁ M₂;
    have hc : Satisfies M.toModel M.root (Box.box c) :=
      by
      intro x Rrx;
      rcases Kripke.MDPCounterexampleFrame.through_original_root Rrx with
        ((rfl | Rrx) | (rfl | Rrx))
      · exact (Satisfies.and_def.mp <| (Satisfies.and_def.mp hM₁).1).1;
      · exact (Satisfies.and_def.mp <| (Satisfies.and_def.mp hM₁).1).2 _ Rrx
      · exact (Satisfies.and_def.mp <| (Satisfies.and_def.mp hM₂).1).1;
      · exact (Satisfies.and_def.mp <| (Satisfies.and_def.mp hM₂).1).2 _ Rrx
    have hp₁ : ¬(Satisfies M.toModel M.root (Box.box φ₁)) :=
      by
      dsimp [Satisfies]; push Not; use .inr (.inl M₁.root); constructor;
      · apply M.root_rooted; simp;
      · exact (Satisfies.and_def.mp hM₁).2;
    have hp₂ : ¬(Satisfies M.toModel M.root (Box.box φ₂)) :=
      by
      dsimp [Satisfies]; push Not; use .inr (.inr M₂.root); constructor;
      · apply M.root_rooted; simp;
      · exact (Satisfies.and_def.mp hM₂).2;
    have : ¬(Satisfies M.toModel M.root (Vee.vee (Box.box φ₁) (Box.box φ₂))) := by
      apply Satisfies.not_def.mpr; apply Satisfies.or_def.not.mpr; push Not; exact ⟨hp₁, hp₂⟩;
    have :
      ¬(Satisfies M.toModel M.root (Arrow.arrow (Box.box c) (Vee.vee (Box.box φ₁) (Box.box φ₂)))) :=
      Classical.not_imp.mpr ⟨hc, this⟩;
    have := Hilbert.GL.Kripke.iff_unprovable_exists_unsatisfies_FiniteTransitiveTree.mpr ⟨M, this⟩;
    contradiction;
  rcases this with (h | h) <;>
    { subst e; have := imply_box_box_of_imply_boxdot_plain! h;
      have := imp_trans''! collect_box_conj! this; have := FiniteContext.provable_iff.mpr this;
      have := Context.provable_iff.mpr <| by use List.box Δ;
      tauto;
    };


-- @@ L205-211 expanded
theorem modal_disjunctive (h : Provable Hilbert.GL (Vee.vee (Box.box φ₁) (Box.box φ₂))) :
    Provable Hilbert.GL φ₁ ∨ Provable Hilbert.GL φ₂ :=
  by
  have : Provable Hilbert.GL ∅ (Box.box φ₁) ∨ Provable Hilbert.GL ∅ (Box.box φ₂) := by
    simpa using MDP_Aux (X := ∅) (φ₁ := φ₁) (φ₂ := φ₂) <| Context.of! h;
  rcases this with (h | h) <;>
    { have := unnec! <| Context.emptyPrf! h; tauto;
    }


-- @@ L213-213 verbatim
end GL

-- @@ L214-214 verbatim
end Hilbert


-- @@ L216-216 verbatim
end Modal

-- @@ L217-217 verbatim
end LO
