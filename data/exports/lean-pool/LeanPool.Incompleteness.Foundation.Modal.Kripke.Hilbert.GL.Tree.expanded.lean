/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Kripke.Tree
public import LeanPool.Incompleteness.Foundation.Modal.Hilbert.WellKnown
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.AxiomL
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.GL.Completeness
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.GL.Soundness


-- @@ L14-14 verbatim
/-! # Tree -/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
namespace LO

-- @@ L20-20 verbatim
namespace Modal


-- @@ L22-22 verbatim
open Kripke

-- @@ L23-23 verbatim
open Entailment

-- @@ L24-24 verbatim
open Formula.Kripke



-- @@ L27-27 verbatim
namespace Kripke


-- @@ L29-29 verbatim
variable (T : Kripke.FiniteTransitiveTree)


-- @@ L31-39 expanded
lemma valid_on_FiniteTransitiveTreeClass_of_valid_on_TransitiveIrreflexiveFrameClass
    (h : Realize Kripke.TransitiveIrreflexiveFiniteFrameClass φ) :
    ∀ T : Kripke.FiniteTransitiveTree, Realize T.toFrame φ :=
  by
  intro T; apply @h T.toFrame; use T.toFiniteFrame; refine ⟨⟨?_, ?_⟩, rfl⟩;
  · exact T.rel_transitive;
  · exact T.rel_irreflexive;


-- @@ L41-45 expanded
lemma satisfies_at_root_on_FiniteTransitiveTree
    (h : ∀ T : FiniteTransitiveTree, Realize T.toFrame φ) :
    ∀ M : FiniteTransitiveTreeModel, Satisfies M.toModel M.root φ := by intro M;
  exact h M.toFiniteTransitiveTree M.Val M.root;


-- @@ L47-57 expanded
open Classical in
lemma valid_on_TransitiveIrreflexiveFrameClass_of_satisfies_at_root_on_FiniteTransitiveTree :
    (∀ M : FiniteTransitiveTreeModel, Satisfies M.toModel M.root φ) →
      Realize TransitiveIrreflexiveFiniteFrameClass φ :=
  by rintro H _ ⟨F, ⟨F_trans, F_irrefl⟩, rfl⟩ V r; let M : Kripke.Model := ⟨F.toFrame, V⟩;
  apply Model.PointGenerated.modal_equivalent_at_root F_trans r |>.mp;
  apply
    Model.TransitiveTreeUnravelling.modal_equivalence_at_root (M :=
        (Frame.PointGenerated M r).toModel) (Frame.PointGenerated.rel_transitive F_trans)
        ⟨r, by tauto⟩ |>.mp;
  exact
    H
      ⟨(F.FiniteTransitiveTreeUnravelling F_trans F_irrefl r),
        (M.FiniteTransitiveTreeUnravelling r).Val⟩;


-- @@ L59-59 verbatim
end Kripke



-- @@ L62-62 verbatim
namespace Hilbert

-- @@ L63-63 verbatim
namespace GL

-- @@ L64-64 verbatim
namespace Kripke


-- @@ L66-77 expanded
theorem iff_provable_satisfies_FiniteTransitiveTree :
    Provable Hilbert.GL φ ↔ (∀ M : FiniteTransitiveTreeModel, Satisfies M.toModel M.root φ) :=
  by
  constructor;
  · intro h M;
    have : Realize TransitiveIrreflexiveFiniteFrameClass φ := Hilbert.GL.Kripke.finiteSound.sound h;
    have := valid_on_FiniteTransitiveTreeClass_of_valid_on_TransitiveIrreflexiveFrameClass this;
    exact satisfies_at_root_on_FiniteTransitiveTree this M;
  · intro h; apply Hilbert.GL.Kripke.finiteComplete.complete; intro F hF V;
    apply
      valid_on_TransitiveIrreflexiveFrameClass_of_satisfies_at_root_on_FiniteTransitiveTree h hF;


-- @@ L79-83 expanded
lemma iff_unprovable_exists_unsatisfies_FiniteTransitiveTree :
    Unprovable Hilbert.GL φ ↔ ∃ M : FiniteTransitiveTreeModel, ¬Satisfies M.toModel M.root φ := by
  apply Iff.not_left; push Not; exact iff_provable_satisfies_FiniteTransitiveTree;


-- @@ L85-85 verbatim
end Kripke

-- @@ L86-86 verbatim
end GL

-- @@ L87-87 verbatim
end Hilbert


-- @@ L89-89 verbatim
end Modal

-- @@ L90-90 verbatim
end LO
