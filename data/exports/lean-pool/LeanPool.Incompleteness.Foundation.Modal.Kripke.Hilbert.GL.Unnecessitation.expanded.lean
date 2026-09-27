/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Hilbert.WellKnown
import LeanPool.Incompleteness.Foundation.Modal.Entailment.K
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.GL.Tree
import LeanPool.Incompleteness.Foundation.Modal.Kripke.SimpleExtension


-- @@ L13-13 verbatim
/-! # Unnecessitation -/


-- @@ L15-15 verbatim
@[expose] public section



-- @@ L18-18 verbatim
namespace LO

-- @@ L19-19 verbatim
namespace Modal


-- @@ L21-21 verbatim
open Entailment

-- @@ L22-22 verbatim
open Kripke

-- @@ L23-23 verbatim
open Formula.Kripke


-- @@ L25-25 verbatim
namespace Hilbert

-- @@ L26-26 verbatim
namespace GL


-- @@ L28-57 expanded
lemma imply_boxdot_plain_of_imply_box_box :
    Provable Hilbert.GL (Arrow.arrow (Box.box φ) (Box.box ψ)) →
      Provable Hilbert.GL (Arrow.arrow (boxdot φ) ψ) :=
  by
  contrapose; intro h; have := Kripke.iff_unprovable_exists_unsatisfies_FiniteTransitiveTree.mp h;
  obtain ⟨M, hs⟩ := this;
  have hs : Satisfies M.toModel M.root (Wedge.wedge (boxdot φ) (Tilde.tilde ψ)) := by
    simp_all [Satisfies];
  replace hs :=
    @FiniteTransitiveTreeModel.SimpleExtension.modal_equivalence_original_world M M.root
        (Wedge.wedge (boxdot φ) (Tilde.tilde ψ)) |>.mp
      hs;
  have ⟨hs₁₂, hs₃⟩ := Satisfies.and_def.mp hs; have ⟨hs₁, hs₂⟩ := Satisfies.and_def.mp hs₁₂;
  have hbp :
    Satisfies (FiniteTransitiveTree.SimpleExtension M).toModel
      ((FiniteTransitiveTree.SimpleExtension M).root) (Box.box φ) :=
    by
    intro x hx;
    rcases
      @Kripke.FiniteTransitiveTree.SimpleExtension.through_original_root M.toFiniteTransitiveTree x
        hx with
      (rfl | hr);
    · assumption;
    · apply hs₂; exact hr;
  have hbq :
    ¬(Satisfies (FiniteTransitiveTree.SimpleExtension M).toModel
        ((FiniteTransitiveTree.SimpleExtension M).root) (Box.box ψ)) :=
    by
    apply Satisfies.box_def.not.mpr; push Not; use M.root; constructor;
    · apply (FiniteTransitiveTree.SimpleExtension M).toRootedFrame.root_rooted M.root;
      simp [FiniteTransitiveTreeModel.SimpleExtension, Kripke.FiniteTransitiveTree.SimpleExtension];
      -- TODO: extract lemma
      
    · assumption;
  apply Kripke.iff_unprovable_exists_unsatisfies_FiniteTransitiveTree.mpr;
  use FiniteTransitiveTree.SimpleExtension M; exact Classical.not_imp.mpr ⟨hbp, hbq⟩;


-- @@ L59-63 expanded
theorem unnecessitation! : Provable Hilbert.GL (Box.box φ) → Provable Hilbert.GL φ := by intro h;
  have : Provable Hilbert.GL (Arrow.arrow (Box.box ⊤) (Box.box φ)) := imply₁'! (ψ := Box.box ⊤) h;
  have : Provable Hilbert.GL (Arrow.arrow (boxdot ⊤) φ) := imply_boxdot_plain_of_imply_box_box this;
  exact mdp this boxdotverum!;


-- @@ L65-66 verbatim
noncomputable instance : Entailment.Unnecessitation Hilbert.GL :=
  ⟨fun h => unnecessitation! ⟨h⟩ |>.some⟩


-- @@ L68-68 verbatim
end GL

-- @@ L69-69 verbatim
end Hilbert


-- @@ L71-71 verbatim
end Modal

-- @@ L72-72 verbatim
end LO
