/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Kripke.FiniteFrame
public import LeanPool.Incompleteness.Foundation.Modal.Hilbert.WellKnown
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Filteration
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Geach


-- @@ L13-13 verbatim
/-! # S4 -/


-- @@ L15-15 verbatim
@[expose] public section



-- @@ L18-18 verbatim
namespace LO

-- @@ L19-19 verbatim
namespace Modal


-- @@ L21-21 verbatim
open Kripke

-- @@ L22-22 verbatim
open Geachean


-- @@ L24-26 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.ReflexiveTransitiveFrameClass : FrameClass :=
  { F | Std.Refl F ∧ IsTrans F.World F.Rel }

-- @@ L27-29 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.ReflexiveTransitiveFiniteFrameClass : FiniteFrameClass :=
  { F | Std.Refl F.Rel ∧ IsTrans F.World F.Rel }


-- @@ L31-35 verbatim
instance : ReflexiveTransitiveFrameClass.DefinedBy Hilbert.S4.axioms := by
  convert MultiGeacheanFrameClass.isDefinedByGeachHilbertAxioms {⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩};
  · unfold ReflexiveTransitiveFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.reflexive_def, Geachean.transitive_def];
  · exact Hilbert.S4.eq_Geach;


-- @@ L37-37 verbatim
namespace Hilbert

-- @@ L38-38 verbatim
namespace S4


-- @@ L40-45 verbatim
instance _root_.LO.Modal.Hilbert.S4.Kripke.sound :
    Sound (Hilbert.S4) (Kripke.ReflexiveTransitiveFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩})
  · exact eq_Geach
  · unfold ReflexiveTransitiveFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.reflexive_def, Geachean.transitive_def];


-- @@ L47-49 verbatim
instance _root_.LO.Modal.Hilbert.S4.Kripke.consistent : Entailment.Consistent (Hilbert.S4) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩});
  exact eq_Geach;


-- @@ L51-56 verbatim
instance _root_.LO.Modal.Hilbert.S4.Kripke.complete :
    Complete (Hilbert.S4) (Kripke.ReflexiveTransitiveFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩});
  · exact eq_Geach;
  · unfold ReflexiveTransitiveFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.reflexive_def, Geachean.transitive_def];


-- @@ L58-79 verbatim
open finestFilterationTransitiveClosureModel in
instance _root_.LO.Modal.Hilbert.S4.Kripke.finiteComplete :
    Complete (Hilbert.S4) (ReflexiveTransitiveFiniteFrameClass) :=
  ⟨by
  intro φ hp;
  apply Kripke.complete.complete;
  intro F ⟨F_refl, F_trans⟩ V x;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := finestFilterationTransitiveClosureModel M φ.subformulas;
  apply @filteration M φ.subformulas _ FM ?filterOf x φ (by simp) |>.mpr;
  · apply hp (by
      suffices Finite (FilterEqvQuotient M φ.subformulas) by
        simp only [FiniteFrameClass.toFrameClass];
        use ⟨FM.toFrame⟩;
        refine ⟨⟨?_, transitive⟩, rfl⟩;
        · exact reflexive_of_transitive_reflexive (by apply F_trans) F_refl;
      apply FilterEqvQuotient.finite;
      simp;
    ) FM.Val;
  · apply finestFilterationTransitiveClosureModel.filterOf;
    exact F_trans;
⟩


-- @@ L81-81 verbatim
end S4

-- @@ L82-82 verbatim
end Hilbert


-- @@ L84-84 verbatim
end Modal

-- @@ L85-85 verbatim
end LO
