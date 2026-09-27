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
/-! # K4 -/


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


-- @@ L24-25 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.TransitiveFrameClass : FrameClass := { F | IsTrans F.World F.Rel }

-- @@ L26-29 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.TransitiveFiniteFrameClass :
    FiniteFrameClass :=
  { F | IsTrans F.World F.Rel }


-- @@ L31-31 verbatim
namespace Hilbert

-- @@ L32-32 verbatim
namespace K4


-- @@ L34-39 verbatim
instance _root_.LO.Modal.Hilbert.K4.Kripke.sound :
    Sound (Hilbert.K4) (Kripke.TransitiveFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 2, 1, 0⟩})
  · exact eq_Geach
  · unfold TransitiveFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.transitive_def];


-- @@ L41-43 verbatim
instance _root_.LO.Modal.Hilbert.K4.Kripke.consistent : Entailment.Consistent (Hilbert.K4) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 2, 1, 0⟩});
  exact eq_Geach;


-- @@ L45-50 verbatim
instance _root_.LO.Modal.Hilbert.K4.Kripke.complete :
    Complete (Hilbert.K4) (Kripke.TransitiveFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 2, 1, 0⟩});
  · exact eq_Geach;
  · unfold TransitiveFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.transitive_def];


-- @@ L52-73 verbatim
open finestFilterationTransitiveClosureModel in
instance _root_.LO.Modal.Hilbert.K4.Kripke.finiteComplete :
    Complete (Hilbert.K4) (TransitiveFiniteFrameClass) :=
  ⟨by
  intro φ hp;
  apply Kripke.complete.complete;
  intro F F_trans V x;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := finestFilterationTransitiveClosureModel M φ.subformulas;
  apply @filteration M φ.subformulas _ FM ?filterOf x φ (by simp) |>.mpr;
  · apply hp (by
      suffices Finite (FilterEqvQuotient M φ.subformulas) by
        simp only [FiniteFrameClass.toFrameClass];
        use ⟨FM.toFrame⟩;
        refine ⟨?_, rfl⟩;
        · exact transitive;
      apply FilterEqvQuotient.finite;
      simp;
    ) FM.Val;
  · apply finestFilterationTransitiveClosureModel.filterOf;
    exact F_trans;
⟩


-- @@ L75-75 verbatim
end K4

-- @@ L76-76 verbatim
end Hilbert


-- @@ L78-78 verbatim
end Modal

-- @@ L79-79 verbatim
end LO
