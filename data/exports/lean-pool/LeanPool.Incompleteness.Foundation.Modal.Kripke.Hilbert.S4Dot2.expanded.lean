/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Hilbert.WellKnown
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.Basic
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Geach


-- @@ L12-12 verbatim
/-! # S4Dot2 -/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-17 verbatim
namespace LO

-- @@ L18-18 verbatim
namespace Modal


-- @@ L20-20 verbatim
open Kripke

-- @@ L21-21 verbatim
open Geachean


-- @@ L23-26 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.ReflexiveTransitiveConfluentFrameClass :
    FrameClass :=
  { F | Std.Refl F ∧ IsTrans F.World F.Rel ∧ Confluent F  }


-- @@ L28-28 verbatim
namespace Hilbert

-- @@ L29-29 verbatim
namespace S4Dot2


-- @@ L31-36 verbatim
instance _root_.LO.Modal.Hilbert.S4Dot2.Kripke.sound :
    Sound (Hilbert.S4Dot2) (ReflexiveTransitiveConfluentFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨1, 1, 1, 1⟩});
  · exact eq_Geach;
  · unfold ReflexiveTransitiveConfluentFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.reflexive_def, Geachean.transitive_def, Geachean.confluent_def];


-- @@ L38-41 verbatim
instance _root_.LO.Modal.Hilbert.S4Dot2.Kripke.consistent :
    Entailment.Consistent (Hilbert.S4Dot2) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨1, 1, 1, 1⟩});
  exact eq_Geach;


-- @@ L43-48 verbatim
instance _root_.LO.Modal.Hilbert.S4Dot2.Kripke.complete :
    Complete (Hilbert.S4Dot2) (ReflexiveTransitiveConfluentFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨1, 1, 1, 1⟩});
  · exact eq_Geach;
  · unfold ReflexiveTransitiveConfluentFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.reflexive_def, Geachean.transitive_def, Geachean.confluent_def];


-- @@ L50-50 verbatim
end S4Dot2

-- @@ L51-51 verbatim
end Hilbert


-- @@ L53-53 verbatim
end Modal

-- @@ L54-54 verbatim
end LO
