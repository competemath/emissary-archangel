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
/-! # KB4 -/


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


-- @@ L23-25 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.SymmetricTransitiveFrameClass : FrameClass :=
  { F | IsSymmetric F ∧ IsTrans F.World F.Rel }


-- @@ L27-27 verbatim
namespace Hilbert

-- @@ L28-28 verbatim
namespace KB4


-- @@ L30-35 verbatim
instance _root_.LO.Modal.Hilbert.KB4.Kripke.sound :
    Sound (Hilbert.KB4) (Kripke.SymmetricTransitiveFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 1, 0, 1⟩, ⟨0, 2, 1, 0⟩});
  · exact eq_Geach;
  · unfold SymmetricTransitiveFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.symmetric_def, Geachean.transitive_def];


-- @@ L37-39 verbatim
instance _root_.LO.Modal.Hilbert.KB4.Kripke.consistent : Entailment.Consistent (Hilbert.KB4) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 1, 0, 1⟩, ⟨0, 2, 1, 0⟩});
  exact eq_Geach;


-- @@ L41-46 verbatim
instance _root_.LO.Modal.Hilbert.KB4.Kripke.complete :
    Complete (Hilbert.KB4) (Kripke.SymmetricTransitiveFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 1, 0, 1⟩, ⟨0, 2, 1, 0⟩});
  · exact eq_Geach;
  · unfold SymmetricTransitiveFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.symmetric_def, Geachean.transitive_def];


-- @@ L48-48 verbatim
end KB4

-- @@ L49-49 verbatim
end Hilbert


-- @@ L51-51 verbatim
end Modal

-- @@ L52-52 verbatim
end LO
