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
/-! # KB -/


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


-- @@ L23-24 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.SymmetricFrameClass : FrameClass := { F | IsSymmetric F }


-- @@ L26-26 verbatim
namespace Hilbert

-- @@ L27-27 verbatim
namespace KB


-- @@ L29-34 verbatim
instance _root_.LO.Modal.Hilbert.KB.Kripke.sound :
    Sound (Hilbert.KB) (Kripke.SymmetricFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 1, 0, 1⟩});
  · exact eq_Geach;
  · unfold SymmetricFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.symmetric_def];


-- @@ L36-38 verbatim
instance _root_.LO.Modal.Hilbert.KB.Kripke.consistent : Entailment.Consistent (Hilbert.KB) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 1, 0, 1⟩});
  exact eq_Geach;


-- @@ L40-45 verbatim
instance _root_.LO.Modal.Hilbert.KB.Kripke.complete :
    Complete (Hilbert.KB) (Kripke.SymmetricFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 1, 0, 1⟩});
  · exact eq_Geach;
  · unfold SymmetricFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.symmetric_def];


-- @@ L47-47 verbatim
end KB

-- @@ L48-48 verbatim
end Hilbert


-- @@ L50-50 verbatim
end Modal

-- @@ L51-51 verbatim
end LO
