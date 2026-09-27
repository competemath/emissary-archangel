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
/-! # KB5 -/


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
abbrev _root_.LO.Modal.Kripke.SymmetricEuclideanFrameClass :
    FrameClass :=
  { F | IsSymmetric F ∧ Euclidean F }


-- @@ L28-28 verbatim
namespace Hilbert

-- @@ L29-29 verbatim
namespace KB5


-- @@ L31-36 verbatim
instance _root_.LO.Modal.Hilbert.KB5.Kripke.sound :
    Sound (Hilbert.KB5) (Kripke.SymmetricEuclideanFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 1, 0, 1⟩, ⟨1, 1, 0, 1⟩});
  · exact eq_Geach;
  · unfold SymmetricEuclideanFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.symmetric_def, Geachean.euclidean_def];


-- @@ L38-40 verbatim
instance _root_.LO.Modal.Hilbert.KB5.Kripke.consistent : Entailment.Consistent (Hilbert.KB5) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 1, 0, 1⟩, ⟨1, 1, 0, 1⟩});
  exact eq_Geach;


-- @@ L42-47 verbatim
instance _root_.LO.Modal.Hilbert.KB5.Kripke.complete :
    Complete (Hilbert.KB5) (Kripke.SymmetricEuclideanFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 1, 0, 1⟩, ⟨1, 1, 0, 1⟩});
  · exact eq_Geach;
  · unfold SymmetricEuclideanFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.symmetric_def, Geachean.euclidean_def];


-- @@ L49-49 verbatim
end KB5

-- @@ L50-50 verbatim
end Hilbert


-- @@ L52-52 verbatim
end Modal

-- @@ L53-53 verbatim
end LO
