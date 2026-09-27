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
/-! # K45 -/


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
abbrev _root_.LO.Modal.Kripke.TransitiveEuclideanFrameClass : FrameClass :=
  { F | IsTrans F.World F.Rel ∧ Euclidean F }


-- @@ L27-27 verbatim
namespace Hilbert

-- @@ L28-28 verbatim
namespace K45


-- @@ L30-35 verbatim
instance _root_.LO.Modal.Hilbert.K45.Kripke.sound :
    Sound (Hilbert.K45) (Kripke.TransitiveEuclideanFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 2, 1, 0⟩, ⟨1, 1, 0, 1⟩});
  · exact eq_Geach;
  · unfold TransitiveEuclideanFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.euclidean_def, Geachean.transitive_def];


-- @@ L37-39 verbatim
instance _root_.LO.Modal.Hilbert.K45.Kripke.consistent : Entailment.Consistent (Hilbert.K45) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 2, 1, 0⟩, ⟨1, 1, 0, 1⟩});
  exact eq_Geach;


-- @@ L41-46 verbatim
instance _root_.LO.Modal.Hilbert.K45.Kripke.complete :
    Complete (Hilbert.K45) (Kripke.TransitiveEuclideanFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 2, 1, 0⟩, ⟨1, 1, 0, 1⟩});
  · exact eq_Geach;
  · unfold TransitiveEuclideanFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.euclidean_def, Geachean.transitive_def];


-- @@ L48-48 verbatim
end K45

-- @@ L49-49 verbatim
end Hilbert


-- @@ L51-51 verbatim
end Modal

-- @@ L52-52 verbatim
end LO
