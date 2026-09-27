/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Hilbert.WellKnown
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.FiniteFrame
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Geach


-- @@ L12-12 verbatim
/-! # K5 -/


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
abbrev _root_.LO.Modal.Kripke.EuclideanFrameClass : FrameClass := { F | Euclidean F }

-- @@ L25-28 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.EuclideanFiniteFrameClass :
    FiniteFrameClass :=
  { F | Euclidean F.Rel }


-- @@ L30-30 verbatim
namespace Hilbert

-- @@ L31-31 verbatim
namespace K5


-- @@ L33-38 verbatim
instance _root_.LO.Modal.Hilbert.K5.Kripke.sound :
    Sound (Hilbert.K5) (Kripke.EuclideanFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨1, 1, 0, 1⟩})
  · exact eq_Geach
  · unfold EuclideanFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.euclidean_def];


-- @@ L40-42 verbatim
instance _root_.LO.Modal.Hilbert.K5.Kripke.consistent : Entailment.Consistent (Hilbert.K5) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨1, 1, 0, 1⟩});
  exact eq_Geach;


-- @@ L44-49 verbatim
instance _root_.LO.Modal.Hilbert.K5.Kripke.complete :
    Complete (Hilbert.K5) (Kripke.EuclideanFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨1, 1, 0, 1⟩});
  · exact eq_Geach;
  · unfold EuclideanFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.euclidean_def];


-- @@ L51-51 verbatim
end K5

-- @@ L52-52 verbatim
end Hilbert


-- @@ L54-54 verbatim
end Modal

-- @@ L55-55 verbatim
end LO
