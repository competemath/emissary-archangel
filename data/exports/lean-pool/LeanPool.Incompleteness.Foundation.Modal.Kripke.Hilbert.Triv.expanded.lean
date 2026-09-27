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
/-! # Triv -/


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
abbrev _root_.LO.Modal.Kripke.ReflexiveCoreflexiveFrameClass :
    FrameClass :=
  { F | Std.Refl F.Rel ∧ Coreflexive F }

-- @@ L27-28 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.EqualityFrameClass : FrameClass := { F | Equality F }


-- @@ L30-39 verbatim
lemma _root_.LO.Modal.Kripke.eq_EqualityFrameClass_ReflexiveCoreflexiveFrameClass :
    EqualityFrameClass = ReflexiveCoreflexiveFrameClass := by
  ext F;
  constructor;
  · intro hEq;
    constructor;
    · exact ⟨refl_of_equality hEq⟩;
    · exact corefl_of_equality hEq;
  · rintro ⟨hRefl, hCorefl⟩;
    exact equality_of_refl_corefl hRefl.refl hCorefl;



-- @@ L42-42 verbatim
namespace Hilbert

-- @@ L43-43 verbatim
namespace Triv


-- @@ L45-50 verbatim
instance _root_.LO.Modal.Hilbert.Triv.Kripke.soundReflCorefl :
    Sound (Hilbert.Triv) (Kripke.ReflexiveCoreflexiveFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 0⟩})
  · exact eq_Geach
  · unfold ReflexiveCoreflexiveFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.reflexive_def, Geachean.coreflexive_def];


-- @@ L52-55 verbatim
instance _root_.LO.Modal.Hilbert.Triv.Kripke.soundEquality :
    Sound (Hilbert.Triv) (Kripke.EqualityFrameClass) := by
  rw [eq_EqualityFrameClass_ReflexiveCoreflexiveFrameClass];
  exact Kripke.soundReflCorefl;


-- @@ L57-59 verbatim
instance _root_.LO.Modal.Hilbert.Triv.Kripke.consistent : Entailment.Consistent (Hilbert.Triv) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 0⟩});
  exact eq_Geach;


-- @@ L61-66 verbatim
instance _root_.LO.Modal.Hilbert.Triv.Kripke.completeReflCorefl :
    Complete (Hilbert.Triv) (Kripke.ReflexiveCoreflexiveFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 0⟩});
  · exact eq_Geach;
  · unfold ReflexiveCoreflexiveFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.reflexive_def, Geachean.coreflexive_def];


-- @@ L68-71 verbatim
instance _root_.LO.Modal.Hilbert.Triv.Kripke.completeEquality :
    Complete (Hilbert.Triv) (Kripke.EqualityFrameClass) := by
  rw [eq_EqualityFrameClass_ReflexiveCoreflexiveFrameClass];
  exact Kripke.completeReflCorefl;


-- @@ L73-73 verbatim
end Triv

-- @@ L74-74 verbatim
end Hilbert



-- @@ L77-77 verbatim
end Modal

-- @@ L78-78 verbatim
end LO
