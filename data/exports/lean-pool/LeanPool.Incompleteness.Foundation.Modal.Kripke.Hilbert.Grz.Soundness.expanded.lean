/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Hilbert.WellKnown
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.AxiomGrz
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Soundness


-- @@ L12-12 verbatim
/-! # Soundness -/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-17 verbatim
namespace LO

-- @@ L18-18 verbatim
namespace Modal


-- @@ L20-20 verbatim
open Formula

-- @@ L21-21 verbatim
open Formula.Kripke

-- @@ L22-22 verbatim
open Entailment

-- @@ L23-23 verbatim
open Entailment.Context

-- @@ L24-24 verbatim
open Kripke


-- @@ L26-26 verbatim
namespace Kripke


-- @@ L28-31 verbatim
instance : ReflexiveTransitiveAntiSymmetricFiniteFrameClass.DefinedBy {Axioms.K (atom 0) (atom 1),
    Axioms.Grz (atom 0)} :=
  FiniteFrameClass.definedBy_with_axiomK
    ReflexiveTransitiveAntiSymmetricFiniteFrameClass.definedByAxiomGrz


-- @@ L33-39 verbatim
instance : ReflexiveTransitiveAntiSymmetricFiniteFrameClass.IsNonempty := by
  use ⟨Unit, fun _ _ => True⟩;
  constructor
  · exact ⟨fun _ => trivial⟩
  · constructor
    · exact ⟨fun _ _ _ _ _ => trivial⟩
    · exact ⟨fun x y _ _ => by cases x; cases y; rfl⟩


-- @@ L41-41 verbatim
end Kripke


-- @@ L43-43 verbatim
namespace Hilbert

-- @@ L44-44 verbatim
namespace Grz


-- @@ L46-48 verbatim
instance _root_.LO.Modal.Hilbert.Grz.Kripke.sound :
    Sound (Hilbert.Grz) (Kripke.ReflexiveTransitiveAntiSymmetricFiniteFrameClass) :=
  inferInstance


-- @@ L50-51 verbatim
instance _root_.LO.Modal.Hilbert.Grz.Kripke.consistent : Entailment.Consistent (Hilbert.Grz) :=
  Kripke.Hilbert.consistent_of_FiniteFrameClass ReflexiveTransitiveAntiSymmetricFiniteFrameClass


-- @@ L53-53 verbatim
end Grz

-- @@ L54-54 verbatim
end Hilbert


-- @@ L56-56 verbatim
end Modal

-- @@ L57-57 verbatim
end LO
