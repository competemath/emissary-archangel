/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Kripke.AxiomL
public import LeanPool.Incompleteness.Foundation.Modal.Hilbert.WellKnown
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
instance :
    TransitiveIrreflexiveFiniteFrameClass.DefinedBy {Axioms.K (atom 0) (atom 1),
    Axioms.L (atom 0)} :=
  FiniteFrameClass.definedBy_with_axiomK TransitiveIrreflexiveFiniteFrameClass.DefinedByL


-- @@ L33-37 verbatim
instance : TransitiveIrreflexiveFiniteFrameClass.IsNonempty := by
  use ⟨Unit, fun _ _ => False⟩;
  constructor
  · exact ⟨fun _ _ _ h _ => False.elim h⟩
  · exact ⟨fun _ h => h⟩


-- @@ L39-39 verbatim
end Kripke



-- @@ L42-42 verbatim
namespace Hilbert

-- @@ L43-43 verbatim
namespace GL


-- @@ L45-47 verbatim
instance _root_.LO.Modal.Hilbert.GL.Kripke.finiteSound :
    Sound (Hilbert.GL) TransitiveIrreflexiveFiniteFrameClass :=
  inferInstance


-- @@ L49-50 verbatim
instance _root_.LO.Modal.Hilbert.GL.Kripke.consistent : Entailment.Consistent (Hilbert.GL) :=
  Kripke.Hilbert.consistent_of_FiniteFrameClass TransitiveIrreflexiveFiniteFrameClass


-- @@ L52-52 verbatim
end GL

-- @@ L53-53 verbatim
end Hilbert


-- @@ L55-55 verbatim
end Modal

-- @@ L56-56 verbatim
end LO
