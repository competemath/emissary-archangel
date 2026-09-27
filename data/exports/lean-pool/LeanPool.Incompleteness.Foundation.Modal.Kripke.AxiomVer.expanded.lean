/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Kripke.Basic


-- @@ L10-10 verbatim
/-! # AxiomVer -/


-- @@ L12-12 verbatim
@[expose] public section



-- @@ L15-15 verbatim
namespace LO

-- @@ L16-16 verbatim
namespace Modal


-- @@ L18-18 verbatim
open Formula.Kripke


-- @@ L20-20 verbatim
namespace Kripke


-- @@ L22-23 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev IsolatedFrameClass : FrameClass := { F | Isolated F }


-- @@ L25-27 verbatim
instance : IsolatedFrameClass.IsNonempty := by
  use ⟨Unit, fun _ _ => False⟩;
  tauto;


-- @@ L29-39 verbatim
instance _root_.LO.Modal.Kripke.IsolatedFrameClass.DefinedByAxiomVer :
    IsolatedFrameClass.DefinedByFormula (Axioms.Ver (.atom 0)) :=
  FrameClass.definedByFormula_of_iff_mem_validate <| by
  intro F;
  constructor;
  · intro h V x y Rxy;
    have := h Rxy;
    contradiction;
  · intro h x y Rxy;
    have := h (fun _ _ => False) x y Rxy;
    simp [Formula.Kripke.Satisfies] at this;


-- @@ L41-41 verbatim
end Kripke


-- @@ L43-43 verbatim
end Modal

-- @@ L44-44 verbatim
end LO
