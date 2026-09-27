/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Kripke.AxiomVer
public import LeanPool.Incompleteness.Foundation.Modal.Hilbert.WellKnown
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.Completeness
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Soundness


-- @@ L13-13 verbatim
/-! # Ver -/


-- @@ L15-15 verbatim
@[expose] public section



-- @@ L18-18 verbatim
namespace LO

-- @@ L19-19 verbatim
namespace Modal


-- @@ L21-21 verbatim
open Kripke


-- @@ L23-23 verbatim
namespace Kripke


-- @@ L25-25 verbatim
open Entailment


-- @@ L27-27 verbatim
variable {S} [Entailment (Formula ℕ) S]

-- @@ L28-28 verbatim
variable {𝓢 : S} [Entailment.Consistent 𝓢]


-- @@ L30-34 expanded
instance [Entailment.Ver 𝓢] : Canonical 𝓢 IsolatedFrameClass :=
  ⟨by
    intro x y Rxy;
    have : Realize (canonicalModel 𝓢) (Box.box ⊥) :=
      iff_valid_on_canonicalModel_deducible.mpr axiomVer!
    exact this x _ Rxy; ⟩


-- @@ L36-36 verbatim
end Kripke



-- @@ L39-39 verbatim
namespace Hilbert

-- @@ L40-40 verbatim
namespace Ver


-- @@ L42-44 verbatim
instance _root_.LO.Modal.Hilbert.Ver.Kripke.sound : Sound (Hilbert.Ver) IsolatedFrameClass := by
  have := FrameClass.definedBy_with_axiomK IsolatedFrameClass.DefinedByAxiomVer;
  infer_instance;


-- @@ L46-48 verbatim
instance _root_.LO.Modal.Hilbert.Ver.Kripke.consistent : Entailment.Consistent (Hilbert.Ver) :=
  have := FrameClass.definedBy_with_axiomK IsolatedFrameClass.DefinedByAxiomVer;
  Kripke.Hilbert.consistent_of_FrameClass IsolatedFrameClass


-- @@ L50-51 verbatim
instance _root_.LO.Modal.Hilbert.Ver.Kripke.complete : Complete (Hilbert.Ver) IsolatedFrameClass :=
  inferInstance


-- @@ L53-53 verbatim
end Ver

-- @@ L54-54 verbatim
end Hilbert


-- @@ L56-56 verbatim
end Modal

-- @@ L57-57 verbatim
end LO
