/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Logic.HilbertStyle.Supplemental
public import LeanPool.Incompleteness.Foundation.Modal.Entailment.Basic


-- @@ L11-11 verbatim
/-! # Triv -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
namespace LO

-- @@ L17-17 verbatim
namespace Entailment


-- @@ L19-19 verbatim
open FiniteContext


-- @@ L21-21 verbatim
variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]

-- @@ L22-22 verbatim
variable {𝓢 : S} [Entailment.Triv 𝓢]


-- @@ L24-24 verbatim
namespace Triv


-- @@ L26-32 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected def axiomGrz :
    Entailment.Prf 𝓢
      (Arrow.arrow (Box.box (Arrow.arrow (Box.box (Arrow.arrow φ (Box.box φ))) φ)) φ) :=
  by have : Entailment.Prf 𝓢 (Arrow.arrow φ (Box.box φ)) := axiomTc; have d₁ := nec this;
  have d₂ :
    Entailment.Prf 𝓢
      (Arrow.arrow (Box.box (Arrow.arrow φ (Box.box φ)))
        (Arrow.arrow (Arrow.arrow (Box.box (Arrow.arrow φ (Box.box φ))) φ) φ)) :=
    pPqQ;
  have := mdp d₂ d₁; exact impTrans'' axiomT this;


-- @@ L33-33 verbatim
instance : HasAxiomGrz 𝓢 := ⟨fun _ ↦ Triv.axiomGrz⟩


-- @@ L35-35 verbatim
end Triv


-- @@ L37-37 verbatim
end Entailment

-- @@ L38-38 verbatim
end LO
