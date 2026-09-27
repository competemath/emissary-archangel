/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Entailment.K


-- @@ L10-10 verbatim
/-! # Grz -/


-- @@ L12-12 verbatim
@[expose] public section



-- @@ L15-15 verbatim
namespace LO

-- @@ L16-16 verbatim
namespace Entailment


-- @@ L18-18 verbatim
open FiniteContext


-- @@ L20-20 verbatim
variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]

-- @@ L21-21 verbatim
variable {𝓢 : S} [Entailment.Grz 𝓢]


-- @@ L23-23 verbatim
namespace Grz


-- @@ L25-27 expanded
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def lemmaAxiomFourAxiomT :
    Entailment.Prf 𝓢
      (Arrow.arrow (Box.box φ) (Wedge.wedge φ (Arrow.arrow (Box.box φ) (Box.box (Box.box φ))))) :=
  impTrans'' (lemmaGrz₁ (φ := φ)) axiomGrz


-- @@ L29-31 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected noncomputable def axiomFour :
    Entailment.Prf 𝓢 (Arrow.arrow (Box.box φ) (Box.box (Box.box φ))) :=
  ppq <| impTrans'' lemmaAxiomFourAxiomT and₂


-- @@ L32-32 verbatim
noncomputable instance : HasAxiomFour 𝓢 := ⟨fun _ ↦ Grz.axiomFour⟩


-- @@ L34-35 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected noncomputable def axiomT : Entailment.Prf 𝓢 (Arrow.arrow (Box.box φ) φ) :=
  impTrans'' lemmaAxiomFourAxiomT and₁


-- @@ L36-36 verbatim
noncomputable instance : HasAxiomT 𝓢 := ⟨fun _ ↦ Grz.axiomT⟩


-- @@ L38-38 verbatim
end Grz


-- @@ L40-40 verbatim
end Entailment

-- @@ L41-41 verbatim
end LO
