/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Entailment.K


-- @@ L10-10 verbatim
/-! # KTc -/


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
variable {𝓢 : S}


-- @@ L23-23 verbatim
namespace KTc


-- @@ L25-25 verbatim
variable [Entailment.KTc 𝓢]


-- @@ L27-28 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected def axiomFour : Entailment.Prf 𝓢 (Axioms.Four φ) :=
  axiomTc


-- @@ L29-29 verbatim
instance : HasAxiomFour 𝓢 := ⟨fun _ ↦ KTc.axiomFour⟩


-- @@ L31-32 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected def axiomFive : Entailment.Prf 𝓢 (Arrow.arrow (Dia.dia φ) (Box.box (Dia.dia φ))) :=
  axiomTc


-- @@ L33-33 verbatim
instance : HasAxiomFive 𝓢 := ⟨fun _ ↦ KTc.axiomFive⟩


-- @@ L35-36 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected def axiomDiaT : Entailment.Prf 𝓢 (Arrow.arrow (Dia.dia φ) φ) :=
  impTrans'' (and₁' diaDuality) (contra₂' axiomTc)


-- @@ L37-37 verbatim
instance : HasAxiomDiaT 𝓢 := ⟨fun _ ↦ KTc.axiomDiaT⟩


-- @@ L39-39 verbatim
end KTc



-- @@ L42-42 verbatim
namespace KTc'


-- @@ L44-44 verbatim
variable [Entailment.KTc' 𝓢]


-- @@ L46-49 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected def axiomTc : Entailment.Prf 𝓢 (Arrow.arrow φ (Box.box φ)) :=
  impTrans'' (contra₃' (impTrans'' (and₂' diaDuality) diaT)) boxDne


-- @@ L50-50 verbatim
instance : HasAxiomTc 𝓢 := ⟨fun _ ↦ KTc'.axiomTc⟩


-- @@ L52-52 verbatim
end KTc'



-- @@ L55-55 verbatim
end Entailment

-- @@ L56-56 verbatim
end LO
