/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Hilbert.WellKnown
public import LeanPool.Incompleteness.Foundation.Modal.Entailment.S5
import LeanPool.Incompleteness.Foundation.Modal.Entailment.KTc
import LeanPool.Incompleteness.Foundation.Modal.Entailment.Triv


-- @@ L13-13 verbatim
/-! # S5Grz -/


-- @@ L15-15 verbatim
@[expose] public section



-- @@ L18-18 verbatim
namespace LO

-- @@ L19-19 verbatim
namespace Entailment


-- @@ L21-21 verbatim
variable {S F : Type*} [BasicModalLogicalConnective F] [Entailment F S]

-- @@ L22-22 verbatim
variable {𝓢 : S}



-- @@ L25-25 verbatim
section «lp_section_1»


-- @@ L27-27 verbatim
variable [DecidableEq F]

-- @@ L28-28 verbatim
variable [Entailment.S5 𝓢]


-- @@ L30-33 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def lem₁DiaTOfS5Grz :
    Entailment.Prf 𝓢
      (Arrow.arrow
        (Arrow.arrow (Tilde.tilde (Box.box (Tilde.tilde φ)))
          (Tilde.tilde (Box.box (Tilde.tilde (Box.box φ)))))
        (Arrow.arrow (Dia.dia φ) (Dia.dia (Box.box φ)))) :=
  impTrans'' (revDhypImp' diaDualityMp) (dhypImp' diaDualityMpr)


-- @@ L35-36 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def lem₂DiaTOfS5Grz :
    Entailment.Prf 𝓢
      (Arrow.arrow (Arrow.arrow (Dia.dia φ) (Dia.dia (Box.box φ))) (Arrow.arrow (Dia.dia φ) φ)) :=
  dhypImp' rmDiabox


-- @@ L38-38 verbatim
end «lp_section_1»



-- @@ L41-42 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class S5Grz (𝓢 : S) extends Entailment.S5 𝓢, HasAxiomGrz 𝓢


-- @@ L44-44 verbatim
namespace S5Grz


-- @@ L46-46 verbatim
variable [DecidableEq F]

-- @@ L47-47 verbatim
variable [Entailment.S5Grz 𝓢]


-- @@ L49-61 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected def diaT : Entailment.Prf 𝓢 (Arrow.arrow (Dia.dia φ) φ) := by
  have :
    Entailment.Prf 𝓢
      (Arrow.arrow (Arrow.arrow φ (Box.box φ))
        (Arrow.arrow (Tilde.tilde (Box.box φ)) (Tilde.tilde φ))) :=
    contra₀;
  have :
    Entailment.Prf 𝓢
      (Arrow.arrow (Box.box (Arrow.arrow φ (Box.box φ)))
        (Box.box (Arrow.arrow (Tilde.tilde (Box.box φ)) (Tilde.tilde φ)))) :=
    implyBoxDistribute' this;
  have :
    Entailment.Prf 𝓢
      (Arrow.arrow (Box.box (Arrow.arrow φ (Box.box φ)))
        (Arrow.arrow (Box.box (Tilde.tilde (Box.box φ))) (Box.box (Tilde.tilde φ)))) :=
    impTrans'' this axiomK;
  have :
    Entailment.Prf 𝓢
      (Arrow.arrow (Box.box (Arrow.arrow φ (Box.box φ)))
        (Arrow.arrow (Tilde.tilde (Box.box (Tilde.tilde φ)))
          (Tilde.tilde (Box.box (Tilde.tilde (Box.box φ)))))) :=
    impTrans'' this contra₀;
  have :
    Entailment.Prf 𝓢
      (Arrow.arrow (Box.box (Arrow.arrow φ (Box.box φ)))
        (Arrow.arrow (Dia.dia φ) (Dia.dia (Box.box φ)))) :=
    impTrans'' this lem₁DiaTOfS5Grz;
  have :
    Entailment.Prf 𝓢
      (Arrow.arrow (Box.box (Arrow.arrow φ (Box.box φ))) (Arrow.arrow (Dia.dia φ) (Box.box φ))) :=
    impTrans'' this <| dhypImp' diaboxBox;
  have :
    Entailment.Prf 𝓢
      (Arrow.arrow (Box.box (Arrow.arrow φ (Box.box φ))) (Arrow.arrow (Dia.dia φ) φ)) :=
    impTrans'' this <| dhypImp' axiomT;
  have :
    Entailment.Prf 𝓢
      (Arrow.arrow (Dia.dia φ) (Arrow.arrow (Box.box (Arrow.arrow φ (Box.box φ))) φ)) :=
    impSwap' this;
  have :
    Entailment.Prf 𝓢
      (Arrow.arrow (Box.box (Dia.dia φ))
        (Box.box (Arrow.arrow (Box.box (Arrow.arrow φ (Box.box φ))) φ))) :=
    implyBoxDistribute' this;
  have : Entailment.Prf 𝓢 (Arrow.arrow (Box.box (Dia.dia φ)) φ) := impTrans'' this axiomGrz;
  exact impTrans'' axiomFive this;


-- @@ L63-63 verbatim
instance : HasAxiomDiaT 𝓢 := ⟨fun _ ↦ S5Grz.diaT⟩

-- @@ L64-64 verbatim
instance : Entailment.KTc' 𝓢 where


-- @@ L66-66 verbatim
end S5Grz


-- @@ L68-68 verbatim
end Entailment

-- @@ L69-69 verbatim
end LO



-- @@ L72-72 verbatim
namespace LO

-- @@ L73-73 verbatim
namespace Modal

-- @@ L74-74 verbatim
namespace Hilbert


-- @@ L76-76 verbatim
open Entailment


-- @@ L78-81 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev S5Grz :
    Hilbert ℕ :=
  ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Five (.atom 0), Axioms.Grz (.atom 0)}⟩

-- @@ L82-82 verbatim
instance : (Hilbert.S5Grz).HasK where p := 0; q := 1;

-- @@ L83-83 verbatim
instance : (Hilbert.S5Grz).HasT where p := 0

-- @@ L84-84 verbatim
instance : (Hilbert.S5Grz).HasFive where p := 0

-- @@ L85-85 verbatim
instance : (Hilbert.S5Grz).HasGrz where p := 0

-- @@ L86-86 verbatim
instance : Entailment.S5Grz (Hilbert.S5Grz) where

-- @@ L87-87 verbatim
instance : Entailment.KTc' (Hilbert.S5Grz) where


-- @@ L89-94 expanded
theorem iff_provable_S5Grz_provable_Triv : (Provable Hilbert.S5Grz φ) ↔ (Provable Hilbert.Triv φ) :=
  by
  constructor; · apply fun h ↦ (weakerThan_of_dominate_axioms @h).subset; simp;
  · apply fun h ↦ (weakerThan_of_dominate_axioms @h).subset;
    rintro φ (⟨_, _, rfl⟩ | (⟨_, rfl⟩ | ⟨_, rfl⟩)) <;> simp;


-- @@ L96-96 verbatim
end Hilbert

-- @@ L97-97 verbatim
end Modal

-- @@ L98-98 verbatim
end LO
