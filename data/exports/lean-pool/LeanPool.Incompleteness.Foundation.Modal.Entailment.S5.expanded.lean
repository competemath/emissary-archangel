/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Entailment.K


-- @@ L10-10 verbatim
/-! # S5 -/


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

-- @@ L21-23 verbatim
variable {𝓢 : S} [Entailment.S5 𝓢]

-- MEMO: need more simple proof

-- @@ L24-36 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def diaboxBox : Entailment.Prf 𝓢 (Arrow.arrow (Dia.dia (Box.box φ)) (Box.box φ)) :=
  by
  have :
    Entailment.Prf 𝓢 (Arrow.arrow (Dia.dia (Tilde.tilde φ)) (Box.box (Dia.dia (Tilde.tilde φ)))) :=
    axiomFive;
  have :
    Entailment.Prf 𝓢
      (Arrow.arrow (Tilde.tilde (Box.box (Dia.dia (Tilde.tilde φ))))
        (Tilde.tilde (Dia.dia (Tilde.tilde φ)))) :=
    contra₀' this;
  have :
    Entailment.Prf 𝓢 (Arrow.arrow (Tilde.tilde (Box.box (Dia.dia (Tilde.tilde φ)))) (Box.box φ)) :=
    impTrans'' this boxDualityMpr;
  refine impTrans'' ?_ this; refine impTrans'' diaDualityMp <| ?_
  apply contra₀'; apply implyBoxDistribute'; refine impTrans'' diaDualityMp ?_; apply contra₀';
  apply implyBoxDistribute'; apply dni;


-- @@ L37-40 expanded
omit [DecidableEq F] in
@[simp]
lemma diaboxBox! : Provable 𝓢 (Arrow.arrow (Dia.dia (Box.box φ)) (Box.box φ)) := by
  classical exact ⟨diaboxBox⟩


-- @@ L42-43 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def diaboxBox' (h : Entailment.Prf 𝓢 (Dia.dia (Box.box φ))) : Entailment.Prf 𝓢 (Box.box φ) :=
  mdp diaboxBox h


-- @@ L44-47 expanded
omit [DecidableEq F] in
lemma diaboxBox'! (h : Provable 𝓢 (Dia.dia (Box.box φ))) : Provable 𝓢 (Box.box φ) := by
  classical exact ⟨diaboxBox' h.some⟩


-- @@ L49-50 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def rmDiabox : Entailment.Prf 𝓢 (Arrow.arrow (Dia.dia (Box.box φ)) φ) :=
  impTrans'' diaboxBox axiomT


-- @@ L51-54 expanded
omit [DecidableEq F] in
@[simp]
lemma rmDiabox! : Provable 𝓢 (Arrow.arrow (Dia.dia (Box.box φ)) φ) := by classical exact ⟨rmDiabox⟩


-- @@ L56-57 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def rmDiabox' (h : Entailment.Prf 𝓢 (Dia.dia (Box.box φ))) : Entailment.Prf 𝓢 φ :=
  mdp rmDiabox h


-- @@ L58-61 expanded
omit [DecidableEq F] in
lemma rmDiabox'! (h : Provable 𝓢 (Dia.dia (Box.box φ))) : Provable 𝓢 φ := by
  classical exact ⟨rmDiabox' h.some⟩


-- @@ L63-63 verbatim
end Entailment

-- @@ L64-64 verbatim
end LO
