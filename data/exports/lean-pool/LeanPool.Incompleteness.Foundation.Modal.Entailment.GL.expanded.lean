/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Entailment.K4


-- @@ L10-10 verbatim
/-! # GL -/


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
variable {𝓢 : S} [Entailment.GL 𝓢]


-- @@ L23-32 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def goedel2 :
    Entailment.Prf 𝓢
      (LogicalConnective.iff (Tilde.tilde (Box.box ⊥))
          (Tilde.tilde (Box.box (Tilde.tilde (Box.box ⊥)))) :
        F) :=
  by
  apply negReplaceIff'; apply iffIntro; · apply implyBoxDistribute'; exact efq;
  · exact impTrans'' (by apply implyBoxDistribute'; exact and₁' negEquiv; ) axiomL;


-- @@ L33-36 expanded
omit [DecidableEq F] in
lemma goedel2! :
    Provable 𝓢
      (LogicalConnective.iff (Tilde.tilde (Box.box ⊥))
          (Tilde.tilde (Box.box (Tilde.tilde (Box.box ⊥)))) :
        F) :=
  by classical exact ⟨goedel2⟩


-- @@ L38-41 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Entailment.goedel2'.mp :
    Entailment.Prf 𝓢 (Tilde.tilde (Box.box ⊥) : F) →
      Entailment.Prf 𝓢 (Tilde.tilde (Box.box (Tilde.tilde (Box.box ⊥)) : F)) :=
  by intro h; exact mdp (and₁' goedel2) h;


-- @@ L42-45 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Entailment.goedel2'.mpr :
    Entailment.Prf 𝓢 (Tilde.tilde (Box.box (Tilde.tilde (Box.box ⊥)) : F)) →
      Entailment.Prf 𝓢 (Tilde.tilde (Box.box ⊥) : F) :=
  by intro h; exact mdp (and₂' goedel2) h;


-- @@ L46-50 expanded
omit [DecidableEq F] in
lemma goedel2'! :
    Provable 𝓢 (Tilde.tilde (Box.box ⊥) : F) ↔
      Provable 𝓢 (Tilde.tilde (Box.box (Tilde.tilde (Box.box ⊥)) : F)) :=
  by classical exact ⟨fun ⟨h⟩ ↦ ⟨goedel2'.mp h⟩, fun ⟨h⟩ ↦ ⟨goedel2'.mpr h⟩⟩


-- @@ L53-53 verbatim
namespace GL


-- @@ L55-63 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected def axiomFour : Entailment.Prf 𝓢 (Axioms.Four φ) :=
  by
  dsimp [Axioms.Four];
  have : Entailment.Prf 𝓢 (Arrow.arrow φ (Arrow.arrow (boxdot (Box.box φ)) (boxdot φ))) := by
    apply deduct'; apply deduct;
    exact and₃' (FiniteContext.byAxm) (and₁' (ψ := Box.box (Box.box φ)) <| FiniteContext.byAxm);
  have : Entailment.Prf 𝓢 (Arrow.arrow φ (Arrow.arrow (Box.box (boxdot φ)) (boxdot φ))) :=
    impTrans'' this (implyLeftReplace BoxBoxdotBoxDotbox);
  exact impTrans'' (impTrans'' (implyBoxDistribute' this) axiomL) (implyBoxDistribute' <| and₂);


-- @@ L64-64 verbatim
instance : HasAxiomFour 𝓢 := ⟨fun _ ↦ GL.axiomFour⟩

-- @@ L65-65 verbatim
instance : Entailment.K4 𝓢 where


-- @@ L67-68 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected def axiomH : Entailment.Prf 𝓢 (Axioms.H φ) :=
  impTrans'' (implyBoxDistribute' and₁) axiomL


-- @@ L69-69 verbatim
instance : HasAxiomH 𝓢 := ⟨fun _ ↦ GL.axiomH⟩


-- @@ L71-71 verbatim
end GL


-- @@ L73-86 expanded
/-- The intermediate boxed Grzegorczyk derivation obtained from the Löb principle. -/
noncomputable def lemBoxdotGrzOfL :
    Entailment.Prf 𝓢
      (Arrow.arrow (boxdot (Arrow.arrow (boxdot (Arrow.arrow φ (boxdot φ))) φ))
        (Arrow.arrow (Box.box (Arrow.arrow φ (boxdot φ))) φ)) :=
  by
  have :
    Entailment.Prf 𝓢
      (Arrow.arrow (Wedge.wedge (Box.box (Arrow.arrow φ (boxdot φ))) (Tilde.tilde φ))
        (boxdot (Arrow.arrow φ (boxdot φ)))) :=
    by
    apply deduct'; apply and₃'; · exact mdp (of efqImplyNot₁) and₂;
    · exact mdp (of (impId _)) and₁;
  have :
    Entailment.Prf 𝓢
      (Arrow.arrow (Tilde.tilde (boxdot (Arrow.arrow φ (boxdot φ))))
        (Vee.vee (Tilde.tilde (Box.box (Arrow.arrow φ (boxdot φ)))) φ)) :=
    impTrans'' (contra₀' this) <| impTrans'' demorgan₄ (orReplaceRight dne);
  have :
    Entailment.Prf 𝓢
      (Arrow.arrow (Vee.vee (Tilde.tilde (boxdot (Arrow.arrow φ (boxdot φ)))) φ)
        (Vee.vee (Tilde.tilde (Box.box (Arrow.arrow φ (boxdot φ)))) φ)) :=
    or₃'' this or₂;
  have :
    Entailment.Prf 𝓢
      (Arrow.arrow (Vee.vee (Tilde.tilde (boxdot (Arrow.arrow φ (boxdot φ)))) φ)
        (Arrow.arrow (Box.box (Arrow.arrow φ (boxdot φ))) φ)) :=
    impTrans'' this implyOfNotOr;
  have :
    Entailment.Prf 𝓢
      (Arrow.arrow (Arrow.arrow (boxdot (Arrow.arrow φ (boxdot φ))) φ)
        (Arrow.arrow (Box.box (Arrow.arrow φ (boxdot φ))) φ)) :=
    impTrans'' NotOrOfImply this;
  exact impTrans'' boxdotAxiomT this;


-- @@ L88-100 expanded
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def boxdotGrzOfL :
    Entailment.Prf 𝓢 (Arrow.arrow (boxdot (Arrow.arrow (boxdot (Arrow.arrow φ (boxdot φ))) φ)) φ) :=
  by
  have :
    Entailment.Prf 𝓢
      (Arrow.arrow (Box.box (Arrow.arrow (boxdot (Arrow.arrow φ (boxdot φ))) φ))
        (Arrow.arrow (Box.box (boxdot (Arrow.arrow φ (boxdot φ)))) (Box.box φ))) :=
    axiomK;
  have :
    Entailment.Prf 𝓢
      (Arrow.arrow (Box.box (Arrow.arrow (boxdot (Arrow.arrow φ (boxdot φ))) φ))
        (Arrow.arrow (Box.box (Arrow.arrow φ (boxdot φ))) (Box.box φ))) :=
    impTrans'' this <| implyLeftReplace <| implyBoxBoxBoxdot;
  have :
    Entailment.Prf 𝓢
      (Arrow.arrow (Box.box (Arrow.arrow (boxdot (Arrow.arrow φ (boxdot φ))) φ))
        (Arrow.arrow (Box.box (Arrow.arrow φ (boxdot φ))) (Arrow.arrow φ (boxdot φ)))) :=
    by apply deduct'; apply deduct; apply deduct;
    exact
      and₃' FiniteContext.byAxm <| mdp (mdp (of this) (FiniteContext.byAxm)) (FiniteContext.byAxm);
  have :
    Entailment.Prf 𝓢
      (Arrow.arrow (Box.box (Box.box (Arrow.arrow (boxdot (Arrow.arrow φ (boxdot φ))) φ)))
        (Box.box (Arrow.arrow (Box.box (Arrow.arrow φ (boxdot φ))) (Arrow.arrow φ (boxdot φ))))) :=
    implyBoxDistribute' this;
  have :
    Entailment.Prf 𝓢
      (Arrow.arrow (Box.box (Arrow.arrow (boxdot (Arrow.arrow φ (boxdot φ))) φ))
        (Box.box (Arrow.arrow (Box.box (Arrow.arrow φ (boxdot φ))) (Arrow.arrow φ (boxdot φ))))) :=
    impTrans'' axiomFour this;
  have :
    Entailment.Prf 𝓢
      (Arrow.arrow (Box.box (Arrow.arrow (boxdot (Arrow.arrow φ (boxdot φ))) φ))
        (Box.box (Arrow.arrow φ (boxdot φ)))) :=
    impTrans'' this axiomL;
  have :
    Entailment.Prf 𝓢
      (Arrow.arrow (boxdot (Arrow.arrow (boxdot (Arrow.arrow φ (boxdot φ))) φ))
        (Box.box (Arrow.arrow φ (boxdot φ)))) :=
    impTrans'' boxdotBox this;
  exact mdp₁ lemBoxdotGrzOfL this;


-- @@ L101-104 expanded
omit [DecidableEq F] in
@[simp]
lemma boxdotGrzOfL! :
    Provable 𝓢 (Arrow.arrow (boxdot (Arrow.arrow (boxdot (Arrow.arrow φ (boxdot φ))) φ)) φ) := by
  classical exact ⟨boxdotGrzOfL⟩


-- @@ L107-112 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def implyBoxdotBoxdotOfImplyBoxdotPlain (h : Entailment.Prf 𝓢 (Arrow.arrow (boxdot φ) ψ)) :
    Entailment.Prf 𝓢 (Arrow.arrow (boxdot φ) (boxdot ψ)) := by
  have : Entailment.Prf 𝓢 (Arrow.arrow (Box.box (boxdot φ)) (Box.box ψ)) := implyBoxDistribute' h;
  have : Entailment.Prf 𝓢 (Arrow.arrow (Box.box φ) (Box.box ψ)) :=
    impTrans'' implyBoxBoxBoxdot this;
  have : Entailment.Prf 𝓢 (Arrow.arrow (boxdot φ) (Box.box ψ)) := impTrans'' boxdotBox this;
  exact implyRightAnd h this;


-- @@ L113-117 expanded
omit [DecidableEq F] in
lemma implyBoxdotBoxdotOfImplyBoxdotPlain! (h : Provable 𝓢 (Arrow.arrow (boxdot φ) ψ)) :
    Provable 𝓢 (Arrow.arrow (boxdot φ) (boxdot ψ)) := by
  classical exact ⟨implyBoxdotBoxdotOfImplyBoxdotPlain h.some⟩


-- @@ L120-125 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def implyBoxdotAxiomTOfImplyBoxdotBoxdot
    (h : Entailment.Prf 𝓢 (Arrow.arrow (boxdot φ) (boxdot ψ))) :
    Entailment.Prf 𝓢 (Arrow.arrow (boxdot φ) (Arrow.arrow (Box.box ψ) ψ)) := by apply deduct';
  apply deduct;
  have : Prf 𝓢 [Box.box ψ, boxdot φ] (boxdot ψ) := mdp (FiniteContext.of h) (FiniteContext.byAxm);
  exact and₁' this;


-- @@ L126-130 expanded
omit [DecidableEq F] in
lemma implyBoxdotAxiomTOfImplyBoxdotBoxdot! (h : Provable 𝓢 (Arrow.arrow (boxdot φ) (boxdot ψ))) :
    Provable 𝓢 (Arrow.arrow (boxdot φ) (Arrow.arrow (Box.box ψ) ψ)) := by
  classical exact ⟨implyBoxdotAxiomTOfImplyBoxdotBoxdot h.some⟩


-- @@ L133-137 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def implyBoxBoxOfImplyBoxdotAxiomT
    (h : Entailment.Prf 𝓢 (Arrow.arrow (boxdot φ) (Arrow.arrow (Box.box ψ) ψ))) :
    Entailment.Prf 𝓢 (Arrow.arrow (Box.box φ) (Box.box ψ)) := by
  have :
    Entailment.Prf 𝓢 (Arrow.arrow (Box.box (boxdot φ)) (Box.box (Arrow.arrow (Box.box ψ) ψ))) :=
    implyBoxDistribute' h;
  have : Entailment.Prf 𝓢 (Arrow.arrow (Box.box (boxdot φ)) (Box.box ψ)) := impTrans'' this axiomL;
  exact impTrans'' implyBoxBoxBoxdot this;


-- @@ L138-142 expanded
omit [DecidableEq F] in
lemma implyBoxBoxOfImplyBoxdotAxiomT!
    (h : Provable 𝓢 (Arrow.arrow (boxdot φ) (Arrow.arrow (Box.box ψ) ψ))) :
    Provable 𝓢 (Arrow.arrow (Box.box φ) (Box.box ψ)) := by
  classical exact ⟨implyBoxBoxOfImplyBoxdotAxiomT h.some⟩


-- @@ L145-149 expanded
omit [DecidableEq F] in
lemma imply_box_box_of_imply_boxdot_plain! (h : Provable 𝓢 (Arrow.arrow (boxdot φ) ψ)) :
    Provable 𝓢 (Arrow.arrow (Box.box φ) (Box.box ψ)) := by
  classical
    exact
    implyBoxBoxOfImplyBoxdotAxiomT! <|
      implyBoxdotAxiomTOfImplyBoxdotBoxdot! <| implyBoxdotBoxdotOfImplyBoxdotPlain! h


-- @@ L151-151 verbatim
end Entailment

-- @@ L152-152 verbatim
end LO
