/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Logic.HilbertStyle.Context


-- @@ L10-10 verbatim
/-! # Supplemental -/


-- @@ L12-12 verbatim
@[expose] public section



-- @@ L15-15 verbatim
namespace LO

-- @@ L16-16 verbatim
namespace Entailment


-- @@ L18-22 verbatim
variable {F : Type*} [LogicalConnective F] [DecidableEq F]
         {S : Type*} [Entailment F S]
         {𝓢 : S} [Entailment.Minimal 𝓢]
         {φ ψ χ : F}
         {Γ Δ : List F}


-- @@ L24-24 verbatim
open NegationEquiv

-- @@ L25-25 verbatim
open FiniteContext

-- @@ L26-26 verbatim
open List


-- @@ L28-33 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def mdpIn : Entailment.Prf 𝓢 (Arrow.arrow (Wedge.wedge φ (Arrow.arrow φ ψ)) ψ) := by apply deduct';
  have hp : Prf 𝓢 [φ, Arrow.arrow φ ψ] φ := FiniteContext.byAxm;
  have hpq : Prf 𝓢 [φ, Arrow.arrow φ ψ] (Arrow.arrow φ ψ) := FiniteContext.byAxm; exact mdp hpq hp;


-- @@ L34-37 expanded
omit [DecidableEq F] in
lemma mdpIn! : Provable 𝓢 (Arrow.arrow (Wedge.wedge φ (Arrow.arrow φ ψ)) ψ) := by
  classical exact ⟨mdpIn⟩


-- @@ L39-43 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def botOfMemEither (h₁ : φ ∈ Γ) (h₂ : Tilde.tilde φ ∈ Γ) : Prf 𝓢 Γ ⊥ := by
  have hp : Prf 𝓢 Γ φ := FiniteContext.byAxm h₁;
  have hnp : Prf 𝓢 Γ (Arrow.arrow φ ⊥) := negEquiv'.mp <| FiniteContext.byAxm h₂; exact mdp hnp hp


-- @@ L45-48 expanded
omit [DecidableEq F] in
lemma botOfMemEither! (h₁ : φ ∈ Γ) (h₂ : Tilde.tilde φ ∈ Γ) : Provable 𝓢 Γ ⊥ := by
  classical exact ⟨botOfMemEither h₁ h₂⟩


-- @@ L51-54 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def efqOfMemEither [HasAxiomEFQ 𝓢] (h₁ : φ ∈ Γ) (h₂ : Tilde.tilde φ ∈ Γ) : Prf 𝓢 Γ ψ :=
  efq' <| botOfMemEither h₁ h₂


-- @@ L55-59 expanded
omit [DecidableEq F] in
lemma efqOfMemEither! [HasAxiomEFQ 𝓢] (h₁ : φ ∈ Γ) (h₂ : Tilde.tilde φ ∈ Γ) : Provable 𝓢 Γ ψ := by
  classical exact ⟨efqOfMemEither h₁ h₂⟩


-- @@ L61-63 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def efqImplyNot₁ [HasAxiomEFQ 𝓢] :
    Entailment.Prf 𝓢 (Arrow.arrow (Tilde.tilde φ) (Arrow.arrow φ ψ)) :=
  deduct' <| deduct <| efqOfMemEither (φ := φ) (by simp) (by simp)


-- @@ L64-67 expanded
omit [DecidableEq F] in
@[simp]
lemma efqImplyNot₁! [HasAxiomEFQ 𝓢] : Provable 𝓢 (Arrow.arrow (Tilde.tilde φ) (Arrow.arrow φ ψ)) :=
  by classical exact ⟨efqImplyNot₁⟩


-- @@ L69-71 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def efqImplyNot₂ [HasAxiomEFQ 𝓢] :
    Entailment.Prf 𝓢 (Arrow.arrow φ (Arrow.arrow (Tilde.tilde φ) ψ)) :=
  deduct' <| deduct <| efqOfMemEither (φ := φ) (by simp) (by simp)


-- @@ L72-75 expanded
omit [DecidableEq F] in
@[simp]
lemma efqImplyNot₂! [HasAxiomEFQ 𝓢] : Provable 𝓢 (Arrow.arrow φ (Arrow.arrow (Tilde.tilde φ) ψ)) :=
  by classical exact ⟨efqImplyNot₂⟩


-- @@ L77-83 expanded
omit [DecidableEq F] in
lemma efq_of_neg! [HasAxiomEFQ 𝓢] (h : Provable 𝓢 (Tilde.tilde φ)) : Provable 𝓢 (Arrow.arrow φ ψ) :=
  by
  classical apply provable_iff_provable.mpr; apply deduct_iff.mpr;
  have dnp : Provable 𝓢 [φ] (Arrow.arrow φ ⊥) := of'! <| negEquiv'!.mp h;
  exact efq'! (mdp dnp FiniteContext.id!);


-- @@ L85-88 expanded
omit [DecidableEq F] in
lemma efq_of_neg₂! [HasAxiomEFQ 𝓢] (h : Provable 𝓢 φ) :
    Provable 𝓢 (Arrow.arrow (Tilde.tilde φ) ψ) := by classical exact mdp efqImplyNot₂! h


-- @@ L90-92 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def negMdp (hnp : Entailment.Prf 𝓢 (Tilde.tilde φ)) (hn : Entailment.Prf 𝓢 φ) :
    Entailment.Prf 𝓢 ⊥ :=
  mdp (negEquiv'.mp hnp) hn


-- @@ L94-98 expanded
omit [DecidableEq F] in
lemma negMdp! (hnp : Provable 𝓢 (Tilde.tilde φ)) (hn : Provable 𝓢 φ) : Provable 𝓢 ⊥ := by
  classical
    exact
    ⟨negMdp hnp.some hn.some⟩
      -- infixl:90 "⨀" => negMdp!


-- @@ L100-103 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def dneOr [HasAxiomDNE 𝓢]
    (d : Entailment.Prf 𝓢 (Vee.vee (Tilde.tilde (Tilde.tilde φ)) (Tilde.tilde (Tilde.tilde ψ)))) :
    Entailment.Prf 𝓢 (Vee.vee φ ψ) :=
  or₃''' (impTrans'' dne or₁) (impTrans'' dne or₂) d


-- @@ L104-107 expanded
omit [DecidableEq F] in
lemma dne_or! [HasAxiomDNE 𝓢]
    (d : Provable 𝓢 (Vee.vee (Tilde.tilde (Tilde.tilde φ)) (Tilde.tilde (Tilde.tilde ψ)))) :
    Provable 𝓢 (Vee.vee φ ψ) := by classical exact ⟨dneOr d.some⟩


-- @@ L109-111 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def implyLeftOr' (h : Entailment.Prf 𝓢 (Arrow.arrow φ χ)) :
    Entailment.Prf 𝓢 (Arrow.arrow φ (Vee.vee χ ψ)) :=
  deduct' <| or₁' <| deductInv <| of h


-- @@ L112-115 expanded
omit [DecidableEq F] in
lemma imply_left_or'! (h : Provable 𝓢 (Arrow.arrow φ χ)) :
    Provable 𝓢 (Arrow.arrow φ (Vee.vee χ ψ)) := by classical exact ⟨implyLeftOr' h.some⟩


-- @@ L117-119 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def implyRightOr' (h : Entailment.Prf 𝓢 (Arrow.arrow ψ χ)) :
    Entailment.Prf 𝓢 (Arrow.arrow ψ (Vee.vee φ χ)) :=
  deduct' <| or₂' <| deductInv <| of h


-- @@ L120-123 expanded
omit [DecidableEq F] in
lemma imply_right_or'! (h : Provable 𝓢 (Arrow.arrow ψ χ)) :
    Provable 𝓢 (Arrow.arrow ψ (Vee.vee φ χ)) := by classical exact ⟨implyRightOr' h.some⟩


-- @@ L126-131 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def implyRightAnd (hq : Entailment.Prf 𝓢 (Arrow.arrow φ ψ))
    (hr : Entailment.Prf 𝓢 (Arrow.arrow φ χ)) :
    Entailment.Prf 𝓢 (Arrow.arrow φ (Wedge.wedge ψ χ)) := by apply deduct';
  replace hq : Prf 𝓢 [] (Arrow.arrow φ ψ) := of hq;
  replace hr : Prf 𝓢 [] (Arrow.arrow φ χ) := of hr;
  exact and₃' (mdp' hq FiniteContext.id) (mdp' hr FiniteContext.id)


-- @@ L132-136 expanded
omit [DecidableEq F] in
lemma imply_right_and! (hq : Provable 𝓢 (Arrow.arrow φ ψ)) (hr : Provable 𝓢 (Arrow.arrow φ χ)) :
    Provable 𝓢 (Arrow.arrow φ (Wedge.wedge ψ χ)) := by
  classical exact ⟨implyRightAnd hq.some hr.some⟩


-- @@ L138-141 expanded
omit [DecidableEq F] in
lemma imply_left_and_comm'! (d : Provable 𝓢 (Arrow.arrow (Wedge.wedge φ ψ) χ)) :
    Provable 𝓢 (Arrow.arrow (Wedge.wedge ψ φ) χ) := by classical exact imp_trans''! and_comm! d


-- @@ L143-148 expanded
omit [DecidableEq F] in
lemma dhyp_and_left! (h : Provable 𝓢 (Arrow.arrow φ χ)) :
    Provable 𝓢 (Arrow.arrow (Wedge.wedge ψ φ) χ) := by
  classical apply and_imply_iff_imply_imply'!.mpr; apply deduct'!;
  exact FiniteContext.of'! (Γ := [ψ]) h;


-- @@ L150-154 expanded
omit [DecidableEq F] in
lemma dhyp_and_right! (h : Provable 𝓢 (Arrow.arrow φ χ)) :
    Provable 𝓢 (Arrow.arrow (Wedge.wedge φ ψ) χ) := by
  classical exact imp_trans''! and_comm! (dhyp_and_left! h)


-- @@ L156-161 expanded
omit [DecidableEq F] in
lemma cut! (d₁ : Provable 𝓢 (Arrow.arrow (Wedge.wedge φ₁ c) ψ₁))
    (d₂ : Provable 𝓢 (Arrow.arrow φ₂ (Vee.vee c ψ₂))) :
    Provable 𝓢 (Arrow.arrow (Wedge.wedge φ₁ φ₂) (Vee.vee ψ₁ ψ₂)) := by
  classical apply deduct'!;
  exact
    or₃'''! (imply_left_or'! <| mdp (of'! (and_imply_iff_imply_imply'!.mp d₁)) (and₁'! id!)) or₂!
      (mdp (of'! d₂) (and₂'! id!));


-- @@ L164-166 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def orComm : Entailment.Prf 𝓢 (Arrow.arrow (Vee.vee φ ψ) (Vee.vee ψ φ)) :=
  deduct' <| or₃''' or₂ or₁ FiniteContext.id


-- @@ L167-170 expanded
omit [DecidableEq F] in
lemma or_comm! : Provable 𝓢 (Arrow.arrow (Vee.vee φ ψ) (Vee.vee ψ φ)) := by classical exact ⟨orComm⟩


-- @@ L172-173 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def orComm' (h : Entailment.Prf 𝓢 (Vee.vee φ ψ)) : Entailment.Prf 𝓢 (Vee.vee ψ φ) :=
  mdp orComm h


-- @@ L174-177 expanded
omit [DecidableEq F] in
lemma or_comm'! (h : Provable 𝓢 (Vee.vee φ ψ)) : Provable 𝓢 (Vee.vee ψ φ) := by
  classical exact ⟨orComm' h.some⟩


-- @@ L180-201 expanded
omit [DecidableEq F] in
lemma or_assoc'! : Provable 𝓢 (Vee.vee φ (Vee.vee ψ χ)) ↔ Provable 𝓢 (Vee.vee (Vee.vee φ ψ) χ) := by
  classical
  constructor;
  · intro h;
    exact
      or₃'''! (imply_left_or'! <| imply_left_or'! imp_id!)
        (by apply provable_iff_provable.mpr; apply deduct_iff.mpr;
          exact
            or₃'''! (imply_left_or'! <| imply_right_or'! imp_id!) (imply_right_or'! imp_id!) id!;
          )
        h;
  · intro h;
    exact
      or₃'''!
        (by apply provable_iff_provable.mpr; apply deduct_iff.mpr;
          exact or₃'''! (imply_left_or'! imp_id!) (imply_right_or'! <| imply_left_or'! imp_id!) id!;
          )
        (imply_right_or'! <| imply_right_or'! imp_id!) h;


-- @@ L204-219 expanded
omit [DecidableEq F] in
lemma and_assoc! :
    Provable 𝓢
      (LogicalConnective.iff (Wedge.wedge (Wedge.wedge φ ψ) χ) (Wedge.wedge φ (Wedge.wedge ψ χ))) :=
  by
  classical
  apply iff_intro!;
  · apply FiniteContext.deduct'!;
    have hp : Provable 𝓢 [Wedge.wedge (Wedge.wedge φ ψ) χ] φ := and₁'! <| and₁'! id!;
    have hq : Provable 𝓢 [Wedge.wedge (Wedge.wedge φ ψ) χ] ψ := and₂'! <| and₁'! id!;
    have hr : Provable 𝓢 [Wedge.wedge (Wedge.wedge φ ψ) χ] χ := and₂'! id!;
    exact and₃'! hp (and₃'! hq hr);
  · apply FiniteContext.deduct'!;
    have hp : Provable 𝓢 [Wedge.wedge φ (Wedge.wedge ψ χ)] φ := and₁'! id!;
    have hq : Provable 𝓢 [Wedge.wedge φ (Wedge.wedge ψ χ)] ψ := and₁'! <| and₂'! id!;
    have hr : Provable 𝓢 [Wedge.wedge φ (Wedge.wedge ψ χ)] χ := and₂'! <| and₂'! id!; apply and₃'!;
    · exact and₃'! hp hq;
    · exact hr;


-- @@ L221-224 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def andReplaceLeft' (hc : Entailment.Prf 𝓢 (Wedge.wedge φ ψ))
    (h : Entailment.Prf 𝓢 (Arrow.arrow φ χ)) : Entailment.Prf 𝓢 (Wedge.wedge χ ψ) :=
  and₃' (mdp h (and₁' hc)) (and₂' hc)


-- @@ L225-229 expanded
omit [DecidableEq F] in
lemma and_replace_left'! (hc : Provable 𝓢 (Wedge.wedge φ ψ)) (h : Provable 𝓢 (Arrow.arrow φ χ)) :
    Provable 𝓢 (Wedge.wedge χ ψ) := by classical exact ⟨andReplaceLeft' hc.some h.some⟩


-- @@ L231-233 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def andReplaceLeft (h : Entailment.Prf 𝓢 (Arrow.arrow φ χ)) :
    Entailment.Prf 𝓢 (Arrow.arrow (Wedge.wedge φ ψ) (Wedge.wedge χ ψ)) :=
  deduct' <| andReplaceLeft' FiniteContext.id (of h)


-- @@ L234-237 expanded
omit [DecidableEq F] in
lemma and_replace_left! (h : Provable 𝓢 (Arrow.arrow φ χ)) :
    Provable 𝓢 (Arrow.arrow (Wedge.wedge φ ψ) (Wedge.wedge χ ψ)) := by
  classical exact ⟨andReplaceLeft h.some⟩


-- @@ L240-243 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def andReplaceRight' (hc : Entailment.Prf 𝓢 (Wedge.wedge φ ψ))
    (h : Entailment.Prf 𝓢 (Arrow.arrow ψ χ)) : Entailment.Prf 𝓢 (Wedge.wedge φ χ) :=
  and₃' (and₁' hc) (mdp h (and₂' hc))


-- @@ L244-247 expanded
omit [DecidableEq F] in
lemma andReplaceRight'! (hc : Provable 𝓢 (Wedge.wedge φ ψ)) (h : Provable 𝓢 (Arrow.arrow ψ χ)) :
    Provable 𝓢 (Wedge.wedge φ χ) := by classical exact ⟨andReplaceRight' hc.some h.some⟩


-- @@ L249-251 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def andReplaceRight (h : Entailment.Prf 𝓢 (Arrow.arrow ψ χ)) :
    Entailment.Prf 𝓢 (Arrow.arrow (Wedge.wedge φ ψ) (Wedge.wedge φ χ)) :=
  deduct' <| andReplaceRight' FiniteContext.id (of h)


-- @@ L252-255 expanded
omit [DecidableEq F] in
lemma and_replace_right! (h : Provable 𝓢 (Arrow.arrow ψ χ)) :
    Provable 𝓢 (Arrow.arrow (Wedge.wedge φ ψ) (Wedge.wedge φ χ)) := by
  classical exact ⟨andReplaceRight h.some⟩


-- @@ L258-261 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def andReplace' (hc : Entailment.Prf 𝓢 (Wedge.wedge φ ψ)) (h₁ : Entailment.Prf 𝓢 (Arrow.arrow φ χ))
    (h₂ : Entailment.Prf 𝓢 (Arrow.arrow ψ s)) : Entailment.Prf 𝓢 (Wedge.wedge χ s) :=
  andReplaceRight' (andReplaceLeft' hc h₁) h₂


-- @@ L262-266 expanded
omit [DecidableEq F] in
lemma and_replace'! (hc : Provable 𝓢 (Wedge.wedge φ ψ)) (h₁ : Provable 𝓢 (Arrow.arrow φ χ))
    (h₂ : Provable 𝓢 (Arrow.arrow ψ s)) : Provable 𝓢 (Wedge.wedge χ s) := by
  classical exact ⟨andReplace' hc.some h₁.some h₂.some⟩


-- @@ L268-270 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def andReplace (h₁ : Entailment.Prf 𝓢 (Arrow.arrow φ χ)) (h₂ : Entailment.Prf 𝓢 (Arrow.arrow ψ s)) :
    Entailment.Prf 𝓢 (Arrow.arrow (Wedge.wedge φ ψ) (Wedge.wedge χ s)) :=
  deduct' <| andReplace' FiniteContext.id (of h₁) (of h₂)


-- @@ L271-275 expanded
omit [DecidableEq F] in
lemma and_replace! (h₁ : Provable 𝓢 (Arrow.arrow φ χ)) (h₂ : Provable 𝓢 (Arrow.arrow ψ s)) :
    Provable 𝓢 (Arrow.arrow (Wedge.wedge φ ψ) (Wedge.wedge χ s)) := by
  classical exact ⟨andReplace h₁.some h₂.some⟩


-- @@ L278-281 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def orReplaceLeft' (hc : Entailment.Prf 𝓢 (Vee.vee φ ψ)) (hp : Entailment.Prf 𝓢 (Arrow.arrow φ χ)) :
    Entailment.Prf 𝓢 (Vee.vee χ ψ) :=
  or₃''' (impTrans'' hp or₁) (or₂) hc


-- @@ L282-286 expanded
omit [DecidableEq F] in
lemma or_replace_left'! (hc : Provable 𝓢 (Vee.vee φ ψ)) (hp : Provable 𝓢 (Arrow.arrow φ χ)) :
    Provable 𝓢 (Vee.vee χ ψ) := by classical exact ⟨orReplaceLeft' hc.some hp.some⟩


-- @@ L288-290 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def orReplaceLeft (hp : Entailment.Prf 𝓢 (Arrow.arrow φ χ)) :
    Entailment.Prf 𝓢 (Arrow.arrow (Vee.vee φ ψ) (Vee.vee χ ψ)) :=
  deduct' <| orReplaceLeft' FiniteContext.id (of hp)


-- @@ L291-294 expanded
omit [DecidableEq F] in
lemma or_replace_left! (hp : Provable 𝓢 (Arrow.arrow φ χ)) :
    Provable 𝓢 (Arrow.arrow (Vee.vee φ ψ) (Vee.vee χ ψ)) := by
  classical exact ⟨orReplaceLeft hp.some⟩


-- @@ L297-300 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def orReplaceRight' (hc : Entailment.Prf 𝓢 (Vee.vee φ ψ))
    (hq : Entailment.Prf 𝓢 (Arrow.arrow ψ χ)) : Entailment.Prf 𝓢 (Vee.vee φ χ) :=
  or₃''' (or₁) (impTrans'' hq or₂) hc


-- @@ L301-305 expanded
omit [DecidableEq F] in
lemma or_replace_right'! (hc : Provable 𝓢 (Vee.vee φ ψ)) (hq : Provable 𝓢 (Arrow.arrow ψ χ)) :
    Provable 𝓢 (Vee.vee φ χ) := by classical exact ⟨orReplaceRight' hc.some hq.some⟩


-- @@ L307-309 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def orReplaceRight (hq : Entailment.Prf 𝓢 (Arrow.arrow ψ χ)) :
    Entailment.Prf 𝓢 (Arrow.arrow (Vee.vee φ ψ) (Vee.vee φ χ)) :=
  deduct' <| orReplaceRight' FiniteContext.id (of hq)


-- @@ L310-313 expanded
omit [DecidableEq F] in
lemma or_replace_right! (hq : Provable 𝓢 (Arrow.arrow ψ χ)) :
    Provable 𝓢 (Arrow.arrow (Vee.vee φ ψ) (Vee.vee φ χ)) := by
  classical exact ⟨orReplaceRight hq.some⟩


-- @@ L316-319 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def orReplace' (h : Entailment.Prf 𝓢 (Vee.vee φ₁ ψ₁)) (hp : Entailment.Prf 𝓢 (Arrow.arrow φ₁ φ₂))
    (hq : Entailment.Prf 𝓢 (Arrow.arrow ψ₁ ψ₂)) : Entailment.Prf 𝓢 (Vee.vee φ₂ ψ₂) :=
  orReplaceRight' (orReplaceLeft' h hp) hq


-- @@ L321-325 expanded
omit [DecidableEq F] in
lemma or_replace'! (h : Provable 𝓢 (Vee.vee φ₁ ψ₁)) (hp : Provable 𝓢 (Arrow.arrow φ₁ φ₂))
    (hq : Provable 𝓢 (Arrow.arrow ψ₁ ψ₂)) : Provable 𝓢 (Vee.vee φ₂ ψ₂) := by
  classical exact ⟨orReplace' h.some hp.some hq.some⟩


-- @@ L327-329 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def orReplace (hp : Entailment.Prf 𝓢 (Arrow.arrow φ₁ φ₂))
    (hq : Entailment.Prf 𝓢 (Arrow.arrow ψ₁ ψ₂)) :
    Entailment.Prf 𝓢 (Arrow.arrow (Vee.vee φ₁ ψ₁) (Vee.vee φ₂ ψ₂)) :=
  deduct' <| orReplace' FiniteContext.id (of hp) (of hq)


-- @@ L330-334 expanded
omit [DecidableEq F] in
lemma or_replace! (hp : Provable 𝓢 (Arrow.arrow φ₁ φ₂)) (hq : Provable 𝓢 (Arrow.arrow ψ₁ ψ₂)) :
    Provable 𝓢 (Arrow.arrow (Vee.vee φ₁ ψ₁) (Vee.vee φ₂ ψ₂)) := by
  classical exact ⟨orReplace hp.some hq.some⟩


-- @@ L336-338 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def orReplaceIff (hp : Entailment.Prf 𝓢 (LogicalConnective.iff φ₁ φ₂))
    (hq : Entailment.Prf 𝓢 (LogicalConnective.iff ψ₁ ψ₂)) :
    Entailment.Prf 𝓢 (LogicalConnective.iff (Vee.vee φ₁ ψ₁) (Vee.vee φ₂ ψ₂)) :=
  iffIntro (orReplace (and₁' hp) (and₁' hq)) (orReplace (and₂' hp) (and₂' hq))


-- @@ L339-343 expanded
omit [DecidableEq F] in
lemma or_replace_iff! (hp : Provable 𝓢 (LogicalConnective.iff φ₁ φ₂))
    (hq : Provable 𝓢 (LogicalConnective.iff ψ₁ ψ₂)) :
    Provable 𝓢 (LogicalConnective.iff (Vee.vee φ₁ ψ₁) (Vee.vee φ₂ ψ₂)) := by
  classical exact ⟨orReplaceIff hp.some hq.some⟩


-- @@ L345-350 expanded
omit [DecidableEq F] in
lemma or_assoc! :
    Provable 𝓢 (LogicalConnective.iff (Vee.vee φ (Vee.vee ψ χ)) (Vee.vee (Vee.vee φ ψ) χ)) := by
  classical
  apply iff_intro!; · exact deduct'! <| or_assoc'!.mp id!;
  · exact deduct'! <| or_assoc'!.mpr id!;


-- @@ L352-355 expanded
omit [DecidableEq F] in
lemma or_replace_right_iff! (d : Provable 𝓢 (LogicalConnective.iff ψ χ)) :
    Provable 𝓢 (LogicalConnective.iff (Vee.vee φ ψ) (Vee.vee φ χ)) := by
  classical exact iff_intro! (or_replace_right! <| and₁'! d) (or_replace_right! <| and₂'! d)


-- @@ L357-360 expanded
omit [DecidableEq F] in
lemma or_replace_left_iff! (d : Provable 𝓢 (LogicalConnective.iff φ χ)) :
    Provable 𝓢 (LogicalConnective.iff (Vee.vee φ ψ) (Vee.vee χ ψ)) := by
  classical exact iff_intro! (or_replace_left! <| and₁'! d) (or_replace_left! <| and₂'! d)


-- @@ L363-365 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def andReplaceIff (hp : Entailment.Prf 𝓢 (LogicalConnective.iff φ₁ φ₂))
    (hq : Entailment.Prf 𝓢 (LogicalConnective.iff ψ₁ ψ₂)) :
    Entailment.Prf 𝓢 (LogicalConnective.iff (Wedge.wedge φ₁ ψ₁) (Wedge.wedge φ₂ ψ₂)) :=
  iffIntro (andReplace (and₁' hp) (and₁' hq)) (andReplace (and₂' hp) (and₂' hq))


-- @@ L366-370 expanded
omit [DecidableEq F] in
lemma and_replace_iff! (hp : Provable 𝓢 (LogicalConnective.iff φ₁ φ₂))
    (hq : Provable 𝓢 (LogicalConnective.iff ψ₁ ψ₂)) :
    Provable 𝓢 (LogicalConnective.iff (Wedge.wedge φ₁ ψ₁) (Wedge.wedge φ₂ ψ₂)) := by
  classical exact ⟨andReplaceIff hp.some hq.some⟩


-- @@ L373-379 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def impReplaceIff (hp : Entailment.Prf 𝓢 (LogicalConnective.iff φ₁ φ₂))
    (hq : Entailment.Prf 𝓢 (LogicalConnective.iff ψ₁ ψ₂)) :
    Entailment.Prf 𝓢 (LogicalConnective.iff (Arrow.arrow φ₁ ψ₁) (Arrow.arrow φ₂ ψ₂)) :=
  by
  apply iffIntro;
  · apply deduct';
    exact impTrans'' (of <| and₂' hp) <| impTrans'' (FiniteContext.id) (of <| and₁' hq);
  · apply deduct';
    exact impTrans'' (of <| and₁' hp) <| impTrans'' (FiniteContext.id) (of <| and₂' hq);


-- @@ L380-384 expanded
omit [DecidableEq F] in
lemma imp_replace_iff! (hp : Provable 𝓢 (LogicalConnective.iff φ₁ φ₂))
    (hq : Provable 𝓢 (LogicalConnective.iff ψ₁ ψ₂)) :
    Provable 𝓢 (LogicalConnective.iff (Arrow.arrow φ₁ ψ₁) (Arrow.arrow φ₂ ψ₂)) := by
  classical exact ⟨impReplaceIff hp.some hq.some⟩


-- @@ L386-390 expanded
omit [DecidableEq F] in
lemma imp_replace_iff!' (hp : Provable 𝓢 (LogicalConnective.iff φ₁ φ₂))
    (hq : Provable 𝓢 (LogicalConnective.iff ψ₁ ψ₂)) :
    Provable 𝓢 (Arrow.arrow φ₁ ψ₁) ↔ Provable 𝓢 (Arrow.arrow φ₂ ψ₂) := by
  classical exact provable_iff_of_iff (imp_replace_iff! hp hq)


-- @@ L392-394 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def dni : Entailment.Prf 𝓢 (Arrow.arrow φ (Tilde.tilde (Tilde.tilde φ))) :=
  deduct' <| negEquiv'.mpr <| deduct <| botOfMemEither (φ := φ) (by simp) (by simp)


-- @@ L395-398 expanded
omit [DecidableEq F] in
@[simp]
lemma dni! : Provable 𝓢 (Arrow.arrow φ (Tilde.tilde (Tilde.tilde φ))) := by classical exact ⟨dni⟩


-- @@ L400-401 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def dni' (b : Entailment.Prf 𝓢 φ) : Entailment.Prf 𝓢 (Tilde.tilde (Tilde.tilde φ)) :=
  mdp dni b


-- @@ L402-405 expanded
omit [DecidableEq F] in
lemma dni'! (b : Provable 𝓢 φ) : Provable 𝓢 (Tilde.tilde (Tilde.tilde φ)) := by
  classical exact ⟨dni' b.some⟩


-- @@ L408-409 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def dniOr' (d : Entailment.Prf 𝓢 (Vee.vee φ ψ)) :
    Entailment.Prf 𝓢 (Vee.vee (Tilde.tilde (Tilde.tilde φ)) (Tilde.tilde (Tilde.tilde ψ))) :=
  or₃''' (impTrans'' dni or₁) (impTrans'' dni or₂) d


-- @@ L410-413 expanded
omit [DecidableEq F] in
lemma dni_or'! (d : Provable 𝓢 (Vee.vee φ ψ)) :
    Provable 𝓢 (Vee.vee (Tilde.tilde (Tilde.tilde φ)) (Tilde.tilde (Tilde.tilde ψ))) := by
  classical exact ⟨dniOr' d.some⟩


-- @@ L415-416 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def dniAnd' (d : Entailment.Prf 𝓢 (Wedge.wedge φ ψ)) :
    Entailment.Prf 𝓢 (Wedge.wedge (Tilde.tilde (Tilde.tilde φ)) (Tilde.tilde (Tilde.tilde ψ))) :=
  and₃' (dni' <| and₁' d) (dni' <| and₂' d)


-- @@ L417-420 expanded
omit [DecidableEq F] in
lemma dni_and'! (d : Provable 𝓢 (Wedge.wedge φ ψ)) :
    Provable 𝓢 (Wedge.wedge (Tilde.tilde (Tilde.tilde φ)) (Tilde.tilde (Tilde.tilde ψ))) := by
  classical exact ⟨dniAnd' d.some⟩


-- @@ L422-427 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def falsumDNE : Entailment.Prf 𝓢 (Arrow.arrow (Tilde.tilde (Tilde.tilde ⊥)) ⊥) :=
  by
  apply deduct'
  have d₁ : Prf 𝓢 [Tilde.tilde (Tilde.tilde ⊥)] (Arrow.arrow (Tilde.tilde ⊥) ⊥) :=
    negEquiv'.mp byAxm₀
  have d₂ : Prf 𝓢 [Tilde.tilde (Tilde.tilde ⊥)] (Tilde.tilde ⊥) := negEquiv'.mpr (impId ⊥)
  exact mdp d₁ d₂


-- @@ L429-430 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def falsumDN : Entailment.Prf 𝓢 (LogicalConnective.iff (Tilde.tilde (Tilde.tilde ⊥)) ⊥) :=
  andIntro falsumDNE dni


-- @@ L432-433 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def dn [HasAxiomDNE 𝓢] : Entailment.Prf 𝓢 (LogicalConnective.iff φ (Tilde.tilde (Tilde.tilde φ))) :=
  iffIntro dni dne


-- @@ L434-437 expanded
omit [DecidableEq F] in
@[simp]
lemma dn! [HasAxiomDNE 𝓢] : Provable 𝓢 (LogicalConnective.iff φ (Tilde.tilde (Tilde.tilde φ))) := by
  classical exact ⟨dn⟩


-- @@ L440-450 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def contra₀ :
    Entailment.Prf 𝓢
      (Arrow.arrow (Arrow.arrow φ ψ) (Arrow.arrow (Tilde.tilde ψ) (Tilde.tilde φ))) :=
  by apply deduct'; apply deduct; apply negEquiv'.mpr; apply deduct;
  have dp : Prf 𝓢 [φ, Tilde.tilde ψ, Arrow.arrow φ ψ] φ := FiniteContext.byAxm;
  have dpq : Prf 𝓢 [φ, Tilde.tilde ψ, Arrow.arrow φ ψ] (Arrow.arrow φ ψ) := FiniteContext.byAxm;
  have dq : Prf 𝓢 [φ, Tilde.tilde ψ, Arrow.arrow φ ψ] ψ := mdp dpq dp;
  have dnq : Prf 𝓢 [φ, Tilde.tilde ψ, Arrow.arrow φ ψ] (Arrow.arrow ψ ⊥) :=
    negEquiv'.mp <| FiniteContext.byAxm;
  exact mdp dnq dq;


-- @@ L451-455 expanded
omit [DecidableEq F] in
/-- Imported declaration from the Incompleteness formalization. -/
@[simp]
lemma contra₀! :
    Provable 𝓢 (Arrow.arrow (Arrow.arrow φ ψ) (Arrow.arrow (Tilde.tilde ψ) (Tilde.tilde φ))) := by
  classical exact ⟨contra₀⟩


-- @@ L457-458 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def contra₀' (b : Entailment.Prf 𝓢 (Arrow.arrow φ ψ)) :
    Entailment.Prf 𝓢 (Arrow.arrow (Tilde.tilde ψ) (Tilde.tilde φ)) :=
  mdp contra₀ b


-- @@ L459-462 expanded
omit [DecidableEq F] in
lemma contra₀'! (b : Provable 𝓢 (Arrow.arrow φ ψ)) :
    Provable 𝓢 (Arrow.arrow (Tilde.tilde ψ) (Tilde.tilde φ)) := by classical exact ⟨contra₀' b.some⟩


-- @@ L464-465 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def contra₀x2' (b : Entailment.Prf 𝓢 (Arrow.arrow φ ψ)) :
    Entailment.Prf 𝓢 (Arrow.arrow (Tilde.tilde (Tilde.tilde φ)) (Tilde.tilde (Tilde.tilde ψ))) :=
  contra₀' <| contra₀' b


-- @@ L466-469 expanded
omit [DecidableEq F] in
lemma contra₀x2'! (b : Provable 𝓢 (Arrow.arrow φ ψ)) :
    Provable 𝓢 (Arrow.arrow (Tilde.tilde (Tilde.tilde φ)) (Tilde.tilde (Tilde.tilde ψ))) := by
  classical exact ⟨contra₀x2' b.some⟩


-- @@ L471-472 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def contra₀x2 :
    Entailment.Prf 𝓢
      (Arrow.arrow (Arrow.arrow φ ψ)
        (Arrow.arrow (Tilde.tilde (Tilde.tilde φ)) (Tilde.tilde (Tilde.tilde ψ)))) :=
  deduct' <| contra₀x2' FiniteContext.id


-- @@ L473-476 expanded
omit [DecidableEq F] in
@[simp]
lemma contra₀x2! :
    Provable 𝓢
      (Arrow.arrow (Arrow.arrow φ ψ)
        (Arrow.arrow (Tilde.tilde (Tilde.tilde φ)) (Tilde.tilde (Tilde.tilde ψ)))) :=
  by classical exact ⟨contra₀x2⟩


-- @@ L479-480 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def contra₁' (b : Entailment.Prf 𝓢 (Arrow.arrow φ (Tilde.tilde ψ))) :
    Entailment.Prf 𝓢 (Arrow.arrow ψ (Tilde.tilde φ)) :=
  impTrans'' dni (contra₀' b)


-- @@ L481-484 expanded
omit [DecidableEq F] in
lemma contra₁'! (b : Provable 𝓢 (Arrow.arrow φ (Tilde.tilde ψ))) :
    Provable 𝓢 (Arrow.arrow ψ (Tilde.tilde φ)) := by classical exact ⟨contra₁' b.some⟩


-- @@ L486-487 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def contra₁ :
    Entailment.Prf 𝓢
      (Arrow.arrow (Arrow.arrow φ (Tilde.tilde ψ)) (Arrow.arrow ψ (Tilde.tilde φ))) :=
  deduct' <| contra₁' FiniteContext.id


-- @@ L488-491 expanded
omit [DecidableEq F] in
lemma contra₁! :
    Provable 𝓢 (Arrow.arrow (Arrow.arrow φ (Tilde.tilde ψ)) (Arrow.arrow ψ (Tilde.tilde φ))) := by
  classical exact ⟨contra₁⟩


-- @@ L494-495 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def contra₂' [HasAxiomDNE 𝓢] (b : Entailment.Prf 𝓢 (Arrow.arrow (Tilde.tilde φ) ψ)) :
    Entailment.Prf 𝓢 (Arrow.arrow (Tilde.tilde ψ) φ) :=
  impTrans'' (contra₀' b) dne


-- @@ L496-499 expanded
omit [DecidableEq F] in
lemma contra₂'! [HasAxiomDNE 𝓢] (b : Provable 𝓢 (Arrow.arrow (Tilde.tilde φ) ψ)) :
    Provable 𝓢 (Arrow.arrow (Tilde.tilde ψ) φ) := by classical exact ⟨contra₂' b.some⟩


-- @@ L501-502 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def contra₂ [HasAxiomDNE 𝓢] :
    Entailment.Prf 𝓢
      (Arrow.arrow (Arrow.arrow (Tilde.tilde φ) ψ) (Arrow.arrow (Tilde.tilde ψ) φ)) :=
  deduct' <| contra₂' FiniteContext.id


-- @@ L503-506 expanded
omit [DecidableEq F] in
@[simp]
lemma contra₂! [HasAxiomDNE 𝓢] :
    Provable 𝓢 (Arrow.arrow (Arrow.arrow (Tilde.tilde φ) ψ) (Arrow.arrow (Tilde.tilde ψ) φ)) := by
  classical exact ⟨contra₂⟩


-- @@ L509-510 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def contra₃' [HasAxiomDNE 𝓢] (b : Entailment.Prf 𝓢 (Arrow.arrow (Tilde.tilde φ) (Tilde.tilde ψ))) :
    Entailment.Prf 𝓢 (Arrow.arrow ψ φ) :=
  impTrans'' dni (contra₂' b)


-- @@ L511-514 expanded
omit [DecidableEq F] in
lemma contra₃'! [HasAxiomDNE 𝓢] (b : Provable 𝓢 (Arrow.arrow (Tilde.tilde φ) (Tilde.tilde ψ))) :
    Provable 𝓢 (Arrow.arrow ψ φ) := by classical exact ⟨contra₃' b.some⟩


-- @@ L516-517 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def contra₃ [HasAxiomDNE 𝓢] :
    Entailment.Prf 𝓢
      (Arrow.arrow (Arrow.arrow (Tilde.tilde φ) (Tilde.tilde ψ)) (Arrow.arrow ψ φ)) :=
  deduct' <| contra₃' FiniteContext.id


-- @@ L518-521 expanded
omit [DecidableEq F] in
@[simp 1100]
lemma contra₃! [HasAxiomDNE 𝓢] :
    Provable 𝓢 (Arrow.arrow (Arrow.arrow (Tilde.tilde φ) (Tilde.tilde ψ)) (Arrow.arrow ψ φ)) := by
  classical exact ⟨contra₃⟩


-- @@ L524-527 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def negReplaceIff' (b : Entailment.Prf 𝓢 (LogicalConnective.iff φ ψ)) :
    Entailment.Prf 𝓢 (LogicalConnective.iff (Tilde.tilde φ) (Tilde.tilde ψ)) :=
  iffIntro (contra₀' <| and₂' b) (contra₀' <| and₁' b)


-- @@ L528-531 expanded
omit [DecidableEq F] in
lemma neg_replace_iff'! (b : Provable 𝓢 (LogicalConnective.iff φ ψ)) :
    Provable 𝓢 (LogicalConnective.iff (Tilde.tilde φ) (Tilde.tilde ψ)) := by
  classical exact ⟨negReplaceIff' b.some⟩


-- @@ L534-536 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def iffNegLeftToRight' [HasAxiomDNE 𝓢]
    (h : Entailment.Prf 𝓢 (LogicalConnective.iff φ (Tilde.tilde ψ))) :
    Entailment.Prf 𝓢 (LogicalConnective.iff (Tilde.tilde φ) ψ) :=
  iffIntro (contra₂' <| and₂' h) (contra₁' <| and₁' h)


-- @@ L537-541 expanded
omit [DecidableEq F] in
lemma iff_neg_left_to_right'! [HasAxiomDNE 𝓢]
    (h : Provable 𝓢 (LogicalConnective.iff φ (Tilde.tilde ψ))) :
    Provable 𝓢 (LogicalConnective.iff (Tilde.tilde φ) ψ) := by
  classical exact ⟨iffNegLeftToRight' h.some⟩


-- @@ L543-546 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def iffNegRightToLeft' [HasAxiomDNE 𝓢]
    (h : Entailment.Prf 𝓢 (LogicalConnective.iff (Tilde.tilde φ) ψ)) :
    Entailment.Prf 𝓢 (LogicalConnective.iff φ (Tilde.tilde ψ)) :=
  iffComm' <| iffNegLeftToRight' <| iffComm' h


-- @@ L547-551 expanded
omit [DecidableEq F] in
lemma iff_neg_right_to_left'! [HasAxiomDNE 𝓢]
    (h : Provable 𝓢 (LogicalConnective.iff (Tilde.tilde φ) ψ)) :
    Provable 𝓢 (LogicalConnective.iff φ (Tilde.tilde ψ)) := by
  classical exact ⟨iffNegRightToLeft' h.some⟩


-- @@ L553-553 verbatim
section «lp_section_1»


-- @@ L555-559 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def negnegEquiv :
    Entailment.Prf 𝓢
      (LogicalConnective.iff (Tilde.tilde (Tilde.tilde φ)) (Arrow.arrow (Arrow.arrow φ ⊥) ⊥)) :=
  by
  apply iffIntro; · exact impTrans'' (by apply contra₀'; exact and₂' negEquiv) (and₁' negEquiv)
  · exact impTrans'' (and₂' negEquiv) (by apply contra₀'; exact and₁' negEquiv)


-- @@ L560-563 expanded
omit [DecidableEq F] in
@[simp]
lemma negnegEquiv! :
    Provable 𝓢
      (LogicalConnective.iff (Tilde.tilde (Tilde.tilde φ)) (Arrow.arrow (Arrow.arrow φ ⊥) ⊥)) :=
  by classical exact ⟨negnegEquiv⟩


-- @@ L565-566 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def negnegEquivDne [HasAxiomDNE 𝓢] :
    Entailment.Prf 𝓢 (LogicalConnective.iff φ (Arrow.arrow (Arrow.arrow φ ⊥) ⊥)) :=
  iffTrans'' dn negnegEquiv


-- @@ L567-570 expanded
omit [DecidableEq F] in
lemma negnegEquivDne! [HasAxiomDNE 𝓢] :
    Provable 𝓢 (LogicalConnective.iff φ (Arrow.arrow (Arrow.arrow φ ⊥) ⊥)) := by
  classical exact ⟨negnegEquivDne⟩


-- @@ L572-572 verbatim
end «lp_section_1»


-- @@ L574-578 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def elimContraNeg [HasAxiomElimContra 𝓢] :
    Entailment.Prf 𝓢
      (Arrow.arrow (Arrow.arrow (Arrow.arrow ψ ⊥) (Arrow.arrow φ ⊥)) (Arrow.arrow φ ψ)) :=
  by refine impTrans'' ?_ elimContra; apply deduct';
  exact impTrans'' (impTrans'' (and₁' negEquiv) FiniteContext.byAxm) (and₂' negEquiv);


-- @@ L579-583 expanded
omit [DecidableEq F] in
@[simp]
lemma elimContraNeg! [HasAxiomElimContra 𝓢] :
    Provable 𝓢 (Arrow.arrow (Arrow.arrow (Arrow.arrow ψ ⊥) (Arrow.arrow φ ⊥)) (Arrow.arrow φ ψ)) :=
  by classical exact ⟨elimContraNeg⟩


-- @@ L586-587 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def tne :
    Entailment.Prf 𝓢 (Arrow.arrow (Tilde.tilde (Tilde.tilde (Tilde.tilde φ))) (Tilde.tilde φ)) :=
  contra₀' dni


-- @@ L588-591 expanded
omit [DecidableEq F] in
@[simp]
lemma tne! : Provable 𝓢 (Arrow.arrow (Tilde.tilde (Tilde.tilde (Tilde.tilde φ))) (Tilde.tilde φ)) :=
  by classical exact ⟨tne⟩


-- @@ L593-594 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def tne' (b : Entailment.Prf 𝓢 (Tilde.tilde (Tilde.tilde (Tilde.tilde φ)))) :
    Entailment.Prf 𝓢 (Tilde.tilde φ) :=
  mdp tne b


-- @@ L595-598 expanded
omit [DecidableEq F] in
lemma tne'! (b : Provable 𝓢 (Tilde.tilde (Tilde.tilde (Tilde.tilde φ)))) :
    Provable 𝓢 (Tilde.tilde φ) := by classical exact ⟨tne' b.some⟩


-- @@ L600-601 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def tneIff :
    Entailment.Prf 𝓢
      (LogicalConnective.iff (Tilde.tilde (Tilde.tilde (Tilde.tilde φ))) (Tilde.tilde φ)) :=
  andIntro tne dni


-- @@ L603-605 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def implyLeftReplace (h : Entailment.Prf 𝓢 (Arrow.arrow ψ φ)) :
    Entailment.Prf 𝓢 (Arrow.arrow (Arrow.arrow φ χ) (Arrow.arrow ψ χ)) :=
  deduct' <| impTrans'' (of h) id


-- @@ L606-610 expanded
omit [DecidableEq F] in
lemma replace_imply_left! (h : Provable 𝓢 (Arrow.arrow ψ φ)) :
    Provable 𝓢 (Arrow.arrow (Arrow.arrow φ χ) (Arrow.arrow ψ χ)) := by
  classical exact ⟨implyLeftReplace h.some⟩


-- @@ L612-617 expanded
omit [DecidableEq F] in
lemma replace_imply_left_by_iff'! (h : Provable 𝓢 (LogicalConnective.iff φ ψ)) :
    Provable 𝓢 (Arrow.arrow φ χ) ↔ Provable 𝓢 (Arrow.arrow ψ χ) := by
  classical
  constructor; · exact imp_trans''! <| and₂'! h;
  · exact imp_trans''! <| and₁'! h;


-- @@ L619-624 expanded
omit [DecidableEq F] in
lemma replace_imply_right_by_iff'! (h : Provable 𝓢 (LogicalConnective.iff φ ψ)) :
    Provable 𝓢 (Arrow.arrow χ φ) ↔ Provable 𝓢 (Arrow.arrow χ ψ) := by
  classical
  constructor; · intro hrp; exact imp_trans''! hrp <| and₁'! h;
  · intro hrq; exact imp_trans''! hrq <| and₂'! h;


-- @@ L627-629 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def impSwap' (h : Entailment.Prf 𝓢 (Arrow.arrow φ (Arrow.arrow ψ χ))) :
    Entailment.Prf 𝓢 (Arrow.arrow ψ (Arrow.arrow φ χ)) :=
  deduct' <| deduct <| mdp (mdp (of (Γ := [φ, ψ]) h) FiniteContext.byAxm) FiniteContext.byAxm


-- @@ L630-633 expanded
omit [DecidableEq F] in
lemma imp_swap'! (h : Provable 𝓢 (Arrow.arrow φ (Arrow.arrow ψ χ))) :
    Provable 𝓢 (Arrow.arrow ψ (Arrow.arrow φ χ)) := by classical exact ⟨impSwap' h.some⟩


-- @@ L635-636 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def impSwap :
    Entailment.Prf 𝓢
      (Arrow.arrow (Arrow.arrow φ (Arrow.arrow ψ χ)) (Arrow.arrow ψ (Arrow.arrow φ χ))) :=
  deduct' <| impSwap' FiniteContext.id


-- @@ L637-640 expanded
omit [DecidableEq F] in
@[simp]
lemma imp_swap! :
    Provable 𝓢 (Arrow.arrow (Arrow.arrow φ (Arrow.arrow ψ χ)) (Arrow.arrow ψ (Arrow.arrow φ χ))) :=
  by classical exact ⟨impSwap⟩


-- @@ L642-644 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def ppq (h : Entailment.Prf 𝓢 (Arrow.arrow φ (Arrow.arrow φ ψ))) :
    Entailment.Prf 𝓢 (Arrow.arrow φ ψ) :=
  deduct' <| mdp (mdp (of (Γ := [φ]) h) FiniteContext.byAxm) FiniteContext.byAxm


-- @@ L645-648 expanded
omit [DecidableEq F] in
lemma ppq! (h : Provable 𝓢 (Arrow.arrow φ (Arrow.arrow φ ψ))) : Provable 𝓢 (Arrow.arrow φ ψ) := by
  classical exact ⟨ppq h.some⟩


-- @@ L650-651 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def pPqQ : Entailment.Prf 𝓢 (Arrow.arrow φ (Arrow.arrow (Arrow.arrow φ ψ) ψ)) :=
  impSwap' <| impId _


-- @@ L652-655 expanded
omit [DecidableEq F] in
lemma pPqQ! : Provable 𝓢 (Arrow.arrow φ (Arrow.arrow (Arrow.arrow φ ψ) ψ)) := by
  classical exact ⟨pPqQ⟩


-- @@ L657-658 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def dhypImp' (h : Entailment.Prf 𝓢 (Arrow.arrow φ ψ)) :
    Entailment.Prf 𝓢 (Arrow.arrow (Arrow.arrow χ φ) (Arrow.arrow χ ψ)) :=
  mdp imply₂ (imply₁' h)


-- @@ L659-662 expanded
omit [DecidableEq F] in
lemma dhypImp'! (h : Provable 𝓢 (Arrow.arrow φ ψ)) :
    Provable 𝓢 (Arrow.arrow (Arrow.arrow χ φ) (Arrow.arrow χ ψ)) := by
  classical exact ⟨dhypImp' h.some⟩


-- @@ L664-665 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def revDhypImp' (h : Entailment.Prf 𝓢 (Arrow.arrow ψ φ)) :
    Entailment.Prf 𝓢 (Arrow.arrow (Arrow.arrow φ χ) (Arrow.arrow ψ χ)) :=
  impSwap' <| impTrans'' h pPqQ


-- @@ L666-671 expanded
omit [DecidableEq F] in
lemma revDhypImp'! (h : Provable 𝓢 (Arrow.arrow ψ φ)) :
    Provable 𝓢 (Arrow.arrow (Arrow.arrow φ χ) (Arrow.arrow ψ χ)) := by
  classical
    exact
    ⟨revDhypImp' h.some⟩
      -- TODO: Actually this can be computable but it's too slow.


-- @@ L672-674 expanded
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def dnDistributeImply :
    Entailment.Prf 𝓢
      (Arrow.arrow (Tilde.tilde (Tilde.tilde (Arrow.arrow φ ψ)))
        (Arrow.arrow (Tilde.tilde (Tilde.tilde φ)) (Tilde.tilde (Tilde.tilde ψ)))) :=
  impSwap' <| deduct' <| impTrans'' (contra₀x2' <| deductInv <| of <| impSwap' <| contra₀x2) tne


-- @@ L675-678 expanded
omit [DecidableEq F] in
@[simp]
lemma dn_distribute_imply! :
    Provable 𝓢
      (Arrow.arrow (Tilde.tilde (Tilde.tilde (Arrow.arrow φ ψ)))
        (Arrow.arrow (Tilde.tilde (Tilde.tilde φ)) (Tilde.tilde (Tilde.tilde ψ)))) :=
  by classical exact ⟨dnDistributeImply⟩


-- @@ L680-683 expanded
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def dnDistributeImply'
    (b : Entailment.Prf 𝓢 (Tilde.tilde (Tilde.tilde (Arrow.arrow φ ψ)))) :
    Entailment.Prf 𝓢 (Arrow.arrow (Tilde.tilde (Tilde.tilde φ)) (Tilde.tilde (Tilde.tilde ψ))) :=
  mdp dnDistributeImply b


-- @@ L684-688 expanded
omit [DecidableEq F] in
lemma dn_distribute_imply'! (b : Provable 𝓢 (Tilde.tilde (Tilde.tilde (Arrow.arrow φ ψ)))) :
    Provable 𝓢 (Arrow.arrow (Tilde.tilde (Tilde.tilde φ)) (Tilde.tilde (Tilde.tilde ψ))) := by
  classical exact ⟨dnDistributeImply' b.some⟩


-- @@ L691-692 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def introFalsumOfAnd' (h : Entailment.Prf 𝓢 (Wedge.wedge φ (Tilde.tilde φ))) : Entailment.Prf 𝓢 ⊥ :=
  mdp (negEquiv'.mp <| and₂' h) (and₁' h)


-- @@ L693-696 expanded
omit [DecidableEq F] in
lemma intro_falsum_of_and'! (h : Provable 𝓢 (Wedge.wedge φ (Tilde.tilde φ))) : Provable 𝓢 ⊥ := by
  classical exact ⟨introFalsumOfAnd' h.some⟩


-- @@ L697-698 verbatim
/-- Law of contradiction -/
alias lac'! := intro_falsum_of_and'!


-- @@ L700-702 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def introFalsumOfAnd : Entailment.Prf 𝓢 (Arrow.arrow (Wedge.wedge φ (Tilde.tilde φ)) ⊥) :=
  deduct' <| introFalsumOfAnd' (φ := φ) FiniteContext.id


-- @@ L703-706 expanded
omit [DecidableEq F] in
@[simp]
lemma intro_bot_of_and! : Provable 𝓢 (Arrow.arrow (Wedge.wedge φ (Tilde.tilde φ)) ⊥) := by
  classical exact ⟨introFalsumOfAnd⟩


-- @@ L707-708 verbatim
/-- Law of contradiction -/
alias lac! := intro_bot_of_and!




-- @@ L712-718 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def implyOfNotOr [HasAxiomEFQ 𝓢] :
    Entailment.Prf 𝓢 (Arrow.arrow (Vee.vee (Tilde.tilde φ) ψ) (Arrow.arrow φ ψ)) :=
  or₃''
    (by apply emptyPrf; apply deduct; apply deduct;
      exact efqOfMemEither (φ := φ) (by simp) (by simp))
    imply₁


-- @@ L719-722 expanded
omit [DecidableEq F] in
@[simp]
lemma imply_of_not_or! [HasAxiomEFQ 𝓢] :
    Provable 𝓢 (Arrow.arrow (Vee.vee (Tilde.tilde φ) ψ) (Arrow.arrow φ ψ)) := by
  classical exact ⟨implyOfNotOr⟩


-- @@ L724-725 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def implyOfNotOr' [HasAxiomEFQ 𝓢] (b : Entailment.Prf 𝓢 (Vee.vee (Tilde.tilde φ) ψ)) :
    Entailment.Prf 𝓢 (Arrow.arrow φ ψ) :=
  mdp implyOfNotOr b


-- @@ L726-729 expanded
omit [DecidableEq F] in
lemma imply_of_not_or'! [HasAxiomEFQ 𝓢] (b : Provable 𝓢 (Vee.vee (Tilde.tilde φ) ψ)) :
    Provable 𝓢 (Arrow.arrow φ ψ) := by classical exact ⟨implyOfNotOr' b.some⟩


-- @@ L732-733 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def demorgan₁ :
    Entailment.Prf 𝓢
      (Arrow.arrow (Vee.vee (Tilde.tilde φ) (Tilde.tilde ψ)) (Tilde.tilde (Wedge.wedge φ ψ))) :=
  or₃'' (contra₀' and₁) (contra₀' and₂)


-- @@ L734-737 expanded
omit [DecidableEq F] in
@[simp]
lemma demorgan₁! :
    Provable 𝓢
      (Arrow.arrow (Vee.vee (Tilde.tilde φ) (Tilde.tilde ψ)) (Tilde.tilde (Wedge.wedge φ ψ))) :=
  by classical exact ⟨demorgan₁⟩


-- @@ L739-740 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def demorgan₁' (d : Entailment.Prf 𝓢 (Vee.vee (Tilde.tilde φ) (Tilde.tilde ψ))) :
    Entailment.Prf 𝓢 (Tilde.tilde (Wedge.wedge φ ψ)) :=
  mdp demorgan₁ d


-- @@ L741-744 expanded
omit [DecidableEq F] in
lemma demorgan₁'! (d : Provable 𝓢 (Vee.vee (Tilde.tilde φ) (Tilde.tilde ψ))) :
    Provable 𝓢 (Tilde.tilde (Wedge.wedge φ ψ)) := by classical exact ⟨demorgan₁' d.some⟩


-- @@ L747-756 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def demorgan₂ :
    Entailment.Prf 𝓢
      (Arrow.arrow (Wedge.wedge (Tilde.tilde φ) (Tilde.tilde ψ)) (Tilde.tilde (Vee.vee φ ψ))) :=
  by apply andImplyIffImplyImply'.mpr; apply deduct'; apply deduct; apply negEquiv'.mpr;
  apply deduct;
  exact
    or₃''' (negEquiv'.mp FiniteContext.byAxm) (negEquiv'.mp FiniteContext.byAxm)
      (FiniteContext.byAxm (φ := Vee.vee φ ψ));


-- @@ L757-760 expanded
omit [DecidableEq F] in
@[simp]
lemma demorgan₂! :
    Provable 𝓢
      (Arrow.arrow (Wedge.wedge (Tilde.tilde φ) (Tilde.tilde ψ)) (Tilde.tilde (Vee.vee φ ψ))) :=
  by classical exact ⟨demorgan₂⟩


-- @@ L762-763 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def demorgan₂' (d : Entailment.Prf 𝓢 (Wedge.wedge (Tilde.tilde φ) (Tilde.tilde ψ))) :
    Entailment.Prf 𝓢 (Tilde.tilde (Vee.vee φ ψ)) :=
  mdp demorgan₂ d


-- @@ L764-767 expanded
omit [DecidableEq F] in
lemma demorgan₂'! (d : Provable 𝓢 (Wedge.wedge (Tilde.tilde φ) (Tilde.tilde ψ))) :
    Provable 𝓢 (Tilde.tilde (Vee.vee φ ψ)) := by classical exact ⟨demorgan₂' d.some⟩


-- @@ L770-772 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def demorgan₃ :
    Entailment.Prf 𝓢
      (Arrow.arrow (Tilde.tilde (Vee.vee φ ψ)) (Wedge.wedge (Tilde.tilde φ) (Tilde.tilde ψ))) :=
  deduct' <| and₃' (deductInv <| contra₀' or₁) (deductInv <| contra₀' or₂)


-- @@ L773-776 expanded
omit [DecidableEq F] in
@[simp]
lemma demorgan₃! :
    Provable 𝓢
      (Arrow.arrow (Tilde.tilde (Vee.vee φ ψ)) (Wedge.wedge (Tilde.tilde φ) (Tilde.tilde ψ))) :=
  by classical exact ⟨demorgan₃⟩


-- @@ L778-779 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def demorgan₃' (b : Entailment.Prf 𝓢 (Tilde.tilde (Vee.vee φ ψ))) :
    Entailment.Prf 𝓢 (Wedge.wedge (Tilde.tilde φ) (Tilde.tilde ψ)) :=
  mdp demorgan₃ b


-- @@ L780-786 expanded
omit [DecidableEq F] in
lemma demorgan₃'! (b : Provable 𝓢 (Tilde.tilde (Vee.vee φ ψ))) :
    Provable 𝓢 (Wedge.wedge (Tilde.tilde φ) (Tilde.tilde ψ)) := by
  classical
    exact
    ⟨demorgan₃' b.some⟩
      -- TODO: Actually this can be computable but it's too slow.


-- @@ L787-789 expanded
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def demorgan₄ [HasAxiomDNE 𝓢] :
    Entailment.Prf 𝓢
      (Arrow.arrow (Tilde.tilde (Wedge.wedge φ ψ)) (Vee.vee (Tilde.tilde φ) (Tilde.tilde ψ))) :=
  contra₂' <| deduct' <| andReplace' (demorgan₃' FiniteContext.id) dne dne


-- @@ L790-793 expanded
omit [DecidableEq F] in
@[simp]
lemma demorgan₄! [HasAxiomDNE 𝓢] :
    Provable 𝓢
      (Arrow.arrow (Tilde.tilde (Wedge.wedge φ ψ)) (Vee.vee (Tilde.tilde φ) (Tilde.tilde ψ))) :=
  by classical exact ⟨demorgan₄⟩


-- @@ L795-796 expanded
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def demorgan₄' [HasAxiomDNE 𝓢]
    (b : Entailment.Prf 𝓢 (Tilde.tilde (Wedge.wedge φ ψ))) :
    Entailment.Prf 𝓢 (Vee.vee (Tilde.tilde φ) (Tilde.tilde ψ)) :=
  mdp demorgan₄ b


-- @@ L797-802 expanded
omit [DecidableEq F] in
lemma demorgan₄'! [HasAxiomDNE 𝓢] (b : Provable 𝓢 (Tilde.tilde (Wedge.wedge φ ψ))) :
    Provable 𝓢 (Vee.vee (Tilde.tilde φ) (Tilde.tilde ψ)) := by
  classical
    exact
    ⟨demorgan₄' b.some⟩
      -- TODO: Actually this can be computable but it's too slow.


-- @@ L803-811 expanded
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def NotOrOfImply' [HasAxiomDNE 𝓢] (d : Entailment.Prf 𝓢 (Arrow.arrow φ ψ)) :
    Entailment.Prf 𝓢 (Vee.vee (Tilde.tilde φ) ψ) := by apply dne'; apply negEquiv'.mpr;
  apply deduct';
  have d₁ :
    Prf 𝓢 [Tilde.tilde (Vee.vee (Tilde.tilde φ) ψ)]
      (Wedge.wedge (Tilde.tilde (Tilde.tilde φ)) (Tilde.tilde ψ)) :=
    demorgan₃' <| FiniteContext.id;
  have d₂ : Prf 𝓢 [Tilde.tilde (Vee.vee (Tilde.tilde φ) ψ)] (Arrow.arrow (Tilde.tilde φ) ⊥) :=
    negEquiv'.mp <| and₁' d₁;
  have d₃ : Prf 𝓢 [Tilde.tilde (Vee.vee (Tilde.tilde φ) ψ)] (Tilde.tilde φ) :=
    mdp (of (Γ := [Tilde.tilde (Vee.vee (Tilde.tilde φ) ψ)]) <| contra₀' d) (and₂' d₁);
  exact mdp d₂ d₃;


-- @@ L812-815 expanded
omit [DecidableEq F] in
lemma not_or_of_imply'! [HasAxiomDNE 𝓢] (d : Provable 𝓢 (Arrow.arrow φ ψ)) :
    Provable 𝓢 (Vee.vee (Tilde.tilde φ) ψ) := by classical exact ⟨NotOrOfImply' d.some⟩


-- @@ L817-819 expanded
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def NotOrOfImply [HasAxiomDNE 𝓢] :
    Entailment.Prf 𝓢 (Arrow.arrow (Arrow.arrow φ ψ) (Vee.vee (Tilde.tilde φ) ψ)) :=
  deduct' <| NotOrOfImply' FiniteContext.byAxm


-- @@ L820-825 expanded
omit [DecidableEq F] in
lemma not_or_of_imply! [HasAxiomDNE 𝓢] :
    Provable 𝓢 (Arrow.arrow (Arrow.arrow φ ψ) (Vee.vee (Tilde.tilde φ) ψ)) := by
  classical
    exact
    ⟨NotOrOfImply⟩
      -- TODO: Actually this can be computable but it's too slow.


-- @@ L826-841 expanded
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def dnCollectImply [HasAxiomEFQ 𝓢] :
    Entailment.Prf 𝓢
      (Arrow.arrow (Arrow.arrow (Tilde.tilde (Tilde.tilde φ)) (Tilde.tilde (Tilde.tilde ψ)))
        (Tilde.tilde (Tilde.tilde (Arrow.arrow φ ψ)))) :=
  by apply deduct'; apply negEquiv'.mpr;
  exact
    impTrans''
      (by
        apply deductInv; apply andImplyIffImplyImply'.mp; apply deduct;
        have d₁ :
          Prf 𝓢
            [Wedge.wedge (Arrow.arrow (Tilde.tilde (Tilde.tilde φ)) (Tilde.tilde (Tilde.tilde ψ)))
                (Tilde.tilde (Arrow.arrow φ ψ))]
            (Arrow.arrow (Tilde.tilde (Tilde.tilde φ)) (Tilde.tilde (Tilde.tilde ψ))) :=
          and₁' (ψ := Tilde.tilde (Arrow.arrow φ ψ)) <| FiniteContext.id;
        have d₂ :
          Prf 𝓢
            [Wedge.wedge (Arrow.arrow (Tilde.tilde (Tilde.tilde φ)) (Tilde.tilde (Tilde.tilde ψ)))
                (Tilde.tilde (Arrow.arrow φ ψ))]
            (Wedge.wedge (Tilde.tilde (Tilde.tilde φ)) (Tilde.tilde ψ)) :=
          demorgan₃' <|
            mdp (contra₀' implyOfNotOr)
              (and₂' (φ :=
                  (Arrow.arrow (Tilde.tilde (Tilde.tilde φ)) (Tilde.tilde (Tilde.tilde ψ)))) <|
                FiniteContext.id)
        exact and₃' (and₂' d₂) (mdp d₁ (and₁' d₂)))
      (introFalsumOfAnd (φ := Tilde.tilde ψ));


-- @@ L843-849 expanded
omit [DecidableEq F] in
@[simp]
lemma dn_collect_imply! [HasAxiomEFQ 𝓢] :
    Provable 𝓢
      (Arrow.arrow (Arrow.arrow (Tilde.tilde (Tilde.tilde φ)) (Tilde.tilde (Tilde.tilde ψ)))
        (Tilde.tilde (Tilde.tilde (Arrow.arrow φ ψ)))) :=
  by
  classical
    exact
    ⟨dnCollectImply⟩
      -- TODO: Actually this can be computable but it's too slow.


-- @@ L850-853 expanded
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def dnCollectImply' [HasAxiomEFQ 𝓢]
    (b :
      Entailment.Prf 𝓢 (Arrow.arrow (Tilde.tilde (Tilde.tilde φ)) (Tilde.tilde (Tilde.tilde ψ)))) :
    Entailment.Prf 𝓢 (Tilde.tilde (Tilde.tilde (Arrow.arrow φ ψ))) :=
  mdp dnCollectImply b


-- @@ L854-858 expanded
omit [DecidableEq F] in
lemma dn_collect_imply'! [HasAxiomEFQ 𝓢]
    (b : Provable 𝓢 (Arrow.arrow (Tilde.tilde (Tilde.tilde φ)) (Tilde.tilde (Tilde.tilde ψ)))) :
    Provable 𝓢 (Tilde.tilde (Tilde.tilde (Arrow.arrow φ ψ))) := by
  classical exact ⟨dnCollectImply' b.some⟩


-- @@ L861-866 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def andImplyAndOfImply {φ ψ φ' ψ' : F} (bp : Entailment.Prf 𝓢 (Arrow.arrow φ φ'))
    (bq : Entailment.Prf 𝓢 (Arrow.arrow ψ ψ')) :
    Entailment.Prf 𝓢 (Arrow.arrow (Wedge.wedge φ ψ) (Wedge.wedge φ' ψ')) :=
  deduct' <| andIntro (deductInv' <| impTrans'' and₁ bp) (deductInv' <| impTrans'' and₂ bq)


-- @@ L868-872 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def andIffAndOfIff {φ ψ φ' ψ' : F} (bp : Entailment.Prf 𝓢 (LogicalConnective.iff φ φ'))
    (bq : Entailment.Prf 𝓢 (LogicalConnective.iff ψ ψ')) :
    Entailment.Prf 𝓢 (LogicalConnective.iff (Wedge.wedge φ ψ) (Wedge.wedge φ' ψ')) :=
  iffIntro (andImplyAndOfImply (andLeft bp) (andLeft bq))
    (andImplyAndOfImply (andRight bp) (andRight bq))


-- @@ L875-875 verbatim
section «lp_section_2»


-- @@ L877-885 verbatim
omit [DecidableEq F] in
instance [HasAxiomDNE 𝓢] : HasAxiomEFQ 𝓢 where
  efq φ := by
    classical
    apply contra₃';
    exact impTrans'' (and₁' negEquiv) <| impTrans'' (impSwap' imply₁) (and₂' negEquiv);


-- TODO: Actually this can be computable but it's too slow.

-- @@ L886-890 verbatim
omit [DecidableEq F] in
noncomputable instance [HasAxiomDNE 𝓢] : HasAxiomLEM 𝓢 where
  lem _ := by
    classical
    exact dneOr <| NotOrOfImply' dni


-- @@ L892-902 expanded
omit [DecidableEq F] in
instance [HasAxiomEFQ 𝓢] [HasAxiomLEM 𝓢] : HasAxiomDNE 𝓢 where
  dne
    φ := by
    classical apply deduct';
    exact
      or₃''' (impId _)
          (by apply deduct;
            have nnp :
              Prf 𝓢 [Tilde.tilde φ, Tilde.tilde (Tilde.tilde φ)] (Arrow.arrow (Tilde.tilde φ) ⊥) :=
              negEquiv'.mp <| FiniteContext.byAxm;
            have np : Prf 𝓢 [Tilde.tilde φ, Tilde.tilde (Tilde.tilde φ)] (Tilde.tilde φ) :=
              FiniteContext.byAxm;
            exact efq' <| mdp nnp np; ) <|
        of lem;
    ;


-- @@ L904-908 expanded
omit [DecidableEq F] in
instance [HasAxiomLEM 𝓢] : HasAxiomWeakLEM 𝓢 where
  wlem φ := by classical exact lem (φ := Tilde.tilde φ);


-- @@ L910-916 expanded
omit [DecidableEq F] in
instance [HasAxiomEFQ 𝓢] [HasAxiomLEM 𝓢] : HasAxiomDummett 𝓢 where
  dummett φ
    ψ := by
    classical
      have d₁ : Entailment.Prf 𝓢 (Arrow.arrow φ (Vee.vee (Arrow.arrow φ ψ) (Arrow.arrow ψ φ))) :=
      impTrans'' imply₁ or₂;
    have d₂ :
      Entailment.Prf 𝓢
        (Arrow.arrow (Tilde.tilde φ) (Vee.vee (Arrow.arrow φ ψ) (Arrow.arrow ψ φ))) :=
      impTrans'' efqImplyNot₁ or₁;
    exact or₃''' d₁ d₂ lem;


-- @@ L918-941 expanded
omit [DecidableEq F] in
instance [HasAxiomDummett 𝓢] : HasAxiomWeakLEM 𝓢 where
  wlem
    φ := by
    classical
      haveI :
      Entailment.Prf 𝓢 (Vee.vee (Arrow.arrow φ (Tilde.tilde φ)) (Arrow.arrow (Tilde.tilde φ) φ)) :=
      dummett;
    exact
      or₃'''
        (by apply deduct'; apply or₁'; apply negEquiv'.mpr; apply deduct;
          haveI d₁ : Prf 𝓢 [φ, Arrow.arrow φ (Tilde.tilde φ)] φ := FiniteContext.byAxm;
          haveI d₂ : Prf 𝓢 [φ, Arrow.arrow φ (Tilde.tilde φ)] (Arrow.arrow φ (Tilde.tilde φ)) :=
            FiniteContext.byAxm;
          have := negEquiv'.mp <| mdp d₂ d₁; exact mdp this d₁; )
        (by apply deduct'; apply or₂'; apply negEquiv'.mpr; apply deduct;
          haveI d₁ : Prf 𝓢 [Tilde.tilde φ, Arrow.arrow (Tilde.tilde φ) φ] (Tilde.tilde φ) :=
            FiniteContext.byAxm;
          haveI d₂ :
            Prf 𝓢 [Tilde.tilde φ, Arrow.arrow (Tilde.tilde φ) φ] (Arrow.arrow (Tilde.tilde φ) φ) :=
            FiniteContext.byAxm;
          haveI := mdp d₂ d₁; exact mdp (negEquiv'.mp d₁) this; )
        this;


-- @@ L943-952 expanded
omit [DecidableEq F] in
noncomputable instance [HasAxiomDNE 𝓢] : HasAxiomPeirce 𝓢 where
  peirce φ
    ψ := by
    classical refine or₃''' imply₁ ?_ lem; apply deduct'; apply deduct;
    refine mdp (FiniteContext.byAxm (φ := Arrow.arrow (Arrow.arrow φ ψ) φ)) ?_; apply deduct;
    apply efqOfMemEither (φ := φ) (by aesop) (by aesop)


-- @@ L954-960 expanded
omit [DecidableEq F] in
instance [HasAxiomDNE 𝓢] : HasAxiomElimContra 𝓢 where
  elimContra φ
    ψ := by
    classical apply deduct';
    have :
      Prf 𝓢 [Arrow.arrow (Tilde.tilde ψ) (Tilde.tilde φ)]
        (Arrow.arrow (Tilde.tilde ψ) (Tilde.tilde φ)) :=
      FiniteContext.byAxm;
    exact contra₃' this;


-- @@ L962-962 verbatim
end «lp_section_2»


-- @@ L964-966 expanded
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def implyIffNotOr [HasAxiomDNE 𝓢] :
    Entailment.Prf 𝓢 (LogicalConnective.iff (Arrow.arrow φ ψ) (Vee.vee (Tilde.tilde φ) ψ)) :=
  iffIntro NotOrOfImply (deduct' (orCases efqImplyNot₁ imply₁ byAxm₀))


-- @@ L968-972 expanded
omit [DecidableEq F] in
/-- Imported declaration from the Incompleteness formalization. -/
lemma imply_iff_not_or! [HasAxiomDNE 𝓢] :
    Provable 𝓢 (LogicalConnective.iff (Arrow.arrow φ ψ) (Vee.vee (Tilde.tilde φ) ψ)) := by
  classical exact ⟨implyIffNotOr⟩


-- @@ L974-978 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def conjIffConj : (Γ : List F) → Entailment.Prf 𝓢 (LogicalConnective.iff (List.conj₂ Γ) Γ.conj)
  | [] => iffId ⊤
  | [_] => iffIntro (deduct' <| andIntro FiniteContext.id verum) and₁
  | φ :: ψ :: Γ => andIffAndOfIff (iffId φ) (conjIffConj (ψ :: Γ))


-- @@ L979-982 expanded
omit [DecidableEq F] in
@[simp]
lemma conjIffConj! : Provable 𝓢 (LogicalConnective.iff (List.conj₂ Γ) Γ.conj) := by
  classical exact ⟨conjIffConj Γ⟩


-- @@ L985-989 expanded
omit [DecidableEq F] in
lemma implyLeft_conj_eq_conj! :
    Provable 𝓢 (Arrow.arrow Γ.conj φ) ↔ Provable 𝓢 (Arrow.arrow (List.conj₂ Γ) φ) := by
  classical exact replace_imply_left_by_iff'! <| iff_comm'! conjIffConj!


-- @@ L992-996 expanded
omit [DecidableEq F] in
lemma generalConj'! (h : φ ∈ Γ) : Provable 𝓢 (Arrow.arrow (List.conj₂ Γ) φ) := by
  classical exact replace_imply_left_by_iff'! conjIffConj! |>.mpr (generalConj! h)


-- @@ L997-1000 expanded
omit [DecidableEq F] in
lemma generalConj'₂! (h : φ ∈ Γ) (d : Provable 𝓢 (List.conj₂ Γ)) : Provable 𝓢 φ := by
  classical exact mdp (generalConj'! h) d


-- @@ L1002-1002 verbatim
section «lp_section_3»


-- @@ L1004-1018 expanded
omit [DecidableEq F] in
lemma iff_provable_list_conj {Γ : List F} : (Provable 𝓢 (List.conj₂ Γ)) ↔ (∀ φ ∈ Γ, Provable 𝓢 φ) :=
  by
  classical
    induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp;
  | hcons φ Γ hΓ
    ih =>
    simp_all only [ne_eq, not_false_eq_true, conj₂_cons_nonempty, mem_cons, forall_eq_or_imp]
    constructor;
    · intro h; constructor; · exact and₁'! h;
      · exact ih.mp (and₂'! h);
    · rintro ⟨h₁, h₂⟩; exact and₃'! h₁ (ih.mpr h₂);


-- @@ L1020-1031 expanded
omit [DecidableEq F] in
lemma conjconj_subset! (h : ∀ φ, φ ∈ Γ → φ ∈ Δ) :
    Provable 𝓢 (Arrow.arrow (List.conj₂ Δ) (List.conj₂ Γ)) := by
  classical
    induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle =>
    simp_all only [mem_cons, not_mem_nil, or_false, forall_eq, conj₂_singleton]
    exact generalConj'! h;
  | hcons φ Γ hne
    ih =>
    simp_all only [ne_eq, mem_cons, or_true, implies_true, forall_const, forall_eq_or_imp,
      not_false_eq_true, conj₂_cons_nonempty]
    exact imply_right_and! (generalConj'! h.1) ih;


-- @@ L1033-1044 expanded
omit [DecidableEq F] in
lemma conjconj_provable! (h : ∀ φ, φ ∈ Γ → Provable 𝓢 Δ φ) :
    Provable 𝓢 (Arrow.arrow (List.conj₂ Δ) (List.conj₂ Γ)) := by
  classical
    exact by
    induction Γ using List.induction_with_singleton with
    | hnil => exact imply₁'! verum!;
    | hsingle =>
      simp_all only [mem_cons, not_mem_nil, or_false, forall_eq, conj₂_singleton]
      exact provable_iff.mp h;
    | hcons φ Γ hne
      ih =>
      simp_all only [ne_eq, mem_cons, or_true, implies_true, forall_const, forall_eq_or_imp,
        not_false_eq_true, conj₂_cons_nonempty]
      exact imply_right_and! (provable_iff.mp h.1) ih;


-- @@ L1046-1050 expanded
omit [DecidableEq F] in
lemma conjconj_provable₂! (h : ∀ φ, φ ∈ Γ → Provable 𝓢 Δ φ) : Provable 𝓢 Δ (List.conj₂ Γ) := by
  classical exact provable_iff.mpr <| conjconj_provable! h


-- @@ L1052-1060 expanded
omit [DecidableEq F] in
lemma id_conj! (he : ∀ g ∈ Γ, g = φ) : Provable 𝓢 (Arrow.arrow φ (List.conj₂ Γ)) := by
  classical
    induction Γ using List.induction_with_singleton with
  | hcons χ Γ h
    ih =>
    simp_all only [ne_eq, not_false_eq_true, conj₂_cons_nonempty, mem_cons, forall_eq_or_imp]
    have ⟨he₁, he₂⟩ := he; subst he₁; exact imply_right_and! imp_id! (ih he₂);
  | _ => simp_all;


-- @@ L1062-1066 expanded
omit [DecidableEq F] in
lemma replace_imply_left_conj! (he : ∀ g ∈ Γ, g = φ)
    (hd : Provable 𝓢 (Arrow.arrow (List.conj₂ Γ) ψ)) : Provable 𝓢 (Arrow.arrow φ ψ) := by
  classical exact imp_trans''! (id_conj! he) hd


-- @@ L1068-1077 expanded
omit [DecidableEq F] in
lemma iff_imply_left_cons_conj'! :
    Provable 𝓢 (Arrow.arrow (List.conj₂ (φ :: Γ)) ψ) ↔
      Provable 𝓢 (Arrow.arrow (Wedge.wedge φ (List.conj₂ Γ)) ψ) :=
  by
  classical
    induction Γ with
  | nil =>
    simp only [conj₂_singleton, conj₂_nil, and_imply_iff_imply_imply'!]
    constructor; · intro h; apply imp_swap'!; exact imply₁'! h;
    · intro h; exact mdp (imp_swap'! h) verum!;
  | cons ψ ih => simp;


-- @@ L1079-1090 expanded
omit [DecidableEq F] in
@[simp]
lemma imply_left_concat_conj! :
    Provable 𝓢 (Arrow.arrow (List.conj₂ (Γ ++ Δ)) (Wedge.wedge (List.conj₂ Γ) (List.conj₂ Δ))) := by
  classical
  apply FiniteContext.deduct'!;
  have : Provable 𝓢 [List.conj₂ (Γ ++ Δ)] (List.conj₂ (Γ ++ Δ)) := id!;
  have d := iff_provable_list_conj.mp this; apply and₃'!;
  · apply iff_provable_list_conj.mpr; simp_all
  · apply iff_provable_list_conj.mpr; simp_all


-- @@ L1092-1099 expanded
@[simp]
lemma forthback_conj_remove! :
    Provable 𝓢 (Arrow.arrow (Wedge.wedge (List.conj₂ (Γ.remove φ)) φ) (List.conj₂ Γ)) :=
  by
  apply deduct'!; apply iff_provable_list_conj.mpr; intro ψ hq; by_cases e : ψ = φ;
  · subst e; exact and₂'! id!;
  · exact iff_provable_list_conj.mp (and₁'! id!) ψ (by apply List.mem_remove_iff.mpr; simp_all);


-- @@ L1101-1103 expanded
lemma imply_left_remove_conj! (b : Provable 𝓢 (Arrow.arrow (List.conj₂ Γ) ψ)) :
    Provable 𝓢 (Arrow.arrow (Wedge.wedge (List.conj₂ (Γ.remove φ)) φ) ψ) :=
  imp_trans''! forthback_conj_remove! b


-- @@ L1105-1121 expanded
omit [DecidableEq F] in
lemma iff_concat_conj'! :
    Provable 𝓢 (List.conj₂ (Γ ++ Δ)) ↔ Provable 𝓢 (Wedge.wedge (List.conj₂ Γ) (List.conj₂ Δ)) := by
  classical
  constructor;
  · intro h; replace h := iff_provable_list_conj.mp h; apply and₃'!;
    · apply iff_provable_list_conj.mpr; intro φ hp;
      exact h φ (by simp only [List.mem_append]; left; simpa);
    · apply iff_provable_list_conj.mpr; intro φ hp;
      exact h φ (by simp only [List.mem_append]; right; simpa);
  · intro h; apply iff_provable_list_conj.mpr; simp only [List.mem_append]; rintro φ (hp₁ | hp₂);
    · exact (iff_provable_list_conj.mp <| and₁'! h) φ hp₁;
    · exact (iff_provable_list_conj.mp <| and₂'! h) φ hp₂;


-- @@ L1123-1129 expanded
omit [DecidableEq F] in
@[simp]
lemma iff_concat_conj! :
    Provable 𝓢
      (LogicalConnective.iff (List.conj₂ (Γ ++ Δ)) (Wedge.wedge (List.conj₂ Γ) (List.conj₂ Δ))) :=
  by
  classical
  apply iff_intro!; · apply deduct'!; apply iff_concat_conj'!.mp; exact id!;
  · apply deduct'!; apply iff_concat_conj'!.mpr; exact id!;


-- @@ L1131-1136 expanded
omit [DecidableEq F] in
lemma imply_left_conj_concat! :
    Provable 𝓢 (Arrow.arrow (List.conj₂ (Γ ++ Δ)) φ) ↔
      Provable 𝓢 (Arrow.arrow (Wedge.wedge (List.conj₂ Γ) (List.conj₂ Δ)) φ) :=
  by
  classical
  constructor; · intro h; exact imp_trans''! (and₂'! iff_concat_conj!) h;
  · intro h; exact imp_trans''! (and₁'! iff_concat_conj!) h;


-- @@ L1138-1138 verbatim
end «lp_section_3»



-- @@ L1141-1141 verbatim
section «lp_section_4»


-- @@ L1143-1190 expanded
omit [DecidableEq F] in
lemma iff_concact_disj! [HasAxiomEFQ 𝓢] :
    Provable 𝓢 (LogicalConnective.iff (disj₂ (Γ ++ Δ)) (Vee.vee (disj₂ Γ) (disj₂ Δ))) := by
  classical
  induction Γ using List.induction_with_singleton generalizing Δ <;>
    induction Δ using List.induction_with_singleton;
  case hnil.hnil =>
    simp_all only [append_nil, disj₂_nil]
    apply iff_intro!; · simp;
    · exact or₃''! efq! efq!;
  case hnil.hsingle =>
    simp_all only [nil_append, disj₂_singleton, disj₂_nil]
    apply iff_intro!; · simp;
    · exact or₃''! efq! imp_id!;
  case hsingle.hnil =>
    simp_all only [append_nil, disj₂_nil, disj₂_singleton]
    apply iff_intro!; · simp;
    · exact or₃''! imp_id! efq!;
  case
    hcons.hnil =>
    simp_all only [ne_eq, append_nil, not_false_eq_true, disj₂_cons_nonempty, disj₂_nil]
    apply iff_intro!; · simp;
    · exact or₃''! imp_id! efq!;
  case
    hnil.hcons =>
    simp_all only [ne_eq, nil_append, disj₂_nil, not_false_eq_true, disj₂_cons_nonempty]
    apply iff_intro!; · simp;
    · exact or₃''! efq! imp_id!;
  case hsingle.hsingle => simp_all;
  case hsingle.hcons => simp_all;
  case hcons.hsingle φ ps hps ihp
    ψ =>
    simp_all only [ne_eq, cons_append, append_eq_nil_iff, cons_ne_self, and_self, not_false_eq_true,
      disj₂_cons_nonempty, disj₂_singleton]
    apply iff_trans''! (by apply or_replace_right_iff!; simpa using @ihp [ψ]; ) or_assoc!;
  case hcons.hcons φ ps hps ihp ψ qs hqs
    ihq =>
    simp_all only [ne_eq, cons_append, append_eq_nil_iff, and_self, not_false_eq_true,
      disj₂_cons_nonempty, reduceCtorEq]
    exact
      iff_trans''!
        (by apply or_replace_right_iff!; exact iff_trans''! (@ihp (ψ :: qs)) (by simp_all))
        or_assoc!;


-- @@ L1192-1197 expanded
omit [DecidableEq F] in
lemma iff_concact_disj'! [HasAxiomEFQ 𝓢] :
    Provable 𝓢 (disj₂ (Γ ++ Δ)) ↔ Provable 𝓢 (Vee.vee (disj₂ Γ) (disj₂ Δ)) := by
  classical
  constructor; · intro h; exact mdp (and₁'! iff_concact_disj!) h;
  · intro h; exact mdp (and₂'! iff_concact_disj!) h;


-- @@ L1199-1208 expanded
omit [DecidableEq F] in
lemma implyRight_cons_disj! [HasAxiomEFQ 𝓢] :
    Provable 𝓢 (Arrow.arrow φ (disj₂ (ψ :: Γ))) ↔
      Provable 𝓢 (Arrow.arrow φ (Vee.vee ψ (disj₂ Γ))) :=
  by
  classical
    induction Γ with
  | nil =>
    simp only [disj₂_singleton, disj₂_nil]; constructor; · intro h; exact imp_trans''! h or₁!;
    · intro h; exact imp_trans''! h <| or₃''! imp_id! efq!;
  | cons ψ ih => simp;


-- @@ L1210-1228 expanded
@[simp]
lemma forthback_disj_remove [HasAxiomEFQ 𝓢] :
    Provable 𝓢 (Arrow.arrow (disj₂ Γ) (Vee.vee φ (disj₂ (Γ.remove φ)))) := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle ψ =>
    simp only [disj₂_singleton]; by_cases h : ψ = φ; · subst_vars; simp;
    · simp [(List.remove_singleton_of_ne h)];
  | hcons ψ Γ h ih =>
    simp_all only [ne_eq, not_false_eq_true, disj₂_cons_nonempty]
    by_cases hpq : ψ = φ; · simp_all only [List.remove_cons_self]; exact or₃''! or₁! ih;
    · rw [List.remove_cons_of_ne Γ hpq]; by_cases hqΓ : Γ.remove φ = [];
      · simp_all only [disj₂_nil, disj₂_singleton]
        exact or₃''! or₂! (imp_trans''! ih <| or_replace_right! efq!);
      · simp_all only [ne_eq, not_false_eq_true, disj₂_cons_nonempty]
        exact or₃''! (imp_trans''! or₁! or₂!) (imp_trans''! ih (or_replace_right! or₂!));


-- @@ L1230-1240 expanded
omit [DecidableEq F] in
lemma disj_allsame! [HasAxiomEFQ 𝓢] (hd : ∀ ψ ∈ Γ, ψ = φ) : Provable 𝓢 (Arrow.arrow (disj₂ Γ) φ) :=
  by
  classical
    induction Γ using List.induction_with_singleton with
  | hcons ψ Δ hΔ
    ih =>
    simp_all only [ne_eq, not_false_eq_true, disj₂_cons_nonempty, mem_cons, forall_eq_or_imp]
    have ⟨hd₁, hd₂⟩ := hd; subst hd₁; apply provable_iff_provable.mpr; apply deduct_iff.mpr;
    exact or₃'''! (by simp) (weakening! (by simp) <| provable_iff_provable.mp <| ih hd₂) id!
  | _ => simp_all;


-- @@ L1242-1246 expanded
omit [DecidableEq F] in
lemma disj_allsame'! [HasAxiomEFQ 𝓢] (hd : ∀ ψ ∈ Γ, ψ = φ) (h : Provable 𝓢 (disj₂ Γ)) :
    Provable 𝓢 φ := by classical exact mdp (disj_allsame! hd) h


-- @@ L1248-1248 verbatim
end «lp_section_4»


-- @@ L1250-1250 verbatim
section «lp_section_5»


-- @@ L1252-1252 verbatim
variable [HasAxiomEFQ 𝓢]


-- @@ L1254-1259 expanded
omit [DecidableEq F] in
lemma inconsistent_of_provable_of_unprovable {φ : F} (hp : Provable 𝓢 φ)
    (hn : Provable 𝓢 (Tilde.tilde φ)) : Inconsistent 𝓢 := by
  classical
  have : Provable 𝓢 (Arrow.arrow φ ⊥) := negEquiv'!.mp hn
  intro ψ; exact mdp efq! (mdp this hp)


-- @@ L1261-1261 verbatim
end «lp_section_5»


-- @@ L1263-1263 verbatim
end Entailment

-- @@ L1264-1264 verbatim
end LO
