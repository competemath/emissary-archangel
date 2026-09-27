/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Entailment.Basic
public import LeanPool.Incompleteness.Foundation.Logic.HilbertStyle.Supplemental


-- @@ L11-11 verbatim
/-! # K -/


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
variable {𝓢 : S} [Entailment.K 𝓢]


-- @@ L24-28 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def multiboxAxiomK :
    Entailment.Prf 𝓢
      (Arrow.arrow (multibox n (Arrow.arrow φ ψ)) (Arrow.arrow (multibox n φ) (multibox n ψ))) :=
  by
  induction n with
  | zero => simp only [Function.iterate_zero, id_eq]; apply impId;
  | succ n ih => simpa using impTrans'' (axiomK' <| nec ih) (by apply axiomK);


-- @@ L29-31 expanded
omit [DecidableEq F] in
@[simp]
lemma multiboxAxiomK! :
    Provable 𝓢
      (Arrow.arrow (multibox n (Arrow.arrow φ ψ)) (Arrow.arrow (multibox n φ) (multibox n ψ))) :=
  ⟨multiboxAxiomK⟩


-- @@ L33-34 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def multiboxAxiomK' (h : Entailment.Prf 𝓢 (multibox n (Arrow.arrow φ ψ))) :
    Entailment.Prf 𝓢 (Arrow.arrow (multibox n φ) (multibox n ψ)) :=
  mdp multiboxAxiomK h


-- @@ L35-37 expanded
omit [DecidableEq F] in
@[simp]
lemma multiboxAxiomK'! (h : Provable 𝓢 (multibox n (Arrow.arrow φ ψ))) :
    Provable 𝓢 (Arrow.arrow (multibox n φ) (multibox n ψ)) :=
  ⟨multiboxAxiomK' h.some⟩


-- @@ L39-39 verbatim
alias multiboxedImplyDistribute := multiboxAxiomK'

-- @@ L40-40 verbatim
alias multiboxed_imply_distribute! := multiboxAxiomK'!



-- @@ L43-45 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def boxIff' (h : Entailment.Prf 𝓢 (LogicalConnective.iff φ ψ)) :
    Entailment.Prf 𝓢 (LogicalConnective.iff (Box.box φ) (Box.box ψ)) :=
  iffIntro (axiomK' <| nec <| and₁' h) (axiomK' <| nec <| and₂' h)


-- @@ L46-47 expanded
omit [DecidableEq F] in
@[simp]
lemma box_iff! (h : Provable 𝓢 (LogicalConnective.iff φ ψ)) :
    Provable 𝓢 (LogicalConnective.iff (Box.box φ) (Box.box ψ)) :=
  ⟨boxIff' h.some⟩


-- @@ L49-53 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def multiboxIff' (h : Entailment.Prf 𝓢 (LogicalConnective.iff φ ψ)) :
    Entailment.Prf 𝓢 (LogicalConnective.iff (multibox n φ) (multibox n ψ)) := by
  induction n with
  | zero => simpa;
  | succ n ih => simpa using boxIff' ih;


-- @@ L54-55 expanded
omit [DecidableEq F] in
@[simp]
lemma multibox_iff! (h : Provable 𝓢 (LogicalConnective.iff φ ψ)) :
    Provable 𝓢 (LogicalConnective.iff (multibox n φ) (multibox n ψ)) :=
  ⟨multiboxIff' h.some⟩


-- @@ L58-59 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def diaDualityMp :
    Entailment.Prf 𝓢 (Arrow.arrow (Dia.dia φ) (Tilde.tilde (Box.box (Tilde.tilde φ)))) :=
  and₁' diaDuality


-- @@ L60-62 expanded
omit [DecidableEq F] in
@[simp]
lemma diaDualityMp! :
    Provable 𝓢 (Arrow.arrow (Dia.dia φ) (Tilde.tilde (Box.box (Tilde.tilde φ)))) := by
  classical exact ⟨diaDualityMp⟩


-- @@ L64-65 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def diaDualityMpr :
    Entailment.Prf 𝓢 (Arrow.arrow (Tilde.tilde (Box.box (Tilde.tilde φ))) (Dia.dia φ)) :=
  and₂' diaDuality


-- @@ L66-68 expanded
omit [DecidableEq F] in
@[simp]
lemma diaDualityMpr! :
    Provable 𝓢 (Arrow.arrow (Tilde.tilde (Box.box (Tilde.tilde φ))) (Dia.dia φ)) := by
  classical exact ⟨diaDualityMpr⟩


-- @@ L70-71 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Entailment.diaDuality'.mp (h : Entailment.Prf 𝓢 (Dia.dia φ)) :
    Entailment.Prf 𝓢 (Tilde.tilde (Box.box (Tilde.tilde φ))) :=
  mdp (and₁' diaDuality) h


-- @@ L72-73 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Entailment.diaDuality'.mpr
    (h : Entailment.Prf 𝓢 (Tilde.tilde (Box.box (Tilde.tilde φ)))) : Entailment.Prf 𝓢 (Dia.dia φ) :=
  mdp (and₂' diaDuality) h


-- @@ L75-81 expanded
omit [DecidableEq F] in
lemma dia_duality'! : Provable 𝓢 (Dia.dia φ) ↔ Provable 𝓢 (Tilde.tilde (Box.box (Tilde.tilde φ))) :=
  by classical exact ⟨fun h => ⟨diaDuality'.mp h.some⟩, fun h => ⟨diaDuality'.mpr h.some⟩⟩


-- @@ L83-94 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def multiDiaDuality :
    Entailment.Prf 𝓢
      (LogicalConnective.iff (multidia n φ) (Tilde.tilde (multibox n (Tilde.tilde φ)))) :=
  by
  induction n with
  | zero => simp only [Function.iterate_zero, id_eq]; apply dn;
  | succ n ih =>
    simp only [Dia.multidia_succ, Box.multibox_succ];
    apply iffTrans'' <| diaDuality (φ := multidia n φ); apply negReplaceIff'; apply boxIff';
    apply iffIntro; · exact contra₂' <| and₂' ih;
    · exact contra₁' <| and₁' ih;


-- @@ L95-98 expanded
omit [DecidableEq F] in
lemma multidia_duality! :
    Provable 𝓢 (LogicalConnective.iff (multidia n φ) (Tilde.tilde (multibox n (Tilde.tilde φ)))) :=
  by classical exact ⟨multiDiaDuality⟩


-- @@ L100-105 expanded
omit [DecidableEq F] in
lemma multidia_duality'! :
    Provable 𝓢 (multidia n φ) ↔ Provable 𝓢 (Tilde.tilde (multibox n (Tilde.tilde φ))) := by
  classical
  constructor; · intro h; exact mdp (and₁'! multidia_duality!) h;
  · intro h; exact mdp (and₂'! multidia_duality!) h;


-- @@ L107-116 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def diaIff' (h : Entailment.Prf 𝓢 (LogicalConnective.iff φ ψ)) :
    Entailment.Prf 𝓢 (LogicalConnective.iff (Dia.dia φ) (Dia.dia ψ)) := by
  apply iffTrans'' diaDuality; apply andComm'; apply iffTrans'' diaDuality; apply negReplaceIff';
  apply boxIff'; apply negReplaceIff'; apply andComm'; assumption;


-- @@ L118-121 expanded
omit [DecidableEq F] in
@[simp]
lemma dia_iff! (h : Provable 𝓢 (LogicalConnective.iff φ ψ)) :
    Provable 𝓢 (LogicalConnective.iff (Dia.dia φ) (Dia.dia ψ)) := by
  classical exact ⟨diaIff' h.some⟩


-- @@ L123-127 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def multidiaIff' (h : Entailment.Prf 𝓢 (LogicalConnective.iff φ ψ)) :
    Entailment.Prf 𝓢 (LogicalConnective.iff (multidia n φ) (multidia n ψ)) := by
  induction n with
  | zero => simpa;
  | succ n ih => simpa using diaIff' ih;


-- @@ L128-131 expanded
omit [DecidableEq F] in
@[simp]
lemma multidia_iff! (h : Provable 𝓢 (LogicalConnective.iff φ ψ)) :
    Provable 𝓢 (LogicalConnective.iff (multidia n φ) (multidia n ψ)) := by
  classical exact ⟨multidiaIff' h.some⟩


-- @@ L133-141 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def multiboxDuality :
    Entailment.Prf 𝓢
      (LogicalConnective.iff (multibox n φ) (Tilde.tilde (multidia n (Tilde.tilde φ)))) :=
  by
  induction n with
  | zero => simp only [Function.iterate_zero, id_eq]; apply dn;
  | succ n ih => simp only [Box.multibox_succ, Dia.multidia_succ]; apply iffTrans'' (boxIff' ih);
    apply iffNegRightToLeft'; exact iffComm' <| diaDuality;


-- @@ L143-146 expanded
omit [DecidableEq F] in
@[simp]
lemma multibox_duality! :
    Provable 𝓢 (LogicalConnective.iff (multibox n φ) (Tilde.tilde (multidia n (Tilde.tilde φ)))) :=
  by classical exact ⟨multiboxDuality⟩


-- @@ L148-149 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def boxDuality :
    Entailment.Prf 𝓢 (LogicalConnective.iff (Box.box φ) (Tilde.tilde (Dia.dia (Tilde.tilde φ)))) :=
  multiboxDuality (n := 1)


-- @@ L150-153 expanded
omit [DecidableEq F] in
@[simp]
lemma box_duality! :
    Provable 𝓢 (LogicalConnective.iff (Box.box φ) (Tilde.tilde (Dia.dia (Tilde.tilde φ)))) := by
  classical exact ⟨boxDuality⟩


-- @@ L155-156 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def boxDualityMp :
    Entailment.Prf 𝓢 (Arrow.arrow (Box.box φ) (Tilde.tilde (Dia.dia (Tilde.tilde φ)))) :=
  and₁' boxDuality


-- @@ L157-160 expanded
omit [DecidableEq F] in
@[simp]
lemma boxDualityMp! :
    Provable 𝓢 (Arrow.arrow (Box.box φ) (Tilde.tilde (Dia.dia (Tilde.tilde φ)))) := by
  classical exact ⟨boxDualityMp⟩


-- @@ L162-163 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def boxDualityMp' (h : Entailment.Prf 𝓢 (Box.box φ)) :
    Entailment.Prf 𝓢 (Tilde.tilde (Dia.dia (Tilde.tilde φ))) :=
  mdp boxDualityMp h


-- @@ L164-167 expanded
omit [DecidableEq F] in
lemma boxDualityMp'! (h : Provable 𝓢 (Box.box φ)) :
    Provable 𝓢 (Tilde.tilde (Dia.dia (Tilde.tilde φ))) := by classical exact ⟨boxDualityMp' h.some⟩


-- @@ L169-170 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def boxDualityMpr :
    Entailment.Prf 𝓢 (Arrow.arrow (Tilde.tilde (Dia.dia (Tilde.tilde φ))) (Box.box φ)) :=
  and₂' boxDuality


-- @@ L171-174 expanded
omit [DecidableEq F] in
@[simp]
lemma boxDualityMpr! :
    Provable 𝓢 (Arrow.arrow (Tilde.tilde (Dia.dia (Tilde.tilde φ))) (Box.box φ)) := by
  classical exact ⟨boxDualityMpr⟩


-- @@ L176-177 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def boxDualityMpr' (h : Entailment.Prf 𝓢 (Tilde.tilde (Dia.dia (Tilde.tilde φ)))) :
    Entailment.Prf 𝓢 (Box.box φ) :=
  mdp boxDualityMpr h


-- @@ L178-181 expanded
omit [DecidableEq F] in
lemma boxDualityMpr'! (h : Provable 𝓢 (Tilde.tilde (Dia.dia (Tilde.tilde φ)))) :
    Provable 𝓢 (Box.box φ) := by classical exact ⟨boxDualityMpr' h.some⟩


-- @@ L183-188 expanded
omit [DecidableEq F] in
lemma multibox_duality'! :
    Provable 𝓢 (multibox n φ) ↔ Provable 𝓢 (Tilde.tilde (multidia n (Tilde.tilde φ))) := by
  classical
  constructor; · intro h; exact mdp (and₁'! multibox_duality!) h;
  · intro h; exact mdp (and₂'! multibox_duality!) h;


-- @@ L190-193 expanded
omit [DecidableEq F] in
lemma box_duality'! : Provable 𝓢 (Box.box φ) ↔ Provable 𝓢 (Tilde.tilde (Dia.dia (Tilde.tilde φ))) :=
  by classical exact multibox_duality'! (n := 1)


-- @@ L195-196 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def boxDni : Entailment.Prf 𝓢 (Arrow.arrow (Box.box φ) (Box.box (Tilde.tilde (Tilde.tilde φ)))) :=
  axiomK' <| nec dni


-- @@ L197-200 expanded
omit [DecidableEq F] in
@[simp]
lemma boxDni! : Provable 𝓢 (Arrow.arrow (Box.box φ) (Box.box (Tilde.tilde (Tilde.tilde φ)))) := by
  classical exact ⟨boxDni⟩


-- @@ L202-203 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def boxDni' (h : Entailment.Prf 𝓢 (Box.box φ)) :
    Entailment.Prf 𝓢 (Box.box (Tilde.tilde (Tilde.tilde φ))) :=
  mdp boxDni h


-- @@ L204-207 expanded
omit [DecidableEq F] in
lemma boxDni'! (h : Provable 𝓢 (Box.box φ)) : Provable 𝓢 (Box.box (Tilde.tilde (Tilde.tilde φ))) :=
  by classical exact ⟨boxDni' h.some⟩


-- @@ L209-210 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def boxDne : Entailment.Prf 𝓢 (Arrow.arrow (Box.box (Tilde.tilde (Tilde.tilde φ))) (Box.box φ)) :=
  axiomK' <| nec dne


-- @@ L211-213 expanded
omit [DecidableEq F] in
@[simp]
lemma boxDne! : Provable 𝓢 (Arrow.arrow (Box.box (Tilde.tilde (Tilde.tilde φ))) (Box.box φ)) := by
  classical exact ⟨boxDne⟩


-- @@ L215-216 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def boxDne' (h : Entailment.Prf 𝓢 (Box.box (Tilde.tilde (Tilde.tilde φ)))) :
    Entailment.Prf 𝓢 (Box.box φ) :=
  mdp boxDne h


-- @@ L217-219 expanded
omit [DecidableEq F] in
lemma boxDne'! (h : Provable 𝓢 (Box.box (Tilde.tilde (Tilde.tilde φ)))) : Provable 𝓢 (Box.box φ) :=
  by classical exact ⟨boxDne' h.some⟩


-- @@ L222-223 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def multiboxverum : Entailment.Prf 𝓢 (multibox n ⊤ : F) :=
  multinec verum


-- @@ L224-226 expanded
omit [DecidableEq F] in
@[simp]
lemma multiboxverum! : Provable 𝓢 (multibox n ⊤ : F) := by classical exact ⟨multiboxverum⟩


-- @@ L228-229 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def boxverum : Entailment.Prf 𝓢 (Box.box ⊤ : F) :=
  multiboxverum (n := 1)


-- @@ L230-232 expanded
omit [DecidableEq F] in
@[simp]
lemma boxverum! : Provable 𝓢 (Box.box ⊤ : F) := by classical exact ⟨boxverum⟩


-- @@ L234-235 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def boxdotverum : Entailment.Prf 𝓢 (boxdot ⊤ : F) :=
  andIntro verum boxverum


-- @@ L236-238 expanded
omit [DecidableEq F] in
@[simp]
lemma boxdotverum! : Provable 𝓢 (boxdot ⊤ : F) := by classical exact ⟨boxdotverum⟩


-- @@ L240-243 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def implyMultiboxDistribute' (h : Entailment.Prf 𝓢 (Arrow.arrow φ ψ)) :
    Entailment.Prf 𝓢 (Arrow.arrow (multibox n φ) (multibox n ψ)) :=
  multiboxAxiomK' <| multinec h


-- @@ L244-246 expanded
omit [DecidableEq F] in
lemma imply_multibox_distribute'! (h : Provable 𝓢 (Arrow.arrow φ ψ)) :
    Provable 𝓢 (Arrow.arrow (multibox n φ) (multibox n ψ)) :=
  ⟨implyMultiboxDistribute' h.some⟩


-- @@ L248-249 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def implyBoxDistribute' (h : Entailment.Prf 𝓢 (Arrow.arrow φ ψ)) :
    Entailment.Prf 𝓢 (Arrow.arrow (Box.box φ) (Box.box ψ)) :=
  implyMultiboxDistribute' (n := 1) h


-- @@ L250-251 expanded
omit [DecidableEq F] in
lemma imply_box_distribute'! (h : Provable 𝓢 (Arrow.arrow φ ψ)) :
    Provable 𝓢 (Arrow.arrow (Box.box φ) (Box.box ψ)) :=
  ⟨implyBoxDistribute' h.some⟩


-- @@ L254-257 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def distributeMultiboxAnd :
    Entailment.Prf 𝓢
      (Arrow.arrow (multibox n (Wedge.wedge φ ψ)) (Wedge.wedge (multibox n φ) (multibox n ψ))) :=
  implyRightAnd (implyMultiboxDistribute' and₁) (implyMultiboxDistribute' and₂)


-- @@ L258-263 expanded
omit [DecidableEq F] in
@[simp]
lemma distributeMultiboxAnd! :
    Provable 𝓢
      (Arrow.arrow (multibox n (Wedge.wedge φ ψ)) (Wedge.wedge (multibox n φ) (multibox n ψ))) :=
  by classical exact ⟨distributeMultiboxAnd⟩


-- @@ L265-266 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def distributeBoxAnd :
    Entailment.Prf 𝓢
      (Arrow.arrow (Box.box (Wedge.wedge φ ψ)) (Wedge.wedge (Box.box φ) (Box.box ψ))) :=
  distributeMultiboxAnd (n := 1)


-- @@ L267-270 expanded
omit [DecidableEq F] in
@[simp]
lemma distributeBoxAnd! :
    Provable 𝓢 (Arrow.arrow (Box.box (Wedge.wedge φ ψ)) (Wedge.wedge (Box.box φ) (Box.box ψ))) := by
  classical exact ⟨distributeBoxAnd⟩


-- @@ L272-275 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def distributeMultiboxAnd' (h : Entailment.Prf 𝓢 (multibox n (Wedge.wedge φ ψ))) :
    Entailment.Prf 𝓢 (Wedge.wedge (multibox n φ) (multibox n ψ)) :=
  mdp distributeMultiboxAnd h


-- @@ L276-281 expanded
omit [DecidableEq F] in
lemma distributeMultiboxAnd'! (d : Provable 𝓢 (multibox n (Wedge.wedge φ ψ))) :
    Provable 𝓢 (Wedge.wedge (multibox n φ) (multibox n ψ)) := by
  classical exact ⟨distributeMultiboxAnd' d.some⟩


-- @@ L283-284 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def distributeBoxAnd' (h : Entailment.Prf 𝓢 (Box.box (Wedge.wedge φ ψ))) :
    Entailment.Prf 𝓢 (Wedge.wedge (Box.box φ) (Box.box ψ)) :=
  distributeMultiboxAnd' (n := 1) h


-- @@ L285-288 expanded
omit [DecidableEq F] in
lemma distributeBoxAnd'! (d : Provable 𝓢 (Box.box (Wedge.wedge φ ψ))) :
    Provable 𝓢 (Wedge.wedge (Box.box φ) (Box.box ψ)) := by
  classical exact ⟨distributeBoxAnd' d.some⟩


-- @@ L290-299 expanded
omit [DecidableEq F] in
lemma conj_cons! :
    Provable 𝓢 (LogicalConnective.iff (Wedge.wedge φ (List.conj₂ Γ)) (List.conj₂ (φ :: Γ))) := by
  classical
    induction Γ using List.induction_with_singleton with
  | hnil =>
    simp only [List.conj₂_nil, List.conj₂_singleton]; apply iff_intro!; · simp;
    · exact imply_right_and! (by simp) (by simp);
  | _ => simp;


-- @@ L301-321 expanded
@[simp]
lemma distribute_multibox_conj! :
    Provable 𝓢 (Arrow.arrow (multibox n (List.conj₂ Γ)) (List.conj₂ (List.multibox n Γ))) := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp;
  | hcons φ Γ h ih => simp_all only [ne_eq, not_false_eq_true, List.conj₂_cons_nonempty];
    have h₁ : Provable 𝓢 (Arrow.arrow (multibox n (Wedge.wedge φ (List.conj₂ Γ))) (multibox n φ)) :=
      imply_multibox_distribute'! <| and₁!;
    have h₂ :
      Provable 𝓢
        (Arrow.arrow (multibox n (Wedge.wedge φ (List.conj₂ Γ)))
          (List.conj₂ (List.multibox n Γ))) :=
      imp_trans''! (imply_multibox_distribute'! <| and₂!) ih;
    have := imply_right_and! h₁ h₂;
    exact
      imp_trans''! this <| by
        apply imply_conj'!; intro ψ hq;
        simp only [Finset.mem_toList, List.toFinset_cons, Finset.image_insert, Finset.mem_insert,
          Finset.mem_image, List.mem_toFinset] at hq;
        rcases hq with (rfl | ⟨ψ, hq, rfl⟩)
        · apply and₁!;
        · suffices Provable 𝓢 (Arrow.arrow (List.conj₂ (List.multibox n Γ)) (multibox n ψ)) by
            exact dhyp_and_left! this;
          apply generate_conj'!; simpa;


-- @@ L323-323 expanded
@[simp]
lemma distribute_box_conj! :
    Provable 𝓢 (Arrow.arrow (Box.box (List.conj₂ Γ)) (List.conj₂ (List.box Γ))) :=
  distribute_multibox_conj! (n := 1)


-- @@ L325-329 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def collectMultiboxAnd :
    Entailment.Prf 𝓢
      (Arrow.arrow (Wedge.wedge (multibox n φ) (multibox n ψ)) (multibox n (Wedge.wedge φ ψ))) :=
  by
  have d₁ :
    Entailment.Prf 𝓢 (Arrow.arrow (multibox n φ) (multibox n (Arrow.arrow ψ (Wedge.wedge φ ψ)))) :=
    implyMultiboxDistribute' and₃;
  have d₂ :
    Entailment.Prf 𝓢
      (Arrow.arrow (multibox n (Arrow.arrow ψ (Wedge.wedge φ ψ)))
        (Arrow.arrow (multibox n ψ) (multibox n (Wedge.wedge φ ψ)))) :=
    multiboxAxiomK;
  exact mdp (and₂' (andImplyIffImplyImply _ _ _)) (impTrans'' d₁ d₂);


-- @@ L330-332 expanded
omit [DecidableEq F] in
@[simp]
lemma collectMultiboxAnd! :
    Provable 𝓢
      (Arrow.arrow (Wedge.wedge (multibox n φ) (multibox n ψ)) (multibox n (Wedge.wedge φ ψ))) :=
  ⟨collectMultiboxAnd⟩


-- @@ L334-335 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def collectBoxAnd :
    Entailment.Prf 𝓢
      (Arrow.arrow (Wedge.wedge (Box.box φ) (Box.box ψ)) (Box.box (Wedge.wedge φ ψ))) :=
  collectMultiboxAnd (n := 1)


-- @@ L336-336 expanded
omit [DecidableEq F] in
@[simp]
lemma collectBoxAnd! :
    Provable 𝓢 (Arrow.arrow (Wedge.wedge (Box.box φ) (Box.box ψ)) (Box.box (Wedge.wedge φ ψ))) :=
  ⟨collectBoxAnd⟩


-- @@ L338-339 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def collectMultiboxAnd' (h : Entailment.Prf 𝓢 (Wedge.wedge (multibox n φ) (multibox n ψ))) :
    Entailment.Prf 𝓢 (multibox n (Wedge.wedge φ ψ)) :=
  mdp collectMultiboxAnd h


-- @@ L340-342 expanded
omit [DecidableEq F] in
lemma collectMultiboxAnd'! (h : Provable 𝓢 (Wedge.wedge (multibox n φ) (multibox n ψ))) :
    Provable 𝓢 (multibox n (Wedge.wedge φ ψ)) :=
  ⟨collectMultiboxAnd' h.some⟩


-- @@ L344-345 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def collectBoxAnd' (h : Entailment.Prf 𝓢 (Wedge.wedge (Box.box φ) (Box.box ψ))) :
    Entailment.Prf 𝓢 (Box.box (Wedge.wedge φ ψ)) :=
  collectMultiboxAnd' (n := 1) h


-- @@ L346-347 expanded
omit [DecidableEq F] in
lemma collectBoxAnd'! (h : Provable 𝓢 (Wedge.wedge (Box.box φ) (Box.box ψ))) :
    Provable 𝓢 (Box.box (Wedge.wedge φ ψ)) :=
  ⟨collectBoxAnd' h.some⟩


-- @@ L350-365 expanded
omit [DecidableEq F] in
lemma multiboxConj'_iff! :
    Provable 𝓢 (multibox n (List.conj₂ Γ)) ↔ ∀ φ ∈ Γ, Provable 𝓢 (multibox n φ) := by
  classical
    induction Γ using List.induction_with_singleton with
  | hcons φ Γ h
    ih =>
    simp_all only [ne_eq, not_false_eq_true, List.conj₂_cons_nonempty, List.mem_cons,
      forall_eq_or_imp];
    constructor;
    · intro h; have := distributeMultiboxAnd'! h; constructor; · exact and₁'! this;
      · exact ih.mp (and₂'! this);
    · rintro ⟨h₁, h₂⟩; exact collectMultiboxAnd'! <| and₃'! h₁ (ih.mpr h₂);
  | _ => simp_all;


-- @@ L366-369 expanded
omit [DecidableEq F] in
lemma boxConj'_iff! : Provable 𝓢 (Box.box (List.conj₂ Γ)) ↔ ∀ φ ∈ Γ, Provable 𝓢 (Box.box φ) := by
  classical exact multiboxConj'_iff! (n := 1)


-- @@ L371-374 expanded
lemma multiboxconj_of_conjmultibox! (d : Provable 𝓢 (List.conj₂ (List.multibox n Γ))) :
    Provable 𝓢 (multibox n (List.conj₂ Γ)) := by apply multiboxConj'_iff!.mpr; intro φ hp;
  exact iff_provable_list_conj.mp d (multibox n φ) (by aesop);


-- @@ L376-379 expanded
@[simp]
lemma multibox_cons_conjAux₁! :
    Provable 𝓢
      (Arrow.arrow (List.conj₂ (List.multibox n (φ :: Γ))) (List.conj₂ (List.multibox n Γ))) :=
  by apply conjconj_subset!; simp_all;


-- @@ L381-385 expanded
@[simp]
lemma multibox_cons_conjAux₂! :
    Provable 𝓢 (Arrow.arrow (List.conj₂ (List.multibox n (φ :: Γ))) (multibox n φ)) :=
  by
  suffices
    Provable 𝓢
      (Arrow.arrow (List.conj₂ (List.multibox n (φ :: Γ))) (List.conj₂ (List.multibox n ([φ]))))
    by simpa;
  apply conjconj_subset!; simp_all;


-- @@ L388-390 expanded
@[simp]
lemma multibox_cons_conj! :
    Provable 𝓢
      (Arrow.arrow (List.conj₂ (List.multibox n (φ :: Γ)))
        (Wedge.wedge (List.conj₂ (List.multibox n Γ)) (multibox n φ))) :=
  imply_right_and! multibox_cons_conjAux₁! multibox_cons_conjAux₂!


-- @@ L392-401 expanded
@[simp]
lemma collect_multibox_conj! :
    Provable 𝓢 (Arrow.arrow (List.conj₂ (List.multibox n Γ)) (multibox n (List.conj₂ Γ))) := by
  induction Γ using List.induction_with_singleton with
  | hnil => simpa using imply₁'! multiboxverum!;
  | hsingle => simp;
  | hcons φ Γ h ih => simp_all only [ne_eq, not_false_eq_true, List.conj₂_cons_nonempty];
    exact
      imp_trans''! (imply_right_and! (generalConj'! (by simp)) (imp_trans''! (by simp) ih))
        collectMultiboxAnd!;


-- @@ L403-404 expanded
@[simp]
lemma collect_box_conj! :
    Provable 𝓢 (Arrow.arrow (List.conj₂ (List.box Γ)) (Box.box (List.conj₂ Γ))) :=
  collect_multibox_conj! (n := 1)


-- @@ L407-410 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def collectMultiboxOr :
    Entailment.Prf 𝓢
      (Arrow.arrow (Vee.vee (multibox n φ) (multibox n ψ)) (multibox n (Vee.vee φ ψ))) :=
  or₃'' (multiboxAxiomK' <| multinec or₁) (multiboxAxiomK' <| multinec or₂)


-- @@ L411-413 expanded
omit [DecidableEq F] in
@[simp]
lemma collectMultiboxOr! :
    Provable 𝓢 (Arrow.arrow (Vee.vee (multibox n φ) (multibox n ψ)) (multibox n (Vee.vee φ ψ))) :=
  ⟨collectMultiboxOr⟩


-- @@ L415-416 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def collectBoxOr :
    Entailment.Prf 𝓢 (Arrow.arrow (Vee.vee (Box.box φ) (Box.box ψ)) (Box.box (Vee.vee φ ψ))) :=
  collectMultiboxOr (n := 1)


-- @@ L417-417 expanded
omit [DecidableEq F] in
@[simp]
lemma collectBoxOr! :
    Provable 𝓢 (Arrow.arrow (Vee.vee (Box.box φ) (Box.box ψ)) (Box.box (Vee.vee φ ψ))) :=
  ⟨collectBoxOr⟩


-- @@ L419-420 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def collectMultiboxOr' (h : Entailment.Prf 𝓢 (Vee.vee (multibox n φ) (multibox n ψ))) :
    Entailment.Prf 𝓢 (multibox n (Vee.vee φ ψ)) :=
  mdp collectMultiboxOr h


-- @@ L421-423 expanded
omit [DecidableEq F] in
lemma collectMultiboxOr'! (h : Provable 𝓢 (Vee.vee (multibox n φ) (multibox n ψ))) :
    Provable 𝓢 (multibox n (Vee.vee φ ψ)) :=
  ⟨collectMultiboxOr' h.some⟩


-- @@ L425-426 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def collectBoxOr' (h : Entailment.Prf 𝓢 (Vee.vee (Box.box φ) (Box.box ψ))) :
    Entailment.Prf 𝓢 (Box.box (Vee.vee φ ψ)) :=
  collectMultiboxOr' (n := 1) h


-- @@ L427-428 expanded
omit [DecidableEq F] in
lemma collectBoxOr'! (h : Provable 𝓢 (Vee.vee (Box.box φ) (Box.box ψ))) :
    Provable 𝓢 (Box.box (Vee.vee φ ψ)) :=
  ⟨collectBoxOr' h.some⟩


-- @@ L430-437 expanded
/-- Lift an implication with a disjunctive conclusion through possibility. -/
def diaOrInstOf (h : Entailment.Prf 𝓢 (Arrow.arrow χ (Vee.vee φ ψ))) :
    Entailment.Prf 𝓢 (Arrow.arrow (Dia.dia χ) (Dia.dia (Vee.vee φ ψ))) := by
  apply impTrans'' (and₁' diaDuality); apply impTrans'' ?h (and₂' diaDuality); apply contra₀';
  apply axiomK'; apply nec; exact contra₀' h;


-- @@ L439-440 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def diaOrInst₁ : Entailment.Prf 𝓢 (Arrow.arrow (Dia.dia φ) (Dia.dia (Vee.vee φ ψ))) :=
  diaOrInstOf or₁


-- @@ L441-444 expanded
omit [DecidableEq F] in
@[simp]
lemma dia_or_inst₁! : Provable 𝓢 (Arrow.arrow (Dia.dia φ) (Dia.dia (Vee.vee φ ψ))) := by
  classical exact ⟨diaOrInst₁⟩


-- @@ L446-447 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def diaOrInst₂ : Entailment.Prf 𝓢 (Arrow.arrow (Dia.dia ψ) (Dia.dia (Vee.vee φ ψ))) :=
  diaOrInstOf or₂


-- @@ L448-451 expanded
omit [DecidableEq F] in
@[simp]
lemma dia_or_inst₂! : Provable 𝓢 (Arrow.arrow (Dia.dia ψ) (Dia.dia (Vee.vee φ ψ))) := by
  classical exact ⟨diaOrInst₂⟩


-- @@ L453-454 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def collectDiaOr :
    Entailment.Prf 𝓢 (Arrow.arrow (Vee.vee (Dia.dia φ) (Dia.dia ψ)) (Dia.dia (Vee.vee φ ψ))) :=
  or₃'' diaOrInst₁ diaOrInst₂


-- @@ L455-458 expanded
omit [DecidableEq F] in
@[simp]
lemma collectDiaOr! :
    Provable 𝓢 (Arrow.arrow (Vee.vee (Dia.dia φ) (Dia.dia ψ)) (Dia.dia (Vee.vee φ ψ))) := by
  classical exact ⟨collectDiaOr⟩


-- @@ L460-461 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def collectDiaOr' (h : Entailment.Prf 𝓢 (Vee.vee (Dia.dia φ) (Dia.dia ψ))) :
    Entailment.Prf 𝓢 (Dia.dia (Vee.vee φ ψ)) :=
  mdp collectDiaOr h


-- @@ L462-467 expanded
omit [DecidableEq F] in
@[simp]
lemma collectDiaOr'! (h : Provable 𝓢 (Vee.vee (Dia.dia φ) (Dia.dia ψ))) :
    Provable 𝓢 (Dia.dia (Vee.vee φ ψ)) := by
  classical
    exact
    ⟨collectDiaOr' h.some⟩
      -- TODO: `distributeMultidiaAnd!` is computable but it's too slow, so leave it.


-- @@ L468-478 expanded
omit [DecidableEq F] in
@[simp]
lemma distribute_multidia_and! :
    Provable 𝓢
      (Arrow.arrow (multidia n (Wedge.wedge φ ψ)) (Wedge.wedge (multidia n φ) (multidia n ψ))) :=
  by
  classical
  suffices h :
    Provable 𝓢
      (Arrow.arrow (Tilde.tilde (multibox n (Tilde.tilde (Wedge.wedge φ ψ))))
        (Wedge.wedge (Tilde.tilde (multibox n (Tilde.tilde φ)))
          (Tilde.tilde (multibox n (Tilde.tilde ψ)))))
    by
    exact
      imp_trans''! (imp_trans''! (and₁'! multidia_duality!) h) <|
        and_replace! (and₂'! multidia_duality!) (and₂'! multidia_duality!);
  apply FiniteContext.deduct'!; apply demorgan₃'!; apply FiniteContext.deductInv'!; apply contra₀'!;
  apply imp_trans''! collectMultiboxOr! (imply_multibox_distribute'! demorgan₁!)


-- @@ L480-485 expanded
omit [DecidableEq F] in
@[simp]
lemma distribute_dia_and! :
    Provable 𝓢 (Arrow.arrow (Dia.dia (Wedge.wedge φ ψ)) (Wedge.wedge (Dia.dia φ) (Dia.dia ψ))) := by
  classical
    exact
    distribute_multidia_and! (n := 1)
      -- TODO: `iffConjMultidiaMultidiaconj` is computable but it's too slow, so leave it.


-- @@ L486-501 expanded
@[simp]
lemma iff_conjmultidia_multidiaconj! :
    Provable 𝓢 (Arrow.arrow (multidia n (List.conj₂ Γ)) (List.conj₂ (List.multidia n Γ))) := by
  induction Γ using List.induction_with_singleton with
  | hcons φ Γ h ih => simp_all only [ne_eq, not_false_eq_true, List.conj₂_cons_nonempty];
    exact
      imp_trans''! distribute_multidia_and! <| by apply deduct'!; apply iff_provable_list_conj.mpr;
        intro ψ hq;
        simp only [Finset.mem_toList, List.toFinset_cons, Finset.image_insert, Finset.mem_insert,
          Finset.mem_image, List.mem_toFinset] at hq;
        cases hq with
        | inl => subst_vars; exact and₁'! id!;
        | inr hq => obtain ⟨χ, hr₁, hr₂⟩ := hq;
          exact (iff_provable_list_conj.mp <| mdp (of'! ih) (and₂'! <| id!)) ψ (by aesop);
  | _ => simp


-- @@ L503-506 expanded
omit [DecidableEq F] in
lemma distribute_dia_and'! (h : Provable 𝓢 (Dia.dia (Wedge.wedge φ ψ))) :
    Provable 𝓢 (Wedge.wedge (Dia.dia φ) (Dia.dia ψ)) := by classical exact mdp distribute_dia_and! h


-- @@ L508-514 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def boxdotAxiomK :
    Entailment.Prf 𝓢 (Arrow.arrow (boxdot (Arrow.arrow φ ψ)) (Arrow.arrow (boxdot φ) (boxdot ψ))) :=
  by apply deduct'; apply deduct;
  have d :
    Prf 𝓢 [Wedge.wedge φ (Box.box φ), Wedge.wedge (Arrow.arrow φ ψ) (Box.box (Arrow.arrow φ ψ))]
      (Wedge.wedge (Arrow.arrow φ ψ) (Box.box (Arrow.arrow φ ψ))) :=
    FiniteContext.byAxm;
  exact
    and₃' (mdp (and₁' d) (and₁' (ψ := Box.box φ) (FiniteContext.byAxm))) <|
      mdp (axiomK' <| and₂' d) (and₂' (φ := φ) (FiniteContext.byAxm));


-- @@ L515-518 expanded
omit [DecidableEq F] in
@[simp 1100]
lemma boxdot_axiomK! :
    Provable 𝓢 (Arrow.arrow (boxdot (Arrow.arrow φ ψ)) (Arrow.arrow (boxdot φ) (boxdot ψ))) := by
  classical exact ⟨boxdotAxiomK⟩


-- @@ L520-521 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def boxdotAxiomT : Entailment.Prf 𝓢 (Arrow.arrow (boxdot φ) φ) :=
  and₁


-- @@ L522-523 expanded
omit [DecidableEq F] in
@[simp 1100]
lemma boxdot_axiomT! : Provable 𝓢 (Arrow.arrow (boxdot φ) φ) := by simp_all


-- @@ L525-526 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def boxdotNec (d : Entailment.Prf 𝓢 φ) : Entailment.Prf 𝓢 (boxdot φ) :=
  and₃' d (nec d)


-- @@ L527-529 expanded
omit [DecidableEq F] in
lemma boxdot_nec! (d : Provable 𝓢 φ) : Provable 𝓢 (boxdot φ) := by
  classical exact ⟨boxdotNec d.some⟩


-- @@ L531-532 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def boxdotBox : Entailment.Prf 𝓢 (Arrow.arrow (boxdot φ) (Box.box φ)) :=
  and₂


-- @@ L533-534 expanded
omit [DecidableEq F] in
lemma boxdot_box! : Provable 𝓢 (Arrow.arrow (boxdot φ) (Box.box φ)) := by simp_all


-- @@ L536-537 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def BoxBoxdotBoxDotbox : Entailment.Prf 𝓢 (Arrow.arrow (Box.box (boxdot φ)) (boxdot (Box.box φ))) :=
  impTrans'' distributeBoxAnd (impId _)


-- @@ L538-540 expanded
omit [DecidableEq F] in
lemma boxboxdot_boxdotbox : Provable 𝓢 (Arrow.arrow (Box.box (boxdot φ)) (boxdot (Box.box φ))) := by
  simp_all


-- @@ L543-565 expanded
/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def lemmaGrz₁ :
    Entailment.Prf 𝓢
      (Arrow.arrow (Box.box φ)
        (Box.box
          (Arrow.arrow
            (Box.box
              (Arrow.arrow (Wedge.wedge φ (Arrow.arrow (Box.box φ) (Box.box (Box.box φ))))
                (Box.box (Wedge.wedge φ (Arrow.arrow (Box.box φ) (Box.box (Box.box φ)))))))
            (Wedge.wedge φ (Arrow.arrow (Box.box φ) (Box.box (Box.box φ))))))) :=
  by
  let ψ := Wedge.wedge φ (Arrow.arrow (Box.box φ) (Box.box (Box.box φ)));
  have :
    Entailment.Prf 𝓢
      (Arrow.arrow (Arrow.arrow (Arrow.arrow (Box.box φ) (Box.box (Box.box φ))) (Box.box φ))
        (Box.box φ)) :=
    peirce
  have :
    Entailment.Prf 𝓢
      (Arrow.arrow
        (Arrow.arrow φ (Arrow.arrow (Arrow.arrow (Box.box φ) (Box.box (Box.box φ))) (Box.box φ)))
        (Arrow.arrow φ (Box.box φ))) :=
    dhypImp' this;
  have d₁ :
    Entailment.Prf 𝓢 (Arrow.arrow (Arrow.arrow ψ (Box.box φ)) (Arrow.arrow φ (Box.box φ))) :=
    impTrans''
      (and₁' <| andImplyIffImplyImply φ (Arrow.arrow (Box.box φ) (Box.box (Box.box φ))) (Box.box φ))
      this;
  have : Entailment.Prf 𝓢 (Arrow.arrow ψ φ) := and₁;
  have : Entailment.Prf 𝓢 (Arrow.arrow (Box.box ψ) (Box.box φ)) := implyBoxDistribute' this;
  have d₂ :
    Entailment.Prf 𝓢 (Arrow.arrow (Arrow.arrow ψ (Box.box ψ)) (Arrow.arrow ψ (Box.box φ))) :=
    dhypImp' this;
  have : Entailment.Prf 𝓢 (Arrow.arrow (Arrow.arrow ψ (Box.box ψ)) (Arrow.arrow φ (Box.box φ))) :=
    impTrans'' d₂ d₁;
  have :
    Entailment.Prf 𝓢
      (Arrow.arrow (Box.box (Arrow.arrow ψ (Box.box ψ))) (Box.box (Arrow.arrow φ (Box.box φ)))) :=
    implyBoxDistribute' this;
  have :
    Entailment.Prf 𝓢
      (Arrow.arrow (Box.box (Arrow.arrow ψ (Box.box ψ)))
        (Arrow.arrow (Box.box φ) (Box.box (Box.box φ)))) :=
    impTrans'' this axiomK;
  have :
    Entailment.Prf 𝓢
      (Arrow.arrow (Arrow.arrow φ (Box.box (Arrow.arrow ψ (Box.box ψ))))
        (Arrow.arrow φ (Arrow.arrow (Box.box φ) (Box.box (Box.box φ))))) :=
    dhypImp' this;
  have :
    Entailment.Prf 𝓢
      (Arrow.arrow φ
        (Arrow.arrow (Box.box (Arrow.arrow ψ (Box.box ψ)))
          (Wedge.wedge φ (Arrow.arrow (Box.box φ) (Box.box (Box.box φ)))))) :=
    by
    apply deduct'; apply deduct; apply and₃'; · exact FiniteContext.byAxm;
    · exact mdp (mdp (of this) (imply₁' FiniteContext.byAxm)) (FiniteContext.byAxm);
  have : Entailment.Prf 𝓢 (Arrow.arrow φ (Arrow.arrow (Box.box (Arrow.arrow ψ (Box.box ψ))) ψ)) :=
    this;
  exact implyBoxDistribute' this;


-- @@ L567-572 expanded
omit [DecidableEq F] in
lemma lemmaGrz₁! :
    Provable 𝓢
      (Arrow.arrow (Box.box φ)
        (Box.box
          (Arrow.arrow
            (Box.box
              (Arrow.arrow (Wedge.wedge φ (Arrow.arrow (Box.box φ) (Box.box (Box.box φ))))
                (Box.box (Wedge.wedge φ (Arrow.arrow (Box.box φ) (Box.box (Box.box φ)))))))
            (Wedge.wedge φ (Arrow.arrow (Box.box φ) (Box.box (Box.box φ))))))) :=
  by classical exact ⟨lemmaGrz₁⟩


-- @@ L575-576 expanded
lemma contextual_nec! (h : Provable 𝓢 Γ φ) : Provable 𝓢 (List.box Γ) (Box.box φ) :=
  provable_iff.mpr <| imp_trans''! collect_box_conj! <| imply_box_distribute'! <| provable_iff.mp h


-- @@ L579-579 verbatim
namespace Context


-- @@ L581-581 verbatim
variable {X : Set F}


-- @@ L583-606 expanded
lemma provable_iff_boxed :
    Provable 𝓢 (Set.box X) φ ↔
      ∃ Δ : List F, (∀ ψ ∈ List.box Δ, ψ ∈ Set.box X) ∧ Provable 𝓢 (List.box Δ) φ :=
  by
  constructor;
  · intro h; obtain ⟨Γ, sΓ, hΓ⟩ := Context.provable_iff.mp h; use List.prebox Γ; constructor;
    · rintro ψ hq; apply sΓ ψ;
      simp only [List.eq_prebox_premultibox_one, List.eq_box_multibox_one, Finset.mem_toList,
        Finset.toList_toFinset, Finset.mem_image, Finset.mem_preimage, Function.iterate_one,
        List.mem_toFinset] at hq;
      obtain ⟨χ, _, rfl⟩ := hq; assumption;
    · apply FiniteContext.provable_iff.mpr;
      apply imp_trans''! ?_ (FiniteContext.provable_iff.mp hΓ); apply conjconj_subset!; intro ψ hq;
      have := sΓ ψ hq; obtain ⟨χ, _, rfl⟩ := this; simp_all;
  · rintro ⟨Δ, hΔ, h⟩; apply Context.provable_iff.mpr; use List.box Δ;


-- @@ L608-608 verbatim
end Context


-- @@ L610-610 verbatim
end Entailment

-- @@ L611-611 verbatim
end LO
