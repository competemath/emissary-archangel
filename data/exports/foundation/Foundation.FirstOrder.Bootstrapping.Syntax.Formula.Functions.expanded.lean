module

public import Foundation.FirstOrder.Bootstrapping.Syntax.Formula.Basic
public import Foundation.FirstOrder.Bootstrapping.Syntax.Term.Functions


-- @@ L6-6 verbatim
@[expose] public section

-- @@ L7-7 verbatim
namespace FFL.FirstOrder.Arithmetic.Bootstrapping


-- @@ L9-9 verbatim
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


-- @@ L11-11 verbatim
variable {L : Language} [L.Encodable] [L.LORDefinable]


-- @@ L13-13 verbatim
/-! ### Negation function -/


-- @@ L15-15 verbatim
section negation


-- @@ L17-17 verbatim
namespace Negation


-- @@ L19-29 verbatim
def blueprint : UformulaRec1.Blueprint where
  rel := .mkSigma “y param k R v. !qqNRelDef y k R v”
  nrel := .mkSigma “y param k R v. !qqRelDef y k R v”
  verum := .mkSigma “y param. !qqFalsumDef y”
  falsum := .mkSigma “y param. !qqVerumDef y”
  and := .mkSigma “y param p₁ p₂ y₁ y₂. !qqOrDef y y₁ y₂”
  or := .mkSigma “y param p₁ p₂ y₁ y₂. !qqAndDef y y₁ y₂”
  all := .mkSigma “y param p₁ y₁. !qqExsDef y y₁”
  exs := .mkSigma “y param p₁ y₁. !qqAllDef y y₁”
  allChanges := .mkSigma “param' param. param' = 0”
  exsChanges := .mkSigma “param' param. param' = 0”


-- @@ L31-51 verbatim
noncomputable def construction : UformulaRec1.Construction V blueprint where
  rel {_} := fun k R v ↦ ^nrel k R v
  nrel {_} := fun k R v ↦ ^rel k R v
  verum {_} := ^⊥
  falsum {_} := ^⊤
  and {_} := fun _ _ y₁ y₂ ↦ y₁ ^⋎ y₂
  or {_} := fun _ _ y₁ y₂ ↦ y₁ ^⋏ y₂
  all {_} := fun _ y₁ ↦ ^∃ y₁
  exs {_} := fun _ y₁ ↦ ^∀ y₁
  allChanges := fun _ ↦ 0
  exsChanges := fun _ ↦ 0
  rel_defined := .mk fun v ↦ by simp [blueprint]
  nrel_defined := .mk fun v ↦ by simp [blueprint]
  verum_defined := .mk fun v ↦ by simp [blueprint]
  falsum_defined := .mk fun v ↦ by simp [blueprint]
  and_defined := .mk fun v ↦ by simp [blueprint]
  or_defined := .mk fun v ↦ by simp [blueprint]
  all_defined := .mk fun v ↦ by simp [blueprint]
  exs_defined := .mk fun v ↦ by simp [blueprint]
  allChanges_defined := .mk fun v ↦ by simp [blueprint]
  exChanges_defined := .mk fun v ↦ by simp [blueprint]


-- @@ L53-53 verbatim
end Negation


-- @@ L55-55 verbatim
open Negation


-- @@ L57-57 verbatim
variable (L)


-- @@ L59-59 verbatim
noncomputable def neg (p : V) : V := construction.result L 0 p


-- @@ L61-61 verbatim
noncomputable def negGraph : 𝚺₁.Semisentence 2 := (blueprint.result L).rew (Rew.subst ![#0, ‘0’, #1])


-- @@ L63-63 verbatim
variable {L}


-- @@ L65-65 verbatim
section


-- @@ L67-68 verbatim
instance neg.defined : 𝚺₁-Function₁ neg (V := V) L via negGraph L  := .mk fun v ↦ by
  simpa [negGraph, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using! construction.result_defined.defined ![v 0, 0, v 1]


-- @@ L70-70 verbatim
instance neg.definable : 𝚺₁-Function₁ neg (V := V) L := neg.defined.to_definable


-- @@ L72-72 verbatim
instance neg.definable' : Γ-[m + 1]-Function₁ neg (V := V) L := .of_sigmaOne neg.definable


-- @@ L74-74 verbatim
end


-- @@ L76-77 verbatim
@[simp] lemma neg_rel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    neg L (^rel k R v) = ^nrel k R v := by simp [neg, hR, hv, construction]


-- @@ L79-80 verbatim
@[simp] lemma neg_nrel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    neg L (^nrel k R v) = ^rel k R v := by simp [neg, hR, hv, construction]


-- @@ L82-83 verbatim
@[simp] lemma neg_verum :
    neg L (^⊤ : V) = ^⊥ := by simp [neg, construction]


-- @@ L85-86 verbatim
@[simp] lemma neg_falsum :
    neg L (^⊥ : V) = ^⊤ := by simp [neg, construction]


-- @@ L88-89 verbatim
@[simp] lemma neg_and {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    neg L (p ^⋏ q) = neg L p ^⋎ neg L q := by simp [neg, hp, hq, construction]


-- @@ L91-92 verbatim
@[simp] lemma neg_or {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    neg L (p ^⋎ q) = neg L p ^⋏ neg L q := by simp [neg, hp, hq, construction]


-- @@ L94-95 verbatim
@[simp] lemma neg_all {p : V} (hp : IsUFormula L p) :
    neg L (^∀ p) = ^∃ (neg L p) := by simp [neg, hp, construction]


-- @@ L97-113 verbatim
@[simp] lemma neg_ex {p : V} (hp : IsUFormula L p) :
    neg L (^∃ p) = ^∀ (neg L p) := by simp [neg, hp, construction]

lemma neg_not_uformula {x : V} (h : ¬IsUFormula L x) :
    neg L x = 0 := construction.result_prop_not _ h

lemma IsUFormula.neg {p : V} : IsUFormula L p → IsUFormula L (neg L p) := by
  apply IsUFormula.ISigma1.sigma1_succ_induction
  · definability
  · intro k r v hr hv; simp [hr, hv]
  · intro k r v hr hv; simp [hr, hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p hp ihp; simp [hp, ihp]
  · intro p hp ihp; simp [hp, ihp]


-- @@ L115-125 verbatim
@[simp] lemma IsUFormula.bv_neg {p : V} : IsUFormula L p → bv L (Bootstrapping.neg L p) = bv L p := by
  apply IsUFormula.ISigma1.sigma1_succ_induction
  · definability
  · intro k R v hR hv; simp [*]
  · intro k R v hR hv; simp [*]
  · simp
  · simp
  · intro p q hp hq ihp ihq; simp [hp, hq, hp.neg, hq.neg, ihp, ihq]
  · intro p q hp hq ihp ihq; simp [hp, hq, hp.neg, hq.neg, ihp, ihq]
  · intro p hp ihp; simp [hp, hp.neg, ihp]
  · intro p hp ihp; simp [hp, hp.neg, ihp]


-- @@ L127-137 verbatim
@[simp] lemma IsUFormula.neg_neg {p : V} : IsUFormula L p → Bootstrapping.neg L (Bootstrapping.neg L p) = p := by
  apply IsUFormula.ISigma1.sigma1_succ_induction
  · definability
  · intro k r v hr hv; simp [hr, hv]
  · intro k r v hr hv; simp [hr, hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq; simp [hp, hq, hp.neg, hq.neg, ihp, ihq]
  · intro p q hp hq ihp ihq; simp [hp, hq, hp.neg, hq.neg, ihp, ihq]
  · intro p hp ihp; simp [hp, hp.neg, ihp]
  · intro p hp ihp; simp [hp, hp.neg, ihp]


-- @@ L139-144 verbatim
@[simp] lemma IsUFormula.neg_iff {p : V} : IsUFormula L (Bootstrapping.neg L p) ↔ IsUFormula L p := by
  constructor
  · intro h; by_contra hp
    have Hp : IsUFormula L p := by by_contra hp; simp [neg_not_uformula hp] at h
    contradiction
  · exact IsUFormula.neg


-- @@ L146-154 verbatim
@[simp] lemma IsSemiformula.neg_iff {p : V} : IsSemiformula L n (neg L p) ↔ IsSemiformula L n p := by
  constructor
  · intro h; by_contra hp
    have Hp : IsUFormula L p := by by_contra hp; simp [neg_not_uformula hp] at h
    have : IsSemiformula L n p := ⟨Hp, by simpa [Hp.bv_neg] using h.bv_le⟩
    contradiction
  · intro h; exact ⟨by simp [h.isUFormula], by simpa [h.isUFormula] using h.bv_le⟩

alias ⟨IsSemiformula.elim_neg, IsSemiformula.neg⟩ := IsSemiformula.neg_iff


-- @@ L156-159 verbatim
@[simp] lemma neg_inj_iff {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) : neg L p = neg L q ↔ p = q := by
  constructor
  · intro h; simpa [hp.neg_neg, hq.neg_neg] using congrArg (neg L) h
  · rintro rfl; rfl


-- @@ L161-161 verbatim
end negation


-- @@ L163-163 verbatim
variable (L)


-- @@ L165-165 verbatim
noncomputable def imp (p q : V) : V := neg L p ^⋎ q


-- @@ L167-167 verbatim
notation:60 p:61 " ^→[" L "] " q:60 => Language.imp L p q


-- @@ L169-169 verbatim
noncomputable def impGraph : 𝚺₁.Semisentence 3 := .mkSigma “r p q. ∃ np, !(negGraph L) np p ∧ !qqOrDef r np q”


-- @@ L171-171 verbatim
noncomputable def iff (p q : V) : V := (imp L p q) ^⋏ (imp L q p)


-- @@ L173-174 verbatim
noncomputable def iffGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “r p q. ∃ pq, !(impGraph L) pq p q ∧ ∃ qp, !(impGraph L) qp q p ∧ !qqAndDef r pq qp”


-- @@ L176-176 verbatim
variable {L}


-- @@ L178-178 verbatim
section imp


-- @@ L180-182 verbatim
@[simp] lemma IsUFormula.imp {p q : V} :
    IsUFormula L (imp L p q) ↔ IsUFormula L p ∧ IsUFormula L q := by
  simp [Bootstrapping.imp]


-- @@ L184-186 verbatim
@[simp] lemma IsSemiformula.imp {n p q : V} :
    IsSemiformula L n (imp L p q) ↔ IsSemiformula L n p ∧ IsSemiformula L n q := by
  simp [Bootstrapping.imp]


-- @@ L188-188 verbatim
section


-- @@ L190-190 verbatim
instance imp.defined : 𝚺₁-Function₂ imp (V := V) L via impGraph L := .mk fun v ↦ by simp [impGraph]; rfl


-- @@ L192-192 verbatim
instance imp.definable : 𝚺₁-Function₂ imp (V := V) L := imp.defined.to_definable


-- @@ L194-194 verbatim
instance imp.definable' : Γ-[m + 1]-Function₂ imp (V := V) L := imp.definable.of_sigmaOne


-- @@ L196-196 verbatim
end


-- @@ L198-198 verbatim
end imp


-- @@ L200-200 verbatim
section iff


-- @@ L202-205 verbatim
@[simp] lemma IsUFormula.iff {p q : V} :
    IsUFormula L (iff L p q) ↔ IsUFormula L p ∧ IsUFormula L q := by
  simp only [Bootstrapping.iff, and, imp, and_iff_left_iff_imp, and_imp]
  intros; simp_all


-- @@ L207-210 verbatim
@[simp] lemma IsSemiformula.iff {n p q : V} :
    IsSemiformula L n (iff L p q) ↔ IsSemiformula L n p ∧ IsSemiformula L n q := by
  simp only [Bootstrapping.iff, and, imp, and_iff_left_iff_imp, and_imp]
  intros; simp_all


-- @@ L212-212 verbatim
@[simp] lemma lt_iff_left (p q : V) : p < iff L p q := lt_trans (lt_or_right _ _) (lt_K!_right _ _)


-- @@ L214-214 verbatim
@[simp] lemma lt_iff_right (p q : V) : q < iff L p q := lt_trans (lt_or_right _ _) (lt_K!_left _ _)


-- @@ L216-216 verbatim
section


-- @@ L218-218 verbatim
instance iff.defined : 𝚺₁-Function₂ iff (V := V) L via iffGraph L := .mk fun v ↦ by simp [iffGraph]; rfl


-- @@ L220-220 verbatim
instance iff.definable : 𝚺₁-Function₂ iff (V := V) L := iff.defined.to_definable


-- @@ L222-222 verbatim
instance iff_definable' : Γ-[m + 1]-Function₂ iff (V := V) L := iff.definable.of_sigmaOne


-- @@ L224-224 verbatim
end


-- @@ L226-226 verbatim
end iff


-- @@ L228-228 verbatim
/-! ### Shift function -/


-- @@ L230-230 verbatim
section shift


-- @@ L232-232 verbatim
namespace Shift


-- @@ L234-234 verbatim
variable (L)


-- @@ L236-246 verbatim
noncomputable def blueprint : UformulaRec1.Blueprint where
  rel := .mkSigma “y param k R v. ∃ v', !(termShiftVecGraph L) v' k v ∧ !qqRelDef y k R v'”
  nrel := .mkSigma “y param k R v. ∃ v', !(termShiftVecGraph L) v' k v ∧ !qqNRelDef y k R v'”
  verum := .mkSigma “y param. !qqVerumDef y”
  falsum := .mkSigma “y param. !qqFalsumDef y”
  and := .mkSigma “y param p₁ p₂ y₁ y₂. !qqAndDef y y₁ y₂”
  or := .mkSigma “y param p₁ p₂ y₁ y₂. !qqOrDef y y₁ y₂”
  all := .mkSigma “y param p₁ y₁. !qqAllDef y y₁”
  exs := .mkSigma “y param p₁ y₁. !qqExsDef y y₁”
  allChanges := .mkSigma “param' param. param' = 0”
  exsChanges := .mkSigma “param' param. param' = 0”


-- @@ L248-268 verbatim
noncomputable def construction : UformulaRec1.Construction V (blueprint L) where
  rel {_} := fun k R v ↦ ^rel k R (termShiftVec L k v)
  nrel {_} := fun k R v ↦ ^nrel k R (termShiftVec L k v)
  verum {_} := ^⊤
  falsum {_} := ^⊥
  and {_} := fun _ _ y₁ y₂ ↦ y₁ ^⋏ y₂
  or {_} := fun _ _ y₁ y₂ ↦ y₁ ^⋎ y₂
  all {_} := fun _ y₁ ↦ ^∀ y₁
  exs {_} := fun _ y₁ ↦ ^∃ y₁
  allChanges := fun _ ↦ 0
  exsChanges := fun _ ↦ 0
  rel_defined := .mk fun v ↦ by simp [blueprint]
  nrel_defined := .mk fun v ↦ by simp [blueprint]
  verum_defined := .mk fun v ↦ by simp [blueprint]
  falsum_defined := .mk fun v ↦ by simp [blueprint]
  and_defined := .mk fun v ↦ by simp [blueprint]
  or_defined := .mk fun v ↦ by simp [blueprint]
  all_defined := .mk fun v ↦ by simp [blueprint]
  exs_defined := .mk fun v ↦ by simp [blueprint]
  allChanges_defined := .mk fun v ↦ by simp [blueprint]
  exChanges_defined := .mk fun v ↦ by simp [blueprint]


-- @@ L270-270 verbatim
end Shift


-- @@ L272-272 verbatim
open Shift


-- @@ L274-274 verbatim
variable (L)


-- @@ L276-276 verbatim
noncomputable def shift (p : V) : V := (construction L).result L 0 p


-- @@ L278-278 verbatim
noncomputable def shiftGraph : 𝚺₁.Semisentence 2 := blueprint L |>.result L |>.rew (Rew.subst ![#0, ‘0’, #1])


-- @@ L280-280 verbatim
variable {L}


-- @@ L282-282 verbatim
section


-- @@ L284-285 verbatim
instance shift.defined : 𝚺₁-Function₁[V] shift L via shiftGraph L := .mk fun v ↦ by
  simpa [shiftGraph, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using! (construction L).result_defined.defined ![v 0, 0, v 1]


-- @@ L287-287 verbatim
instance shift.definable : 𝚺₁-Function₁[V] shift L := shift.defined.to_definable


-- @@ L289-289 verbatim
instance shift.definable' : Γ-[m + 1]-Function₁[V] shift L := shift.definable.of_sigmaOne


-- @@ L291-291 verbatim
end


-- @@ L293-294 verbatim
@[simp] lemma shift_rel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    shift L (^relk R v) = ^relk R (termShiftVec L k v) := by simp [shift, hR, hv, construction]


-- @@ L296-297 verbatim
@[simp] lemma shift_nrel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    shift L (^nrelk R v) = ^nrelk R (termShiftVec L k v) := by simp [shift, hR, hv, construction]


-- @@ L299-299 verbatim
@[simp] lemma shift_verum : shift L (^⊤ : V) = ^⊤ := by simp [shift, construction]


-- @@ L301-301 verbatim
@[simp] lemma shift_falsum : shift L (^⊥ : V) = ^⊥ := by simp [shift, construction]


-- @@ L303-304 verbatim
@[simp] lemma shift_and {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    shift L (p ^⋏ q) = shift L p ^⋏ shift L q := by simp [shift, hp, hq, construction]


-- @@ L306-307 verbatim
@[simp] lemma shift_or {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    shift L (p ^⋎ q) = shift L p ^⋎ shift L q := by simp [shift, hp, hq, construction]


-- @@ L309-310 verbatim
@[simp] lemma shift_all {p : V} (hp : IsUFormula L p) :
    shift L (^∀ p) = ^∀ (shift L p) := by simp [shift, hp, construction]


-- @@ L312-352 verbatim
@[simp] lemma shift_exs {p : V} (hp : IsUFormula L p) :
    shift L (^∃ p) = ^∃ (shift L p) := by simp [shift, hp, construction]

lemma shift_not_uformula {x : V} (h : ¬IsUFormula L x) :
    shift L x = 0 := (construction L).result_prop_not _ h

lemma IsUFormula.shift {p : V} : IsUFormula L p → IsUFormula L (shift L p) := by
  apply IsUFormula.ISigma1.sigma1_succ_induction
  · definability
  · intro k r v hr hv; simp [hr, hv]
  · intro k r v hr hv; simp [hr, hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p hp ihp; simp [hp, ihp]
  · intro p hp ihp; simp [hp, ihp]

lemma IsUFormula.bv_shift {p : V} : IsUFormula L p → bv L (Bootstrapping.shift L p) = bv L p := by
  apply IsUFormula.ISigma1.sigma1_succ_induction
  · definability
  · intro k r v hr hv; simp [hr, hv]
  · intro k r v hr hv; simp [hr, hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq, hp.shift, hq.shift]
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq, hp.shift, hq.shift]
  · intro p hp ihp; simp [hp, ihp, hp.shift]
  · intro p hp ihp; simp [hp, ihp, hp.shift]

lemma IsSemiformula.shift {p : V} : IsSemiformula L n p → IsSemiformula L n (shift L p) := by
  apply IsSemiformula.sigma1_structural_induction
  · definability
  · intro n k r v hr hv; simp [hr, hv.isUTerm]
  · intro n k r v hr hv; simp [hr, hv.isUTerm]
  · simp
  · simp
  · intro n p q hp hq ihp ihq; simp [hp.isUFormula, hq.isUFormula, ihp, ihq]
  · intro n p q hp hq ihp ihq; simp [hp.isUFormula, hq.isUFormula, ihp, ihq]
  · intro n p hp ihp; simp [hp.isUFormula, ihp]
  · intro n p hp ihp; simp [hp.isUFormula, ihp]


-- @@ L354-359 verbatim
@[simp] lemma IsUFormula.shift_iff {p : V} : IsUFormula L (Bootstrapping.shift L p) ↔ IsUFormula L p := by
  constructor
  · intro h; by_contra hp
    have Hp : IsUFormula L p := by by_contra hp; simp [shift_not_uformula hp] at h
    contradiction
  · exact IsUFormula.shift


-- @@ L361-377 verbatim
@[simp] lemma IsSemiformula.shift_iff {p : V} : IsSemiformula L n (Bootstrapping.shift L p) ↔ IsSemiformula L n p :=
  ⟨fun h ↦ by
    have : IsUFormula L p := by by_contra hp; simp [shift_not_uformula hp] at h
    exact ⟨this, by simpa [this.bv_shift] using h.bv_le⟩,
    IsSemiformula.shift⟩

lemma shift_neg {p : V} (hp : IsSemiformula L n p) : shift L (neg L p) = neg L (shift L p) := by
  apply IsSemiformula.sigma1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv; simp [hR, hv.isUTerm, hv.termShiftVec.isUTerm]
  · intro n k R v hR hv; simp [hR, hv.isUTerm, hv.termShiftVec.isUTerm]
  · simp
  · simp
  · intro n p q hp hq ihp ihq; simp [hp.isUFormula, hq.isUFormula, hp.shift.isUFormula, hq.shift.isUFormula, ihp, ihq]
  · intro n p q hp hq ihp ihq; simp [hp.isUFormula, hq.isUFormula, hp.shift.isUFormula, hq.shift.isUFormula, ihp, ihq]
  · intro n p hp ih; simp [hp.isUFormula, hp.shift.isUFormula, ih]
  · intro n p hp ih; simp [hp.isUFormula, hp.shift.isUFormula, ih]


-- @@ L379-379 verbatim
end shift


-- @@ L381-381 verbatim
/-! ### Substitution function -/


-- @@ L383-383 verbatim
section subst


-- @@ L385-385 verbatim
namespace Substs


-- @@ L387-387 verbatim
variable (L)


-- @@ L389-399 verbatim
noncomputable def blueprint : UformulaRec1.Blueprint where
  rel    := .mkSigma “y param k R v. ∃ v', !(termSubstVecGraph L) v' k param v ∧ !qqRelDef y k R v'”
  nrel   := .mkSigma “y param k R v. ∃ v', !(termSubstVecGraph L) v' k param v ∧ !qqNRelDef y k R v'”
  verum  := .mkSigma “y param. !qqVerumDef y”
  falsum := .mkSigma “y param. !qqFalsumDef y”
  and    := .mkSigma “y param p₁ p₂ y₁ y₂. !qqAndDef y y₁ y₂”
  or     := .mkSigma “y param p₁ p₂ y₁ y₂. !qqOrDef y y₁ y₂”
  all    := .mkSigma “y param p₁ y₁. !qqAllDef y y₁”
  exs     := .mkSigma “y param p₁ y₁. !qqExsDef y y₁”
  allChanges := .mkSigma “param' param. !(qVecGraph L) param' param”
  exsChanges  := .mkSigma “param' param. !(qVecGraph L) param' param”


-- @@ L401-428 verbatim
noncomputable def construction : UformulaRec1.Construction V (blueprint L) where
  rel (param)  := fun k R v ↦ ^rel k R (termSubstVec L k param v)
  nrel (param) := fun k R v ↦ ^nrel k R (termSubstVec L k param v)
  verum _      := ^⊤
  falsum _     := ^⊥
  and _        := fun _ _ y₁ y₂ ↦ y₁ ^⋏ y₂
  or _         := fun _ _ y₁ y₂ ↦ y₁ ^⋎ y₂
  all _        := fun _ y₁ ↦ ^∀ y₁
  exs _         := fun _ y₁ ↦ ^∃ y₁
  allChanges (param) := qVec L param
  exsChanges (param) := qVec L param
  rel_defined := .mk fun v ↦ by simp [blueprint]
  nrel_defined := .mk fun v ↦ by simp [blueprint]
  verum_defined := .mk fun v ↦ by simp [blueprint]
  falsum_defined := .mk fun v ↦ by simp [blueprint]
  and_defined := .mk fun v ↦ by simp [blueprint]
  or_defined := .mk fun v ↦ by simp [blueprint]
  all_defined := .mk fun v ↦ by simp [blueprint]
  exs_defined := .mk fun v ↦ by simp [blueprint]
  -- Letting `simp` apply `Semiformula.eval_substs` here overflows memory on Lean v4.33.1.
  allChanges_defined := .mk fun v ↦ by
    simp only [blueprint, HierarchySymbol.Semiformula.val_mkSigma]
    rw [Semiformula.eval_substs]
    simp [qVec.defined.df]
  exChanges_defined := .mk fun v ↦ by
    simp only [blueprint, HierarchySymbol.Semiformula.val_mkSigma]
    rw [Semiformula.eval_substs]
    simp [qVec.defined.df]


-- @@ L430-430 verbatim
end Substs


-- @@ L432-432 verbatim
open Substs


-- @@ L434-434 verbatim
variable (L)


-- @@ L436-436 verbatim
noncomputable def subst (w p : V) : V := (construction L).result L w p


-- @@ L438-438 verbatim
noncomputable def substsGraph : 𝚺₁.Semisentence 3 := (blueprint L).result L


-- @@ L440-440 verbatim
variable {L}


-- @@ L442-442 verbatim
section


-- @@ L444-444 verbatim
instance subst.defined : 𝚺₁-Function₂[V] subst L via substsGraph L := (construction L).result_defined


-- @@ L446-446 verbatim
instance subst.definable : 𝚺₁-Function₂[V] subst L := subst.defined.to_definable


-- @@ L448-448 verbatim
instance subst.definable' : Γ-[m + 1]-Function₂[V] subst L := subst.definable.of_sigmaOne


-- @@ L450-450 verbatim
attribute [irreducible] substsGraph


-- @@ L452-452 verbatim
end


-- @@ L454-454 verbatim
variable {m w : V}


-- @@ L456-457 verbatim
@[simp] lemma substs_rel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    subst L w (^relk R v) = ^rel k R (termSubstVec L k w v) := by simp [subst, hR, hv, construction]


-- @@ L459-460 verbatim
@[simp] lemma substs_nrel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    subst L w (^nrelk R v) = ^nrel k R (termSubstVec L k w v) := by simp [subst, hR, hv, construction]


-- @@ L462-462 verbatim
@[simp] lemma substs_verum (w : V) : subst L w ^⊤ = ^⊤ := by simp [subst, construction]


-- @@ L464-464 verbatim
@[simp] lemma substs_falsum (w : V) : subst L w ^⊥ = ^⊥ := by simp [subst, construction]


-- @@ L466-467 verbatim
@[simp] lemma substs_and {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    subst L w (p ^⋏ q) = subst L w p ^⋏ subst L w q := by simp [subst, hp, hq, construction]


-- @@ L469-470 verbatim
@[simp] lemma substs_or {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    subst L w (p ^⋎ q) = subst L w p ^⋎ subst L w q := by simp [subst, hp, hq, construction]


-- @@ L472-473 verbatim
@[simp] lemma substs_all {p} (hp : IsUFormula L p) :
    subst L w (^∀ p) = ^∀ (subst L (qVec L w) p) := by simp [subst, hp, construction]


-- @@ L475-540 verbatim
@[simp] lemma substs_ex {p} (hp : IsUFormula L p) :
    subst L w (^∃ p) = ^∃ (subst L (qVec L w) p) := by simp [subst, hp, construction]

lemma isUFormula_subst_ISigma1.sigma1_succ_induction {P : V → V → V → Prop} (hP : 𝚺₁-Relation₃ P)
    (hRel : ∀ w k R v, L.IsRel k R → IsUTermVec L k v → P w (^relk R v) (^rel k R (termSubstVec L k w v)))
    (hNRel : ∀ w k R v, L.IsRel k R → IsUTermVec L k v → P w (^nrelk R v) (^nrel k R (termSubstVec L k w v)))
    (hverum : ∀ w, P w ^⊤ ^⊤)
    (hfalsum : ∀ w, P w ^⊥ ^⊥)
    (hand : ∀ w p q, IsUFormula L p → IsUFormula L q →
      P w p (subst L w p) → P w q (subst L w q) → P w (p ^⋏ q) (subst L w p ^⋏ subst L w q))
    (hor : ∀ w p q, IsUFormula L p → IsUFormula L q →
      P w p (subst L w p) → P w q (subst L w q) → P w (p ^⋎ q) (subst L w p ^⋎ subst L w q))
    (hall : ∀ w p, IsUFormula L p → P (qVec L w) p (subst L (qVec L w) p) → P w (^∀ p) (^∀ (subst L (qVec L w) p)))
    (hexs : ∀ w p, IsUFormula L p → P (qVec L w) p (subst L (qVec L w) p) → P w (^∃ p) (^∃ (subst L (qVec L w) p))) :
    ∀ {w p}, IsUFormula L p → P w p (subst L w p) := by
  suffices ∀ param p, IsUFormula L p → P param p ((construction L).result L param p) by
    intro w p hp; simpa using! this w p hp
  apply (construction L).uformula_result_induction (P := fun param p y ↦ P param p y)
  · definability
  · intro param k R v hkR hv; simpa using! hRel param k R v hkR hv
  · intro param k R v hkR hv; simpa using! hNRel param k R v hkR hv
  · intro param; simpa using! hverum param
  · intro param; simpa using! hfalsum param
  · intro param p q hp hq ihp ihq
    simpa [subst] using!
      hand param p q hp hq (by simpa [subst] using ihp) (by simpa [subst] using ihq)
  · intro param p q hp hq ihp ihq
    simpa [subst] using!
      hor param p q hp hq (by simpa [subst] using ihp) (by simpa [subst] using ihq)
  · intro param p hp ihp
    simpa using! hall param p hp (by simpa [construction] using! ihp)
  · intro param p hp ihp
    simpa using! hexs param p hp (by simpa [construction] using! ihp)

lemma semiformula_subst_induction {P : V → V → V → V → Prop} (hP : 𝚺₁-Relation₄ P)
    (hRel : ∀ n w k R v, L.IsRel k R → IsSemitermVec L k n v → P n w (^relk R v) (^rel k R (termSubstVec L k w v)))
    (hNRel : ∀ n w k R v, L.IsRel k R → IsSemitermVec L k n v → P n w (^nrelk R v) (^nrel k R (termSubstVec L k w v)))
    (hverum : ∀ n w, P n w ^⊤ ^⊤)
    (hfalsum : ∀ n w, P n w ^⊥ ^⊥)
    (hand : ∀ n w p q, IsSemiformula L n p → IsSemiformula L n q →
      P n w p (subst L w p) → P n w q (subst L w q) → P n w (p ^⋏ q) (subst L w p ^⋏ subst L w q))
    (hor : ∀ n w p q, IsSemiformula L n p → IsSemiformula L n q →
      P n w p (subst L w p) → P n w q (subst L w q) → P n w (p ^⋎ q) (subst L w p ^⋎ subst L w q))
    (hall : ∀ n w p, IsSemiformula L (n + 1) p →
      P (n + 1) (qVec L w) p (subst L (qVec L w) p) → P n w (^∀ p) (^∀ (subst L (qVec L w) p)))
    (hexs : ∀ n w p, IsSemiformula L (n + 1) p →
      P (n + 1) (qVec L w) p (subst L (qVec L w) p) → P n w (^∃ p) (^∃ (subst L (qVec L w) p))) :
    ∀ {n p w}, IsSemiformula L n p → P n w p (subst L w p) := by
  suffices ∀ param n p, IsSemiformula L n p → P n param p ((construction L).result L param p) by
    intro n p w hp; simpa using! this w n p hp
  apply (construction L).semiformula_result_induction (P := fun param n p y ↦ P n param p y)
  · definability
  · intro n param k R v hkR hv; simpa using! hRel n param k R v hkR hv
  · intro n param k R v hkR hv; simpa using! hNRel n param k R v hkR hv
  · intro n param; simpa using! hverum n param
  · intro n param; simpa using! hfalsum n param
  · intro n param p q hp hq ihp ihq
    simpa [subst] using!
      hand n param p q hp hq (by simpa [subst] using ihp) (by simpa [subst] using ihq)
  · intro n param p q hp hq ihp ihq
    simpa [subst] using!
      hor n param p q hp hq (by simpa [subst] using ihp) (by simpa [subst] using ihq)
  · intro n param p hp ihp
    simpa using! hall n param p hp (by simpa [construction] using! ihp)
  · intro n param p hp ihp
    simpa using! hexs n param p hp (by simpa [construction] using! ihp)


-- @@ L542-760 verbatim
@[simp] lemma IsSemiformula.subst {n p m w : V} :
    IsSemiformula L n p → IsSemitermVec L n m w → IsSemiformula L m (subst L w p) := by
  let fw : V → V → V → V → V := fun _ w _ _ ↦ Max.max w (qVec L w)
  have hfw : 𝚺₁-Function₄ fw := by definability
  let fn : V → V → V → V → V := fun _ _ n _ ↦ n + 1
  have hfn : 𝚺₁-Function₄ fn := by definability
  let fm : V → V → V → V → V := fun _ _ _ m ↦ m + 1
  have hfm : 𝚺₁-Function₄ fm := by definability
  apply bounded_all_sigma1_order_induction₃ hfw hfn hfm ?_ ?_ p w n m
  · definability
  intro p w n m ih hp hw
  rcases IsSemiformula.case_iff.mp hp with
    (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ | rfl | rfl | ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, h₁, rfl⟩ | ⟨p₁, h₁, rfl⟩)
  · simp [hR, hv.isUTerm, hw.termSubstVec hv]
  · simp [hR, hv.isUTerm, hw.termSubstVec hv]
  · simp
  · simp
  · have ih₁ : IsSemiformula L m (Bootstrapping.subst L w p₁) := ih p₁ (by simp) w (by simp [fw]) n (by simp [fn]) m (by simp [fm]) h₁ hw
    have ih₂ : IsSemiformula L m (Bootstrapping.subst L w p₂) := ih p₂ (by simp) w (by simp [fw]) n (by simp [fn]) m (by simp [fm]) h₂ hw
    simp [h₁.isUFormula, h₂.isUFormula, ih₁, ih₂]
  · have ih₁ : IsSemiformula L m (Bootstrapping.subst L w p₁) := ih p₁ (by simp) w (by simp [fw]) n (by simp [fn]) m (by simp [fm]) h₁ hw
    have ih₂ : IsSemiformula L m (Bootstrapping.subst L w p₂) := ih p₂ (by simp) w (by simp [fw]) n (by simp [fn]) m (by simp [fm]) h₂ hw
    simp [h₁.isUFormula, h₂.isUFormula, ih₁, ih₂]
  · simpa [h₁.isUFormula] using ih p₁ (by simp) (qVec L w) (by simp [fw]) (n + 1) (by simp [fn]) (m + 1) (by simp [fm]) h₁ hw.qVec
  · simpa [h₁.isUFormula] using ih p₁ (by simp) (qVec L w) (by simp [fw]) (n + 1) (by simp [fn]) (m + 1) (by simp [fm]) h₁ hw.qVec

lemma substs_not_uformula {w x : V} (h : ¬IsUFormula L x) :
    subst L w x = 0 := (construction L).result_prop_not _ h

lemma substs_neg {p} (hp : IsSemiformula L n p) :
    IsSemitermVec L n m w → subst L w (neg L p) = neg L (subst L w p) := by
  revert m w
  apply IsSemiformula.pi1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intros n k R v hR hv m w hw
    rw [neg_rel hR hv.isUTerm, substs_nrel hR hv.isUTerm, substs_rel hR hv.isUTerm, neg_rel hR (hw.termSubstVec hv).isUTerm]
  · intros n k R v hR hv m w hw
    rw [neg_nrel hR hv.isUTerm, substs_rel hR hv.isUTerm, substs_nrel hR hv.isUTerm, neg_nrel hR (hw.termSubstVec hv).isUTerm]
  · intros; simp [*]
  · intros; simp [*]
  · intro n p q hp hq ihp ihq m w hw
    rw [neg_and hp.isUFormula hq.isUFormula,
      substs_or hp.neg.isUFormula hq.neg.isUFormula,
      substs_and hp.isUFormula hq.isUFormula,
      neg_and (hp.subst hw).isUFormula (hq.subst hw).isUFormula,
      ihp hw, ihq hw]
  · intro n p q hp hq ihp ihq m w hw
    rw [neg_or hp.isUFormula hq.isUFormula,
      substs_and hp.neg.isUFormula hq.neg.isUFormula,
      substs_or hp.isUFormula hq.isUFormula,
      neg_or (hp.subst hw).isUFormula (hq.subst hw).isUFormula,
      ihp hw, ihq hw]
  · intro n p hp ih m w hw
    rw [neg_all hp.isUFormula, substs_ex hp.neg.isUFormula,
      substs_all hp.isUFormula, neg_all (hp.subst hw.qVec).isUFormula, ih hw.qVec]
  · intro n p hp ih m w hw
    rw [neg_ex hp.isUFormula, substs_all hp.neg.isUFormula,
      substs_ex hp.isUFormula, neg_ex (hp.subst hw.qVec).isUFormula, ih hw.qVec]

lemma shift_substs {p} (hp : IsSemiformula L n p) :
    IsSemitermVec L n m w → shift L (subst L w p) = subst L (termShiftVec L n w) (shift L p) := by
  revert m w
  apply IsSemiformula.pi1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv m w hw
    rw [substs_rel hR hv.isUTerm,
      shift_rel hR (hw.termSubstVec hv).isUTerm,
      shift_rel hR hv.isUTerm,
      substs_rel hR hv.termShiftVec.isUTerm]
    simp only [qqRel_inj, true_and]
    apply nth_ext' k
      (by rw [len_termShiftVec (hw.termSubstVec hv).isUTerm])
      (by rw [len_termSubstVec hv.termShiftVec.isUTerm])
    intro i hi
    rw [nth_termShiftVec (hw.termSubstVec hv).isUTerm hi,
      nth_termSubstVec hv.isUTerm hi,
      nth_termSubstVec hv.termShiftVec.isUTerm hi,
      nth_termShiftVec hv.isUTerm hi,
      termShift_termSubsts (hv.nth hi) hw]
  · intro n k R v hR hv m w hw
    rw [substs_nrel hR hv.isUTerm,
      shift_nrel hR (hw.termSubstVec hv).isUTerm,
      shift_nrel hR hv.isUTerm,
      substs_nrel hR hv.termShiftVec.isUTerm]
    simp only [qqNRel_inj, true_and]
    apply nth_ext' k
      (by rw [len_termShiftVec (hw.termSubstVec hv).isUTerm])
      (by rw [len_termSubstVec hv.termShiftVec.isUTerm])
    intro i hi
    rw [nth_termShiftVec (hw.termSubstVec hv).isUTerm hi,
      nth_termSubstVec hv.isUTerm hi,
      nth_termSubstVec hv.termShiftVec.isUTerm hi,
      nth_termShiftVec hv.isUTerm hi,
      termShift_termSubsts (hv.nth hi) hw]
  · intro n w hw; simp
  · intro n w hw; simp
  · intro n p q hp hq ihp ihq m w hw
    rw [substs_and hp.isUFormula hq.isUFormula,
      shift_and (hp.subst hw).isUFormula (hq.subst hw).isUFormula,
      shift_and hp.isUFormula hq.isUFormula,
      substs_and hp.shift.isUFormula hq.shift.isUFormula,
      ihp hw, ihq hw]
  · intro n p q hp hq ihp ihq m w hw
    rw [substs_or hp.isUFormula hq.isUFormula,
      shift_or (hp.subst hw).isUFormula (hq.subst hw).isUFormula,
      shift_or hp.isUFormula hq.isUFormula,
      substs_or hp.shift.isUFormula hq.shift.isUFormula,
      ihp hw, ihq hw]
  · intro n p hp ih m w hw
    rw [substs_all hp.isUFormula,
      shift_all (hp.subst hw.qVec).isUFormula,
      shift_all hp.isUFormula,
      substs_all hp.shift.isUFormula,
      ih hw.qVec,
      termShift_qVec hw]
  · intro n p hp ih m w hw
    rw [substs_ex hp.isUFormula,
      shift_exs (hp.subst hw.qVec).isUFormula,
      shift_exs hp.isUFormula,
      substs_ex hp.shift.isUFormula,
      ih hw.qVec,
      termShift_qVec hw]

lemma substs_substs {p} (hp : IsSemiformula L l p) :
    IsSemitermVec L n m w → IsSemitermVec L l n v → subst L w (subst L v p) = subst L (termSubstVec L l w v) p := by
  revert m w n v
  apply IsSemiformula.pi1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro l k R ts hR hts m w n v _ hv
    rw [substs_rel hR hts.isUTerm,
      substs_rel hR (hv.termSubstVec hts).isUTerm,
      substs_rel hR hts.isUTerm]
    simp only [qqRel_inj, true_and]
    apply nth_ext' k (by rw [len_termSubstVec (hv.termSubstVec hts).isUTerm]) (by rw [len_termSubstVec hts.isUTerm])
    intro i hi
    rw [nth_termSubstVec (hv.termSubstVec hts).isUTerm hi,
      nth_termSubstVec hts.isUTerm hi,
      nth_termSubstVec hts.isUTerm hi,
      termSubst_termSubst hv (hts.nth hi)]
  · intro l k R ts hR hts m w n v _ hv
    rw [substs_nrel hR hts.isUTerm,
      substs_nrel hR (hv.termSubstVec hts).isUTerm,
      substs_nrel hR hts.isUTerm]
    simp only [qqNRel_inj, true_and]
    apply nth_ext' k (by rw [len_termSubstVec (hv.termSubstVec hts).isUTerm]) (by rw [len_termSubstVec hts.isUTerm])
    intro i hi
    rw [nth_termSubstVec (hv.termSubstVec hts).isUTerm hi,
      nth_termSubstVec hts.isUTerm hi,
      nth_termSubstVec hts.isUTerm hi,
      termSubst_termSubst hv (hts.nth hi)]
  · intros; simp
  · intros; simp
  · intro l p q hp hq ihp ihq m w n v hw hv
    rw [substs_and hp.isUFormula hq.isUFormula,
      substs_and (hp.subst hv).isUFormula (hq.subst hv).isUFormula,
      substs_and hp.isUFormula hq.isUFormula,
      ihp hw hv, ihq hw hv]
  · intro l p q hp hq ihp ihq m w n v hw hv
    rw [substs_or hp.isUFormula hq.isUFormula,
      substs_or (hp.subst hv).isUFormula (hq.subst hv).isUFormula,
      substs_or hp.isUFormula hq.isUFormula,
      ihp hw hv, ihq hw hv]
  · intro l p hp ih m w n v hw hv
    rw [substs_all hp.isUFormula,
      substs_all (hp.subst hv.qVec).isUFormula,
      substs_all hp.isUFormula,
      ih hw.qVec hv.qVec,
      termSubstVec_qVec_qVec hv hw]
  · intro l p hp ih m w n v hw hv
    rw [substs_ex hp.isUFormula,
      substs_ex (hp.subst hv.qVec).isUFormula,
      substs_ex hp.isUFormula,
      ih hw.qVec hv.qVec,
      termSubstVec_qVec_qVec hv hw]

lemma subst_eq_self {n w : V} (hp : IsSemiformula L n p) (hw : IsSemitermVec L n n w) (H : ∀ i < n, w.[i] = ^#i) :
    subst L w p = p := by
  revert w
  apply IsSemiformula.pi1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv w _ H
    simp only [substs_rel, qqRel_inj, true_and, hR, hv.isUTerm]
    apply nth_ext' k (by simp [*, hv.isUTerm]) (by simp [hv.lh])
    intro i hi
    rw [nth_termSubstVec hv.isUTerm hi, termSubst_eq_self (hv.nth hi) H]
  · intro n k R v hR hv w _ H
    simp only [substs_nrel, qqNRel_inj, true_and, hR, hv.isUTerm]
    apply nth_ext' k (by simp [*, hv.isUTerm]) (by simp [hv.lh])
    intro i hi
    rw [nth_termSubstVec hv.isUTerm hi, termSubst_eq_self (hv.nth hi) H]
  · intro n w _ _; simp
  · intro n w _ _; simp
  · intro n p q hp hq ihp ihq w hw H
    simp [*, hp.isUFormula, hq.isUFormula, ihp hw H, ihq hw H]
  · intro n p q hp hq ihp ihq w hw H
    simp [*, hp.isUFormula, hq.isUFormula, ihp hw H, ihq hw H]
  · intro n p hp ih w hw H
    have H : ∀ i < n + 1, (qVec L w).[i] = ^#i := by
      intro i hi
      rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · simp [qVec]
      · have hi : i < n := by simpa using hi
        simp only [qVec, nth_adjoin_succ]
        rw [nth_termBShiftVec (by simpa [hw.lh] using hw.isUTerm) (by simp [hw.lh, hi])]
        simp [H i hi]
    simp [*, hp.isUFormula, ih hw.qVec H]
  · intro n p hp ih w hw H
    have H : ∀ i < n + 1, (qVec L w).[i] = ^#i := by
      intro i hi
      rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · simp [qVec]
      · have hi : i < n := by simpa using hi
        simp only [qVec, nth_adjoin_succ]
        rw [nth_termBShiftVec (by simpa [hw.lh] using hw.isUTerm) (by simp [hw.lh, hi])]
        simp [H i hi]
    simp [*, hp.isUFormula, ih hw.qVec H]

lemma subst_eq_self₁ (hp : IsSemiformula L 1 p) :
    subst L (^#0 ∷ 0) p = p := subst_eq_self hp (by simp) (by simp)


-- @@ L762-762 verbatim
end subst


-- @@ L764-764 verbatim
variable (L)


-- @@ L766-766 verbatim
noncomputable def substs1 (t u : V) : V := subst L ?[t] u


-- @@ L768-768 verbatim
noncomputable def substs1Graph : 𝚺₁.Semisentence 3 := .mkSigma “ z t p. ∃ v, !adjoinDef v t 0 ∧ !(substsGraph L) z v p”


-- @@ L770-770 verbatim
variable {L}


-- @@ L772-772 verbatim
section substs1


-- @@ L774-774 verbatim
section


-- @@ L776-776 verbatim
instance substs1.defined : 𝚺₁-Function₂[V] substs1 L via substs1Graph L := .mk fun v ↦ by simp [substs1Graph]; rfl


-- @@ L778-778 verbatim
instance substs1.definable : 𝚺₁-Function₂[V] substs1 L := substs1.defined.to_definable


-- @@ L780-780 verbatim
instance substs1.definable' : Γ-[m + 1]-Function₂[V] substs1 L := substs1.definable.of_sigmaOne


-- @@ L782-785 verbatim
end

lemma IsSemiformula.substs1 {n t p : V} (ht : IsSemiterm L n t) (hp : IsSemiformula L 1 p) : IsSemiformula L n (substs1 L t p) :=
  IsSemiformula.subst hp (by simp [ht])


-- @@ L787-787 verbatim
end substs1


-- @@ L789-789 verbatim
variable (L)


-- @@ L791-791 verbatim
noncomputable def free (p : V) : V := substs1 L ^&0 (shift L p)


-- @@ L793-794 verbatim
noncomputable def freeGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “q p. ∃ fz, !qqFvarDef fz 0 ∧ ∃ sp, !(shiftGraph L) sp p ∧ !(substs1Graph L) q fz sp”


-- @@ L796-796 verbatim
variable {L}


-- @@ L798-798 verbatim
/-! ### free function -/


-- @@ L800-800 verbatim
section free


-- @@ L802-802 verbatim
section


-- @@ L804-804 verbatim
instance free.defined : 𝚺₁-Function₁[V] free L via freeGraph L := .mk fun v ↦ by simp [freeGraph, free]


-- @@ L806-806 verbatim
instance free.definable : 𝚺₁-Function₁[V] free L := free.defined.to_definable


-- @@ L808-808 verbatim
instance free.definable' : Γ-[m + 1]-Function₁[V] free L := free.definable.of_sigmaOne


-- @@ L810-810 verbatim
end


-- @@ L812-813 verbatim
@[simp] lemma IsSemiformula.free {p : V} (hp : IsSemiformula L 1 p) : IsFormula L (free L p) :=
  IsSemiformula.substs1 (by simp) hp.shift


-- @@ L815-815 verbatim
end free


-- @@ L817-817 verbatim
section free1


-- @@ L819-819 verbatim
variable (L)


-- @@ L821-821 verbatim
noncomputable def free1 (p : V) : V := subst L ?[^&0, ^#0] (shift L p)


-- @@ L823-823 verbatim
variable {L}


-- @@ L825-826 verbatim
@[simp] lemma IsSemiformula.free1 {p : V} (hp : IsSemiformula L 2 p) : IsSemiformula L 1 (free1 L p) :=
  IsSemiformula.subst (m := 1) hp.shift (SemitermVec.adjoin (SemitermVec.adjoin (IsSemitermVec.empty _) (by simp)) (by simp))


-- @@ L828-828 verbatim
end free1


-- @@ L830-830 verbatim
/-! ### Complexity of formula -/


-- @@ L832-832 verbatim
section complexity


-- @@ L834-834 verbatim
namespace FormulaComplexity


-- @@ L836-846 verbatim
def blueprint : UformulaRec1.Blueprint where
  rel := .mkSigma “y param k R v. y = 0”
  nrel := .mkSigma “y param k R v. y = 0”
  verum := .mkSigma “y param. y = 0”
  falsum := .mkSigma “y param. y = 0”
  and := .mkSigma “y param p₁ p₂ y₁ y₂. !max.dfn y (y₁ + 1) (y₂ + 1)”
  or := .mkSigma “y param p₁ p₂ y₁ y₂. !max.dfn y (y₁ + 1) (y₂ + 1)”
  all := .mkSigma “y param p₁ y₁. y = y₁ + 1”
  exs := .mkSigma “y param p₁ y₁. y = y₁ + 1”
  allChanges := .mkSigma “param' param. param' = 0”
  exsChanges := .mkSigma “param' param. param' = 0”


-- @@ L848-868 verbatim
noncomputable def construction : UformulaRec1.Construction V blueprint where
  rel {_} := fun k R v ↦ 0
  nrel {_} := fun k R v ↦ 0
  verum {_} := 0
  falsum {_} := 0
  and {_} := fun _ _ y₁ y₂ ↦ max y₁ y₂ + 1
  or {_} := fun _ _ y₁ y₂ ↦ max y₁ y₂ + 1
  all {_} := fun _ y₁ ↦ y₁ + 1
  exs {_} := fun _ y₁ ↦ y₁ + 1
  allChanges := fun _ ↦ 0
  exsChanges := fun _ ↦ 0
  rel_defined := .mk fun v ↦ by simp [blueprint]
  nrel_defined := .mk fun v ↦ by simp [blueprint]
  verum_defined := .mk fun v ↦ by simp [blueprint]
  falsum_defined := .mk fun v ↦ by simp [blueprint]
  and_defined := .mk fun v ↦ by simp [blueprint, max_add_add_right]
  or_defined := .mk fun v ↦ by simp [blueprint, max_add_add_right]
  all_defined := .mk fun v ↦ by simp [blueprint]
  exs_defined := .mk fun v ↦ by simp [blueprint]
  allChanges_defined := .mk fun v ↦ by simp [blueprint]
  exChanges_defined := .mk fun v ↦ by simp [blueprint]


-- @@ L870-870 verbatim
end FormulaComplexity


-- @@ L872-872 verbatim
open FormulaComplexity


-- @@ L874-874 verbatim
variable (L)


-- @@ L876-876 verbatim
noncomputable def formulaComplexity (p : V) : V := construction.result L 0 p


-- @@ L878-878 verbatim
noncomputable def formulaComplexityGraph : 𝚺₁.Semisentence 2 := (blueprint.result L).rew (Rew.subst ![#0, ‘0’, #1])


-- @@ L880-880 verbatim
variable {L}


-- @@ L882-882 verbatim
section


-- @@ L884-885 verbatim
instance formulaComplexity.defined : 𝚺₁-Function₁[V] formulaComplexity L via formulaComplexityGraph L := .mk fun v ↦ by
  simpa [formulaComplexityGraph, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using! construction.result_defined.defined ![v 0, 0, v 1]


-- @@ L887-887 verbatim
instance formulaComplexity.definable : 𝚺₁-Function₁[V] formulaComplexity L := formulaComplexity.defined.to_definable


-- @@ L889-889 verbatim
instance formulaComplexity.definable' : Γ-[m + 1]-Function₁[V] formulaComplexity L := .of_sigmaOne formulaComplexity.definable


-- @@ L891-891 verbatim
end


-- @@ L893-894 verbatim
@[simp] lemma formulaComplexity_rel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    formulaComplexity L (^rel k R v) = 0 := by simp [formulaComplexity, hR, hv, construction]


-- @@ L896-897 verbatim
@[simp] lemma formulaComplexity_nrel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    formulaComplexity L (^nrel k R v) = 0 := by simp [formulaComplexity, hR, hv, construction]


-- @@ L899-900 verbatim
@[simp] lemma formulaComplexity_verum :
    formulaComplexity L (^⊤ : V) = 0 := by simp [formulaComplexity, construction]


-- @@ L902-903 verbatim
@[simp] lemma formulaComplexity_falsum :
    formulaComplexity L (^⊥ : V) = 0 := by simp [formulaComplexity, construction]


-- @@ L905-906 verbatim
@[simp] lemma formulaComplexity_and {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    formulaComplexity L (p ^⋏ q) = max (formulaComplexity L p) (formulaComplexity L q) + 1 := by simp [formulaComplexity, hp, hq, construction]


-- @@ L908-909 verbatim
@[simp] lemma formulaComplexity_or {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    formulaComplexity L (p ^⋎ q) = max (formulaComplexity L p) (formulaComplexity L q) + 1 := by simp [formulaComplexity, hp, hq, construction]


-- @@ L911-912 verbatim
@[simp] lemma formulaComplexity_all {p : V} (hp : IsUFormula L p) :
    formulaComplexity L (^∀ p) = formulaComplexity L p + 1 := by simp [formulaComplexity, hp, construction]


-- @@ L914-918 verbatim
@[simp] lemma formulaComplexity_ex {p : V} (hp : IsUFormula L p) :
    formulaComplexity L (^∃ p) = formulaComplexity L p + 1 := by simp [formulaComplexity, hp, construction]

lemma formulaComplexity_not_uformula {x : V} (h : ¬IsUFormula L x) :
    formulaComplexity L x = 0 := construction.result_prop_not _ h


-- @@ L920-930 verbatim
@[simp] lemma formulaComplexity_neg {p : V} : IsUFormula L p → formulaComplexity L (neg L p) = formulaComplexity L p := by
  apply IsUFormula.ISigma1.sigma1_succ_induction
  · definability
  · intro k r v hr hv; simp [hr, hv]
  · intro k r v hr hv; simp [hr, hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p hp ihp; simp [hp, ihp]
  · intro p hp ihp; simp [hp, ihp]


-- @@ L932-1000 verbatim
@[simp] lemma formulaComplexity_shift {p : V} : IsUFormula L p → formulaComplexity L (shift L p) = formulaComplexity L p := by
  apply IsUFormula.ISigma1.sigma1_succ_induction
  · definability
  · intro k r v hr hv; simp [hr, hv]
  · intro k r v hr hv; simp [hr, hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq
    simp [hp, hq, ihp, ihq]
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p hp ihp; simp [hp, ihp]
  · intro p hp ihp; simp [hp, ihp]

lemma fomulaComplexity_substs {p : V} (hp : IsSemiformula L n p) :
    IsSemitermVec L n m w → formulaComplexity L (subst L w p) = formulaComplexity L p := by
  revert m w
  apply IsSemiformula.pi1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv m w hw
    rw [formulaComplexity_rel hR hv.isUTerm, substs_rel hR hv.isUTerm, formulaComplexity_rel hR (hw.termSubstVec hv).isUTerm]
  · intro n k R v hR hv m w hw
    rw [formulaComplexity_nrel hR hv.isUTerm, substs_nrel hR hv.isUTerm, formulaComplexity_nrel hR (hw.termSubstVec hv).isUTerm]
  · intro n m w hw
    rw [substs_verum]
  · intro n m w hw
    rw [substs_falsum]
  · intro n p q hp hq ihp ihq m w hw
    rw [substs_and hp.isUFormula hq.isUFormula,
      formulaComplexity_and (hp.subst hw).isUFormula (hq.subst hw).isUFormula,
      ihp hw, ihq hw,
      formulaComplexity_and hp.isUFormula hq.isUFormula]
  · intro n p q hp hq ihp ihq m w hw
    rw [substs_or hp.isUFormula hq.isUFormula,
      formulaComplexity_or (hp.subst hw).isUFormula (hq.subst hw).isUFormula,
      ihp hw, ihq hw,
      formulaComplexity_or hp.isUFormula hq.isUFormula]
  · intro n p hp ihp m w hw
    rw [substs_all hp.isUFormula,
     formulaComplexity_all (hp.subst hw.qVec).isUFormula,
     ihp (hw.qVec),
     formulaComplexity_all hp.isUFormula]
  · intro n p hp ihp m w hw
    rw [substs_ex hp.isUFormula,
     formulaComplexity_ex (hp.subst hw.qVec).isUFormula,
     ihp (hw.qVec),
     formulaComplexity_ex hp.isUFormula]

lemma fomulaComplexity_substs1 {p : V} (hp : IsSemiformula L 1 p) (ht : IsSemiterm L m t) :
    formulaComplexity L (substs1 L t p) = formulaComplexity L p := by
  unfold substs1
  rw [fomulaComplexity_substs hp (IsSemitermVec.singleton.mpr ht)]


lemma fomulaComplexity_free {p : V} (hp : IsSemiformula L 1 p) :
    formulaComplexity L (free L p) = formulaComplexity L p := by
  unfold free
  have : IsSemiterm (V := V) L 0 ^&0 := by simp
  rw [fomulaComplexity_substs1 hp.shift this,
    formulaComplexity_shift hp.isUFormula]

lemma fomulaComplexity_free1 {p : V} (hp : IsSemiformula L 2 p) :
    formulaComplexity L (free1 L p) = formulaComplexity L p := by
  unfold free1
  have : IsSemiterm (V := V) L 0 ^&0 := by simp
  rw [fomulaComplexity_substs (m := 1) (V := V) hp.shift]
  · rw [formulaComplexity_shift hp.isUFormula]
  · apply IsSemitermVec.adjoin ?_ (by simp)
    apply IsSemitermVec.adjoin ?_ (by simp)
    exact IsSemitermVec.nil _


-- @@ L1002-1002 verbatim
end complexity


-- @@ L1004-1004 verbatim
@[simp] lemma lt_max_succ_left (a b : V) : a < max a b + 1 := lt_succ_iff_le.mpr <| by simp


-- @@ L1006-1006 verbatim
@[simp] lemma lt_max_succ_right (a b : V) : b < max a b + 1 := lt_succ_iff_le.mpr <| by simp


-- @@ L1008-1197 verbatim
/-! A structural induction correspondence to `FFL.FirstOrder.Semiformula.formulaRec`.  -/
lemma IsFormula.sigma1_structural_induction {P : V → Prop} (hP : 𝚺₁-Predicate P)
    (hrel : ∀ k r v, L.IsRel k r → IsTermVec L k v → P (^rel k r v))
    (hnrel : ∀ k r v, L.IsRel k r → IsTermVec L k v → P (^nrel k r v))
    (hverum : P ^⊤)
    (hfalsum : P ^⊥)
    (hand : ∀ p q, IsFormula L p → IsFormula L q → P p → P q → P (p ^⋏ q))
    (hor : ∀ p q, IsFormula L p → IsFormula L q → P p → P q → P (p ^⋎ q))
    (hall : ∀ p, IsSemiformula L 1 p → P (free L p) → P (^∀ p))
    (hexs : ∀ p, IsSemiformula L 1 p → P (free L p) → P (^∃ p)) {p} :
    IsFormula L p → P p := by
  have hm : 𝚺₁-Function₁[V] formulaComplexity L := inferInstance
  let f : V → V := fun p ↦ max p (free L (π₂ (p - 1)))
  have hf : 𝚺₁-Function₁ f := by unfold f; definability
  apply measured_bounded_sigma1_order_induction hm hf ?_ ?_ p
  · definability
  intro p ih hp
  rcases IsSemiformula.case_iff.mp hp with
    (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩
      | rfl | rfl
      | ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, p₂, h₁, h₂, rfl⟩
      | ⟨p₁, h₁, rfl⟩ | ⟨p₁, h₁, rfl⟩)
  · exact hrel _ _ _ hR hv
  · exact hnrel _ _ _ hR hv
  · exact hverum
  · exact hfalsum
  · have ih₁ : P p₁ :=
      ih p₁ (by simp only [le_sup_iff, f]; left; exact le_of_lt <| by simp) (by simp [h₁.isUFormula, h₂.isUFormula]) h₁
    have ih₂ : P p₂ :=
      ih p₂ (by simp only [le_sup_iff, f]; left; exact le_of_lt <| by simp) (by simp [h₁.isUFormula, h₂.isUFormula]) h₂
    exact hand _ _ h₁ h₂ ih₁ ih₂
  · have ih₁ : P p₁ :=
      ih p₁ (by simp only [le_sup_iff, f]; left; exact le_of_lt <| by simp) (by simp [h₁.isUFormula, h₂.isUFormula]) h₁
    have ih₂ : P p₂ :=
      ih p₂ (by simp only [le_sup_iff, f]; left; exact le_of_lt <| by simp) (by simp [h₁.isUFormula, h₂.isUFormula]) h₂
    exact hor _ _ h₁ h₂ ih₁ ih₂
  · have h₁ : IsSemiformula L 1 p₁ := by simpa using h₁
    have : P (free L p₁) := ih (free L p₁) (by simp only [le_sup_iff, f]; right; simp [qqAll])
      (by simp [fomulaComplexity_free h₁, h₁.isUFormula])
      (h₁.free)
    exact hall _ h₁ this
  · have h₁ : IsSemiformula L 1 p₁ := by simpa using h₁
    have : P (free L p₁) := ih (free L p₁) (by simp only [le_sup_iff, f]; right; simp [qqExs])
      (by simp [fomulaComplexity_free h₁, h₁.isUFormula])
      (h₁.free)
    exact hexs _ h₁ this

lemma IsFormula.sigma1_structural_induction₂ {P : V → Prop} (hP : 𝚺₁-Predicate P)
    (hrel : ∀ k r v, L.IsRel k r → IsSemitermVec L k 1 v → P (^rel k r v))
    (hnrel : ∀ k r v, L.IsRel k r → IsSemitermVec L k 1 v → P (^nrel k r v))
    (hverum : P ^⊤)
    (hfalsum : P ^⊥)
    (hand : ∀ p q, IsSemiformula L 1 p → IsSemiformula L 1 q → P p → P q → P (p ^⋏ q))
    (hor : ∀ p q, IsSemiformula L 1 p → IsSemiformula L 1 q → P p → P q → P (p ^⋎ q))
    (hall : ∀ p, IsSemiformula L 2 p → P (free1 L p) → P (^∀ p))
    (hexs : ∀ p, IsSemiformula L 2 p → P (free1 L p) → P (^∃ p)) {p} :
    IsSemiformula L 1 p → P p := by
  have hm : 𝚺₁-Function₁[V] formulaComplexity L := inferInstance
  let f : V → V := fun p ↦ max p (free1 L (π₂ (p - 1)))
  have hf : 𝚺₁-Function₁ f := by unfold f; definability
  apply measured_bounded_sigma1_order_induction hm hf ?_ ?_ p
  · definability
  intro p ih hp
  rcases IsSemiformula.case_iff.mp hp with
    (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩
      | rfl | rfl
      | ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, p₂, h₁, h₂, rfl⟩
      | ⟨p₁, h₁, rfl⟩ | ⟨p₁, h₁, rfl⟩)
  · exact hrel _ _ _ hR hv
  · exact hnrel _ _ _ hR hv
  · exact hverum
  · exact hfalsum
  · have ih₁ : P p₁ :=
      ih p₁ (by simp only [le_sup_iff, f]; left; exact le_of_lt <| by simp) (by simp [h₁.isUFormula, h₂.isUFormula]) h₁
    have ih₂ : P p₂ :=
      ih p₂ (by simp only [le_sup_iff, f]; left; exact le_of_lt <| by simp) (by simp [h₁.isUFormula, h₂.isUFormula]) h₂
    exact hand _ _ h₁ h₂ ih₁ ih₂
  · have ih₁ : P p₁ :=
      ih p₁ (by simp only [le_sup_iff, f]; left; exact le_of_lt <| by simp) (by simp [h₁.isUFormula, h₂.isUFormula]) h₁
    have ih₂ : P p₂ :=
      ih p₂ (by simp only [le_sup_iff, f]; left; exact le_of_lt <| by simp) (by simp [h₁.isUFormula, h₂.isUFormula]) h₂
    exact hor _ _ h₁ h₂ ih₁ ih₂
  · have h₁ : IsSemiformula L 2 p₁ := by simpa [one_add_one_eq_two] using h₁
    have : P (free1 L p₁) := ih (free1 L p₁) (by simp only [le_sup_iff, f]; right; simp [qqAll])
      (by simp [fomulaComplexity_free1 h₁, h₁.isUFormula])
      h₁.free1
    exact hall _ h₁ this
  · have h₁ : IsSemiformula L 2 p₁ := by simpa  [one_add_one_eq_two] using h₁
    have : P (free1 L p₁) := ih (free1 L p₁) (by simp only [le_sup_iff, f]; right; simp [qqExs])
      (by simp [fomulaComplexity_free1 h₁, h₁.isUFormula])
      h₁.free1
    exact hexs _ h₁ this

lemma IsFormula.sigma1_structural_induction₂_ss {P : V → Prop} (hP : 𝚺₁-Predicate P)
    (hrel : ∀ k r v, L.IsRel k r → IsSemitermVec L k 1 v → P (^rel k r v))
    (hnrel : ∀ k r v, L.IsRel k r → IsSemitermVec L k 1 v → P (^nrel k r v))
    (hverum : P ^⊤)
    (hfalsum : P ^⊥)
    (hand : ∀ p q, IsSemiformula L 1 p → IsSemiformula L 1 q → P p → P q → P (p ^⋏ q))
    (hor : ∀ p q, IsSemiformula L 1 p → IsSemiformula L 1 q → P p → P q → P (p ^⋎ q))
    (hall : ∀ p, IsSemiformula L 2 p → P (free1 L <| shift L <| shift L <| p) → P (^∀ p))
    (hexs : ∀ p, IsSemiformula L 2 p → P (free1 L <| shift L <| shift L <| p) → P (^∃ p)) {p} :
    IsSemiformula L 1 p → P p := by
  have hm : 𝚺₁-Function₁[V] formulaComplexity L := inferInstance
  let f : V → V := fun p ↦ max p (free1 L <| shift L <| shift L <| (π₂ (p - 1)))
  have hf : 𝚺₁-Function₁ f := by unfold f; definability
  apply measured_bounded_sigma1_order_induction hm hf ?_ ?_ p
  · definability
  intro p ih hp
  rcases IsSemiformula.case_iff.mp hp with
    (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩
      | rfl | rfl
      | ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, p₂, h₁, h₂, rfl⟩
      | ⟨p₁, h₁, rfl⟩ | ⟨p₁, h₁, rfl⟩)
  · exact hrel _ _ _ hR hv
  · exact hnrel _ _ _ hR hv
  · exact hverum
  · exact hfalsum
  · have ih₁ : P p₁ :=
      ih p₁ (by simp only [le_sup_iff, f]; left; exact le_of_lt <| by simp) (by simp [h₁.isUFormula, h₂.isUFormula]) h₁
    have ih₂ : P p₂ :=
      ih p₂ (by simp only [le_sup_iff, f]; left; exact le_of_lt <| by simp) (by simp [h₁.isUFormula, h₂.isUFormula]) h₂
    exact hand _ _ h₁ h₂ ih₁ ih₂
  · have ih₁ : P p₁ :=
      ih p₁ (by simp only [le_sup_iff, f]; left; exact le_of_lt <| by simp) (by simp [h₁.isUFormula, h₂.isUFormula]) h₁
    have ih₂ : P p₂ :=
      ih p₂ (by simp only [le_sup_iff, f]; left; exact le_of_lt <| by simp) (by simp [h₁.isUFormula, h₂.isUFormula]) h₂
    exact hor _ _ h₁ h₂ ih₁ ih₂
  · have h₁ : IsSemiformula L 2 p₁ := by simpa [one_add_one_eq_two] using h₁
    have : P (free1 L <| shift L <| shift L <| p₁) :=
      ih (free1 L <| shift L <| shift L <| p₁) (by simp only [le_sup_iff, f]; right; simp [qqAll])
      (by rw [fomulaComplexity_free1 h₁.shift.shift, formulaComplexity_shift h₁.shift.isUFormula,
          formulaComplexity_shift h₁.isUFormula]; simp [h₁.isUFormula])
      h₁.shift.shift.free1
    exact hall _ h₁ this
  · have h₁ : IsSemiformula L 2 p₁ := by simpa [one_add_one_eq_two] using h₁
    have : P (free1 L <| shift L <| shift L <| p₁) :=
      ih (free1 L <| shift L <| shift L <| p₁) (by simp only [le_sup_iff, f]; right; simp [qqExs])
      (by rw [fomulaComplexity_free1 h₁.shift.shift, formulaComplexity_shift h₁.shift.isUFormula,
          formulaComplexity_shift h₁.isUFormula]; simp [h₁.isUFormula])
      h₁.shift.shift.free1
    exact hexs _ h₁ this

/-
section fvfree

variable (L)

def Language.IsFVFree (n p : V) : Prop := IsSemiformula L n p ∧ shift L p = p

section

def _root_.FFL.FirstOrder.Arithmetic.LDef.isFVFreeDef (pL : LDef) : 𝚺₁.Semisentence 2 :=
  .mkSigma “n p | !(isSemiformula L).sigma n p ∧ !pshift LDef p p”

lemma isFVFree_defined : 𝚺₁-Relation L.IsFVFree via pL.isFVFreeDef := by
  intro v; simp [LDef.isFVFreeDef, HierarchySymbol.Semiformula.val_sigma, (semiformula_defined L).df.iff, (shift_defined L).df.iff]
  simp [Language.IsFVFree, eq_comm]

end

variable {L}

@[simp] lemma Language.IsFVFree.verum (n : V) : L.IsFVFree n ^⊤[n] := by simp [Language.IsFVFree]

@[simp] lemma Language.IsFVFree.falsum (n : V) : L.IsFVFree n ^⊥[n] := by simp [Language.IsFVFree]

lemma Language.IsFVFree.and {n p q : V} (hp : L.IsFVFree n p) (hq : L.IsFVFree n q) :
    L.IsFVFree n (p ^⋏[n] q) := by simp [Language.IsFVFree, hp.1, hq.1, hp.2, hq.2]

lemma Language.IsFVFree.or {n p q : V} (hp : L.IsFVFree n p) (hq : L.IsFVFree n q) :
    L.IsFVFree n (p ^⋎[n] q) := by simp [Language.IsFVFree, hp.1, hq.1, hp.2, hq.2]

lemma Language.IsFVFree.all {n p : V} (hp : L.IsFVFree (n + 1) p) :
    L.IsFVFree n (^∀¹[n] p) := by simp [Language.IsFVFree, hp.1, hp.2]

lemma Language.IsFVFree.exs {n p : V} (hp : L.IsFVFree (n + 1) p) :
    L.IsFVFree n (^∃¹[n] p) := by simp [Language.IsFVFree, hp.1, hp.2]

@[simp] lemma Language.IsFVFree.neg_iff : L.IsFVFree n (neg L p) ↔ L.IsFVFree n p := by
  constructor
  · intro h
    have hp : Semiformula L n p := IsSemiformula.neg_iff.mp h.1
    have : shift L (neg L p) = neg L p := h.2
    simp [shift_neg hp, neg_inj_iff hp.shift hp] at this
    exact ⟨hp, this⟩
  · intro h; exact ⟨by simp [h.1], by rw [shift_neg h.1, h.2]⟩

end fvfree
-/


-- @@ L1199-1205 verbatim
namespace Arithmetic

-- `Arithmetic` is intentionally re-opened here even though the ambient namespace
-- already contains it; renaming would break the widely-used public API
-- (`Bootstrapping.Arithmetic.*`). Suppress the new dupNamespace linter for the
-- declarations in this namespace (the option is scoped by `namespace`/`end` and
-- reverts automatically at `end Arithmetic`).

-- @@ L1206-1206 verbatim
set_option linter.dupNamespace false


-- @@ L1208-1208 verbatim
noncomputable def qqEQ (x y : V) : V := ^rel 2 (eqIndex : V) ?[x, y]


-- @@ L1210-1210 verbatim
noncomputable def qqNEQ (x y : V) : V := ^nrel 2 (eqIndex : V) ?[x, y]


-- @@ L1212-1212 verbatim
noncomputable def qqLT (x y : V) : V := ^rel 2 (ltIndex : V) ?[x, y]


-- @@ L1214-1214 verbatim
noncomputable def qqNLT (x y : V) : V := ^nrel 2 (ltIndex : V) ?[x, y]


-- @@ L1216-1216 verbatim
notation:75 x:75 " ^= " y:76 => qqEQ x y


-- @@ L1218-1218 verbatim
notation:75 x:75 " ^≠ " y:76 => qqNEQ x y


-- @@ L1220-1220 verbatim
notation:78 x:78 " ^< " y:79 => qqLT x y


-- @@ L1222-1222 verbatim
notation:78 x:78 " ^≮ " y:79 => qqNLT x y


-- @@ L1224-1225 verbatim
@[simp] lemma lt_qqEQ_left (x y : V) : x < x ^= y := by
  simpa using! nth_lt_qqRel_of_lt (i := 0) (k := 2) (r := (eqIndex : V)) (v := ?[x, y]) (by simp)


-- @@ L1227-1228 verbatim
@[simp] lemma lt_qqEQ_right (x y : V) : y < x ^= y := by
  simpa using! nth_lt_qqRel_of_lt (i := 1) (k := 2) (r := (eqIndex : V)) (v := ?[x, y]) (by simp)


-- @@ L1230-1231 verbatim
@[simp] lemma lt_qqLT_left (x y : V) : x < x ^< y := by
  simpa using! nth_lt_qqRel_of_lt (i := 0) (k := 2) (r := (ltIndex : V)) (v := ?[x, y]) (by simp)


-- @@ L1233-1234 verbatim
@[simp] lemma lt_qqLT_right (x y : V) : y < x ^< y := by
  simpa using! nth_lt_qqRel_of_lt (i := 1) (k := 2) (r := (ltIndex : V)) (v := ?[x, y]) (by simp)


-- @@ L1236-1237 verbatim
@[simp] lemma lt_qqNEQ_left (x y : V) : x < x ^≠ y := by
  simpa using! nth_lt_qqNRel_of_lt (i := 0) (k := 2) (r := (eqIndex : V)) (v := ?[x, y]) (by simp)


-- @@ L1239-1240 verbatim
@[simp] lemma lt_qqNEQ_right (x y : V) : y < x ^≠ y := by
  simpa using! nth_lt_qqNRel_of_lt (i := 1) (k := 2) (r := (eqIndex : V)) (v := ?[x, y]) (by simp)


-- @@ L1242-1243 verbatim
@[simp] lemma lt_qqNLT_left (x y : V) : x < x ^≮ y := by
  simpa using! nth_lt_qqNRel_of_lt (i := 0) (k := 2) (r := (ltIndex : V)) (v := ?[x, y]) (by simp)


-- @@ L1245-1246 verbatim
@[simp] lemma lt_qqNLT_right (x y : V) : y < x ^≮ y := by
  simpa using! nth_lt_qqNRel_of_lt (i := 1) (k := 2) (r := (ltIndex : V)) (v := ?[x, y]) (by simp)


-- @@ L1248-1249 verbatim
def _root_.FFL.FirstOrder.Arithmetic.qqEQDef : 𝚺₁.Semisentence 3 :=
  .mkSigma “p x y. ∃ v, !mkVec₂Def v x y ∧ !qqRelDef p 2 ↑eqIndex v”


-- @@ L1251-1252 verbatim
def _root_.FFL.FirstOrder.Arithmetic.qqNEQDef : 𝚺₁.Semisentence 3 :=
  .mkSigma “p x y. ∃ v, !mkVec₂Def v x y ∧ !qqNRelDef p 2 ↑eqIndex v”


-- @@ L1254-1255 verbatim
def _root_.FFL.FirstOrder.Arithmetic.qqLTDef : 𝚺₁.Semisentence 3 :=
  .mkSigma “p x y. ∃ v, !mkVec₂Def v x y ∧ !qqRelDef p 2 ↑ltIndex v”


-- @@ L1257-1258 verbatim
def _root_.FFL.FirstOrder.Arithmetic.qqNLTDef : 𝚺₁.Semisentence 3 :=
  .mkSigma “p x y. ∃ v, !mkVec₂Def v x y ∧ !qqNRelDef p 2 ↑ltIndex v”


-- @@ L1260-1260 verbatim
instance qqEQ_defined : 𝚺₁-Function₂ (qqEQ : V → V → V) via qqEQDef := .mk fun v ↦ by simp [qqEQDef, numeral_eq_natCast, qqEQ]


-- @@ L1262-1262 verbatim
instance qqNEQ_defined : 𝚺₁-Function₂ (qqNEQ : V → V → V) via qqNEQDef := .mk fun v ↦ by simp [qqNEQDef, numeral_eq_natCast, qqNEQ]


-- @@ L1264-1264 verbatim
instance qqLT_defined : 𝚺₁-Function₂ (qqLT : V → V → V) via qqLTDef := .mk fun v ↦ by simp [qqLTDef, numeral_eq_natCast, qqLT]


-- @@ L1266-1266 verbatim
instance qqNLT_defined : 𝚺₁-Function₂ (qqNLT : V → V → V) via qqNLTDef := .mk fun v ↦ by simp [qqNLTDef, numeral_eq_natCast, qqNLT]


-- @@ L1268-1268 verbatim
instance (Γ m) : Γ-[m + 1]-Function₂ (qqEQ : V → V → V) := .of_sigmaOne qqEQ_defined.to_definable


-- @@ L1270-1270 verbatim
instance (Γ m) : Γ-[m + 1]-Function₂ (qqNEQ : V → V → V) := .of_sigmaOne qqNEQ_defined.to_definable


-- @@ L1272-1272 verbatim
instance (Γ m) : Γ-[m + 1]-Function₂ (qqLT : V → V → V) := .of_sigmaOne qqLT_defined.to_definable


-- @@ L1274-1296 verbatim
instance (Γ m) : Γ-[m + 1]-Function₂ (qqNLT : V → V → V) := .of_sigmaOne qqNLT_defined.to_definable

lemma neg_eq {t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) : neg ℒₒᵣ (t ^= u) = t ^≠ u := by
  simp only [qqEQ, qqNEQ]
  rw [neg_rel (L := ℒₒᵣ) (by simp) (by simp [ht, hu])]

lemma neg_neq {t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) : neg ℒₒᵣ (t ^≠ u) = t ^= u := by
  simp only [qqNEQ, qqEQ]
  rw [neg_nrel (L := ℒₒᵣ) (by simp) (by simp [ht, hu])]

lemma neg_lt {t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) : neg ℒₒᵣ (t ^< u) = t ^≮ u := by
  simp only [qqLT, qqNLT]
  rw [neg_rel (L := ℒₒᵣ) (by simp) (by simp [ht, hu])]

lemma neg_nlt {t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) : neg ℒₒᵣ (t ^≮ u) = t ^< u := by
  simp only [qqNLT, qqLT]
  rw [neg_nrel (L := ℒₒᵣ) (by simp) (by simp [ht, hu])]

lemma substs_eq {t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) :
    subst ℒₒᵣ w (t ^= u) = (termSubst ℒₒᵣ w t) ^= (termSubst ℒₒᵣ w u) := by
  simp only [qqEQ]
  rw [substs_rel (L := ℒₒᵣ) (by simp) (by simp [ht, hu])]
  simp [termSubstVec_cons₂ ht hu]


-- @@ L1298-1298 verbatim
end Arithmetic


-- @@ L1300-1300 verbatim
end FFL.FirstOrder.Arithmetic.Bootstrapping
