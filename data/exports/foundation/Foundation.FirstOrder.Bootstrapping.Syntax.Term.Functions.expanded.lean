module

public import Foundation.FirstOrder.Bootstrapping.Syntax.Term.Basic


-- @@ L5-5 verbatim
@[expose] public section

-- @@ L6-6 verbatim
namespace FFL.FirstOrder.Arithmetic.Bootstrapping


-- @@ L8-8 verbatim
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


-- @@ L10-10 verbatim
section


-- @@ L12-12 verbatim
variable {L : Language} [L.Encodable] [L.LORDefinable]


-- @@ L14-14 verbatim
namespace TermSubst


-- @@ L16-19 verbatim
def blueprint : Language.TermRec.Blueprint 1 where
  bvar := .mkSigma “y z w. !nthDef y w z”
  fvar := .mkSigma “y x w. !qqFvarDef y x”
  func := .mkSigma “y k f v v' w. !qqFuncDef y k f v'”


-- @@ L21-27 verbatim
noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar (param z)        := (param 1).[z]
  fvar (_     x)        := ^&x
  func (_     k f _ v') := ^func k f v'
  bvar_defined := .mk fun v ↦ by simp [blueprint]
  fvar_defined := .mk fun v ↦ by simp [blueprint]
  func_defined := .mk fun v ↦ by simp [blueprint]


-- @@ L29-29 verbatim
end TermSubst


-- @@ L31-31 verbatim
section termSubst


-- @@ L33-33 verbatim
open TermSubst


-- @@ L35-35 verbatim
variable (L)


-- @@ L37-37 verbatim
noncomputable def termSubst (w t : V) : V := construction.result L ![w] t


-- @@ L39-39 verbatim
noncomputable def termSubstVec (k w v : V) : V := construction.resultVec L ![w] k v


-- @@ L41-41 verbatim
noncomputable def termSubstGraph : 𝚺₁.Semisentence 3 := (blueprint.result L).rew <| Rew.subst ![#0, #2, #1]


-- @@ L43-43 verbatim
noncomputable def termSubstVecGraph : 𝚺₁.Semisentence 4 := (blueprint.resultVec L).rew <| Rew.subst ![#0, #1, #3, #2]


-- @@ L45-45 verbatim
variable {L}


-- @@ L47-47 verbatim
variable {n m w : V}


-- @@ L49-50 verbatim
@[simp] lemma termSubst_bvar (z) :
    termSubst L w ^#z = w.[z] := by simp [termSubst, construction]


-- @@ L52-53 verbatim
@[simp] lemma termSubst_fvar (x) :
    termSubst L w ^&x = ^&x := by simp [termSubst, construction]


-- @@ L55-57 verbatim
@[simp] lemma termSubst_func {k f v} (hkf : L.IsFunc k f) (hv : IsUTermVec L k v) :
    termSubst L w (^func k f v) = ^func k f (termSubstVec L k w v) := by
  simp [termSubst, construction, hkf, hv]; rfl


-- @@ L59-59 verbatim
section


-- @@ L61-63 verbatim
instance termSubst.defined : 𝚺₁-Function₂ termSubst (V := V) L via termSubstGraph L := .mk fun v ↦ by
  simpa [termSubstGraph, termSubst, Matrix.constant_eq_singleton, Matrix.comp_vecCons']
    using construction.result_defined.defined ![v 0, v 2, v 1]


-- @@ L65-65 verbatim
instance termSubst.definable : 𝚺₁-Function₂ termSubst (V := V) L := termSubst.defined.to_definable


-- @@ L67-67 verbatim
instance termSubst.definable' : Γ-[k + 1]-Function₂ termSubst (V := V) L := termSubst.definable.of_sigmaOne


-- @@ L69-71 verbatim
instance termSubstVec.defined : 𝚺₁-Function₃ termSubstVec (V := V) L via termSubstVecGraph L := .mk fun v ↦ by
  simpa [termSubstVecGraph, termSubstVec, Matrix.constant_eq_singleton, Matrix.comp_vecCons']
    using construction.resultVec_defined.defined ![v 0, v 1, v 3, v 2]


-- @@ L73-73 verbatim
instance termSubstVec.definable : 𝚺₁-Function₃ termSubstVec (V := V) L := termSubstVec.defined.to_definable


-- @@ L75-75 verbatim
instance termSubstVec.definable' : Γ-[i + 1]-Function₃ termSubstVec (V := V) L := termSubstVec.definable.of_sigmaOne


-- @@ L77-77 verbatim
end


-- @@ L79-80 verbatim
@[simp] lemma len_termSubstVec {k ts : V} (hts : IsUTermVec L k ts) :
    len (termSubstVec L k w ts) = k := construction.resultVec_lh L _ hts


-- @@ L82-84 verbatim
@[simp] lemma nth_termSubstVec {k ts i : V} (hts : IsUTermVec L k ts) (hi : i < k) :
    (termSubstVec L k w ts).[i] = termSubst L w ts.[i] :=
  construction.nth_resultVec L _ hts hi


-- @@ L86-90 verbatim
@[simp] lemma termSubstVec_nil (w : V) : termSubstVec L 0 w 0 = 0 := construction.resultVec_nil L _

lemma termSubstVec_cons {k t ts : V} (ht : IsUTerm L t) (hts : IsUTermVec L k ts) :
    termSubstVec L (k + 1) w (t ∷ ts) = termSubst L w t ∷ termSubstVec L k w ts :=
  construction.resultVec_cons L ![w] hts ht


-- @@ L92-94 verbatim
@[simp] lemma termSubstVec_cons₁ {t : V} (ht : IsUTerm L t) :
    termSubstVec L 1 w ?[t] = ?[termSubst L w t] := by
  rw [show (1 : V) = 0 + 1  by simp, termSubstVec_cons] <;> simp [*]


-- @@ L96-98 verbatim
@[simp] lemma termSubstVec_cons₂ {t₁ t₂ : V} (ht₁ : IsUTerm L t₁) (ht₂ : IsUTerm L t₂) :
    termSubstVec L 2 w ?[t₁, t₂] = ?[termSubst L w t₁, termSubst L w t₂] := by
  rw [show (2 : V) = 0 + 1 + 1  by simp [one_add_one_eq_two], termSubstVec_cons] <;> simp [*]


-- @@ L100-108 verbatim
@[simp] lemma IsSemitermVec.termSubst {t} (hw : IsSemitermVec L n m w) (ht : IsSemiterm L n t) : IsSemiterm L m (termSubst L w t) := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simpa using hw.nth hz
  · intro x; simp
  · intro k f v hkf hv ih
    simp only [hkf, hv.isUTerm, termSubst_func, IsSemiterm.func, true_and]
    exact IsSemitermVec.iff.mpr
      ⟨by simp [hv.isUTerm], fun i hi ↦ by rw [nth_termSubstVec hv.isUTerm hi]; exact ih i hi⟩


-- @@ L110-111 verbatim
@[simp] lemma IsUTermVec.termSubst {t} (hw : IsUTermVec L n w) (ht : IsSemiterm L n t) : IsUTerm L (termSubst L w t) :=
  IsSemitermVec.termSubst hw.isSemitermVec ht |>.isUTerm


-- @@ L113-115 verbatim
@[simp] lemma IsSemitermVec.termSubstVec {k n m v} (hw : IsSemitermVec L n m w) (hv : IsSemitermVec L k n v) :
    IsSemitermVec L k m (termSubstVec L k w v) := IsSemitermVec.iff.mpr
  ⟨by simp [hv.isUTerm], fun i hi ↦ by rw [nth_termSubstVec hv.isUTerm hi]; exact hw.termSubst (hv.nth hi)⟩


-- @@ L117-156 verbatim
@[simp] lemma substs_nil {t : V} (ht : IsSemiterm L 0 t) : termSubst L 0 t = t := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z; simp
  · intro x; simp
  · intro k f v hf hv ih
    simp only [hf, hv.isUTerm, termSubst_func, qqFunc_inj, true_and]
    apply nth_ext' k (by simp [hv.isUTerm]) (by simp [hv.lh])
    intro i hi
    simp [nth_termSubstVec hv.isUTerm hi, ih i hi]

lemma termSubst_termSubst {l n w v t : V} (hv : IsSemitermVec L l n v) (ht : IsSemiterm L l t) :
    termSubst L w (termSubst L v t) = termSubst L (termSubstVec L l w v) t := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz
    rw [termSubst_bvar z, termSubst_bvar z, nth_termSubstVec hv.isUTerm hz]
  · intro x; simp
  · intro k f ts hf hts ih
    rw [termSubst_func hf hts.isUTerm,
      termSubst_func hf (hv.termSubstVec hts).isUTerm,
      termSubst_func hf hts.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k (by rw [len_termSubstVec (hv.termSubstVec hts).isUTerm]) (by rw [len_termSubstVec hts.isUTerm])
    intro i hi
    rw [nth_termSubstVec (hv.termSubstVec hts).isUTerm hi,
      nth_termSubstVec hts.isUTerm hi, nth_termSubstVec hts.isUTerm hi, ih i hi]

lemma termSubst_eq_self {n w t : V} (ht : IsSemiterm L n t) (H : ∀ i < n, w.[i] = ^#i) :
    termSubst L w t = t := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simp [hz, H]
  · intro x; simp
  · intro k f v hf hv ih
    rw [termSubst_func hf hv.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k (by rw [len_termSubstVec hv.isUTerm]) (by simp [hv.lh])
    intro i hi
    rw [nth_termSubstVec hv.isUTerm hi, ih i hi]


-- @@ L158-158 verbatim
end termSubst


-- @@ L160-160 verbatim
namespace TermShift


-- @@ L162-165 verbatim
def blueprint : Language.TermRec.Blueprint 0 where
  bvar := .mkSigma “y z. !qqBvarDef y z”
  fvar := .mkSigma “y x. !qqFvarDef y (x + 1)”
  func := .mkSigma “y k f v v'. !qqFuncDef y k f v'”


-- @@ L167-173 verbatim
noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar (_ z)        := ^#z
  fvar (_ x)        := ^&(x + 1)
  func (_ k f _ v') := ^func k f v'
  bvar_defined := .mk fun v ↦ by simp [blueprint]
  fvar_defined := .mk fun v ↦ by simp [blueprint]
  func_defined := .mk fun v ↦ by simp [blueprint]


-- @@ L175-175 verbatim
end TermShift


-- @@ L177-177 verbatim
section termShift


-- @@ L179-179 verbatim
open TermShift


-- @@ L181-181 verbatim
variable (L)


-- @@ L183-183 verbatim
noncomputable def termShift (t : V) : V := construction.result L ![] t


-- @@ L185-185 verbatim
noncomputable def termShiftVec (k v : V) : V := construction.resultVec L ![] k v


-- @@ L187-187 verbatim
noncomputable def termShiftGraph : 𝚺₁.Semisentence 2 := blueprint.result L


-- @@ L189-189 verbatim
noncomputable def termShiftVecGraph : 𝚺₁.Semisentence 3 := blueprint.resultVec L


-- @@ L191-191 verbatim
variable {L}


-- @@ L193-193 verbatim
variable {n : V}


-- @@ L195-196 verbatim
@[simp] lemma termShift_bvar (z : V) :
    termShift L ^#z = ^#z := by simp [termShift, construction]


-- @@ L198-199 verbatim
@[simp] lemma termShift_fvar (x : V) :
    termShift L ^&x = ^&(x + 1) := by simp [termShift, construction]


-- @@ L201-203 verbatim
@[simp] lemma termShift_func {k f v : V} (hkf : L.IsFunc k f) (hv : IsUTermVec L k v) :
    termShift L (^func k f v) = ^func k f (termShiftVec L k v) := by
  simp [termShift, construction, hkf, hv]; rfl


-- @@ L205-205 verbatim
section


-- @@ L207-208 verbatim
instance termShift.defined : 𝚺₁-Function₁ termShift (V := V) L via termShiftGraph L := .mk fun v ↦ by
  simpa [termShiftGraph, termShift] using! construction.result_defined.defined v


-- @@ L210-210 verbatim
instance termShift.definable : 𝚺₁-Function₁ termShift (V := V) L := termShift.defined.to_definable


-- @@ L212-212 verbatim
instance termShift.definable' : Γ-[i + 1]-Function₁ termShift (V := V) L := termShift.definable.of_sigmaOne


-- @@ L214-215 verbatim
instance termShiftVec.defined : 𝚺₁-Function₂ termShiftVec (V := V) L via termShiftVecGraph L := .mk fun v ↦ by
  simpa [termShiftVecGraph, termShiftVec] using! construction.resultVec_defined.defined v


-- @@ L217-217 verbatim
instance termShiftVec.definable : 𝚺₁-Function₂ termShiftVec (V := V) L := termShiftVec.defined.to_definable


-- @@ L219-219 verbatim
instance termShiftVec.definable' : Γ-[i + 1]-Function₂ termShiftVec (V := V) L := termShiftVec.definable.of_sigmaOne


-- @@ L221-221 verbatim
end


-- @@ L223-224 verbatim
@[simp] lemma len_termShiftVec {k ts : V} (hts : IsUTermVec L k ts) :
    len (termShiftVec L k ts) = k := construction.resultVec_lh L _ hts


-- @@ L226-227 verbatim
@[simp] lemma nth_termShiftVec {k ts i : V} (hts : IsUTermVec L k ts) (hi : i < k) :
    (termShiftVec L k ts).[i] = termShift L ts.[i] := construction.nth_resultVec L _ hts hi


-- @@ L229-233 verbatim
@[simp] lemma termShiftVec_nil : termShiftVec (V := V) L 0 0 = 0 := construction.resultVec_nil L ![]

lemma termShiftVec_cons {k t ts : V} (ht : IsUTerm L t) (hts : IsUTermVec L k ts) :
    termShiftVec L (k + 1) (t ∷ ts) = termShift L t ∷ termShiftVec L k ts :=
  construction.resultVec_cons L ![] hts ht


-- @@ L235-237 verbatim
@[simp] lemma termShiftVec_cons₁ {t₁ : V} (ht₁ : IsUTerm L t₁) :
    termShiftVec L 1 (?[t₁] : V) = ?[termShift L t₁] := by
  rw [show (1 : V) = 0 + 1  by simp, termShiftVec_cons] <;> simp [*]


-- @@ L239-241 verbatim
@[simp] lemma termShiftVec_cons₂ {t₁ t₂ : V} (ht₁ : IsUTerm L t₁) (ht₂ : IsUTerm L t₂) :
    termShiftVec L 2 (?[t₁, t₂] : V) = ?[termShift L t₁, termShift L t₂] := by
  rw [show (2 : V) = 0 + 1 + 1  by simp [one_add_one_eq_two], termShiftVec_cons] <;> simp [ht₁, ht₂]


-- @@ L243-250 verbatim
@[simp] lemma IsUTerm.termShift {t} (ht : IsUTerm L t) : IsUTerm L (termShift L t : V) := by
  apply IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z; simp
  · intro x; simp
  · intro k f v hkf hv ih;
    simp only [hkf, hv, termShift_func, func_iff, true_and]
    exact ⟨by simp [hv], by intro i hi; rw [nth_termShiftVec hv hi]; exact ih i hi⟩


-- @@ L252-263 verbatim
@[simp] lemma IsSemiterm.termShift {t : V} (ht : IsSemiterm L n t) : IsSemiterm L n (termShift L t) := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simp [hz]
  · intro x; simp
  · intro k f v hkf hv ih;
    simp only [hkf, hv.isUTerm, termShift_func, func, true_and]
    refine IsSemitermVec.iff.mpr ⟨?_, ?_⟩
    · simp [termShiftVec, hv.isUTerm]
    · intro i hi
      rw [nth_termShiftVec hv.isUTerm hi]
      exact ih i hi


-- @@ L265-266 verbatim
@[simp] lemma IsUTermVec.termShiftVec {k v : V} (hv : IsUTermVec L k v) : IsUTermVec L k (termShiftVec L k v) :=
    ⟨by simp [hv], fun i hi ↦ by rw [nth_termShiftVec hv hi]; exact (hv.nth hi).termShift⟩


-- @@ L268-271 verbatim
@[simp] lemma IsSemitermVec.termShiftVec {k n v : V} (hv : IsSemitermVec L k n v) : IsSemitermVec L k n (termShiftVec L k v) :=
  IsSemitermVec.iff.mpr
    ⟨by simp [hv.isUTerm], fun i hi ↦ by
      rw [nth_termShiftVec hv.isUTerm hi]; exact (hv.nth hi).termShift⟩


-- @@ L273-285 verbatim
@[simp] lemma IsUTerm.termBVtermShift {t : V} (ht : IsUTerm L t) : termBV L (Bootstrapping.termShift L t) = termBV L t := by
  apply IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · simp
  · simp
  · intro k f v hf hv ih
    rw [termShift_func hf hv,
      termBV_func hf hv.termShiftVec,
      termBV_func hf hv]
    congr 1
    apply nth_ext' k (by simp [*]) (by simp [*])
    intro i hi
    simp [*]


-- @@ L287-291 verbatim
@[simp] lemma IsUTermVec.termBVVectermShiftVec {v : V} (hv : IsUTermVec L k v) :
    termBVVec L k (Bootstrapping.termShiftVec L k v) = termBVVec L k v := by
  apply nth_ext' k (by simp [*]) (by simp [*])
  intro i hi
  simp [*, IsUTerm.termBVtermShift (hv.nth hi)]


-- @@ L293-293 verbatim
end termShift


-- @@ L295-295 verbatim
namespace TermBShift


-- @@ L297-300 verbatim
def blueprint : Language.TermRec.Blueprint 0 where
  bvar := .mkSigma “y z. !qqBvarDef y (z + 1)”
  fvar := .mkSigma “y x. !qqFvarDef y x”
  func := .mkSigma “y k f v v'. !qqFuncDef y k f v'”


-- @@ L302-308 verbatim
noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar (_ z)        := ^#(z + 1)
  fvar (_ x)        := ^&x
  func (_ k f _ v') := ^func k f v'
  bvar_defined := .mk fun v ↦ by simp [blueprint]
  fvar_defined := .mk fun v ↦ by simp [blueprint]
  func_defined := .mk fun v ↦ by simp [blueprint]


-- @@ L310-310 verbatim
end TermBShift


-- @@ L312-312 verbatim
section termBShift


-- @@ L314-314 verbatim
open TermBShift


-- @@ L316-316 verbatim
variable (L)


-- @@ L318-318 verbatim
noncomputable def termBShift (t : V) : V := construction.result L ![] t


-- @@ L320-320 verbatim
noncomputable def termBShiftVec (k v : V) : V := construction.resultVec L ![] k v


-- @@ L322-322 verbatim
noncomputable def termBShiftGraph : 𝚺₁.Semisentence 2 := blueprint.result L


-- @@ L324-324 verbatim
noncomputable def termBShiftVecGraph : 𝚺₁.Semisentence 3 := blueprint.resultVec L


-- @@ L326-326 verbatim
variable {L}


-- @@ L328-329 verbatim
@[simp] lemma termBShift_bvar (z : V) :
    termBShift L ^#z = ^#(z + 1) := by simp [termBShift, construction]


-- @@ L331-332 verbatim
@[simp] lemma termBShift_fvar (x : V) :
    termBShift L ^&x = ^&x := by simp [termBShift, construction]


-- @@ L334-336 verbatim
@[simp] lemma termBShift_func {k f v : V} (hkf : L.IsFunc k f) (hv : IsUTermVec L k v) :
    termBShift L (^func k f v) = ^func k f (termBShiftVec L k v) := by
  simp [termBShift, construction, hkf, hv]; rfl


-- @@ L338-338 verbatim
section


-- @@ L340-341 verbatim
instance termBShift.defined : 𝚺₁-Function₁ termBShift (V := V) L via termBShiftGraph L := .mk fun v ↦ by
  simpa using! construction.result_defined.defined v


-- @@ L343-343 verbatim
instance termBShift.definable : 𝚺₁-Function₁ termBShift (V := V) L := termBShift.defined.to_definable


-- @@ L345-345 verbatim
instance termBShift.definable' : Γ-[i + 1]-Function₁ termBShift (V := V) L := termBShift.definable.of_sigmaOne


-- @@ L347-348 verbatim
instance termBShiftVec.defined : 𝚺₁-Function₂ termBShiftVec (V := V) L via termBShiftVecGraph L := .mk fun v ↦ by
  simpa using! construction.resultVec_defined.defined v


-- @@ L350-350 verbatim
instance termBShiftVec.definable : 𝚺₁-Function₂ termBShiftVec (V := V) L := termBShiftVec.defined.to_definable


-- @@ L352-352 verbatim
instance termBShiftVec.definable' : Γ-[i + 1]-Function₂ termBShiftVec (V := V) L := termBShiftVec.definable.of_sigmaOne


-- @@ L354-354 verbatim
end


-- @@ L356-357 verbatim
@[simp] lemma len_termBShiftVec {k ts : V} (hts : IsUTermVec L k ts) :
    len (termBShiftVec L k ts) = k := construction.resultVec_lh L _ hts


-- @@ L359-361 verbatim
@[simp] lemma nth_termBShiftVec {k ts i : V} (hts : IsUTermVec L k ts) (hi : i < k) :
    (termBShiftVec L k ts).[i] = termBShift L ts.[i] :=
  construction.nth_resultVec L _ hts hi


-- @@ L363-368 verbatim
@[simp] lemma termBShiftVec_nil : termBShiftVec (V := V) L 0 0 = 0 :=
  construction.resultVec_nil L ![]

lemma termBShiftVec_cons {k t ts : V} (ht : IsUTerm L t) (hts : IsUTermVec L k ts) :
    termBShiftVec L (k + 1) (t ∷ ts) = termBShift L t ∷ termBShiftVec L k ts :=
  construction.resultVec_cons L ![] hts ht


-- @@ L370-372 verbatim
@[simp] lemma termBShiftVec_cons₁ {t₁ : V} (ht₁ : IsUTerm L t₁) :
    termBShiftVec L 1 (?[t₁] : V) = ?[termBShift L t₁] := by
  rw [show (1 : V) = 0 + 1  by simp, termBShiftVec_cons] <;> simp [*]


-- @@ L374-376 verbatim
@[simp] lemma termBShiftVec_cons₂ {t₁ t₂ : V} (ht₁ : IsUTerm L t₁) (ht₂ : IsUTerm L t₂) :
    termBShiftVec L 2 (?[t₁, t₂] : V) = ?[termBShift L t₁, termBShift L t₂] := by
  rw [show (2 : V) = 0 + 1 + 1  by simp [one_add_one_eq_two], termBShiftVec_cons] <;> simp [*]


-- @@ L378-389 verbatim
@[simp] lemma IsSemiterm.termBShift {t : V} (ht : IsSemiterm L n t) : IsSemiterm L (n + 1) (termBShift L t) := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simp [hz]
  · intro x; simp
  · intro k f v hkf hv ih;
    simp only [hkf, hv.isUTerm, termBShift_func, func, true_and]
    refine IsSemitermVec.iff.mpr ⟨?_, ?_⟩
    · simp [hv.isUTerm]
    · intro i hi
      rw [nth_termBShiftVec hv.isUTerm hi]
      exact ih i hi


-- @@ L391-411 verbatim
@[simp] lemma IsSemitermVec.termBShiftVec {k n v : V} (hv : IsSemitermVec L k n v) : IsSemitermVec L k (n + 1) (termBShiftVec L k v) :=
  IsSemitermVec.iff.mpr
  ⟨by simp [hv.isUTerm], fun i hi ↦ by
    rw [nth_termBShiftVec hv.isUTerm hi]; exact (hv.nth hi).termBShift⟩

lemma termBShift_termShift {t : V} (ht : IsSemiterm L n t) : termBShift L (termShift L t) = termShift L (termBShift L t) := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simp
  · intro x; simp
  · intro k f v hkf hv ih
    rw [termShift_func hkf hv.isUTerm,
      termBShift_func hkf hv.termShiftVec.isUTerm,
      termBShift_func hkf hv.isUTerm,
      termShift_func hkf hv.termBShiftVec.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k
      (by rw [len_termBShiftVec hv.termShiftVec.isUTerm]) (by rw [len_termShiftVec hv.termBShiftVec.isUTerm])
    intro i hi
    rw [nth_termBShiftVec hv.termShiftVec.isUTerm hi, nth_termShiftVec hv.isUTerm hi,
      nth_termShiftVec hv.termBShiftVec.isUTerm hi, nth_termBShiftVec hv.isUTerm hi, ih i hi]


-- @@ L413-471 verbatim
end termBShift

/-
namespace TermFreeAt

def blueprint : Language.TermRec.Blueprint 1 where
  bvar := .mkSigma “y z m. (z < m → !qqBvarDef y z) ∧ (¬z < m → !qqFvarDef y 0)”
  fvar := .mkSigma “y x m. !qqFvarDef y (x + 1)”
  func := .mkSigma “y k f v v' m. !qqFuncDef y k f v'”

noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar param z        := if z < param 0 then ^#z else ^&0
  fvar param x        := ^&(x + 1)
  func param k f _ v' := ^func k f v'
  bvar_defined := by
    intro v
    by_cases C : v 1 < v 2 <;> simp [blueprint, C]
  fvar_defined := by intro v; simp [blueprint]
  func_defined := by intro v; simp [blueprint]

end TermFreeAt

section termFreeAt

open TermFreeAt

variable (L)

noncomputable def termFreeAt (m t : V) : V := construction.result L ![m] t

noncomputable def termFreeAtVec (m k v : V) : V := construction.resultVec L ![m] k v

def termFreeAtGraph : 𝚺₁.Semisentence 3 := (blueprint.result L).rew <| Rew.subst ![#0, #2, #1]

def termFreeAtVecGraph : 𝚺₁.Semisentence 4 := (blueprint.resultVec L).rew <| Rew.subst ![#0, #1, #3, #2]

variable {L}

@[simp] lemma termFreeAt_bvar (m z : V) :
    termFreeAt L m ^#z = if z < m then ^#z else ^&0 := by simp [termFreeAt, construction]

@[simp] lemma termFreeAt_fvar (m x : V) :
    termFreeAt L m ^&x = ^&(x + 1) := by simp [termFreeAt, construction]

@[simp] lemma termFreeAt_func {m k f v : V} (hkf : L.IsFunc k f) (hv : IsUTermVec L k v) :
    termFreeAt L m (^func k f v) = ^func k f (termFreeAtVec L m k v) := by
  simp [termFreeAt, construction, hkf, hv]; rfl

section

lemma termFreeAt.defined : 𝚺₁-Function₂[V] termFreeAt L via termFreeAtGraph L := by
  intro v
  simpa [termFreeAtGraph, termFreeAt, Matrix.constant_eq_singleton, Matrix.comp_vecCons']
    using construction.result_defined (L := L) ![v 0, v 2, v 1]

end

end termFreeAt
-/

-- @@ L472-472 verbatim
variable (L)


-- @@ L474-474 verbatim
noncomputable def qVec (w : V) : V := ^#0 ∷ termBShiftVec L (len w) w


-- @@ L476-477 verbatim
noncomputable def qVecGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “w' w. ∃ k, !lenDef k w ∧ ∃ sw, !(termBShiftVecGraph L) sw k w ∧ ∃ t, !qqBvarDef t 0 ∧ !adjoinDef w' t sw”


-- @@ L479-479 verbatim
variable {L}


-- @@ L481-481 verbatim
section


-- @@ L483-483 verbatim
instance qVec.defined : 𝚺₁-Function₁[V] qVec L via qVecGraph L := .mk fun v ↦ by simp [qVecGraph]; rfl


-- @@ L485-485 verbatim
instance qVec.definable : 𝚺₁-Function₁[V] qVec L := qVec.defined.to_definable


-- @@ L487-487 verbatim
instance qVec.definable' : Γ-[m + 1]-Function₁[V] qVec L := qVec.definable.of_sigmaOne


-- @@ L489-489 verbatim
end


-- @@ L491-602 verbatim
@[simp] lemma len_qVec {k w : V} (h : IsUTermVec L k w) : len (qVec L w) = k + 1 := by
  rcases h.lh; simp [qVec, h]

lemma IsSemitermVec.qVec {k n w : V} (h : IsSemitermVec L k n w) : IsSemitermVec L (k + 1) (n + 1) (qVec L w) := by
  rcases h.lh
  refine IsSemitermVec.iff.mpr ⟨?_, ?_⟩
  · simp [h.isUTerm, Bootstrapping.qVec]
  · intro i hi
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp [Bootstrapping.qVec]
    · simpa [Bootstrapping.qVec, nth_termBShiftVec h.isUTerm (by simpa using hi)] using
        h.nth (by simpa using hi) |>.termBShift

lemma substs_cons_bShift {u t w : V} (ht : IsSemiterm L n t) :
    termSubst L (u ∷ w) (termBShift L t) = termSubst L w t := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simp
  · intro x; simp
  · intro k f v hf hv ih
    rw [termBShift_func hf hv.isUTerm,
      termSubst_func hf hv.termBShiftVec.isUTerm,
      termSubst_func hf hv.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k
      (by rw [len_termSubstVec hv.termBShiftVec.isUTerm])
      (by rw [len_termSubstVec hv.isUTerm])
    intro i hi
    rw [nth_termSubstVec hv.termBShiftVec.isUTerm hi,
      nth_termSubstVec hv.isUTerm hi,
      nth_termBShiftVec hv.isUTerm hi,
      ih i hi]

lemma termShift_termSubsts {n m w t : V} (ht : IsSemiterm L n t) (hw : IsSemitermVec L n m w) :
    termShift L (termSubst L w t) = termSubst L (termShiftVec L n w) (termShift L t) := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simp [nth_termShiftVec hw.isUTerm hz]
  · intro x; simp
  · intro k f v hf hv ih
    rw [termSubst_func hf hv.isUTerm,
      termShift_func hf (hw.termSubstVec hv).isUTerm,
      termShift_func hf hv.isUTerm,
      termSubst_func hf hv.termShiftVec.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k
      (by rw [len_termShiftVec (hw.termSubstVec hv).isUTerm])
      (by rw [len_termSubstVec hv.termShiftVec.isUTerm])
    intro i hi
    rw [nth_termShiftVec (hw.termSubstVec hv).isUTerm hi,
      nth_termSubstVec hv.isUTerm hi,
      nth_termSubstVec hv.termShiftVec.isUTerm hi,
      nth_termShiftVec hv.isUTerm hi, ih i hi]

lemma bShift_substs {n m w t : V} (ht : IsSemiterm L n t) (hw : IsSemitermVec L n m w) :
    termBShift L (termSubst L w t) = termSubst L (termBShiftVec L n w) t := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simp [nth_termBShiftVec hw.isUTerm hz]
  · intro x; simp
  · intro k f v hf hv ih
    rw [termSubst_func hf hv.isUTerm,
      termBShift_func hf (hw.termSubstVec hv).isUTerm,
      termSubst_func hf hv.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k
      (by rw [len_termBShiftVec (hw.termSubstVec hv).isUTerm])
      (by rw [len_termSubstVec hv.isUTerm])
    intro i hi
    simp [nth_termBShiftVec (hw.termSubstVec hv).isUTerm hi, nth_termSubstVec hv.isUTerm hi, ih i hi]

lemma substs_qVec_bShift {n t m w : V} (ht : IsSemiterm L n t) (hw : IsSemitermVec L n m w) :
    termSubst L (qVec L w) (termBShift L t) = termBShift L (termSubst L w t) := by
  rcases hw.lh
  simp [qVec, substs_cons_bShift ht, bShift_substs ht hw]

lemma termSubstVec_qVec_qVec {l n m : V} (hv : IsSemitermVec L l n v) (hw : IsSemitermVec L n m w) :
    termSubstVec L (l + 1) (qVec L w) (qVec L v) = qVec L (termSubstVec L l w v) := by
  apply nth_ext' (len v + 1)
    (by rw [len_termSubstVec hv.qVec.isUTerm, hv.lh])
    (by rw [len_qVec (hw.termSubstVec hv).isUTerm, hv.lh])
  intro i hi
  unfold qVec
  rcases hv.lh; rcases hw.lh
  rw [(hw.termSubstVec hv).lh]
  rw [termSubstVec_cons (by simp) (by rcases hv.lh; exact hv.termBShiftVec.isUTerm)]
  rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
  · simp
  · have hi : i < len v := by simpa using hi
    simp [nth_termSubstVec hv.termBShiftVec.isUTerm hi,
      nth_termBShiftVec hv.isUTerm hi,
      nth_termBShiftVec (hw.termSubstVec hv).isUTerm hi,
      nth_termSubstVec hv.isUTerm hi,
      substs_cons_bShift (hv.nth hi),
      bShift_substs (hv.nth hi) hw]

lemma termShift_qVec {n m w : V} (hw : IsSemitermVec L n m w) :
    termShiftVec L (n + 1) (qVec L w) = qVec L (termShiftVec L n w) := by
  apply nth_ext' (n + 1)
    (by rw [len_termShiftVec hw.qVec.isUTerm])
    (by rw [len_qVec hw.termShiftVec.isUTerm])
  intro i hi
  rw [nth_termShiftVec hw.qVec.isUTerm hi]
  unfold qVec
  rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
  · simp
  · rcases hw.lh
    rw [nth_adjoin_succ, nth_adjoin_succ,
      nth_termBShiftVec hw.isUTerm (by simpa using hi),
      nth_termBShiftVec (by simp [hw.isUTerm]) (by simpa [hw.isUTerm] using hi),
      nth_termShiftVec hw.isUTerm (by simpa using hi),
      termBShift_termShift (hw.nth (by simpa using hi))]


-- @@ L604-604 verbatim
section fvfree


-- @@ L606-606 verbatim
variable (L)


-- @@ L608-608 verbatim
def IsTermFVFree (n t : V) : Prop := IsSemiterm L n t ∧ termShift L t = t


-- @@ L610-610 verbatim
variable {L}


-- @@ L612-613 verbatim
@[simp] lemma IsTermFVFree.bvar (x : V) : IsTermFVFree L n ^#x ↔ x < n := by
  simp [IsTermFVFree]


-- @@ L615-616 verbatim
@[simp] lemma IsTermFVFree.fvar (x : V) : ¬IsTermFVFree L n ^&x := by
  simp [IsTermFVFree]


-- @@ L618-618 verbatim
end fvfree


-- @@ L620-620 verbatim
end


-- @@ L622-628 verbatim
namespace Arithmetic

-- `Arithmetic` is intentionally re-opened here even though the ambient namespace
-- already contains it; renaming would break the widely-used public API
-- (`Bootstrapping.Arithmetic.*`). Suppress the new dupNamespace linter for the
-- declarations in this namespace (the option is scoped by `namespace`/`end` and
-- reverts automatically at `end Arithmetic`).

-- @@ L629-629 verbatim
set_option linter.dupNamespace false


-- @@ L631-631 verbatim
protected def zero : ℕ := qqFuncN 0 zeroIndex 0


-- @@ L633-633 verbatim
protected def one : ℕ := qqFuncN 0 oneIndex 0


-- @@ L635-635 verbatim
noncomputable def qqAdd (x y : V) : V := ^func 2 (addIndex : V) ?[x, y]


-- @@ L637-637 verbatim
noncomputable def qqMul (x y : V) : V := ^func 2 (mulIndex : V) ?[x, y]


-- @@ L639-639 verbatim
notation "𝟎" => Arithmetic.zero


-- @@ L641-641 verbatim
notation "𝟏" => Arithmetic.one


-- @@ L643-643 verbatim
infixl:80 " ^+ " => qqAdd


-- @@ L645-645 verbatim
infixl:82 " ^* " => qqMul


-- @@ L647-647 verbatim
section


-- @@ L649-650 verbatim
def qqAddGraph : 𝚺₁.Semisentence 3 :=
  .mkSigma “t x y. ∃ v, !mkVec₂Def v x y ∧ !qqFuncDef t 2 ↑addIndex v”


-- @@ L652-653 verbatim
def qqMulGraph : 𝚺₁.Semisentence 3 :=
  .mkSigma “t x y. ∃ v, !mkVec₂Def v x y ∧ !qqFuncDef t 2 ↑mulIndex v”


-- @@ L655-656 verbatim
instance qqAdd_defined : 𝚺₁-Function₂ (qqAdd : V → V → V) via qqAddGraph := .mk fun v ↦ by
  simp [qqAddGraph, numeral_eq_natCast, qqAdd]


-- @@ L658-659 verbatim
instance qqMul_defined : 𝚺₁-Function₂ (qqMul : V → V → V) via qqMulGraph := .mk fun v ↦ by
  simp [qqMulGraph, numeral_eq_natCast, qqMul]


-- @@ L661-661 verbatim
instance : Γ-[m + 1]-Function₂ (qqAdd : V → V → V) := .of_sigmaOne qqAdd_defined.to_definable


-- @@ L663-663 verbatim
instance : Γ-[m + 1]-Function₂ (qqMul : V → V → V) := .of_sigmaOne qqMul_defined.to_definable


-- @@ L665-665 verbatim
end


-- @@ L667-668 verbatim
@[simp] lemma lt_qqAdd_left (x y : V) : x < x ^+ y := by
  simpa using! nth_lt_qqFunc_of_lt (i := 0) (k := 2) (f := (addIndex : V)) (v := ?[x, y]) (by simp)


-- @@ L670-671 verbatim
@[simp] lemma lt_qqAdd_right (x y : V) : y < x ^+ y := by
  simpa using! nth_lt_qqFunc_of_lt (i := 1) (k := 2) (f := (addIndex : V)) (v := ?[x, y]) (by simp)


-- @@ L673-674 verbatim
@[simp] lemma lt_qqMul_left (x y : V) : x < x ^* y := by
  simpa using! nth_lt_qqFunc_of_lt (i := 0) (k := 2) (f := (mulIndex : V)) (v := ?[x, y]) (by simp)


-- @@ L676-677 verbatim
@[simp] lemma lt_qqMul_right (x y : V) : y < x ^* y := by
  simpa using! nth_lt_qqFunc_of_lt (i := 1) (k := 2) (f := (mulIndex : V)) (v := ?[x, y]) (by simp)


-- @@ L679-680 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma qqFunc_absolute (k f v : ℕ) : ((^func k f v : ℕ) : V) = ^func (k : V) (f : V) (v : V) := by simp [qqFunc, nat_cast_pair]


-- @@ L682-683 verbatim
@[simp] lemma zero_semiterm : IsSemiterm ℒₒᵣ n (𝟎 : V) := by
  simp [Arithmetic.zero, qqFunc_absolute, qqFuncN_eq_qqFunc]


-- @@ L685-686 verbatim
@[simp] lemma one_semiterm : IsSemiterm ℒₒᵣ n (𝟏 : V) := by
  simp [Arithmetic.one, qqFunc_absolute, qqFuncN_eq_qqFunc]


-- @@ L688-690 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma coe_zero_eq : (𝟎 : V) = (^func 0 ⌜(Language.Zero.zero : (ℒₒᵣ).Func 0)⌝ 0) := by
  simp [Arithmetic.zero, qqFuncN_eq_qqFunc, qqFunc, nat_cast_pair]; rfl


-- @@ L692-694 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma coe_one_eq : (𝟏 : V) = (^func 0 ⌜(Language.One.one : (ℒₒᵣ).Func 0)⌝ 0) := by
  simp [Arithmetic.one, qqFuncN_eq_qqFunc, qqFunc, nat_cast_pair]; rfl


-- @@ L696-696 verbatim
namespace Numeral


-- @@ L698-700 verbatim
def blueprint : PR.Blueprint 0 where
  zero := .mkSigma “y. y = ↑Arithmetic.one”
  succ := .mkSigma “y t n. !qqAddGraph y t ↑Arithmetic.one”


-- @@ L702-706 verbatim
noncomputable def construction : PR.Construction V blueprint where
  zero := fun _ ↦ 𝟏
  succ := fun _ _ t ↦ t ^+ 𝟏
  zero_defined := .mk fun v ↦ by simp [blueprint, numeral_eq_natCast]
  succ_defined := .mk fun v ↦ by simp [qqAdd, blueprint, numeral_eq_natCast]


-- @@ L708-708 verbatim
noncomputable def numeralAux (x : V) : V := construction.result ![] x


-- @@ L710-710 verbatim
@[simp] lemma numeralAux_zero : numeralAux (0 : V) = 𝟏 := by simp [numeralAux, construction]


-- @@ L712-712 verbatim
@[simp] lemma numeralAux_succ (x : V) : numeralAux (x + 1) = numeralAux x ^+ 𝟏 := by simp [numeralAux, construction]


-- @@ L714-714 verbatim
section


-- @@ L716-716 verbatim
def numeralAuxGraph : 𝚺₁.Semisentence 2 := blueprint.resultDef


-- @@ L718-719 verbatim
instance numeralAux.defined : 𝚺₁-Function₁ (numeralAux : V → V) via numeralAuxGraph := .mk
  fun v ↦ by simp [construction.result_defined_iff, numeralAuxGraph]; rfl


-- @@ L721-721 verbatim
instance numeralAux.definable : 𝚺-[0 + 1]-Function₁ (numeralAux : V → V) := numeralAux.defined.to_definable


-- @@ L723-723 verbatim
end


-- @@ L725-730 verbatim
@[simp] lemma lt_numeralAux_self (n : V) : n < numeralAux n := by
    induction n using ISigma1.sigma1_succ_induction
    · definability
    case zero => simp [Arithmetic.one, qqFuncN_eq_qqFunc]
    case succ n ih =>
      refine lt_of_lt_of_le ((add_lt_add_iff_right 1).mpr ih) (by simp [succ_le_iff_lt])


-- @@ L732-736 verbatim
@[simp] lemma numeralAux_semiterm (n x : V) : IsSemiterm ℒₒᵣ n (numeralAux x) := by
  induction x using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ x ih => simp [qqAdd, ih]


-- @@ L738-738 verbatim
end Numeral


-- @@ L740-740 verbatim
section numeral


-- @@ L742-742 verbatim
open Numeral


-- @@ L744-744 verbatim
noncomputable def numeral (x : V) : V := if x = 0 then 𝟎 else numeralAux (x - 1)


-- @@ L746-749 verbatim
def numeralGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “t x.
    (x = 0 → t = ↑Arithmetic.zero) ∧
    (x ≠ 0 → ∃ x', !subDef x' x 1 ∧ !numeralAuxGraph t x')”


-- @@ L751-751 verbatim
@[simp] lemma numeral_zero : numeral (0 : V) = 𝟎 := by simp [numeral]


-- @@ L753-753 verbatim
@[simp] lemma numeral_one : numeral (1 : V) = 𝟏 := by simp [numeral]


-- @@ L755-760 verbatim
@[simp] lemma numeral_add_two : numeral (n + 1 + 1 : V) = numeral (n + 1) ^+ 𝟏 := by simp [numeral]

lemma numeral_succ_pos (pos : 0 < n) : numeral (n + 1 : V) = numeral n ^+ 𝟏 := by
  rcases zero_or_succ n with (rfl | ⟨n, rfl⟩)
  · simp at pos
  simp [numeral]


-- @@ L762-763 verbatim
@[simp] lemma numeral_semiterm (n x : V) : IsSemiterm ℒₒᵣ n (numeral x) := by
  by_cases hx : x = 0 <;> simp [hx, numeral]


-- @@ L765-765 verbatim
@[simp] lemma numeral_uterm (x : V) : IsUTerm ℒₒᵣ (numeral x) := (numeral_semiterm 0 x).isUTerm


-- @@ L767-770 verbatim
@[simp] lemma le_numeral_self (n : V) : n ≤ numeral n := by
  rcases zero_or_succ n with (rfl | ⟨n, rfl⟩)
  · simp
  · simp [numeral, succ_le_iff_lt]


-- @@ L772-772 verbatim
section


-- @@ L774-776 verbatim
instance numeral_defined : 𝚺₁-Function₁ (numeral : V → V) via numeralGraph := .mk fun v ↦ by
  simp [numeralGraph, numeral_eq_natCast]
  by_cases hv1 : v 1 = 0 <;> simp [hv1, numeral]


-- @@ L778-778 verbatim
instance numeral_definable : 𝚺₁-Function₁ (numeral : V → V) := numeral_defined.to_definable


-- @@ L780-780 verbatim
instance numeral_definable' : Γ-[m + 1]-Function₁ (numeral : V → V) := .of_sigmaOne numeral_definable


-- @@ L782-782 verbatim
end


-- @@ L784-794 verbatim
@[simp] lemma numeral_substs {w : V} (_ : IsSemitermVec ℒₒᵣ n m w) (x : V) :
    termSubst ℒₒᵣ w (numeral x) = numeral x := by
  induction x using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp [Arithmetic.zero, qqFunc_absolute, qqFuncN_eq_qqFunc]
  case succ x ih =>
    rcases zero_or_succ x with (rfl | ⟨x, rfl⟩)
    · simp [Arithmetic.one, qqFunc_absolute, qqFuncN_eq_qqFunc]
    · simp only [numeral_add_two, qqAdd]
      rw [termSubst_func (L := ℒₒᵣ) (by simp) (by simp [Arithmetic.one, qqFunc_absolute, qqFuncN_eq_qqFunc])]
      simp [ih, Arithmetic.one, qqFunc_absolute, qqFuncN_eq_qqFunc]


-- @@ L796-806 verbatim
@[simp] lemma numeral_shift (x : V) :
    termShift ℒₒᵣ (numeral x) = numeral x := by
  induction x using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp [Arithmetic.zero, qqFunc_absolute, qqFuncN_eq_qqFunc]
  case succ x ih =>
    rcases zero_or_succ x with (rfl | ⟨x, rfl⟩)
    · simp [Arithmetic.one, qqFunc_absolute, qqFuncN_eq_qqFunc]
    · simp only [numeral_add_two, qqAdd]
      rw [termShift_func (L := ℒₒᵣ) (by simp) (by simp [Arithmetic.one, qqFunc_absolute, qqFuncN_eq_qqFunc])]
      simp [ih, Arithmetic.one, qqFunc_absolute, qqFuncN_eq_qqFunc]


-- @@ L808-816 verbatim
@[simp] lemma numeral_bShift (x : V) :
    termBShift ℒₒᵣ (numeral x) = numeral x := by
  induction x using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp [Arithmetic.zero, qqFunc_absolute, qqFuncN_eq_qqFunc]
  case succ x ih =>
    rcases zero_or_succ x with (rfl | ⟨x, rfl⟩)
    · simp [Arithmetic.one, qqFunc_absolute, qqFuncN_eq_qqFunc]
    · simp [qqAdd, ih, Arithmetic.one, qqFunc_absolute, qqFuncN_eq_qqFunc]


-- @@ L818-818 verbatim
end numeral


-- @@ L820-820 verbatim
end Arithmetic


-- @@ L822-822 verbatim
end FFL.FirstOrder.Arithmetic.Bootstrapping
