/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.PerturbationTheory.WickContraction.ExtractEquiv

-- @@ L9-13 verbatim
/-!

# List of uncontracted elements of a Wick contraction

-/


-- @@ L15-15 verbatim
@[expose] public section


-- @@ L17-17 verbatim
open FieldSpecification

-- @@ L18-18 verbatim
variable {𝓕 : FieldSpecification}


-- @@ L20-20 verbatim
namespace WickContraction

-- @@ L21-21 verbatim
variable {n : ℕ} (c : WickContraction n)

-- @@ L22-22 verbatim
open Physlib.List

-- @@ L23-23 verbatim
open Physlib.Fin


-- @@ L25-29 verbatim
/-!

## Some properties of lists of fin

-/


-- @@ L31-33 verbatim
lemma fin_list_sorted_monotone_sorted {n m : ℕ} (l: List (Fin n)) (hl : l.Pairwise (· ≤ ·))
    (f : Fin n → Fin m) (hf : StrictMono f) : (List.map f l).Pairwise (· ≤ ·) :=
  hl.map f fun _ _ hab => hf.monotone hab


-- @@ L35-38 verbatim
lemma fin_list_sorted_succAboveEmb_sorted (l: List (Fin n)) (hl : l.Pairwise (· ≤ ·))
    (i : Fin n.succ) : ((List.map i.succAboveEmb l)).Pairwise (· ≤ ·) := by
  refine fin_list_sorted_monotone_sorted l hl i.succAboveEmb ?_
  simpa only [Fin.coe_succAboveEmb] using Fin.strictMono_succAbove i


-- @@ L40-50 verbatim
lemma fin_finset_sort_map_monotone {n m : ℕ} (a : Finset (Fin n)) (f : Fin n ↪ Fin m)
    (hf : StrictMono f) : (a.sort (· ≤ ·)).map f =
    ((a.map f).sort (· ≤ ·)) := by
  have h1 : ((a.sort (· ≤ ·)).map f).Pairwise (· ≤ ·) :=
    fin_list_sorted_monotone_sorted _ (a.pairwise_sort _) f hf
  have h2 : ((a.sort (· ≤ ·)).map f).Nodup := (a.sort_nodup _).map f.injective
  have h3 : ((a.sort (· ≤ ·)).map f).toFinset = a.map f := by
    ext a
    simp
  rw [← h3]
  exact ((List.toFinset_sort (· ≤ ·) h2).mpr h1).symm


-- @@ L52-82 verbatim
lemma fin_list_sorted_split :
    (l : List (Fin n)) → (hl : l.Pairwise (· ≤ ·)) → (i : ℕ) →
    l = l.filter (fun x => x.1 < i) ++ l.filter (fun x => i ≤ x.1)
  | [], _, _ => by simp
  | a :: l, hl, i => by
    simp only [List.pairwise_cons] at hl
    by_cases ha : a < i
    · conv_lhs => rw [fin_list_sorted_split l hl.2 i]
      rw [← List.cons_append]
      rw [List.filter_cons_of_pos, List.filter_cons_of_neg]
      simp only [decide_eq_true_eq, not_le, ha]
      simp [ha]
    · have hx : List.filter (fun x => decide (x.1 < i)) (a :: l) = [] := by
        simp only [ha, decide_false, Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg,
          List.filter_eq_nil_iff, decide_eq_true_eq, not_lt]
        intro b hb
        have hb' := hl.1 b hb
        omega
      simp only [hx, List.nil_append]
      rw [List.filter_cons_of_pos]
      simp only [List.cons.injEq, true_and]
      have hl' := fin_list_sorted_split l hl.2 i
      have hx : List.filter (fun x => decide (x.1 < i)) l = [] := by
        simp only [List.filter_eq_nil_iff, decide_eq_true_eq, not_lt]
        intro b hb
        have hb' := hl.1 b hb
        omega
      simp only [hx, List.nil_append] at hl'
      conv_lhs => rw [hl']
      simp only [decide_eq_true_eq]
      omega


-- @@ L84-106 verbatim
lemma fin_list_sorted_indexOf_filter_le_mem :
    (l : List (Fin n)) → (hl : l.Pairwise (· ≤ ·)) → (i : Fin n) →
    (hl : i ∈ l) →
    List.idxOf i (List.filter (fun x => decide (↑i ≤ ↑x)) l) = 0
  | [], _, _, _ => by simp
  | a :: l, hl, i, hi => by
    simp only [List.pairwise_cons] at hl
    by_cases ha : i ≤ a
    · simp only [ha, decide_true, List.filter_cons_of_pos]
      have ha : a = i := by
        simp only [List.mem_cons] at hi
        rcases hi with rfl | hi
        · rfl
        · exact Fin.le_antisymm (hl.1 i hi) ha
      subst ha
      simp
    · simp only [not_le] at ha
      rw [List.filter_cons_of_neg (by simpa using ha)]
      rw [fin_list_sorted_indexOf_filter_le_mem l hl.2]
      simp only [List.mem_cons] at hi
      rcases hi with hi | hi
      · omega
      · exact hi


-- @@ L108-117 verbatim
lemma fin_list_sorted_indexOf_mem :
    (l : List (Fin n)) → (hl : l.Pairwise (· ≤ ·)) → (i : Fin n) →
    (hi : i ∈ l) →
    l.idxOf i = (l.filter (fun x => x.1 < i.1)).length := by
  intro l hl i hi
  conv_lhs => rw [fin_list_sorted_split l hl i]
  rw [List.idxOf_append_of_notMem]
  · erw [fin_list_sorted_indexOf_filter_le_mem l hl i hi]
    simp
  · simp


-- @@ L119-144 verbatim
lemma orderedInsert_of_fin_list_sorted :
    (l : List (Fin n)) → (hl : l.Pairwise (· ≤ ·)) → (i : Fin n) →
    List.orderedInsert (· ≤ ·) i l = l.filter (fun x => x.1 < i.1) ++
    i :: l.filter (fun x => i.1 ≤ x.1)
  | [], _, _ => by simp
  | a :: l, hl, i => by
    simp only [List.pairwise_cons] at hl
    by_cases ha : i ≤ a
    · simp only [List.orderedInsert_cons, ha, ↓reduceIte, Fin.val_fin_lt, decide_eq_true_eq,
      not_lt, List.filter_cons_of_neg, Fin.val_fin_le, decide_true, List.filter_cons_of_pos]
      have h1 : List.filter (fun x => decide (↑x < ↑i)) l = [] := by
        simp only [List.filter_eq_nil_iff, decide_eq_true_eq, not_lt]
        intro a ha
        have ha' := hl.1 a ha
        omega
      have hl : l = List.filter (fun x => decide (i ≤ x)) l := by
        conv_lhs => rw [fin_list_sorted_split l hl.2 i]
        simp [h1]
      simp [← hl, h1]
    · simp only [List.orderedInsert_cons, ha, ↓reduceIte, Fin.val_fin_lt, Fin.val_fin_le,
      decide_false, Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg]
      rw [List.filter_cons_of_pos]
      rw [orderedInsert_of_fin_list_sorted l hl.2 i]
      simp only [Fin.val_fin_lt, Fin.val_fin_le, List.cons_append]
      simp only [decide_eq_true_eq]
      omega


-- @@ L146-161 verbatim
lemma orderedInsert_eq_insertIdx_of_fin_list_sorted (l : List (Fin n)) (hl : l.Pairwise (· ≤ ·))
    (i : Fin n) :
    List.orderedInsert (· ≤ ·) i l = l.insertIdx (l.filter (fun x => x.1 < i.1)).length i := by
  let n : Fin l.length.succ := ⟨(List.filter (fun x => decide (x < i)) l).length, by
    have h1 := l.length_filter_le (fun x => x.1 < i.1)
    simp only [Fin.val_fin_lt] at h1
    omega⟩
  simp only [Fin.val_fin_lt]
  conv_rhs => rw [insertIdx_eq_take_drop _ _ n]
  rw [orderedInsert_of_fin_list_sorted l hl i]
  congr
  all_goals
    conv_rhs =>
      rhs
      rw [fin_list_sorted_split l hl i]
    simp [n]


-- @@ L163-167 verbatim
/-!

## Uncontracted List

-/


-- @@ L169-171 verbatim
/-- Given a Wick contraction `c`, the ordered list of elements of `Fin n` which are not contracted,
  i.e. do not appear anywhere in `c.1`. -/
def uncontractedList : List (Fin n) := List.filter (fun x => x ∈ c.uncontracted) (List.finRange n)


-- @@ L173-175 verbatim
lemma uncontractedList_mem_iff (i : Fin n) :
    i ∈ c.uncontractedList ↔ i ∈ c.uncontracted := by
  simp [uncontractedList]


-- @@ L177-179 verbatim
@[simp]
lemma uncontractedList_empty : (empty (n := n)).uncontractedList = List.finRange n := by
  simp [uncontractedList]


-- @@ L181-182 verbatim
lemma nil_zero_uncontractedList : (empty (n := 0)).uncontractedList = [] := by
  simp [empty, uncontractedList]


-- @@ L184-187 verbatim
lemma congr_uncontractedList {n m : ℕ} (h : n = m) (c : WickContraction n) :
    ((congr h) c).uncontractedList = List.map (finCongr h) c.uncontractedList := by
  subst h
  simp [congr]


-- @@ L189-191 verbatim
lemma uncontractedList_get_mem_uncontracted (i : Fin c.uncontractedList.length) :
    c.uncontractedList.get i ∈ c.uncontracted := by
  simp [← uncontractedList_mem_iff]


-- @@ L193-197 verbatim
lemma uncontractedList_sorted : List.Pairwise (· ≤ ·) c.uncontractedList := by
  rw [uncontractedList]
  apply List.Pairwise.filter
  rw [← List.ofFn_id]
  exact List.pairwise_ofFn.mpr fun _ _ h => h.le


-- @@ L199-203 verbatim
lemma uncontractedList_sorted_lt : List.Pairwise (· < ·) c.uncontractedList := by
  rw [uncontractedList]
  apply List.Pairwise.filter
  rw [← List.ofFn_id]
  exact List.pairwise_ofFn.mpr fun ⦃i j⦄ a => a


-- @@ L205-207 verbatim
lemma uncontractedList_nodup : c.uncontractedList.Nodup := by
  rw [uncontractedList]
  exact (List.nodup_finRange n).filter _


-- @@ L209-211 verbatim
lemma uncontractedList_toFinset (c : WickContraction n) :
    c.uncontractedList.toFinset = c.uncontracted := by
  simp [uncontractedList]


-- @@ L213-218 verbatim
lemma uncontractedList_eq_sort (c : WickContraction n) :
    c.uncontractedList = c.uncontracted.sort (· ≤ ·) := by
  symm
  rw [← uncontractedList_toFinset]
  exact (List.toFinset_sort (α := Fin n) (· ≤ ·) (uncontractedList_nodup c)).mpr
    (uncontractedList_sorted c)


-- @@ L220-222 verbatim
lemma uncontractedList_length_eq_card (c : WickContraction n) :
    c.uncontractedList.length = c.uncontracted.card := by
  rw [uncontractedList_eq_sort, Finset.length_sort]


-- @@ L224-234 verbatim
lemma filter_uncontractedList (c : WickContraction n) (p : Fin n → Prop) [DecidablePred p] :
    (c.uncontractedList.filter p) = (c.uncontracted.filter p).sort (· ≤ ·) := by
  have h1 : (c.uncontractedList.filter p).Pairwise (· ≤ ·) := (uncontractedList_sorted c).filter _
  have h2 : (c.uncontractedList.filter p).Nodup := (uncontractedList_nodup c).filter _
  have h3 : (c.uncontractedList.filter p).toFinset = c.uncontracted.filter p := by
    ext a
    simp only [List.toFinset_filter, decide_eq_true_eq, Finset.mem_filter, List.mem_toFinset,
      and_congr_left_iff]
    rw [uncontractedList_mem_iff]
    simp
  rw [← (List.toFinset_sort (· ≤ ·) h2).mpr h1, h3]


-- @@ L236-240 verbatim
/-!

## uncontractedIndexEquiv

-/


-- @@ L242-255 verbatim
/-- The equivalence between the positions of `c.uncontractedList` i.e. elements of
  `Fin (c.uncontractedList).length` and the finite set `c.uncontracted` considered as a finite type.
-/
def uncontractedIndexEquiv (c : WickContraction n) :
    Fin (c.uncontractedList).length ≃ c.uncontracted where
  toFun i := ⟨c.uncontractedList.get i, c.uncontractedList_get_mem_uncontracted i⟩
  invFun i := ⟨List.idxOf i.1 c.uncontractedList,
    List.idxOf_lt_length_iff.mpr ((c.uncontractedList_mem_iff i.1).mpr i.2)⟩
  left_inv i := by
    ext
    exact List.get_idxOf (uncontractedList_nodup c) _
  right_inv i := by
    ext
    simp


-- @@ L257-260 verbatim
@[simp]
lemma uncontractedList_getElem_uncontractedIndexEquiv_symm (k : c.uncontracted) :
    c.uncontractedList[(c.uncontractedIndexEquiv.symm k).val] = k := by
  simp [uncontractedIndexEquiv]


-- @@ L262-268 verbatim
lemma uncontractedIndexEquiv_symm_eq_filter_length (k : c.uncontracted) :
    (c.uncontractedIndexEquiv.symm k).val =
    (List.filter (fun i => i < k.val) c.uncontractedList).length := by
  simp only [uncontractedIndexEquiv, List.get_eq_getElem, Equiv.coe_fn_symm_mk]
  rw [fin_list_sorted_indexOf_mem _ (uncontractedList_sorted c) _
    ((c.uncontractedList_mem_iff _).mpr k.2)]
  simp


-- @@ L270-277 verbatim
lemma take_uncontractedIndexEquiv_symm (k : c.uncontracted) :
    c.uncontractedList.take (c.uncontractedIndexEquiv.symm k).val =
    c.uncontractedList.filter (fun i => i < k.val) := by
  conv_lhs =>
    rhs
    rw [fin_list_sorted_split c.uncontractedList (uncontractedList_sorted c) k.val]
  rw [uncontractedIndexEquiv_symm_eq_filter_length]
  simp

-- @@ L278-282 verbatim
/-!

## Uncontracted List get

-/


-- @@ L284-290 verbatim
/-- Given a Wick Contraction `φsΛ` of a list `φs` of `𝓕.FieldOp`. The list
  `φsΛ.uncontractedListGet` of `𝓕.FieldOp` is defined as the list `φs` with
  all contracted positions removed, leaving the uncontracted `𝓕.FieldOp`.

  The notation `[φsΛ]ᵘᶜ` is used for `φsΛ.uncontractedListGet`. -/
def uncontractedListGet {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length) :
    List 𝓕.FieldOp := φsΛ.uncontractedList.map φs.get


-- @@ L292-293 verbatim
@[inherit_doc uncontractedListGet]
scoped[WickContraction] notation "[" φsΛ "]ᵘᶜ" => uncontractedListGet φsΛ


-- @@ L295-298 verbatim
@[simp]
lemma uncontractedListGet_empty {φs : List 𝓕.FieldOp} :
    (empty (n := φs.length)).uncontractedListGet = φs := by
  simp [uncontractedListGet]


-- @@ L300-304 verbatim
/-!

## uncontractedFieldOpEquiv

-/


-- @@ L306-312 verbatim
/-- The equivalence between the type `Option c.uncontracted` for `WickContraction φs.length` and
  `Option (Fin (c.uncontractedList.map φs.get).length)`, that is optional positions of
  `c.uncontractedList.map φs.get` induced by `uncontractedIndexEquiv`. -/
def uncontractedFieldOpEquiv (φs : List 𝓕.FieldOp) (φsΛ : WickContraction φs.length) :
    Option φsΛ.uncontracted ≃ Option (Fin [φsΛ]ᵘᶜ.length) :=
  Equiv.optionCongr (φsΛ.uncontractedIndexEquiv.symm.trans
    (finCongr (by simp [uncontractedListGet])))


-- @@ L314-317 verbatim
@[simp]
lemma uncontractedFieldOpEquiv_none (φs : List 𝓕.FieldOp) (φsΛ : WickContraction φs.length) :
    (uncontractedFieldOpEquiv φs φsΛ).toFun none = none := by
  simp [uncontractedFieldOpEquiv]


-- @@ L319-323 verbatim
lemma uncontractedFieldOpEquiv_list_sum [AddCommMonoid α] (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (f : Option (Fin [φsΛ]ᵘᶜ.length) → α) :
    ∑ (i : Option (Fin [φsΛ]ᵘᶜ.length)), f i =
    ∑ (i : Option φsΛ.uncontracted), f (φsΛ.uncontractedFieldOpEquiv φs i) := by
  rw [(φsΛ.uncontractedFieldOpEquiv φs).sum_comp]


-- @@ L325-329 verbatim
/-!

## uncontractedListEmd

-/


-- @@ L331-335 verbatim
/-- The embedding of `Fin [φsΛ]ᵘᶜ.length` into `Fin φs.length`. -/
def uncontractedListEmd {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length} :
    Fin [φsΛ]ᵘᶜ.length ↪ Fin φs.length := ((finCongr (by simp [uncontractedListGet])).trans
  φsΛ.uncontractedIndexEquiv).toEmbedding.trans
  (Function.Embedding.subtype fun x => x ∈ φsΛ.uncontracted)


-- @@ L337-341 verbatim
lemma uncontractedListEmd_congr {φs : List 𝓕.FieldOp} {φsΛ φsΛ' : WickContraction φs.length}
    (h : φsΛ = φsΛ') : φsΛ.uncontractedListEmd =
    (finCongr (by simp [h])).toEmbedding.trans φsΛ'.uncontractedListEmd := by
  subst h
  rfl


-- @@ L343-346 verbatim
lemma uncontractedListEmd_toFun_eq_get (φs : List 𝓕.FieldOp) (φsΛ : WickContraction φs.length) :
    (uncontractedListEmd (φsΛ := φsΛ)).toFun =
    φsΛ.uncontractedList.get ∘ (finCongr (by simp [uncontractedListGet])) := by
  rfl


-- @@ L348-353 verbatim
lemma uncontractedListEmd_strictMono {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    {i j : Fin [φsΛ]ᵘᶜ.length} (h : i < j) : uncontractedListEmd i < uncontractedListEmd j := by
  simp only [uncontractedListEmd, uncontractedIndexEquiv, List.get_eq_getElem,
    Equiv.trans_toEmbedding, Function.Embedding.trans_apply, Equiv.coe_toEmbedding, finCongr_apply,
    Equiv.coe_fn_mk, Fin.val_cast, Function.Embedding.coe_subtype]
  exact φsΛ.uncontractedList_sorted_lt.sortedLT.strictMono_get h


-- @@ L355-357 verbatim
lemma uncontractedListEmd_mem_uncontracted {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    (i : Fin [φsΛ]ᵘᶜ.length) : uncontractedListEmd i ∈ φsΛ.uncontracted := by
  simp [uncontractedListEmd]


-- @@ L359-370 verbatim
lemma uncontractedListEmd_surjective_mem_uncontracted {φs : List 𝓕.FieldOp}
    {φsΛ : WickContraction φs.length} (i : Fin φs.length) (hi : i ∈ φsΛ.uncontracted) :
    ∃ j, φsΛ.uncontractedListEmd j = i := by
  simp only [uncontractedListEmd, Equiv.trans_toEmbedding, Function.Embedding.trans_apply,
    Equiv.coe_toEmbedding, finCongr_apply, Function.Embedding.coe_subtype]
  have hj : ∃ j, φsΛ.uncontractedIndexEquiv j = ⟨i, hi⟩ :=
    φsΛ.uncontractedIndexEquiv.surjective ⟨i, hi⟩
  generalize_proofs h1
  obtain ⟨j, hj⟩ := hj
  obtain ⟨j', rfl⟩ := (finCongr h1).surjective j
  use j'
  erw [hj]


-- @@ L372-382 verbatim
@[simp]
lemma uncontractedListEmd_finset_disjoint_left {φs : List 𝓕.FieldOp}
    {φsΛ : WickContraction φs.length} (a : Finset (Fin [φsΛ]ᵘᶜ.length))
    (b : Finset (Fin φs.length)) (hb : b ∈ φsΛ.1) : Disjoint (a.map uncontractedListEmd) b := by
  rw [Finset.disjoint_left]
  intro x hx
  simp only [Finset.mem_map] at hx
  obtain ⟨x, hx, rfl⟩ := hx
  have h1 := uncontractedListEmd_mem_uncontracted x
  rw [mem_uncontracted_iff_not_contracted] at h1
  exact h1 b hb


-- @@ L384-391 verbatim
lemma uncontractedListEmd_finset_not_mem {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    (a : Finset (Fin [φsΛ]ᵘᶜ.length)) :
    a.map uncontractedListEmd ∉ φsΛ.1 := by
  by_contra hn
  have h1 := uncontractedListEmd_finset_disjoint_left a (a.map uncontractedListEmd) hn
  simp only [disjoint_self, Finset.bot_eq_empty, Finset.map_eq_empty] at h1
  have h2 := φsΛ.2.1 (a.map uncontractedListEmd) hn
  simp [h1] at h2


-- @@ L393-397 verbatim
@[simp]
lemma getElem_uncontractedListEmd {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    (k : Fin [φsΛ]ᵘᶜ.length) : φs[(uncontractedListEmd k).1] = [φsΛ]ᵘᶜ[k.1] := by
  simp only [uncontractedListGet, List.getElem_map, List.get_eq_getElem]
  rfl


-- @@ L399-403 verbatim
@[simp]
lemma uncontractedListEmd_empty {φs : List 𝓕.FieldOp} :
    (empty (n := φs.length)).uncontractedListEmd = (finCongr (by simp)).toEmbedding := by
  ext x
  simp [uncontractedListEmd, uncontractedIndexEquiv]


-- @@ L405-409 verbatim
/-!

## Uncontracted List for extractEquiv symm none

-/


-- @@ L411-413 verbatim
lemma uncontractedList_succAboveEmb_sorted (c : WickContraction n) (i : Fin n.succ) :
    ((List.map i.succAboveEmb c.uncontractedList)).Pairwise (· ≤ ·) := by
  exact fin_list_sorted_succAboveEmb_sorted _ (uncontractedList_sorted c) i


-- @@ L415-417 verbatim
lemma uncontractedList_succAboveEmb_nodup (c : WickContraction n) (i : Fin n.succ) :
    ((List.map i.succAboveEmb c.uncontractedList)).Nodup := by
  exact (uncontractedList_nodup c).map i.succAboveEmb.injective


-- @@ L419-423 verbatim
lemma uncontractedList_succAbove_orderedInsert_nodup (c : WickContraction n) (i : Fin n.succ) :
    (List.orderedInsert (· ≤ ·) i (List.map i.succAboveEmb c.uncontractedList)).Nodup := by
  apply (List.perm_orderedInsert (· ≤ ·) i _).symm.nodup
  simp only [Nat.succ_eq_add_one, List.nodup_cons, List.mem_map, not_exists, not_and]
  exact ⟨fun x _ => Fin.succAbove_ne i x, uncontractedList_succAboveEmb_nodup c i⟩


-- @@ L425-428 verbatim
lemma uncontractedList_succAbove_orderedInsert_sorted (c : WickContraction n) (i : Fin n.succ) :
    (List.orderedInsert (· ≤ ·) i
      (List.map i.succAboveEmb c.uncontractedList)).Pairwise (· ≤ ·) := by
  exact List.Pairwise.orderedInsert i _ (uncontractedList_succAboveEmb_sorted c i)


-- @@ L430-435 verbatim
lemma uncontractedList_succAbove_orderedInsert_toFinset (c : WickContraction n) (i : Fin n.succ) :
    (List.orderedInsert (· ≤ ·) i (List.map i.succAboveEmb c.uncontractedList)).toFinset =
    (Insert.insert i (Finset.map i.succAboveEmb c.uncontracted)) := by
  ext a
  rw [← uncontractedList_toFinset]
  simp


-- @@ L437-443 verbatim
lemma uncontractedList_succAbove_orderedInsert_eq_sort (c : WickContraction n) (i : Fin n.succ) :
    (List.orderedInsert (· ≤ ·) i (List.map i.succAboveEmb c.uncontractedList)) =
    (Insert.insert i (Finset.map i.succAboveEmb c.uncontracted)).sort (· ≤ ·) := by
  rw [← uncontractedList_succAbove_orderedInsert_toFinset]
  exact ((List.toFinset_sort (α := Fin n.succ) (· ≤ ·)
    (uncontractedList_succAbove_orderedInsert_nodup c i)).mpr
    (uncontractedList_succAbove_orderedInsert_sorted c i)).symm


-- @@ L445-449 verbatim
lemma uncontractedList_extractEquiv_symm_none (c : WickContraction n) (i : Fin n.succ) :
    ((extractEquiv i).symm ⟨c, none⟩).uncontractedList =
    List.orderedInsert (· ≤ ·) i (List.map i.succAboveEmb c.uncontractedList) := by
  rw [uncontractedList_eq_sort, extractEquiv_symm_none_uncontracted,
    uncontractedList_succAbove_orderedInsert_eq_sort]


-- @@ L451-455 verbatim
/-!

## Uncontracted List for extractEquiv symm some

-/


-- @@ L457-467 verbatim
lemma uncontractedList_succAboveEmb_eraseIdx_toFinset (c : WickContraction n) (i : Fin n.succ)
    (k : ℕ) (hk : k < c.uncontractedList.length) :
    ((List.map i.succAboveEmb c.uncontractedList).eraseIdx k).toFinset =
    (c.uncontracted.map i.succAboveEmb).erase (i.succAboveEmb c.uncontractedList[k]) := by
  ext a
  simp only [Fin.coe_succAboveEmb, List.mem_toFinset, Fin.succAboveEmb_apply, Finset.mem_erase,
    ne_eq, Finset.mem_map]
  rw [mem_eraseIdx_nodup _ _ _ (by simpa using hk)]
  · simp only [List.mem_map, List.getElem_map, ne_eq, uncontractedList_mem_iff]
    tauto
  · exact uncontractedList_succAboveEmb_nodup c i


-- @@ L469-472 verbatim
lemma uncontractedList_succAboveEmb_eraseIdx_sorted (c : WickContraction n) (i : Fin n.succ)
    (k: ℕ) : ((List.map i.succAboveEmb c.uncontractedList).eraseIdx k).Pairwise (· ≤ ·) := by
  apply Physlib.List.eraseIdx_sorted
  exact uncontractedList_succAboveEmb_sorted c i


-- @@ L474-476 verbatim
lemma uncontractedList_succAboveEmb_eraseIdx_nodup (c : WickContraction n) (i : Fin n.succ) (k: ℕ) :
    ((List.map i.succAboveEmb c.uncontractedList).eraseIdx k).Nodup := by
  exact (uncontractedList_succAboveEmb_nodup c i).eraseIdx k


-- @@ L478-486 verbatim
lemma uncontractedList_succAboveEmb_eraseIdx_eq_sort (c : WickContraction n) (i : Fin n.succ)
    (k : ℕ) (hk : k < c.uncontractedList.length) :
    ((List.map i.succAboveEmb c.uncontractedList).eraseIdx k) =
    ((c.uncontracted.map i.succAboveEmb).erase
    (i.succAboveEmb c.uncontractedList[k])).sort (· ≤ ·) := by
  rw [← uncontractedList_succAboveEmb_eraseIdx_toFinset]
  exact ((List.toFinset_sort (α := Fin n.succ) (· ≤ ·)
    (uncontractedList_succAboveEmb_eraseIdx_nodup c i k)).mpr
    (uncontractedList_succAboveEmb_eraseIdx_sorted c i k)).symm


-- @@ L488-499 verbatim
lemma uncontractedList_extractEquiv_symm_some (c : WickContraction n) (i : Fin n.succ)
    (k : c.uncontracted) : ((extractEquiv i).symm ⟨c, some k⟩).uncontractedList =
    ((c.uncontractedList).map i.succAboveEmb).eraseIdx (c.uncontractedIndexEquiv.symm k) := by
  rw [uncontractedList_eq_sort, uncontractedList_succAboveEmb_eraseIdx_eq_sort]
  swap
  simp only [Fin.is_lt]
  congr
  simp only [Nat.succ_eq_add_one, extractEquiv, Equiv.coe_fn_symm_mk,
    uncontractedList_getElem_uncontractedIndexEquiv_symm, Fin.succAboveEmb_apply]
  rw [insertAndContractNat_some_uncontracted]
  ext a
  simp


-- @@ L501-506 verbatim
lemma uncontractedList_succAboveEmb_toFinset (c : WickContraction n) (i : Fin n.succ) :
    (List.map i.succAboveEmb c.uncontractedList).toFinset =
    (Finset.map i.succAboveEmb c.uncontracted) := by
  ext a
  rw [← c.uncontractedList_toFinset]
  simp


-- @@ L508-512 verbatim
/-!

## uncontractedListOrderPos

-/


-- @@ L514-519 verbatim
/-- Given a Wick contraction `c : WickContraction n` and a `Fin n.succ`, the number of elements
  of `c.uncontractedList` which are less than `i`.
  Suppose we want to insert into `c` at position `i`, then this is the position we would
  need to insert into `c.uncontractedList`. -/
def uncontractedListOrderPos (c : WickContraction n) (i : Fin n.succ) : ℕ :=
  (List.filter (fun x => x.1 < i.1) c.uncontractedList).length


-- @@ L521-525 verbatim
@[simp]
lemma uncontractedListOrderPos_le_length (c : WickContraction n) (i : Fin n.succ) :
    c.uncontractedListOrderPos i ≤ c.uncontractedList.length := by
  simpa only [uncontractedListOrderPos] using
    c.uncontractedList.length_filter_le fun x => x.1 < i.1


-- @@ L527-531 verbatim
lemma take_uncontractedListOrderPos_eq_filter (c : WickContraction n) (i : Fin n.succ) :
    (c.uncontractedList.take (c.uncontractedListOrderPos i)) =
    c.uncontractedList.filter (fun x => x.1 < i.1) := by
  nth_rewrite 1 [fin_list_sorted_split c.uncontractedList (uncontractedList_sorted c) i]
  simp only [uncontractedListOrderPos, Nat.succ_eq_add_one, List.take_left']


-- @@ L533-537 verbatim
lemma take_uncontractedListOrderPos_eq_filter_sort (c : WickContraction n) (i : Fin n.succ) :
    (c.uncontractedList.take (c.uncontractedListOrderPos i)) =
    (c.uncontracted.filter (fun x => x.1 < i.1)).sort (· ≤ ·) := by
  rw [take_uncontractedListOrderPos_eq_filter]
  exact filter_uncontractedList c fun x => x.1 < i.1


-- @@ L539-556 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma orderedInsert_succAboveEmb_uncontractedList_eq_insertIdx (c : WickContraction n)
    (i : Fin n.succ) :
    (List.orderedInsert (· ≤ ·) i (List.map i.succAboveEmb c.uncontractedList)) =
    (List.map i.succAboveEmb c.uncontractedList).insertIdx (uncontractedListOrderPos c i) i := by
  rw [orderedInsert_eq_insertIdx_of_fin_list_sorted _ (uncontractedList_succAboveEmb_sorted c i)]
  congr 1
  simp only [Nat.succ_eq_add_one, Fin.val_fin_lt, Fin.coe_succAboveEmb, uncontractedListOrderPos]
  rw [List.filter_map]
  simp only [List.length_map]
  congr
  funext x
  simp only [Function.comp_apply, Fin.succAbove, decide_eq_decide]
  split
  · simp only [Fin.lt_def, Fin.val_castSucc]
  · rename_i h
    simp_all only [Fin.lt_def, Fin.val_castSucc, not_lt, Fin.val_succ]
    omega


-- @@ L558-558 verbatim
end WickContraction
