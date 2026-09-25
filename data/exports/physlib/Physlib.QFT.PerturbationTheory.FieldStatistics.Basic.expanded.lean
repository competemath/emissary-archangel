/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Mathematics.List.InsertIdx
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Data.List.Sort

-- @@ L14-20 verbatim
/-!

# Field statistics

Basic properties related to whether a field, or list of fields, is bosonic or fermionic.

-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-29 verbatim
/-- The type `FieldStatistic` is the type containing two elements `bosonic` and `fermionic`.
  This type is used to specify if a field or operator obeys bosonic or fermionic statistics. -/
inductive FieldStatistic : Type where
  | bosonic : FieldStatistic
  | fermionic : FieldStatistic
deriving DecidableEq


-- @@ L31-31 verbatim
namespace FieldStatistic


-- @@ L33-33 verbatim
variable {𝓕 : Type}


-- @@ L35-62 verbatim
/-- The type `FieldStatistic` carries an instance of a commutative group in which
- `bosonic * bosonic = bosonic`
- `bosonic * fermionic = fermionic`
- `fermionic * bosonic = fermionic`
- `fermionic * fermionic = bosonic`

This group is isomorphic to `ℤ₂`. -/
@[simp]
instance : CommGroup FieldStatistic where
  one := bosonic
  mul a b :=
    match a, b with
    | bosonic, bosonic => bosonic
    | bosonic, fermionic => fermionic
    | fermionic, bosonic => fermionic
    | fermionic, fermionic => bosonic
  inv a := a
  mul_assoc a b c := by
    cases a <;> cases b <;> cases c <;>
    dsimp [HMul.hMul]
  one_mul a := by
    cases a <;> dsimp [HMul.hMul]
  mul_one a := by
    cases a <;> dsimp [HMul.hMul]
  inv_mul_cancel a := by
    cases a <;> dsimp only [HMul.hMul, Nat.succ_eq_add_one] <;> rfl
  mul_comm a b := by
    cases a <;> cases b <;> rfl


-- @@ L64-65 verbatim
@[simp]
lemma bosonic_mul_bosonic : bosonic * bosonic = bosonic := rfl


-- @@ L67-68 verbatim
@[simp]
lemma bosonic_mul_fermionic : bosonic * fermionic = fermionic := rfl


-- @@ L70-71 verbatim
@[simp]
lemma fermionic_mul_bosonic : fermionic * bosonic = fermionic := rfl


-- @@ L73-74 verbatim
@[simp]
lemma fermionic_mul_fermionic : fermionic * fermionic = bosonic := rfl


-- @@ L76-78 verbatim
@[simp]
lemma mul_bosonic (a : FieldStatistic) : a * bosonic = a := by
  cases a <;> rfl


-- @@ L80-82 verbatim
@[simp]
lemma mul_self (a : FieldStatistic) : a * a = 1 := by
  cases a <;> rfl


-- @@ L84-92 verbatim
/-- Field statics form a finite type. -/
instance : Fintype FieldStatistic where
  elems := {bosonic, fermionic}
  complete := by
    intro c
    cases c
    · exact Finset.mem_insert_self bosonic {fermionic}
    · refine Finset.insert_eq_self.mp ?_
      exact rfl


-- @@ L94-97 verbatim
@[simp]
lemma fermionic_not_eq_bonsic : ¬ fermionic = bosonic := by
  intro h
  exact FieldStatistic.noConfusion h


-- @@ L99-100 verbatim
lemma bonsic_eq_fermionic_false : bosonic = fermionic ↔ false := by
  simp only [reduceCtorEq, Bool.false_eq_true]


-- @@ L102-106 verbatim
@[simp]
lemma neq_fermionic_iff_eq_bosonic (a : FieldStatistic) : ¬ a = fermionic ↔ a = bosonic := by
  fin_cases a
  · simp
  · simp


-- @@ L108-112 verbatim
@[simp]
lemma neq_bosonic_iff_eq_fermionic (a : FieldStatistic) : ¬ a = bosonic ↔ a = fermionic := by
  fin_cases a
  · simp
  · simp


-- @@ L114-118 verbatim
@[simp]
lemma bosonic_ne_iff_fermionic_eq (a : FieldStatistic) : ¬ bosonic = a ↔ fermionic = a := by
  fin_cases a
  · simp
  · simp


-- @@ L120-124 verbatim
@[simp]
lemma fermionic_ne_iff_bosonic_eq (a : FieldStatistic) : ¬ fermionic = a ↔ bosonic = a := by
  fin_cases a
  · simp
  · simp


-- @@ L126-128 verbatim
lemma eq_self_if_eq_bosonic {a : FieldStatistic} :
    (if a = bosonic then bosonic else fermionic) = a := by
  fin_cases a <;> rfl


-- @@ L130-132 verbatim
lemma eq_self_if_bosonic_eq {a : FieldStatistic} :
    (if bosonic = a then bosonic else fermionic) = a := by
  fin_cases a <;> rfl


-- @@ L134-135 verbatim
lemma mul_eq_one_iff (a b : FieldStatistic) : a * b = 1 ↔ a = b := by
  fin_cases a <;> fin_cases b <;> simp


-- @@ L137-138 verbatim
lemma one_eq_mul_iff (a b : FieldStatistic) : 1 = a * b ↔ a = b := by
  fin_cases a <;> fin_cases b <;> simp


-- @@ L140-144 verbatim
lemma mul_eq_iff_eq_mul (a b c : FieldStatistic) : a * b = c ↔ a = b * c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp only [bosonic_mul_fermionic, fermionic_not_eq_bonsic, mul_self,
      reduceCtorEq, fermionic_mul_bosonic, true_iff, iff_true]
  all_goals rfl


-- @@ L146-150 verbatim
lemma mul_eq_iff_eq_mul' (a b c : FieldStatistic) : a * b = c ↔ b = a * c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp only [bosonic_mul_fermionic, fermionic_not_eq_bonsic, mul_self,
      reduceCtorEq, fermionic_mul_bosonic, true_iff, iff_true]
  all_goals rfl


-- @@ L152-156 verbatim
/-- The field statistics of a list of fields is fermionic if there is an odd number of fermions,
  otherwise it is bosonic. -/
def ofList (s : 𝓕 → FieldStatistic) : (φs : List 𝓕) → FieldStatistic
  | [] => bosonic
  | φ :: φs => if s φ = ofList s φs then bosonic else fermionic


-- @@ L158-162 verbatim
lemma ofList_cons_eq_mul (s : 𝓕 → FieldStatistic) (φ : 𝓕) (φs : List 𝓕) :
    ofList s (φ :: φs) = s φ * ofList s φs := by
  have ha (a b : FieldStatistic) : (if a = b then bosonic else fermionic) = a * b := by
    fin_cases a <;> fin_cases b <;> rfl
  exact ha (s φ) (ofList s φs)


-- @@ L164-168 verbatim
lemma ofList_eq_prod (s : 𝓕 → FieldStatistic) : (φs : List 𝓕) →
    ofList s φs = (List.map s φs).prod
  | [] => rfl
  | φ :: φs => by
    rw [ofList_cons_eq_mul, List.map_cons, List.prod_cons, ofList_eq_prod]


-- @@ L170-174 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma ofList_singleton (s : 𝓕 → FieldStatistic) (φ : 𝓕) : ofList s [φ] = s φ := by
  simp only [ofList]
  rw [eq_self_if_eq_bosonic]


-- @@ L176-178 verbatim
@[simp]
lemma ofList_freeMonoid (s : 𝓕 → FieldStatistic) (φ : 𝓕) : ofList s (FreeMonoid.of φ) = s φ :=
  ofList_singleton s φ


-- @@ L180-181 verbatim
@[simp]
lemma ofList_empty (s : 𝓕 → FieldStatistic) : ofList s [] = bosonic := rfl


-- @@ L183-195 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma ofList_append (s : 𝓕 → FieldStatistic) (φs φs' : List 𝓕) :
    ofList s (φs ++ φs') = if ofList s φs = ofList s φs' then bosonic else fermionic := by
  induction φs with
  | nil =>
    simp only [List.nil_append, ofList_empty, eq_self_if_bosonic_eq]
  | cons a l ih =>
    have hab (a b c : FieldStatistic) :
        (if a = (if b = c then bosonic else fermionic) then bosonic else fermionic) =
        if (if a = b then bosonic else fermionic) = c then bosonic else fermionic := by
      fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl
    simp only [List.cons_append, ofList, ih, hab]


-- @@ L197-202 verbatim
lemma ofList_append_eq_mul (s : 𝓕 → FieldStatistic) (φs φs' : List 𝓕) :
    ofList s (φs ++ φs') = ofList s φs * ofList s φs' := by
  rw [ofList_append]
  have ha (a b : FieldStatistic) : (if a = b then bosonic else fermionic) = a * b := by
    fin_cases a <;> fin_cases b <;> rfl
  exact ha _ _


-- @@ L204-207 verbatim
lemma ofList_perm (s : 𝓕 → FieldStatistic) {l l' : List 𝓕} (h : l.Perm l') :
    ofList s l = ofList s l' := by
  rw [ofList_eq_prod, ofList_eq_prod]
  exact List.Perm.prod_eq (List.Perm.map s h)


-- @@ L209-211 verbatim
lemma ofList_orderedInsert (s : 𝓕 → FieldStatistic) (le1 : 𝓕 → 𝓕 → Prop) [DecidableRel le1]
    (φs : List 𝓕) (φ : 𝓕) : ofList s (List.orderedInsert le1 φ φs) = ofList s (φ :: φs) :=
  ofList_perm s (List.perm_orderedInsert le1 φ φs)


-- @@ L213-216 verbatim
@[simp]
lemma ofList_insertionSort (s : 𝓕 → FieldStatistic) (le1 : 𝓕 → 𝓕 → Prop) [DecidableRel le1]
    (φs : List 𝓕) : ofList s (List.insertionSort le1 φs) = ofList s φs :=
  ofList_perm s (List.perm_insertionSort le1 φs)


-- @@ L218-248 verbatim
lemma ofList_map_eq_finset_prod (s : 𝓕 → FieldStatistic) :
    (φs : List 𝓕) → (l : List (Fin φs.length)) → (hl : l.Nodup) →
    ofList s (l.map φs.get) = ∏ (i : Fin φs.length), if i ∈ l then s φs[i] else 1
  | [], [], _ => rfl
  | [], i :: l, hl => Fin.elim0 i
  | φ :: φs, [], hl => by
    simp only [List.length_cons, List.map_nil, ofList_empty, List.not_mem_nil, ↓reduceIte,
      Finset.prod_const_one]
    rfl
  | φ :: φs, i :: l, hl => by
    simp only [List.length_cons, List.map_cons, List.get_eq_getElem, List.mem_cons, Fin.getElem_fin]
    rw [ofList_cons_eq_mul]
    rw [ofList_map_eq_finset_prod s (φ :: φs) l]
    have h1 : s (φ :: φs)[↑i] = ∏ (j : Fin (φ :: φs).length),
      if j = i then s (φ :: φs)[↑i] else 1 := by
      rw [Fintype.prod_ite_eq']
    erw [h1]
    rw [← Finset.prod_mul_distrib]
    congr
    funext a
    simp only [List.length_cons, mul_ite, ite_mul, one_mul, mul_one]
    by_cases ha : a = i
    · simp only [ha, ↓reduceIte, mul_self, true_or]
      rw [if_neg]
      rfl
      simp only [List.length_cons, List.nodup_cons] at hl
      exact hl.1
    · simp only [ha, ↓reduceIte, false_or]
      rfl
    simp only [List.length_cons, List.nodup_cons] at hl
    exact hl.2


-- @@ L250-252 verbatim
lemma ofList_pair (s : 𝓕 → FieldStatistic) (φ1 φ2 : 𝓕) :
    ofList s [φ1, φ2] = s φ1 * s φ2 := by
  rw [ofList_cons_eq_mul, ofList_singleton]


-- @@ L254-258 verbatim
/-!

## ofList and take

-/


-- @@ L260-260 verbatim
section ofListTake

-- @@ L261-261 verbatim
open Physlib.List

-- @@ L262-262 verbatim
variable (q : 𝓕 → FieldStatistic)

-- @@ L263-266 verbatim
lemma ofList_take_insert (n : ℕ) (φ : 𝓕) (φs : List 𝓕) :
    ofList q (List.take n φs) = ofList q (List.take n (List.insertIdx φs n φ)) := by
  congr 1
  rw [take_insert_same]


-- @@ L268-271 verbatim
lemma ofList_take_eraseIdx (n : ℕ) (φs : List 𝓕) :
    ofList q (List.take n (φs.eraseIdx n)) = ofList q (List.take n φs) := by
  congr 1
  rw [take_eraseIdx_same]


-- @@ L273-276 verbatim
lemma ofList_take_zero (φs : List 𝓕) :
    ofList q (List.take 0 φs) = 1 := by
  simp only [List.take_zero, ofList_empty]
  rfl


-- @@ L278-281 verbatim
lemma ofList_take_succ_cons (n : ℕ) (φ1 : 𝓕) (φs : List 𝓕) :
    ofList q ((φ1 :: φs).take (n + 1)) = q φ1 * ofList q (φs.take n) := by
  simp only [List.take_succ_cons]
  rw [ofList_cons_eq_mul]


-- @@ L283-285 verbatim
lemma ofList_take_insertIdx_gt (n m : ℕ) (φ1 : 𝓕) (φs : List 𝓕) (hn : n < m) :
    ofList q ((List.insertIdx φs m φ1).take n) = ofList q (φs.take n) := by
  rw [take_insert_gt φ1 n m hn φs]


-- @@ L287-293 verbatim
lemma ofList_insert_lt_eq (n m : ℕ) (φ1 : 𝓕) (φs : List 𝓕) (hn : m ≤ n)
    (hm : m ≤ φs.length) :
    ofList q ((List.insertIdx φs m φ1).take (n + 1)) =
    ofList q ((φ1 :: φs).take (n + 1)) := by
  apply ofList_perm
  simp only [List.take_succ_cons]
  refine take_insert_let φ1 n m hn φs hm


-- @@ L295-299 verbatim
lemma ofList_take_insertIdx_le (n m : ℕ) (φ1 : 𝓕) (φs : List 𝓕) (hn : m ≤ n) (hm : m ≤ φs.length) :
    ofList q ((List.insertIdx φs m φ1).take (n + 1)) = q φ1 * ofList q (φs.take n) := by
  rw [ofList_insert_lt_eq, ofList_take_succ_cons]
  · exact hn
  · exact hm


-- @@ L301-317 verbatim
/-- The instance of an additive monoid on `FieldStatistic`. -/
instance : AddMonoid FieldStatistic where
  zero := bosonic
  add a b := a * b
  nsmul n a := ∏ (i : Fin n), a
  zero_add a := by
    cases a <;> rfl
  add_zero a := by
    cases a <;> rfl
  add_assoc a b c := by
    cases a <;> cases b <;> cases c <;> rfl
  nsmul_zero a := by
    show (∏ _i : Fin 0, a) = (1 : FieldStatistic)
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_zero]
  nsmul_succ a n := by
    show (∏ _i : Fin (a + 1), n) = (∏ _i : Fin a, n) * n
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_succ]


-- @@ L319-320 verbatim
@[simp]
lemma add_eq_mul (a b : FieldStatistic) : a + b = a * b := rfl


-- @@ L322-322 verbatim
end ofListTake

-- @@ L323-323 verbatim
end FieldStatistic
