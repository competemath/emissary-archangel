/-
Copyright (c) 2026 Vincent Trélat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Trélat
-/
module

public import Mathlib.SetTheory.ZFC.Basic
import LeanPool.ZFLean.Basic
import Mathlib.Tactic.Attr.Core


-- @@ L12-26 verbatim
/-!
# Boolean algebra on `ZFSet`

This file defines the boolean algebra on `ZFSet` and the type of booleans `ZFBool`.
It defines the following operations:
- `not` : negation
- `and` : conjunction
- `or` : disjunction
- `true` : ZF true value
- `false` : ZF false value
- `𝔹` : set of ZF booleans
- `toBool` : conversion from `ZFBool` to `Bool`
- `ofBool` : conversion from `Bool` to `ZFBool`

-/


-- @@ L28-28 verbatim
@[expose] public section


-- @@ L30-30 verbatim
noncomputable section


-- @@ L32-32 verbatim
/-! ## Preliminary definitions -/


-- @@ L34-34 verbatim
namespace ZFSet


-- @@ L36-37 verbatim
/-- Symmetric difference of two sets, denoted by `Δ`. -/
def symmDiff (p q : ZFSet) : ZFSet := (p \ q) ∪ (q \ p)

-- @@ L38-39 verbatim
/-- Imported ZFLean declaration. -/
infix:70 " Δ " => symmDiff


-- @@ L41-43 expanded
@[simp]
theorem mem_symmDiff (x p q : ZFSet) : x ∈ symmDiff p q ↔ (x ∈ p ∧ x ∉ q) ∨ (x ∈ q ∧ x ∉ p) := by
  simp only [symmDiff, mem_union, mem_sdiff]


-- @@ L45-48 expanded
@[simp]
theorem symmDiff_empty (p : ZFSet) : symmDiff p ∅ = p :=
  by
  ext x
  simp only [mem_symmDiff, notMem_empty, not_false_eq_true, and_true, false_and, or_false]


-- @@ L50-52 expanded
theorem symmDiff_comm (p q : ZFSet) : symmDiff p q = symmDiff q p :=
  by
  ext x
  simpa only [mem_symmDiff] using Or.comm


-- @@ L54-57 expanded
@[simp]
theorem symmDiff_self (p : ZFSet) : symmDiff p p = ∅ :=
  by
  ext x
  simp only [mem_symmDiff, and_not_self, or_self, notMem_empty]


-- @@ L60-60 verbatim
/-! ## ZF Boolean Algebra -/


-- @@ L62-63 verbatim
/-- False value defined as the empty set. -/
abbrev zffalse : ZFSet := ∅

-- @@ L64-65 verbatim
/-- True value defined as the singleton containing the empty set. -/
abbrev zftrue : ZFSet := {zffalse}

-- @@ L66-67 verbatim
/-- Set of ZF booleans, defined as the set containing `zffalse` and `zftrue`. -/
abbrev 𝔹 : ZFSet := {zffalse,zftrue}

-- @@ L68-69 verbatim
/-- Type of ZF booleans. -/
abbrev ZFBool := { x // x ∈ 𝔹 }


-- @@ L71-74 verbatim
theorem zftrue_ne_zffalse : zftrue ≠ zffalse := by
  intro h
  rw [ZFSet.ext_iff, zffalse, zftrue] at h
  simp_all


-- @@ L76-76 verbatim
namespace ZFBool


-- @@ L78-79 verbatim
theorem zftrue_mem_𝔹 : zftrue ∈ 𝔹 := by
  simp_all


-- @@ L81-82 verbatim
theorem zffalse_mem_𝔹 : zffalse ∈ 𝔹 := by
  simp_all


-- @@ L84-88 verbatim
lemma _root_.ZFSet.ZFBool.𝔹.nonempty : ZFSet.𝔹 ≠ ∅ := by
  intro h
  rw [ZFSet.ext_iff] at h
  simp only [ZFSet.notMem_empty, iff_false] at h
  exact h ZFSet.zffalse ZFSet.ZFBool.zffalse_mem_𝔹


-- @@ L90-91 verbatim
/-- False value, lifted on `ZFBool`. -/
abbrev false : ZFBool := ⟨zffalse, zffalse_mem_𝔹⟩

-- @@ L92-93 verbatim
/-- True value, lifted on `ZFBool`. -/
abbrev true : ZFBool := ⟨zftrue, zftrue_mem_𝔹⟩

-- @@ L94-94 verbatim
instance BoolTop : Top ZFBool := ⟨true⟩

-- @@ L95-95 verbatim
instance BoolBot : Bot ZFBool := ⟨false⟩

-- @@ L96-96 verbatim
theorem top_eq_true : ⊤ = true := rfl

-- @@ L97-97 verbatim
@[simp] theorem bot_eq_false : ⊥ = false := rfl

-- @@ L98-102 verbatim
theorem true_ne_false : (⊤ : ZFBool) ≠ ⊥ := by
  intro h
  rw [top_eq_true, bot_eq_false] at h
  injection h with h
  nomatch zftrue_ne_zffalse h


-- @@ L104-105 verbatim
theorem mem_𝔹_iff (p : ZFSet) : p ∈ 𝔹 ↔ p = zffalse ∨ p = zftrue := by
  rw [mem_insert_iff, mem_singleton]


-- @@ L107-112 verbatim
@[simp]
theorem powerset_false : zffalse.powerset = zftrue := by
  unfold zftrue zffalse
  ext x
  simp only [mem_powerset, mem_singleton]
  exact ⟨subset_of_empty, (subset_of_subset_of_eq (fun _ a => a) ·)⟩


-- @@ L114-162 verbatim
/--
The enumeration of the powerset of `𝔹`.
-/
theorem powerset_𝔹_def :
  ZFSet.𝔹.powerset = {∅, {ZFSet.zffalse}, {ZFSet.zftrue}, {ZFSet.zffalse, ZFSet.zftrue}} := by
  ext1 x
  constructor
  · intro h
    rw [ZFSet.mem_powerset, ZFSet.𝔹] at h
    simp_rw [ZFSet.mem_insert_iff, ZFSet.mem_singleton]
    by_cases hx : x = ∅
    · left; exact hx
    · right
      by_cases hx' : ZFSet.zffalse ∈ x
      · rw [← or_assoc, or_comm, ← or_assoc]
        left
        by_cases hx'' : ZFSet.zftrue ∈ x
        · left
          ext1 s
          constructor
          · intro hs; exact h hs
          · intro hs; rcases (ZFSet.ZFBool.mem_𝔹_iff s).mp hs with rfl | rfl <;> assumption
        · right
          ext1 s
          constructor
          · intro hs
            rw [ZFSet.mem_singleton]
            rcases ZFSet.ZFBool.mem_𝔹_iff s |>.mp (h hs) with rfl | rfl <;> trivial
          · simp_all
      · by_cases hx'' : ZFSet.zftrue ∈ x
        · right
          left
          ext1 s
          constructor
          · intro hs
            rw [ZFSet.mem_singleton]
            rcases (ZFSet.ZFBool.mem_𝔹_iff s).mp (h hs) with rfl | rfl <;> trivial
          · simp_all
        · simp_rw [ZFSet.subset_def, ZFSet.ZFBool.mem_𝔹_iff] at h
          obtain ⟨w, hw⟩ := nonempty_exists_iff.mp hx
          rcases h hw with rfl | rfl <;> contradiction
  · intro hx
    simp_rw [ZFSet.mem_insert_iff, ZFSet.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> rw [ZFSet.mem_powerset]
    · exact ZFSet.empty_subset ZFSet.𝔹
    · intro _ hx
      simp_all
    · intro _ hx
      simp_all


-- @@ L164-170 expanded
/-- Boolean negation, defined as the symmetric difference with `true`. -/
protected abbrev not (p : ZFBool) : ZFBool :=
  ⟨symmDiff true p.1, by
    let ⟨p, hp⟩ := p
    rw [mem_𝔹_iff] at hp ⊢
    rcases hp with rfl | rfl
    · simp_all
    · simp_all⟩


-- @@ L172-185 verbatim
/-- Cases elimination for `ZFBool`. -/
@[cases_eliminator]
def casesOn {motive : ZFBool → Sort _}
  (p : ZFBool)
  (false : motive ⊥)
  (true : motive ⊤) : motive p := by
  obtain ⟨P, hP⟩ := p
  have := mem_𝔹_iff P |>.mp hP
  by_cases h : P = zffalse
  · subst h
    exact false
  · have := Or.resolve_left this h
    subst this
    exact true


-- @@ L187-198 verbatim
/-- Boolean conjunction, defined as set intersection. -/
protected abbrev and (p q : ZFBool) : ZFBool :=
  let ⟨P, hP⟩ := p
  let ⟨Q, hQ⟩ := q
  ⟨P ∩ Q, by
    rw [mem_𝔹_iff]
    rw [mem_𝔹_iff] at hP hQ
    cases hP <;> cases hQ <;> subst_eqs
    · exact Or.inl (by ext1; rw [mem_inter, and_self])
    · exact Or.inl (by ext1; simp only [mem_inter, notMem_empty, false_and])
    · exact Or.inl (by ext1; simp only [mem_inter, notMem_empty, and_false])
    · exact Or.inr (by ext1; simp only [mem_inter, and_self])⟩

-- @@ L199-200 verbatim
/-- Imported ZFLean declaration. -/
infixl:55 " ⋀ " => ZFBool.and

-- @@ L201-213 verbatim
/-- Imported ZFLean declaration. -/
protected abbrev or (p q : ZFBool) : ZFBool :=
  let ⟨P, hP⟩ := p
  let ⟨Q, hQ⟩ := q
  ⟨P ∪ Q,
    by
    rw [mem_𝔹_iff]
    rw [mem_𝔹_iff] at hP hQ
    cases hP <;> cases hQ <;> subst_eqs
    · exact Or.inl (by ext1; rw [mem_union, or_self])
    · exact Or.inr (by ext1; simp only [mem_union, notMem_empty, mem_singleton, false_or])
    · exact Or.inr (by ext1; simp only [mem_union, notMem_empty, or_false])
    · exact Or.inr (by ext1; simp only [mem_union, or_self])⟩

-- @@ L214-215 verbatim
/-- Imported ZFLean declaration. -/
infixl:55 " ⋁ " => ZFBool.or


-- @@ L217-217 verbatim
/-! ### Boolean algebra -/


-- @@ L219-225 verbatim
theorem not_true_eq_false : ZFBool.not ⊤ = ⊥ := by
  rw [Subtype.mk.injEq]
  ext1
  rw [mem_symmDiff]
  constructor
  · rintro (⟨l, r⟩ | ⟨l, r⟩) <;> nomatch r l
  · simp_all


-- @@ L227-237 verbatim
theorem not_false_eq_true : ZFBool.not ⊥ = ⊤ := by
  rw [Subtype.mk.injEq]
  ext1
  rw [mem_symmDiff]
  constructor
  · rintro (⟨l, r⟩ | ⟨l, r⟩)
    · exact l
    · nomatch notMem_empty _ l
  · intro h
    left
    exact ⟨h, notMem_empty _⟩


-- @@ L239-245 expanded
theorem and_comm (p q : ZFBool) : ZFBool.and p q = ZFBool.and q p :=
  by
  obtain ⟨P, hP⟩ := p
  obtain ⟨Q, hQ⟩ := q
  rw [Subtype.mk.injEq]
  ext1
  repeat rw [mem_inter]
  exact And.comm


-- @@ L247-254 expanded
theorem and_assoc (p q r : ZFBool) :
    ZFBool.and (ZFBool.and p q) r = ZFBool.and p (ZFBool.and q r) :=
  by
  obtain ⟨P, hP⟩ := p
  obtain ⟨Q, hQ⟩ := q
  obtain ⟨R, hR⟩ := r
  rw [Subtype.mk.injEq]
  ext1
  repeat rw [mem_inter]
  exact _root_.and_assoc


-- @@ L256-266 expanded
theorem and_true (p : ZFBool) : ZFBool.and p ⊤ = p :=
  by
  obtain ⟨P, hP⟩ := p
  rw [Subtype.mk.injEq]
  ext1
  rw [mem_inter]
  rw [mem_𝔹_iff] at hP
  rw [and_iff_left_iff_imp]
  intro h
  rcases hP with rfl | rfl
  · simp only [notMem_empty] at h
  · assumption


-- @@ L268-270 expanded
@[simp]
theorem and_false (p : ZFBool) : ZFBool.and p ⊥ = ⊥ := by simp_all


-- @@ L272-281 expanded
theorem and_iff (p q : ZFBool) : ZFBool.and p q = ⊤ ↔ p = ⊤ ∧ q = ⊤ :=
  by
  constructor
  · intro h
    cases q using casesOn with
    | false =>
      rw [and_false] at h
      nomatch true_ne_false h.symm
    | true => exact ⟨and_true p ▸ h, rfl⟩
  · rintro (⟨rfl, rfl⟩)
    rw [and_true]


-- @@ L283-284 expanded
theorem and_intro (p q : ZFBool) : p = ⊤ ∧ q = ⊤ → ZFBool.and p q = ⊤ :=
  and_iff p q |>.mpr


-- @@ L286-292 expanded
theorem or_comm (p q : ZFBool) : ZFBool.or p q = ZFBool.or q p :=
  by
  obtain ⟨P, hP⟩ := p
  obtain ⟨Q, hQ⟩ := q
  rw [Subtype.mk.injEq]
  ext1
  repeat rw [mem_union]
  exact Or.comm


-- @@ L294-301 expanded
theorem or_assoc (p q r : ZFBool) : ZFBool.or (ZFBool.or p q) r = ZFBool.or p (ZFBool.or q r) :=
  by
  obtain ⟨P, hP⟩ := p
  obtain ⟨Q, hQ⟩ := q
  obtain ⟨R, hR⟩ := r
  rw [Subtype.mk.injEq]
  ext1
  repeat rw [mem_union]
  exact _root_.or_assoc


-- @@ L303-311 expanded
theorem or_true (p : ZFBool) : ZFBool.or p ⊤ = ⊤ :=
  by
  obtain ⟨P, hP⟩ := p
  rw [Subtype.mk.injEq]
  ext1
  rw [mem_union]
  rw [mem_𝔹_iff] at hP
  cases hP <;> subst_eqs
  · simp only [notMem_empty, mem_singleton, false_or, top_eq_true]
  · exact or_iff_left_of_imp id


-- @@ L313-317 expanded
theorem or_false (p : ZFBool) : ZFBool.or p ⊥ = p :=
  by
  obtain ⟨P, hP⟩ := p
  rw [Subtype.mk.injEq]
  ext1
  simp_all


-- @@ L319-330 expanded
theorem or_iff (p q : ZFBool) : ZFBool.or p q = ⊤ ↔ p = ⊤ ∨ q = ⊤ :=
  by
  constructor
  · intro h
    cases p using casesOn with
    | false =>
      rw [or_comm, or_false] at h
      exact Or.inr h
    | true => exact Or.inl rfl
  · intro h
    rcases h with rfl | rfl
    · rw [or_comm, or_true]
    · rw [or_true]


-- @@ L332-333 expanded
theorem or_intro (p q : ZFBool) : p = ⊤ ∨ q = ⊤ → ZFBool.or p q = ⊤ :=
  or_iff p q |>.mpr


-- @@ L335-341 verbatim
open Classical in
/-- Conversion of `ZFBool` to `Lean.Bool`. -/
def toBool : ZFBool → Bool
  | ⟨b, hb⟩ =>
    if h : b = zftrue then Bool.true
    else if h' : b = zffalse then Bool.false
    else False.elim (by rcases (ZFBool.mem_𝔹_iff b |>.mp hb) <;> contradiction)


-- @@ L343-348 verbatim
theorem toBool_false : toBool ⊥ = Bool.false := by
  rw [toBool]
  split_ifs with h h'
  · nomatch zftrue_ne_zffalse h.symm
  · rfl
  · nomatch h'


-- @@ L350-355 verbatim
theorem toBool_true : toBool ⊤ = Bool.true := by
  rw [toBool]
  split_ifs with h h'
  · rfl
  · nomatch h rfl
  · nomatch h'


-- @@ L357-362 expanded
theorem toBool_and (p q : ZFBool) : (ZFBool.and p q).toBool = (p.toBool && q.toBool) :=
  by
  cases p <;> cases q
  · rw [and_false, toBool_false, Bool.false_and]
  · rw [and_true, toBool_true, toBool_false, Bool.false_and]
  · rw [and_false, toBool_true, toBool_false, Bool.and_false]
  · rw [and_true, toBool_true, Bool.true_and]


-- @@ L364-369 expanded
theorem toBool_or (p q : ZFBool) : (ZFBool.or p q).toBool = (p.toBool || q.toBool) :=
  by
  cases p <;> cases q
  · rw [or_false, toBool_false, Bool.false_or]
  · rw [or_true, toBool_true, toBool_false, Bool.or_true]
  · rw [or_false, toBool_true, toBool_false, Bool.true_or]
  · rw [or_true, toBool_true, Bool.true_or]


-- @@ L371-376 verbatim
theorem toBool_not (p : ZFBool) : toBool p.not = ¬ p.toBool := by
  cases p
  · rw [not_false_eq_true, toBool_true, toBool_false, Bool.false_eq_true, Bool.coe_sort_true]
    exact _root_.not_false_eq_true.symm
  · rw [not_true_eq_false, toBool_false, toBool_true, Bool.coe_false]
    exact eq_false (fun h => h rfl) |>.symm


-- @@ L378-385 verbatim
theorem not_top_iff_bot {P : ZFBool} : P ≠ ⊤ ↔ P = ⊥ := by
  constructor
  · intro
    cases P <;> trivial
  · intro _ h
    subst P
    injections h
    nomatch zftrue_ne_zffalse h.symm


-- @@ L387-394 verbatim
theorem not_bot_iff_top {P : ZFBool} : P ≠ ⊥ ↔ P = ⊤ := by
  constructor
  · intro
    cases P <;> trivial
  · intro _ h
    subst P
    injections h
    nomatch zftrue_ne_zffalse h


-- @@ L396-399 verbatim
/-- Conversion of `Lean.Bool` to `ZFBool` -/
def ofBool : Bool → ZFBool
  | .true  => ⟨zftrue, ZFBool.zftrue_mem_𝔹⟩
  | .false => ⟨zffalse, ZFBool.zffalse_mem_𝔹⟩


-- @@ L401-402 verbatim
theorem mem_ofBool_𝔹 (b : Bool) : (ofBool b).val ∈ 𝔹 := by
  simp_all


-- @@ L404-406 verbatim
theorem sub_ofBool_singleton_𝔹 (b : Bool) : {(ofBool b).val} ⊆ 𝔹 := by
  intro
  simp_all


-- @@ L408-415 verbatim
theorem to_Bool_ofBool (b : Bool) : ZFBool.toBool (ofBool b) = b := by
  cases b <;> rw [ofBool, ZFBool.toBool]
  · split_ifs with h
    · nomatch zftrue_ne_zffalse.symm h
    · rfl
    · generalize_proofs
      contradiction
  · simp_all


-- @@ L417-420 verbatim
theorem of_Bool_toBool (b : ZFBool) : ofBool b.toBool = b := by
  obtain ⟨b, hb⟩ := b
  rw [ZFBool.toBool, ofBool.eq_def]
  split_ifs with h <;> (first | subst b | contradiction) <;> trivial


-- @@ L422-436 verbatim
theorem ofBool_decide_eq_true_iff {P : Prop} [Decidable P] : ofBool (decide P) = ⊤ ↔ P := by
  constructor
  · intro h
    cases hP : decide P with
    | false =>
      rw [hP] at h
      unfold ofBool at h
      injection h with h
      nomatch zftrue_ne_zffalse h.symm
    | true => exact decide_eq_true_eq.mp hP
  · intro h
    cases hP : decide P with
    | false =>
      simp_all
    | true => rfl


-- @@ L438-452 verbatim
theorem ofBool_decide_eq_false_iff {P : Prop} [Decidable P] : ofBool (decide P) = ⊥ ↔ ¬P := by
  constructor
  · intro h
    cases hP : decide P with
    | false => exact decide_eq_false_iff_not.mp hP
    | true =>
      rw [hP] at h
      unfold ofBool at h
      injection h with h
      nomatch zftrue_ne_zffalse h
  · intro h
    cases hP : decide P with
    | false => rfl
    | true =>
      simp_all


-- @@ L454-459 verbatim
/-- The equivalence between ZF booleans and Lean booleans. -/
def instEquivBool : ZFBool ≃ Bool where
  toFun := toBool
  invFun := ofBool
  left_inv := of_Bool_toBool
  right_inv := to_Bool_ofBool


-- @@ L461-461 verbatim
instance : Coe Bool ZFBool := ⟨ofBool⟩

-- @@ L462-462 verbatim
instance : Coe ZFBool Bool := ⟨toBool⟩


-- @@ L464-464 verbatim
end ZFBool




-- @@ L468-468 verbatim
namespace ZFBool


-- @@ L470-471 expanded
theorem and_coe (p q : ZFBool) : ZFBool.and p q = ((p : Bool) && (q : Bool)) := by
  rw [← toBool_and, of_Bool_toBool]


-- @@ L472-473 expanded
theorem or_coe (p q : ZFBool) : ZFBool.or p q = ((p : Bool) || (q : Bool)) := by
  rw [← toBool_or, of_Bool_toBool]


-- @@ L474-475 verbatim
theorem not_coe (p : ZFBool) : ZFBool.not p = ¬(p : Bool) := by
  rw [← toBool_not]


-- @@ L477-480 expanded
theorem and_or_distrib_left (p q r : ZFBool) :
    ZFBool.and p (ZFBool.or q r) = ZFBool.or (ZFBool.and p q) (ZFBool.and p r) :=
  by
  rw [and_coe, or_coe, and_coe, and_coe, or_coe]
  iterate 3 rw [to_Bool_ofBool]
  rw [Bool.and_or_distrib_left]


-- @@ L482-482 verbatim
end ZFBool


-- @@ L484-484 verbatim
end ZFSet


-- @@ L486-486 verbatim
end
