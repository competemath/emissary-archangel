/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import LeanPool.QuasiBorelSpaces.List.Encoding
public import LeanPool.QuasiBorelSpaces.MeasureTheory.List
public import LeanPool.QuasiBorelSpaces.Option
public import LeanPool.QuasiBorelSpaces.Nat
public import LeanPool.QuasiBorelSpaces.ProbabilityMeasure
import LeanPool.QuasiBorelSpaces.Basic
import LeanPool.QuasiBorelSpaces.Prop
import Mathlib.Tactic.Positivity.Finset


-- @@ L17-33 verbatim
/-!
# Lists over Quasi-Borel Spaces

This file defines the quasi-borel structure on lists and proves various operations
on lists are homomorphisms.

## Main definitions

* `QuasiBorelSpace (List A)`: the quasi-borel structure on lists
* `sequence`: converts a list of probability measures into a measure over lists

## Main results

* Basic list operations (`cons`, `tail`, `append`, `map`, etc.) are homomorphisms
* List query operations (`mem`, `elem`, `length`, `get`, etc.) are homomorphisms
* Set-like operations (`insert`, `union`, `erase`, `diff`) are homomorphisms
-/


-- @@ L35-35 verbatim
@[expose] public section


-- @@ L37-37 verbatim
variable {A B C : Type*} [QuasiBorelSpace A] [QuasiBorelSpace B] [QuasiBorelSpace C]


-- @@ L39-39 verbatim
namespace List.Encoding


-- @@ L41-41 verbatim
open QuasiBorelSpace


-- @@ L43-43 verbatim
/-! ## Encoding Homomorphisms -/


-- @@ L45-59 verbatim
/-- `cons` is a homomorphism. -/
@[fun_prop]
lemma isHom_cons : IsHom (fun x : A × List.Encoding A ↦ cons x.1 x.2) := by
  apply Sigma.isHom_distrib'
  apply Sigma.isHom_elim
  intro i
  dsimp only [cons]
  apply Sigma.isHom_mk'
  simp only [Pi.isHom_iff]
  intro j
  cases j using Fin.cases with
  | zero => simp only [Fin.cases_zero, Prod.isHom_fst]
  | succ i =>
    simp only [Fin.cases_succ]
    fun_prop


-- @@ L61-76 verbatim
/-- Folding over an encoded list is a homomorphism. -/
@[fun_prop]
lemma isHom_fold
      {cons : A → B → B} (hcons : IsHom fun (x, y) ↦ cons x y) (nil : B)
    : IsHom (foldr cons nil) := by
  apply Sigma.isHom_elim
  intro i
  induction i with
  | zero => simp only [foldr, isHom_const']
  | succ n ih =>
    simp only [foldr]
    apply Prod.isHom_of_uncurry
    · exact hcons
    · fun_prop
    · apply isHom_comp' ih
      fun_prop


-- @@ L78-78 verbatim
end List.Encoding


-- @@ L80-80 verbatim
namespace QuasiBorelSpace.List


-- @@ L82-82 verbatim
/-! ## QuasiBorel Structure -/


-- @@ L84-85 verbatim
/-- The `QuasiBorelSpace` structure on `List A`. -/
instance : QuasiBorelSpace (List A) := lift List.Encoding.encode


-- @@ L87-90 verbatim
/-- `encode` is a homomorphism. -/
@[simp, fun_prop]
lemma isHom_encode : IsHom (List.Encoding.encode (A := A)) := by
  apply isHom_of_lift


-- @@ L92-96 verbatim
/-- List `cons` is a homomorphism. -/
@[simp, fun_prop]
lemma isHom_cons : IsHom (fun x : A × List A ↦ x.1 :: x.2) := by
  simp only [isHom_to_lift, List.Encoding.encode_cons]
  fun_prop


-- @@ L98-103 verbatim
/-- `cons` is a homomorphism when composed with other homomorphisms. -/
lemma isHom_cons'
    {f : A → B} (hf : IsHom f)
    {g : A → List B} (hg : IsHom g)
    : IsHom (fun x ↦ f x :: g x) := by
  fun_prop


-- @@ L105-105 verbatim
/-! ## Basic List Operations -/


-- @@ L107-120 verbatim
/-- `foldr` is a homomorphism. -/
@[local fun_prop]
lemma isHom_foldr
    {cons : A → B → B} (hcons : IsHom fun (x, xs) ↦ cons x xs) (nil : B)
    : IsHom (List.foldr cons nil) := by
  have : List.foldr cons nil = fun xs ↦ List.Encoding.foldr cons nil (List.Encoding.encode xs) := by
    ext xs
    induction xs with
    | nil =>
      simp only [List.foldr_nil, List.Encoding.encode_nil, List.Encoding.foldr_nil]
    | cons head tail ih =>
      simp only [List.foldr_cons, ih, List.Encoding.encode_cons, List.Encoding.foldr_cons]
  rw [this]
  fun_prop


-- @@ L122-136 expanded
/-- `foldr` is a homomorphism when composed with other homomorphisms. -/
@[fun_prop]
lemma isHom_foldr' {cons : A → B → C → C} (hcons : IsHom fun (x, y, z) ↦ cons x y z) {nil : A → C}
    (hnil : IsHom nil) {f : A → List B} (hf : IsHom f) :
    IsHom (fun x ↦ List.foldr (cons x) (nil x) (f x)) :=
  by
  have {x} :
    List.foldr (cons x) (nil x) (f x) =
      List.foldr (β := QuasiBorelHom A C) (fun y k ↦ .mk (fun x ↦ cons x y (k x))) (.mk nil) (f x)
        x :=
    by
    induction f x with
    | nil => simp only [List.foldr_nil, QuasiBorelHom.coe_mk]
    | cons x xs ih => simp only [List.foldr_cons, ih, QuasiBorelHom.coe_mk]
  simp only [this]
  fun_prop


-- @@ L138-147 verbatim
/-- `map` is a homomorphism. -/
@[fun_prop]
lemma isHom_map
    {f : A → B → C} (hf : IsHom fun (x, y) ↦ f x y)
    {g : A → List B} (hg : IsHom g)
    : IsHom (fun x ↦ List.map (f x) (g x)) := by
  have {f : B → C} {xs : List B} : List.map f xs = List.foldr (fun x ↦ (f x :: ·)) [] xs := by
    simp only [List.foldr_cons_eq_append, List.append_nil]
  simp only [this]
  fun_prop


-- @@ L149-149 verbatim
/-! ## List Queries -/


-- @@ L151-174 expanded
/-- `getElem?` is a homomorphism. -/
@[fun_prop]
lemma isHom_getElem_opt {f : A → List B} (hf : IsHom f) {g : A → ℕ} (hg : IsHom g) :
    IsHom (fun x ↦ (f x)[g x]?) :=
  by
  have {x} :
    (f x)[g x]? =
      List.foldr (fun x k ↦ .mk fun i ↦ Nat.casesOn i (.some x) k)
        (.mk fun _ ↦ .none : QuasiBorelHom ℕ (Option B)) (f x) (g x) :=
    by
    generalize g x = n
    induction f x generalizing n with
    | nil => simp_all
    | cons head tail ih =>
      cases n with
      | zero => simp_all
      | succ n => simp_all
  simp only [this]
  fun_prop


-- @@ L176-183 verbatim
/-- `length` is a homomorphism. -/
@[fun_prop]
lemma isHom_length : IsHom (List.length : List A → ℕ) := by
  have : (List.length : List A → ℕ) = List.foldr (fun _ n ↦ n.succ) 0 := by
    funext xs
    simp_all
  rw [this]
  fun_prop


-- @@ L185-205 verbatim
/-- `get` is a homomorphism for valid indices. -/
@[fun_prop]
lemma isHom_get
    {f : A → List B} (hf : IsHom f)
    {g : A → ℕ} (hg : IsHom g)
    (h : ∀ x, g x < (f x).length)
    : IsHom (fun x ↦ (f x)[g x]'(h x)) := by
  by_cases hB : Nonempty B
  · have : Inhabited B := ⟨hB.some⟩
    have : (fun x ↦ (f x)[g x]'(h x)) = fun x ↦ ((f x)[g x]?).getD default := by
      simp_all
    simp only [this]
    exact QuasiBorelSpace.Option.isHom_getD (isHom_getElem_opt hf hg) (by fun_prop)
  · rw [isHom_def]
    intro p
    have {x} : f x = [] := by
      cases f x with
      | nil => rfl
      | cons head _ => exact absurd ⟨head⟩ hB
    simp only [this, List.length_nil, not_lt_zero] at h
    exact absurd (h (p 0)) (by simp)


-- @@ L207-219 verbatim
/-- `ofFn` is a homomorphism. -/
@[fun_prop]
lemma isHom_ofFn
    {n} {f : A → Fin n → B} (hf : IsHom fun (x, y) ↦ f x y)
    : IsHom (fun x ↦ List.ofFn (f x)) := by
  revert f
  induction n with
  | zero => intro; simp
  | succ n ih =>
      intro f hf
      have : IsHom (fun x ↦ List.ofFn fun i : Fin n ↦ f x (Fin.succ i)) :=
        ih (by fun_prop)
      simpa [List.ofFn_succ] using isHom_cons' (by fun_prop) this


-- @@ L221-236 verbatim
/-- `tail` is a homomorphism. -/
@[fun_prop]
lemma isHom_tail : IsHom (List.tail : List A → List A) := by
  have {xs : List A}
      : (xs, List.tail xs)
      = (List.foldr (fun x (ys, _) ↦ (x :: ys, ys)) ([], []) xs) := by
    induction xs with
    | nil => rfl
    | cons head tail ih =>
      simp only [Prod.ext_iff] at ih
      simp only [List.tail_cons, List.foldr_cons, ← ih]
  have : List.tail
       = fun xs : List A ↦ (List.foldr (fun x (ys, _) ↦ (x :: ys, ys)) ([], []) xs).2 := by
    grind
  rw [this]
  fun_prop


-- @@ L238-242 verbatim
/-- List `append` is a homomorphism. -/
@[fun_prop]
lemma isHom_append : IsHom (fun x : List A × List A ↦ x.1 ++ x.2) := by
  simp only [← List.foldr_cons_eq_append']
  fun_prop


-- @@ L244-244 verbatim
/-! ## List Membership and Set Operations -/


-- @@ L246-259 verbatim
/-- List membership is a homomorphism. -/
@[fun_prop]
lemma isHom_mem [IsHomDiagonal B]
    {f : A → B} (hf : IsHom f)
    {g : A → List B} (hg : IsHom g)
    : IsHom (fun x ↦ f x ∈ g x) := by
  have {x} {xs : List B}
      : x ∈ xs
      ↔ List.foldr (fun y p ↦ x = y ∨ p) False xs := by
    induction xs with
    | nil => simp only [List.not_mem_nil, List.foldr_nil]
    | cons head tail ih => simp only [List.mem_cons, ih, List.foldr_cons]
  simp only [this]
  fun_prop


-- @@ L261-267 verbatim
/-- `elem` is a homomorphism. -/
@[fun_prop]
lemma isHom_elem
    [DecidableEq B] [IsHomDiagonal B] {f : A → B} (hf : IsHom f) {g : A → List B} (hg : IsHom g)
    : IsHom (fun x ↦ List.elem (f x) (g x)) := by
  simp only [List.elem_eq_mem]
  fun_prop


-- @@ L269-276 verbatim
/-- `insert` is a homomorphism. -/
@[simp, fun_prop]
lemma isHom_insert
    [DecidableEq B] [IsHomDiagonal B]
    {f : A → B} (hf : IsHom f)
    {g : A → List B} (hg : IsHom g)
    : IsHom (fun x ↦ insert (f x) (g x)) := by
  apply Prop.isHom_ite <;> fun_prop


-- @@ L278-287 verbatim
/-- List `union` is a homomorphism. -/
@[fun_prop]
lemma isHom_union
    [DecidableEq A] [IsHomDiagonal A]
    : IsHom (fun x : List A × List A ↦ x.1.union x.2) := by
  unfold List.union
  apply isHom_foldr'
  · apply isHom_insert <;> fun_prop
  · fun_prop
  · fun_prop


-- @@ L289-312 verbatim
/-- `erase` is a homomorphism. -/
@[fun_prop]
lemma isHom_erase
    [BEq A] [LawfulBEq A] [IsHomDiagonal A]
    : IsHom (fun x : List A × A ↦ x.1.erase x.2) := by
  classical
  have {xs : List A} {x : A}
      : (xs.erase x, xs)
      = List.foldr
          (fun y (zs, ws) ↦ (if x = y then ws else y :: zs, y :: ws))
          ([], [])
          xs := by
    symm
    simp only [Prod.ext_iff]
    induction xs with
    | nil => simp only [List.erase_nil, List.foldr_nil, and_self]
    | cons head tail ih =>
      by_cases h : head = x
      · simp only [h, List.foldr_cons, ↓reduceIte, ih, List.erase_cons_head, and_self]
      · have h' : x ≠ head := by grind
        simp_all
  simp only [Prod.ext_iff] at this
  simp only [this.1]
  fun_prop


-- @@ L314-330 expanded
/-- List `diff` is a homomorphism. -/
@[fun_prop]
lemma isHom_diff [BEq A] [LawfulBEq A] [IsHomDiagonal A] :
    IsHom (fun x : List A × List A ↦ List.diff x.1 x.2) :=
  by
  have {xs ys : List A} :
    xs.diff ys =
      List.foldr (β := QuasiBorelHom (List A) (List A)) (fun x k ↦ .mk fun ys ↦ k (ys.erase x))
        (.mk id) ys xs :=
    by
    induction ys generalizing xs with
    | nil => simp only [List.diff_nil, List.foldr_nil, QuasiBorelHom.coe_mk, id_eq]
    | cons head tail ih => simp only [List.diff_cons, ih, List.foldr_cons, QuasiBorelHom.coe_mk]
  simp only [this]
  fun_prop


-- @@ L332-332 verbatim
/-! ## Measurable Structure -/


-- @@ L334-339 verbatim
/-- The `MeasurableQuasiBorelSpace` instance for `List A`. -/
instance
    [MeasurableSpace A] [MeasurableQuasiBorelSpace A]
    : MeasurableQuasiBorelSpace (List A) where
  isHom_iff_measurable φ := by
    simp only [isHom_to_lift, isHom_iff_measurable, MeasureTheory.List.measurable_to_encode]


-- @@ L341-341 verbatim
/-! ## Probability Measures on Lists -/


-- @@ L343-350 verbatim
/--
Converts a sequence of measures into a measure of sequences, where each element
is drawn from an element of the original sequence.
-/
@[simp]
noncomputable def sequence : List (ProbabilityMeasure A) → ProbabilityMeasure (List A)
  | [] => .unit []
  | μ :: μs => .bind (fun x ↦ .map (x :: ·) (sequence μs)) μ


-- @@ L352-356 verbatim
/-- Lifting integration to sequences. -/
@[simp]
noncomputable def lintegral (k : List A → ENNReal) : List (ProbabilityMeasure A) → ENNReal
  | [] => k []
  | μ :: μs => μ.lintegral fun x ↦ lintegral (fun xs ↦ k (x :: xs)) μs


-- @@ L358-370 verbatim
/-- Computing the integral of a sequence. -/
@[simp]
lemma lintegral_sequence
    (μs : List (ProbabilityMeasure A))
    (k : List A → ENNReal) (hk : IsHom k)
    : (sequence μs).lintegral k = lintegral k μs := by
  induction μs generalizing k with
  | nil => simp (disch := fun_prop) only [sequence, ProbabilityMeasure.lintegral_unit, lintegral]
  | cons head tail ih =>
    have : IsHom (fun x ↦ ProbabilityMeasure.map (x :: ·) (sequence tail)) := by fun_prop
    simp (disch := fun_prop) only [
      sequence, ProbabilityMeasure.lintegral_bind,
      ProbabilityMeasure.lintegral_map, ih, lintegral]


-- @@ L372-372 verbatim
/-! ## Point Separation -/


-- @@ L374-397 verbatim
/-- The `SeparatesPoints` instance for `List A`. -/
instance [SeparatesPoints A] : SeparatesPoints (List A) where
  separates xs ys h := by
    induction xs generalizing ys with
    | nil =>
      cases ys with
      | nil => rfl
      | cons head tail =>
        specialize h (List.foldr (fun _ _ ↦ False) True) (by fun_prop)
        simp only [List.foldr_nil, List.foldr_cons, imp_false, not_true_eq_false] at h
    | cons head tail ih =>
      cases ys with
      | nil =>
        specialize h (List.foldr (fun _ _ ↦ True) False) (by fun_prop)
        simp only [List.foldr_cons, List.foldr_nil, imp_false, not_true_eq_false] at h
      | cons head tail =>
        simp only [List.cons.injEq]
        apply And.intro
        · apply separatesPoints_def
          intro p hp hhead
          apply h (List.foldr (fun x _ ↦ p x) False) (by fun_prop) hhead
        · apply ih
          intro p hp htail
          apply h (p ∘ List.tail) (by fun_prop) htail


-- @@ L399-399 verbatim
end QuasiBorelSpace.List
