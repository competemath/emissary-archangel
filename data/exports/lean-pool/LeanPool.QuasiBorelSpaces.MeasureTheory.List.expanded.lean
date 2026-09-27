/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import LeanPool.QuasiBorelSpaces.List.Encoding
import LeanPool.QuasiBorelSpaces.MeasureTheory.Sigma


-- @@ L12-16 verbatim
/-!
# LeanPool.QuasiBorelSpaces.MeasureTheory.List

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.MeasureTheory.List`.
-/


-- @@ L18-18 verbatim
@[expose] public section



-- @@ L21-24 verbatim
variable
  {A : Type*} [MeasurableSpace A]
  {B : Type*} [MeasurableSpace B]
  {C : Type*} [MeasurableSpace C]


-- @@ L26-26 verbatim
namespace List.Encoding


-- @@ L28-28 verbatim
open MeasureTheory


-- @@ L30-45 verbatim
@[fun_prop, simp]
lemma measurable_cons : Measurable (fun x : A × Encoding A ↦ cons x.1 x.2) := by
  apply Sigma.measurable_distrib'
  apply Sigma.measurable_elim
  intro n
  simp only [cons]
  apply Sigma.measurable_mk'
  apply Measurable.of_eval
  rintro ⟨i, _⟩
  cases i with
  | zero =>
    simp only [Fin.zero_eta, Fin.cases_zero]
    fun_prop
  | succ n =>
    simp only [Fin.cases_succ']
    fun_prop


-- @@ L47-73 verbatim
@[fun_prop]
lemma measurable_fold
      {cons : A → B → B} (hcons : Measurable fun (x, y) ↦ cons x y) (nil : B)
    : Measurable (Encoding.foldr cons nil) := by
  apply Sigma.measurable_elim
  intro i
  induction i with
  | zero =>
    have {x : Fin 0 → A} : ⟨0, x⟩ = Encoding.nil := by
      simp only [Encoding.nil, Sigma.mk.injEq, heq_eq_eq, true_and]
      ext i
      apply Fin.elim0 i
    simp only [this, foldr_nil, measurable_const]
  | succ n ih =>
    have {x : Fin (n + 1) → A} : ⟨n + 1, x⟩ = Encoding.cons (x 0) ⟨n, x ∘ Fin.succ⟩ := by
      simp only [Encoding.cons, Sigma.mk.injEq, heq_eq_eq, true_and]
      ext i
      cases i using Fin.cases <;> rfl
    simp only [this, foldr_cons]
    apply Measurable.fun_comp
      (g := fun x : _ × _ ↦ cons x.1 x.2)
      (f := fun x ↦ (_, _))
    · assumption
    · apply Measurable.prodMk
      · fun_prop
      · apply Measurable.fun_comp ih
        fun_prop


-- @@ L75-75 verbatim
end List.Encoding


-- @@ L77-77 verbatim
namespace MeasureTheory.List


-- @@ L79-80 verbatim
instance instMeasurableSpaceListLeanPool : MeasurableSpace (List A) :=
  MeasurableSpace.comap List.Encoding.encode inferInstance


-- @@ L82-84 verbatim
@[fun_prop]
lemma measurable_encode : Measurable (List.Encoding.encode (A := A)) := by
  apply comap_measurable


-- @@ L86-98 verbatim
@[local simp]
lemma measurable_to_encode
    (f : A → List B)
    : Measurable f ↔ Measurable (fun x ↦ List.Encoding.encode (f x)) := by
  apply Iff.intro
  · intro h
    exact measurable_encode.comp h
  · intro h X hX
    rw [MeasurableSpace.measurableSet_comap] at hX
    rcases hX with ⟨Y, hY, hX⟩
    show MeasurableSet (f ⁻¹' X)
    rw [← hX]
    apply h hY


-- @@ L100-103 verbatim
@[local fun_prop, simp]
lemma measurable_cons : Measurable (fun ((x : A), xs) ↦ x :: xs) := by
  simp only [measurable_to_encode, List.Encoding.encode_cons]
  fun_prop


-- @@ L105-110 verbatim
@[fun_prop]
lemma measurable_cons'
    {f : A → B} (hf : Measurable f)
    {g : A → List B} (hg : Measurable g)
    : Measurable (fun x ↦ f x :: g x) := by
  fun_prop


-- @@ L112-124 verbatim
@[fun_prop]
lemma measurable_foldr
    {cons : A → B → B} (hcons : Measurable fun (x, xs) ↦ cons x xs) (nil : B)
    : Measurable (List.foldr cons nil) := by
  have : List.foldr cons nil = fun xs ↦ List.Encoding.foldr cons nil (.encode xs) := by
    ext xs
    induction xs with
    | nil =>
      simp only [List.foldr_nil, List.Encoding.encode_nil, List.Encoding.foldr_nil]
    | cons head tail ih =>
      simp only [List.foldr_cons, ih, List.Encoding.encode_cons, List.Encoding.foldr_cons]
  rw [this]
  fun_prop


-- @@ L126-134 verbatim
instance [DiscreteMeasurableSpace A] [Countable A] : DiscreteMeasurableSpace (List A) where
  forall_measurableSet X := by
    rw [MeasurableSpace.measurableSet_comap]
    use .encode '' X
    apply And.intro
    · have {n} : DiscreteMeasurableSpace (Fin n → A) := by
        apply MeasurableSingletonClass.toDiscreteMeasurableSpace
      apply MeasurableSet.of_discrete (α := (n : ℕ) × (Fin n → A))
    · simp_all


-- @@ L136-136 verbatim
end MeasureTheory.List
