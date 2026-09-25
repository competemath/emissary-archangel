/-
Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Jose Fernandez Morales
-/
module

public import Physlib.SpaceAndTime.Space.Derivatives.Basic
public import Physlib.SpaceAndTime.Space.Derivatives.MultiIndex

-- @@ L10-41 verbatim
/-!
# Iterated derivatives on `Space d`

## i. Overview

This module defines iterated coordinate derivatives on `Space d` indexed by multi-indices.

The implementation is intentionally modest. A multi-index is first expanded into a canonical list
of coordinate directions, and the iterated derivative is then defined by repeated application of
`Space.deriv` along that list.

## ii. Key results

- `Space.iteratedDeriv` : iterated coordinate derivatives on `Space d`.
- `∂^[I] f` : notation for the iterated derivative indexed by the multi-index `I`.
- `Space.iteratedDeriv_add`, `Space.iteratedDeriv_const_smul` :
  algebraic compatibility for smooth scalar-valued functions.
- `Space.iteratedDeriv_contDiff` : smooth scalar-valued functions remain smooth after
  iterated coordinate differentiation.
- `Space.tsupport_iteratedDeriv_subset` :
  the support of an iterated spatial derivative is contained in that of the original function.

## iii. Table of contents

- A. Iterated derivatives on `Space d`
- B. Algebraic and regularity lemmas
- C. Support lemmas

## iv. References

* None.
-/


-- @@ L43-43 verbatim
@[expose] public section


-- @@ L45-45 verbatim
namespace Space


-- @@ L47-47 verbatim
open Physlib

-- @@ L48-48 verbatim
open scoped ContDiff


-- @@ L50-50 verbatim
variable {M : Type} {d : ℕ}


-- @@ L52-55 verbatim
/-!
## A. Iterated derivatives on `Space d`

-/


-- @@ L57-60 verbatim
/-- The iterated coordinate derivative on `Space d` indexed by a multi-index. -/
noncomputable def iteratedDeriv [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (I : MultiIndex d) (f : Space d → M) : Space d → M :=
  I.toList.foldr (fun i g => deriv i g) f


-- @@ L62-63 verbatim
@[inherit_doc iteratedDeriv]
macro "∂^[" I:term "]" : term => `(iteratedDeriv $I)


-- @@ L65-70 verbatim
private lemma iteratedDerivList_contDiff (L : List (Fin d)) {f : Space d → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (L.foldr (fun i g => deriv i g) f) := by
  induction L generalizing f with
  | nil => simpa using hf
  | cons i L ih => exact (contDiff_apply ℝ ℝ i).comp (Space.deriv_contDiff (n := ∞) (ih hf))


-- @@ L72-81 verbatim
private lemma iteratedDerivList_add (L : List (Fin d)) {f g : Space d → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    L.foldr (fun i h => deriv i h) (f + g) =
      L.foldr (fun i h => deriv i h) f + L.foldr (fun i h => deriv i h) g := by
  induction L generalizing f g with
  | nil => rfl
  | cons i L ih =>
      simp only [List.foldr, ih hf hg]
      exact Space.deriv_add _ _ ((iteratedDerivList_contDiff L hf).differentiable (by simp))
        ((iteratedDerivList_contDiff L hg).differentiable (by simp))


-- @@ L83-91 verbatim
private lemma iteratedDerivList_const_smul (L : List (Fin d)) (c : ℝ) {f : Space d → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    L.foldr (fun i h => deriv i h) (c • f) =
      c • L.foldr (fun i h => deriv i h) f := by
  induction L generalizing f with
  | nil => rfl
  | cons i L ih =>
      simp only [List.foldr, ih hf]
      exact Space.deriv_const_smul c ((iteratedDerivList_contDiff L hf).differentiable (by simp))


-- @@ L93-96 expanded
@[simp]
lemma iteratedDeriv_zero [AddCommGroup M] [Module ℝ M] [TopologicalSpace M] (f : Space d → M) :
    (iteratedDeriv 0) f = f := by simp [iteratedDeriv, Physlib.MultiIndex.toList_zero]


-- @@ L98-103 expanded
@[simp]
lemma iteratedDeriv_increment_zero [NeZero d] [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (I : MultiIndex d) (f : Space d → M) :
    (iteratedDeriv (MultiIndex.increment I 0)) f = (deriv 0) ((iteratedDeriv I) f) :=
  by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
  simp [iteratedDeriv, Physlib.MultiIndex.toList_increment_zero]


-- @@ L105-109 expanded
@[simp]
lemma iteratedDeriv_single [AddCommGroup M] [Module ℝ M] [TopologicalSpace M] (i : Fin d)
    (f : Space d → M) : (iteratedDeriv (MultiIndex.increment 0 i)) f = (deriv i) f := by
  simp [iteratedDeriv, Physlib.MultiIndex.toList_single]


-- @@ L111-114 expanded
lemma iteratedDeriv_add (I : MultiIndex d) {f g : Space d → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) : (iteratedDeriv I) (f + g) = (iteratedDeriv I) f + (iteratedDeriv I) g :=
  by simpa [iteratedDeriv] using iteratedDerivList_add I.toList hf hg


-- @@ L116-119 expanded
lemma iteratedDeriv_const_smul (I : MultiIndex d) (c : ℝ) {f : Space d → ℝ} (hf : ContDiff ℝ ∞ f) :
    (iteratedDeriv I) (c • f) = c • (iteratedDeriv I) f := by
  simpa [iteratedDeriv] using iteratedDerivList_const_smul I.toList c hf


-- @@ L121-125 expanded
/-- Iterated spatial derivatives preserve smoothness for scalar-valued functions. -/
lemma iteratedDeriv_contDiff (I : MultiIndex d) {f : Space d → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ ((iteratedDeriv I) f) := by
  simpa [iteratedDeriv] using iteratedDerivList_contDiff I.toList hf


-- @@ L127-132 verbatim
/-- The topological support of a spatial derivative is contained in that of the original
function. -/
lemma tsupport_deriv_subset (i : Fin d) {f : Space d → ℝ} :
    tsupport (deriv i f) ⊆ tsupport f := by
  simpa [deriv_eq_fderiv_fun] using
    (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := fun x => f x) (v := basis i))


-- @@ L134-143 verbatim
private lemma iteratedDerivList_commute_deriv (L : List (Fin d)) (i : Fin d)
    {f : Space d → ℝ} (hf : ContDiff ℝ ∞ f) :
    L.foldr (fun j g => deriv j g) (deriv i f) =
      deriv i (L.foldr (fun j g => deriv j g) f) := by
  induction L generalizing f with
  | nil => rfl
  | cons j L ih =>
      simp only [List.foldr, ih hf]
      exact Space.deriv_commute _
        ((iteratedDerivList_contDiff L hf).of_le (WithTop.coe_le_coe.mpr le_top))


-- @@ L145-150 expanded
/-- An extra spatial derivative commutes with iterated spatial derivatives for smooth
scalar-valued functions. -/
lemma deriv_iteratedDeriv_commute (i : Fin d) (I : MultiIndex d) {f : Space d → ℝ}
    (hf : ContDiff ℝ ∞ f) : deriv i ((iteratedDeriv I) f) = (iteratedDeriv I) (deriv i f) := by
  simpa [iteratedDeriv] using (iteratedDerivList_commute_deriv I.toList i hf).symm


-- @@ L152-156 verbatim
private lemma tsupport_iteratedDerivList_subset (L : List (Fin d)) {f : Space d → ℝ} :
    tsupport (L.foldr (fun i g => deriv i g) f) ⊆ tsupport f := by
  induction L generalizing f with
  | nil => simp
  | cons i L ih => simpa [List.foldr] using (tsupport_deriv_subset i).trans ih


-- @@ L158-162 expanded
/-- The topological support of an iterated spatial derivative is contained in that of the
original function. -/
lemma tsupport_iteratedDeriv_subset (I : MultiIndex d) {f : Space d → ℝ} :
    tsupport ((iteratedDeriv I) f) ⊆ tsupport f := by
  simpa [iteratedDeriv] using tsupport_iteratedDerivList_subset I.toList (f := f)


-- @@ L164-169 expanded
/-- An iterated spatial derivative vanishes outside the topological support of the original
function. -/
lemma iteratedDeriv_eq_zero_of_notMem_tsupport (I : MultiIndex d) {f : Space d → ℝ} {x : Space d}
    (hx : x ∉ tsupport f) : (iteratedDeriv I) f x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx (tsupport_iteratedDeriv_subset I h)


-- @@ L171-171 verbatim
end Space
