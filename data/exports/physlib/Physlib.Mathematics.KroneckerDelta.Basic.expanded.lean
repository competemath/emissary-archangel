/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

-- @@ L13-40 verbatim
/-!

# Kronecker delta

## i. Overview

This module defines the Kronecker delta `kroneckerDelta i j` (notation `δ[i,j]`), equal to
`1` when `i = j` and `0` otherwise, together with its behaviour under scalar multiplication,
symmetrization, and finite sums. It also defines the `generalizedKroneckerDelta`, the
determinant of a matrix of Kronecker deltas.

## ii. Key results

- `kroneckerDelta` : the Kronecker delta on a type with decidable equality.
- `generalizedKroneckerDelta` : the determinant form `det (δ[μᵢ, νⱼ])`.

## iii. Table of contents

- A. The Kronecker delta
- B. Conditions for smul to vanish
- C. Symmetrization
- D. Sums
- E. The generalized Kronecker delta

## iv. References

* None.
-/


-- @@ L42-42 verbatim
@[expose] public section


-- @@ L44-44 verbatim
namespace KroneckerDelta


-- @@ L46-46 verbatim
variable {α M : Type*} [DecidableEq α]


-- @@ L48-52 verbatim
/-!

## A. The Kronecker delta

-/


-- @@ L54-55 verbatim
/-- The Kronecker delta function, `ite (i = j) 1 0`. -/
def kroneckerDelta (i j : α) : ℕ := if i = j then 1 else 0


-- @@ L57-58 verbatim
@[inherit_doc]
notation "δ[" i "," j "]" => kroneckerDelta i j


-- @@ L60-61 expanded
@[simp]
lemma eq_one_of_same (i : α) : kroneckerDelta i i = 1 :=
  if_pos rfl


-- @@ L63-63 expanded
lemma eq_zero_of_ne {i j : α} (h : i ≠ j) : kroneckerDelta i j = 0 :=
  if_neg h


-- @@ L65-69 expanded
@[simp]
lemma eq_of_coe {p : α → Prop} (i j : Subtype p) : kroneckerDelta (i : α) j = kroneckerDelta i j :=
  by
  rcases eq_or_ne i j with (rfl | hne)
  · repeat rw [eq_one_of_same]
  · rw [eq_zero_of_ne hne, eq_zero_of_ne <| Subtype.coe_ne_coe.mpr hne]


-- @@ L71-72 expanded
lemma eq_zero_of_not {p : α → Prop} {i j : α} (hi : ¬p i) (hj : p j) : kroneckerDelta i j = 0 :=
  eq_zero_of_ne (fun h ↦ hi (h ▸ hj))


-- @@ L74-77 verbatim
/-- The Kronecker delta is invariant under the component-index equivalence `finSumFinEquiv`. -/
lemma kroneckerDelta_finSumFinEquiv (a b : Fin 1 ⊕ Fin 3) :
    kroneckerDelta (finSumFinEquiv a) (finSumFinEquiv b) = kroneckerDelta a b := by
  simp only [kroneckerDelta, Equiv.apply_eq_iff_eq]


-- @@ L79-83 verbatim
/-!

## B. Conditions for smul to vanish

-/


-- @@ L85-89 expanded
lemma smul_of_eq_zero [AddMonoid M] (i j : α) {f : α → α → M} (hf : f i i = 0) :
    kroneckerDelta i j • f i j = 0 :=
  by
  rcases eq_or_ne i j with (rfl | hne)
  · exact smul_eq_zero_of_right _ hf
  · exact smul_eq_zero_of_left (eq_zero_of_ne hne) _


-- @@ L91-95 expanded
lemma smul_eq_zero_iff [AddMonoid M] (i j : α) (f : α → α → M) :
    kroneckerDelta i j • f i j = 0 ↔ i ≠ j ∨ f i i = 0 :=
  by
  rcases eq_or_ne i j with (rfl | hne)
  · simp
  · simp [eq_zero_of_ne, hne]


-- @@ L97-100 expanded
lemma smul_eq_zero_iff' [AddMonoid M] (i : α) (f : α → α → M) :
    (∀ j : α, kroneckerDelta i j • f i j = 0) ↔ f i i = 0 :=
  by
  refine ⟨fun h ↦ ?_, fun hf j ↦ smul_of_eq_zero i j hf⟩
  simpa [one_nsmul] using h i


-- @@ L102-104 expanded
lemma smul_eq_zero_iff'' [AddMonoid M] (f : α → α → M) :
    (∀ i j : α, kroneckerDelta i j • f i j = 0) ↔ ∀ i : α, f i i = 0 :=
  forall_congr' fun j ↦ smul_eq_zero_iff' j f


-- @@ L106-110 verbatim
/-!

## C. Symmetrization

-/


-- @@ L112-112 expanded
lemma symm (i j : α) : kroneckerDelta i j = kroneckerDelta j i :=
  ite_cond_congr <| Eq.propIntro Eq.symm Eq.symm


-- @@ L114-117 expanded
lemma smul_symm [AddMonoid M] (i j : α) (f : α → α → M) :
    kroneckerDelta i j • f j i = kroneckerDelta i j • f i j :=
  by
  rcases eq_or_ne i j with (rfl | hne)
  · rfl
  · simp only [eq_zero_of_ne hne, zero_smul]


-- @@ L119-123 expanded
lemma symmetrize [AddMonoid M] (i j : α) (f : α → α → M) :
    kroneckerDelta i j • (f i j + f j i) = (2 * kroneckerDelta i j) • f i j :=
  by
  rcases eq_or_ne i j with (rfl | hne)
  · simp [two_nsmul]
  · simp [eq_zero_of_ne hne]


-- @@ L125-130 expanded
lemma symmetrize' [AddCommMonoid M] {K : Type*} [Semifield K] [CharZero K] [Module K M] (i j : α)
    (f : α → α → M) :
    kroneckerDelta i j • (2 : K)⁻¹ • (f i j + f j i) = kroneckerDelta i j • f i j :=
  by
  rcases eq_or_ne i j with (rfl | hne)
  · simp only [eq_one_of_same, one_nsmul, ← two_smul K, smul_smul]
    rw [inv_mul_cancel₀ (OfNat.zero_ne_ofNat 2).symm, one_smul]
  · simp [eq_zero_of_ne hne]


-- @@ L132-136 expanded
@[simp]
lemma smul_sub_eq_zero [AddGroup M] (i j : α) (f : α → α → M) :
    kroneckerDelta i j • (f i j - f j i) = 0 :=
  by
  rcases eq_or_ne i j with (rfl | hne)
  · exact smul_eq_zero_of_right _ (sub_self <| f i i)
  · exact smul_eq_zero_of_left (eq_zero_of_ne hne) _


-- @@ L138-142 verbatim
/-!

## D. Sums

-/


-- @@ L144-144 verbatim
section Sums

-- @@ L145-145 verbatim
open Finset


-- @@ L147-147 verbatim
variable [AddCommMonoid M]


-- @@ L149-151 expanded
@[simp]
lemma sum_mul [Fintype α] (i j : α) :
    ∑ k : α, kroneckerDelta i k * kroneckerDelta k j = kroneckerDelta i j := by
  simp [kroneckerDelta]


-- @@ L153-155 expanded
@[simp]
lemma sum_smul [Fintype α] (i : α) (f : α → M) : ∑ j : α, kroneckerDelta i j • f j = f i := by
  simp [kroneckerDelta]


-- @@ L157-159 expanded
lemma sum_sum_smul_eq_zero [Fintype α] {f : α → α → M} (hf : ∀ i : α, f i i = 0) :
    ∑ i : α, ∑ j : α, kroneckerDelta i j • f i j = 0 := by simp [sum_smul, hf, sum_const_zero]


-- @@ L161-163 expanded
lemma finset_sum_smul (s : Finset α) (i : α) (f : α → M) :
    ∑ j ∈ s, kroneckerDelta i j • f j = if i ∈ s then f i else 0 := by simp [kroneckerDelta]


-- @@ L165-169 expanded
lemma finset_sum_sum_smul_eq_zero {s s' : Finset α} {f : α → α → M} (hf : ∀ i ∈ s ∩ s', f i i = 0) :
    ∑ i ∈ s, ∑ j ∈ s', kroneckerDelta i j • f i j = 0 :=
  by
  simp only [finset_sum_smul, Finset.sum_ite_mem]
  rw [← sum_coe_sort]
  simp [hf]


-- @@ L171-171 verbatim
end Sums


-- @@ L173-177 verbatim
/-!

## E. The generalized Kronecker delta

-/


-- @@ L179-179 verbatim
section Generalized

-- @@ L180-180 verbatim
open Matrix


-- @@ L182-183 verbatim
/-- Integer-valued Kronecker entry via the existing `kroneckerDelta`. -/
local notation "δℤ" => (fun ρ σ => ((kroneckerDelta ρ σ : ℕ) : ℤ))


-- @@ L185-192 verbatim
/-- Generalized Kronecker delta:
`δ^{μ₁...μₙ}_{ν₁...νₙ} = det (δ[μᵢ, νⱼ])`.

This is defined for any finite type `α` with decidable equality. -/
def generalizedKroneckerDelta {α ι : Type} [DecidableEq α]
    [DecidableEq ι] [Fintype ι]
    (μ : ι → α) (ν : ι → α) : ℤ :=
  Matrix.det (fun i j => δℤ (μ i) (ν j))


-- @@ L194-203 verbatim
/-- Swapping two of the upper indices of the generalized Kronecker delta negates it.
This is one row transposition of the underlying determinant. -/
lemma generalizedKroneckerDelta_swap {α ι : Type} [DecidableEq α] [DecidableEq ι] [Fintype ι]
    (μ ν : ι → α) {i j : ι} (hij : i ≠ j) :
    generalizedKroneckerDelta (μ ∘ Equiv.swap i j) ν = - generalizedKroneckerDelta μ ν := by
  show (Matrix.submatrix (Matrix.of fun a b => ((kroneckerDelta (μ a) (ν b) : ℕ) : ℤ))
      (Equiv.swap i j) id).det
    = -(Matrix.of fun a b => ((kroneckerDelta (μ a) (ν b) : ℕ) : ℤ)).det
  rw [Matrix.det_permute, Equiv.Perm.sign_swap hij]
  simp


-- @@ L205-214 verbatim
/-- Simultaneously reindexing the upper and lower slots of a generalized Kronecker delta by the
same permutation leaves it unchanged. -/
@[simp]
lemma generalizedKroneckerDelta_comp_perm {α ι : Type} [DecidableEq α] [DecidableEq ι]
    [Fintype ι] (μ ν : ι → α) (e : Equiv.Perm ι) :
    generalizedKroneckerDelta (μ ∘ e) (ν ∘ e) = generalizedKroneckerDelta μ ν := by
  show (Matrix.submatrix
      (Matrix.of fun i j => ((kroneckerDelta (μ i) (ν j) : ℕ) : ℤ)) e e).det =
    (Matrix.of fun i j => ((kroneckerDelta (μ i) (ν j) : ℕ) : ℤ)).det
  exact Matrix.det_submatrix_equiv_self e _


-- @@ L216-216 verbatim
end Generalized


-- @@ L218-218 verbatim
end KroneckerDelta
