/-
Copyright (c) 2024 Yaël Dillies, Isabel Dahlgren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Isabel Dahlgren
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise


-- @@ L10-12 verbatim
/-!
# Multidimensional corners
-/


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
namespace NOF

-- @@ L17-17 verbatim
variable {ι G : Type*} {a : ι → ι → G} {v : ι → G}


-- @@ L19-19 verbatim
def forget (i : ι) (x : ι → G) (j : {j : ι // j ≠ i}) : G := x j


-- @@ L21-21 verbatim
def IsForbiddenPatternWithTip (a : ι → ι → G) (v : ι → G) : Prop := ∀ ⦃i j⦄, i ≠ j → a i j = v j


-- @@ L23-27 verbatim
def IsForbiddenPattern (a : ι → ι → G) : Prop := ∃ v, IsForbiddenPatternWithTip a v

lemma isForbiddenPatternWithTip_iff_forget :
    IsForbiddenPatternWithTip a v ↔ ∀ i, forget i v = forget i (a i) := by
  simp [funext_iff, IsForbiddenPatternWithTip, eq_comm, forget]


-- @@ L29-30 verbatim
protected alias ⟨IsForbiddenPatternWithTip.forget, IsForbiddenPatternWithTip.of_forget⟩ :=
  isForbiddenPatternWithTip_iff_forget


-- @@ L32-32 verbatim
variable [Fintype ι] [AddCommGroup G]


-- @@ L34-36 verbatim
structure IsMultidimCorner (a : ι → ι → G) (b : ι → G) : Prop where
  sum_eq_sum : ∀ i j, ∑ k, a i k = ∑ k, a j k
  isForbiddenPatternWithTip : IsForbiddenPatternWithTip a b


-- @@ L38-55 verbatim
variable [DecidableEq ι]

lemma isMultidimCorner_forget_of_isForbiddenPattern (a : ι → ι → G) (h : IsForbiddenPattern a)
    (hS : ∀ i, ∑ j, a i j = 0) (i : ι) :
    IsMultidimCorner (fun j ↦ forget i (a j)) (forget i (a i)) := by
    rw [IsForbiddenPattern] at h
    obtain ⟨v, hv⟩ := h
    refine ⟨fun k l ↦ ?_, fun k l hneq ↦ ?_⟩
    · rw [← sub_eq_zero]
      calc
        ∑ j : {j // j ≠ i}, a k j - ∑ j : { j // j ≠ i }, a l j
          = ∑ j : {j // j ≠ i}, (a k j - a l j) := by rw [Finset.sum_sub_distrib]
        _ = ∑ j ∈ {i}ᶜ, (a k j - a l j) := (Finset.sum_subtype _ (by simp) (a k - a l)).symm
        _ = ∑ j ∈ {i}ᶜ, (a k j - a l j) + (a k i - a l i) := by simp [hv k.2, hv l.2]
        _ = ∑ j : ι, (a k j - a l j) := by rw [← Fintype.sum_eq_sum_compl_add]
        _ = 0 := by rw [Finset.sum_sub_distrib, sub_eq_zero, hS k, hS l]
    · rw [forget, forget, hv, hv l.2.symm]
      aesop


-- @@ L57-57 verbatim
end NOF
