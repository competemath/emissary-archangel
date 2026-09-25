/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import AddCombi.Convolution.Finite.Defs

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Conjneg
import Mathlib.Analysis.Complex.Order
import Mathlib.Data.Rat.Star


-- @@ L15-15 verbatim
public section


-- @@ L17-17 verbatim
open Finset Function Real

-- @@ L18-18 verbatim
open scoped ComplexConjugate NNReal Pointwise


-- @@ L20-20 verbatim
variable {G K : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]

-- @@ L21-21 verbatim
variable [Semifield K] [CharZero K] [LinearOrder K] [IsStrictOrderedRing K] {f g : G → K}


-- @@ L23-24 expanded
lemma conv_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ conv f g := fun _a ↦
  expect_nonneg fun _x _ ↦ mul_nonneg (hf _) (hg _)


-- @@ L26-26 expanded
lemma conv_apply_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) (a : G) : 0 ≤ (conv f g) a :=
  conv_nonneg hf hg _


-- @@ L28-33 expanded
@[simp]
lemma support_conv (hf : 0 ≤ f) (hg : 0 ≤ g) : support (conv f g) = support f + support g :=
  by
  refine (support_conv_subset _ _).antisymm ?_
  rintro _ ⟨a, ha, b, hb, rfl⟩
  rw [mem_support, conv_apply_add]
  exact
    ne_of_gt <|
      expect_pos' (fun c _ ↦ mul_nonneg (hf _) <| hg _)
        ⟨0, mem_univ _,
          mul_pos ((hf _).lt_of_ne' <| by simpa using ha) <| (hg _).lt_of_ne' <| by simpa using hb⟩


-- @@ L35-41 expanded
lemma conv_pos (hf : 0 < f) (hg : 0 < g) : 0 < conv f g :=
  by
  rw [Pi.lt_def] at hf hg ⊢
  obtain ⟨hf, a, ha⟩ := hf
  obtain ⟨hg, b, hb⟩ := hg
  refine ⟨conv_nonneg hf hg, a + b, ?_⟩
  rw [conv_apply_add]
  exact expect_pos' (fun c _ ↦ mul_nonneg (hf _) <| hg _) ⟨0, by simpa using mul_pos ha hb⟩


-- @@ L43-43 verbatim
variable [StarRing K] [StarOrderedRing K]


-- @@ L45-47 expanded
omit [IsStrictOrderedRing K] in
lemma dconv_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ dconv f g := fun _a ↦
  expect_nonneg fun _x _ ↦ mul_nonneg (hf _) <| star_nonneg_iff.2 <| hg _


-- @@ L49-50 expanded
omit [IsStrictOrderedRing K] in
lemma dconv_apply_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) (a : G) : 0 ≤ (dconv f g) a :=
  dconv_nonneg hf hg _


-- @@ L52-54 expanded
@[simp]
lemma support_dconv (hf : 0 ≤ f) (hg : 0 ≤ g) : support (dconv f g) = support f - support g := by
  simpa [sub_eq_add_neg] using support_conv hf (conjneg_nonneg.2 hg)


-- @@ L56-57 expanded
lemma dconv_pos (hf : 0 < f) (hg : 0 < g) : 0 < dconv f g := by rw [← conv_conjneg];
  exact conv_pos hf (conjneg_pos.2 hg)

