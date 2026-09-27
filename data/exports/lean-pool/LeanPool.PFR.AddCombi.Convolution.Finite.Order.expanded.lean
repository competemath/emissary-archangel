/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/

module
public import LeanPool.PFR.AddCombi.Convolution.Finite.Defs

public import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Conjneg
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.Complex.Order
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.Positivity.Finset


-- @@ L19-21 verbatim
/-!
# Ordered finite convolution estimates
-/


-- @@ L23-23 verbatim
open Finset Function Real

-- @@ L24-24 verbatim
open scoped ComplexConjugate NNReal Pointwise


-- @@ L26-26 verbatim
variable {G K : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]

-- @@ L27-27 verbatim
variable [Semifield K] [CharZero K] [LinearOrder K] [IsStrictOrderedRing K] {f g : G → K}


-- @@ L29-31 expanded
public lemma conv_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ conv f g := fun _a ↦
  expect_nonneg fun _x _ ↦ mul_nonneg (hf _) (hg _)


-- @@ L37-44 expanded
public lemma conv_pos (hf : 0 < f) (hg : 0 < g) : 0 < conv f g :=
  by
  rw [Pi.lt_def] at hf hg ⊢
  obtain ⟨hf, a, ha⟩ := hf
  obtain ⟨hg, b, hb⟩ := hg
  refine ⟨conv_nonneg hf hg, a + b, ?_⟩
  rw [conv_apply_add]
  exact expect_pos' (fun c _ ↦ mul_nonneg (hf _) <| hg _) ⟨0, by simpa using mul_pos ha hb⟩


-- @@ L46-46 verbatim
variable [StarRing K] [StarOrderedRing K]


-- @@ L48-51 expanded
omit [IsStrictOrderedRing K] in
public lemma dconv_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ dconv f g := fun _a ↦
  expect_nonneg fun _x _ ↦ mul_nonneg (hf _) <| star_nonneg_iff.2 <| hg _


-- @@ L53-55 expanded
omit [IsStrictOrderedRing K] in
public lemma dconv_apply_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) (a : G) : 0 ≤ (dconv f g) a :=
  dconv_nonneg hf hg _


-- @@ L59-61 expanded
public lemma dconv_pos (hf : 0 < f) (hg : 0 < g) : 0 < dconv f g := by rw [← conv_conjneg];
  exact conv_pos hf (conjneg_pos.2 hg)

