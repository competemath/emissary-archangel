/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex


-- @@ L10-14 verbatim
/-!
# Complements on homological complexes

Material destined for `Mathlib.Algebra.Homology.HomologicalComplex`.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-20 verbatim
/-- The predecessor function of the cochain complex shape on `ℕ` is truncated subtraction. -/
lemma CochainComplex.prev_nat (j : ℕ) : (ComplexShape.up ℕ).prev j = j - 1 := by
  cases j <;> simp
