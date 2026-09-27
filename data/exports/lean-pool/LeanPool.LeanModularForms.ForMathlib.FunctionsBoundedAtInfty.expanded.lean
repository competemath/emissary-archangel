/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty


-- @@ L10-10 verbatim
/-! # FunctionsBoundedAtInfty -/


-- @@ L12-12 verbatim
@[expose] public section



-- @@ L15-17 verbatim
open UpperHalfPlane

/-This is from the Sphere Pack project, so might not actually be for mathlib.-/


-- @@ L19-21 verbatim
theorem isBoundedAtImInfty_neg_iff (f : ℍ → ℂ) :
    IsBoundedAtImInfty (-f) ↔ IsBoundedAtImInfty f := by
  simp_rw [UpperHalfPlane.isBoundedAtImInfty_iff, Pi.neg_apply, norm_neg]


-- @@ L23-23 verbatim
alias ⟨_, IsBoundedAtImInfty.neg⟩ := isBoundedAtImInfty_neg_iff
