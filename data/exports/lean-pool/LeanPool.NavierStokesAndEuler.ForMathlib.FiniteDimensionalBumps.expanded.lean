/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension


-- @@ L12-12 verbatim
/-! The existence of smooth bumps, separated from their construction. -/


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-20 verbatim
/-- A finite-dimensional real normed space admits smooth bump functions.
This proof can be activated as an instance locally when defining cutoff data. -/
theorem FiniteDimensional.hasContDiffBump (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    HasContDiffBump E := by infer_instance
