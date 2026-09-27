/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import Mathlib.Analysis.Normed.Module.Basic


-- @@ L10-12 verbatim
/-!
# LeanPool.SardMoreira.NormedSpace
-/


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
namespace NNReal


-- @@ L18-18 verbatim
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]


-- @@ L20-21 verbatim
protected theorem norm_smul (a : ℝ≥0) (x : E) : ‖a • x‖ = a * ‖x‖ := by
  simp [NNReal.smul_def, norm_smul]


-- @@ L23-24 verbatim
protected theorem nnnorm_smul (a : ℝ≥0) (x : E) : ‖a • x‖₊ = a * ‖x‖₊ := by
  simp [NNReal.smul_def, nnnorm_smul]


-- @@ L26-27 verbatim
protected theorem enorm_smul (a : ℝ≥0) (x : E) : ‖a • x‖ₑ = a * ‖x‖ₑ := by
  simp [enorm_eq_nnnorm, NNReal.nnnorm_smul]


-- @@ L29-30 verbatim
protected theorem dist_smul (a : ℝ≥0) (x y : E) : dist (a • x) (a • y) = a * dist x y := by
  simp [NNReal.smul_def, dist_smul₀]


-- @@ L32-33 verbatim
protected theorem nndist_smul (a : ℝ≥0) (x y : E) : nndist (a • x) (a • y) = a * nndist x y := by
  simp [NNReal.smul_def, nndist_smul₀]


-- @@ L35-36 verbatim
protected theorem edist_smul (a : ℝ≥0) (x y : E) : edist (a • x) (a • y) = a * edist x y := by
  simp only [edist_nndist, NNReal.nndist_smul, ENNReal.coe_mul]


-- @@ L38-38 verbatim
end NNReal
