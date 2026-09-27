/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.Smooth


-- @@ L10-15 verbatim
/-!
# Backward Gaussian test functions

The backward test function used in the local energy calculation is recorded
together with its nonnegativity.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
open scoped Topology



-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
namespace CKN.Foundation.Heat


-- @@ L26-26 verbatim
open CKN.Foundation.Parabolic


-- @@ L28-30 verbatim
/-- Rescaled backward heat test function centered at time `r ^ 2`. -/
def backwardHeatTestFunction (r : ℝ) (x : Vec3) (t : ℝ) : ℝ :=
  r ^ 2 * heatKernel x (r ^ 2 - t)


-- @@ L32-36 verbatim
lemma backwardHeatTestFunction_nonneg {r : ℝ} {x : Vec3} {t : ℝ}
    (_ : 0 < r) (_ : t < r ^ 2) :
    0 ≤ backwardHeatTestFunction r x t := by
  rw [backwardHeatTestFunction]
  exact mul_nonneg (sq_nonneg r) (heatKernel_nonneg _ _)


-- @@ L38-38 verbatim
end CKN.Foundation.Heat
