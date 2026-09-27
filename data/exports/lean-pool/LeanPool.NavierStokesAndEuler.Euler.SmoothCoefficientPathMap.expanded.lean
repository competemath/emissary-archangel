/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothCoefficientPath
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Bounds


-- @@ L13-13 verbatim
/-! Bounded linear images of genuine uniformly smooth coefficient paths. -/


-- @@ L15-15 verbatim
@[expose] public section



-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-20 verbatim
namespace EulerMeanCoefficients.SmoothCoefficientPath


-- @@ L22-22 verbatim
open ContinuousLinearMap EulerSmoothLimit

-- @@ L23-23 verbatim
open scoped BoundedContinuousFunction ContDiff


-- @@ L25-27 verbatim
variable {K V W : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]


-- @@ L29-39 verbatim
/-- Apply a fixed bounded linear map to the actual field and all its literal derivative jets. -/
def map (L : V →L[ℝ] W) (A : SmoothCoefficientPath K V) : SmoothCoefficientPath K W where
  field := mapCoefficientPath L A.field
  smooth t := L.contDiff.comp (A.smooth t)
  jet n := mapCoefficientPath (ContinuousLinearMap.compContinuousMultilinearMapL ℝ
    (fun _ : Fin n => Space) V W L) (A.jet n)
  jet_eq n t x := by
    change L.compContinuousMultilinearMap (A.jet n t x) =
      iteratedFDeriv ℝ n (fun y : Space => L (A.field t y)) x
    rw [A.jet_eq]
    exact (L.iteratedFDeriv_comp_left ((A.smooth t).contDiffAt (x := x)) (i := n) (by simp)).symm


-- @@ L41-42 verbatim
@[simp] theorem map_apply (L : V →L[ℝ] W) (A : SmoothCoefficientPath K V) (t : K) (x : Space) :
    (map L A).field t x = L (A.field t x) := rfl


-- @@ L44-51 verbatim
/-- Contraction of coefficient values preserves every actual spatial derivative bound. -/
theorem map_derivative_bound (L : V →L[ℝ] W) (hL : ‖L‖ ≤ 1) (A : SmoothCoefficientPath K V)
    (n : ℕ) (C : ℝ)
    (hb : ∀ t x, ‖iteratedFDeriv ℝ n (A.field t : Space → V) x‖ ≤ C) (t : K) (x : Space) :
    ‖iteratedFDeriv ℝ n ((map L A).field t : Space → W) x‖ ≤ C := by
  have h := L.norm_iteratedFDeriv_comp_left ((A.smooth t).contDiffAt (x := x)) (n := n) (by simp)
  exact h.trans ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans (by
      simpa only [one_mul] using hb t x))


-- @@ L53-53 verbatim
end EulerMeanCoefficients.SmoothCoefficientPath
