/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldJoint
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.Deriv.Comp


-- @@ L13-14 verbatim
/-! Fixed bounded linear maps preserve the actual spatial and time jets of
smooth bounded coefficient paths. -/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
noncomputable section



-- @@ L22-22 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L24-24 verbatim
universe u


-- @@ L26-26 verbatim
namespace SmoothTimeField


-- @@ L28-31 verbatim
variable {K E V W : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]


-- @@ L33-36 verbatim
/-- Cache the standard `NormedAddCommGroup (E [×n]→L[ℝ] V)` instance to shorten typeclass
synthesis. -/
local instance instSmoothTimeFieldLinear1 (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] V) :=
    inferInstance

-- @@ L37-38 verbatim
/-- Cache the standard `NormedSpace ℝ (E [×n]→L[ℝ] V)` instance to shorten typeclass synthesis. -/
local instance instSmoothTimeFieldLinear2 (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] V) := inferInstance

-- @@ L39-42 verbatim
/-- Cache the standard `NormedAddCommGroup (E [×n]→L[ℝ] W)` instance to shorten typeclass
synthesis. -/
local instance instSmoothTimeFieldLinear3 (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] W) :=
    inferInstance

-- @@ L43-44 verbatim
/-- Cache the standard `NormedSpace ℝ (E [×n]→L[ℝ] W)` instance to shorten typeclass synthesis. -/
local instance instSmoothTimeFieldLinear4 (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] W) := inferInstance

-- @@ L45-48 verbatim
/-- Cache the standard `NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] V))` instance to shorten typeclass
synthesis. -/
local instance instSmoothTimeFieldLinear5 (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] V)) :=
    inferInstance

-- @@ L49-52 verbatim
/-- Cache the standard `NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] V))` instance to shorten typeclass
synthesis. -/
local instance instSmoothTimeFieldLinear6 (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] V)) :=
    inferInstance

-- @@ L53-56 verbatim
/-- Cache the standard `NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] W))` instance to shorten typeclass
synthesis. -/
local instance instSmoothTimeFieldLinear7 (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] W)) :=
    inferInstance

-- @@ L57-60 verbatim
/-- Cache the standard `NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] W))` instance to shorten typeclass
synthesis. -/
local instance instSmoothTimeFieldLinear8 (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] W)) :=
    inferInstance


-- @@ L62-72 verbatim
/-- Map, bundling `field`, `smooth`, `jet`, `jet_eq`. -/
def map (L : V →L[ℝ] W) (A : SmoothTimeField K E V) : SmoothTimeField K E W where
  field := mapPath L A.field
  smooth t := L.contDiff.comp (A.smooth t)
  jet n := mapPath
    (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin n => E) V W L) (A.jet n)
  jet_eq n t x := by
    change L.compContinuousMultilinearMap (A.jet n t x) =
      iteratedFDeriv ℝ n (L ∘ (A.field t : E → V)) x
    rw [A.jet_eq]
    exact (L.iteratedFDeriv_comp_left (A.smooth t).contDiffAt (by simp)).symm


-- @@ L74-75 verbatim
@[simp] theorem map_apply (L : V →L[ℝ] W) (A : SmoothTimeField K E V) (t : K) (x : E) :
    (A.map L).field t x = L (A.field t x) := rfl


-- @@ L77-79 verbatim
@[simp] theorem map_jet_apply (L : V →L[ℝ] W) (A : SmoothTimeField K E V)
    (n : ℕ) (t : K) (x : E) :
    (A.map L).jet n t x = L.compContinuousMultilinearMap (A.jet n t x) := rfl


-- @@ L81-91 verbatim
theorem map_jet_norm_le (L : V →L[ℝ] W) (A : SmoothTimeField K E V) (n : ℕ) :
    ‖(A.map L).jet n‖ ≤ ‖L‖ * ‖A.jet n‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg L) (norm_nonneg _))).2
  intro t
  apply (BoundedContinuousFunction.norm_le
    (mul_nonneg (norm_nonneg L) (norm_nonneg _))).2
  intro x
  rw [map_jet_apply]
  exact (L.norm_compContinuousMultilinearMap_le (A.jet n t x)).trans
    (mul_le_mul_of_nonneg_left
      (((A.jet n t).norm_coe_le_norm x).trans ((A.jet n).norm_coe_le_norm t)) (norm_nonneg L))


-- @@ L93-93 verbatim
end SmoothTimeField


-- @@ L95-95 verbatim
namespace SmoothTimeField


-- @@ L97-97 verbatim
open Set


-- @@ L99-102 verbatim
variable {E V W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {T : ℝ} {hT : 0 ≤ T}


-- @@ L104-108 verbatim
theorem TimeDerivative.map (L : V →L[ℝ] W)
    {A A₁ : SmoothTimeField (Icc (0 : ℝ) T) E V}
    (h : TimeDerivative T hT A A₁) : TimeDerivative T hT (A.map L) (A₁.map L) := by
  intro t x
  exact L.hasFDerivAt.comp_hasDerivWithinAt (t : ℝ) (h t x)


-- @@ L110-110 verbatim
end SmoothTimeField
