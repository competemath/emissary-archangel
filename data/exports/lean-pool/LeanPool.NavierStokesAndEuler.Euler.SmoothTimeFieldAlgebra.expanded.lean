/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldJoint
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.Deriv.Add


-- @@ L14-14 verbatim
/-! Addition of actual smooth bounded fields and their genuine time jets. -/


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


-- @@ L28-30 verbatim
variable {K E V : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]


-- @@ L32-35 verbatim
/-- Cache the standard `NormedAddCommGroup (E [×n]→L[ℝ] V)` instance to shorten typeclass
synthesis. -/
local instance instSmoothTimeFieldAlgebra1 (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] V) :=
    inferInstance

-- @@ L36-37 verbatim
/-- Cache the standard `NormedSpace ℝ (E [×n]→L[ℝ] V)` instance to shorten typeclass synthesis. -/
local instance instSmoothTimeFieldAlgebra2 (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] V) := inferInstance

-- @@ L38-41 verbatim
/-- Cache the standard `NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] V))` instance to shorten typeclass
synthesis. -/
local instance instSmoothTimeFieldAlgebra3 (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] V)) :=
    inferInstance

-- @@ L42-45 verbatim
/-- Cache the standard `NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] V))` instance to shorten typeclass
synthesis. -/
local instance instSmoothTimeFieldAlgebra4 (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] V)) :=
    inferInstance


-- @@ L47-57 verbatim
/-- Add, bundling `field`, `smooth`, `jet`, `jet_eq`. -/
def add (A B : SmoothTimeField K E V) : SmoothTimeField K E V where
  field := A.field + B.field
  smooth t := (A.smooth t).add (B.smooth t)
  jet n := A.jet n + B.jet n
  jet_eq n t x := by
    change A.jet n t x + B.jet n t x =
      iteratedFDeriv ℝ n ((A.field t : E → V) + (B.field t : E → V)) x
    rw [A.jet_eq, B.jet_eq]
    exact (iteratedFDeriv_add_apply ((A.smooth t).contDiffAt.of_le (by simp))
      ((B.smooth t).contDiffAt.of_le (by simp))).symm


-- @@ L59-60 verbatim
@[simp] theorem add_apply (A B : SmoothTimeField K E V) (t : K) (x : E) :
    (A.add B).field t x = A.field t x + B.field t x := rfl


-- @@ L62-63 verbatim
theorem add_jet_norm_le (A B : SmoothTimeField K E V) (n : ℕ) :
    ‖(A.add B).jet n‖ ≤ ‖A.jet n‖ + ‖B.jet n‖ := norm_add_le _ _


-- @@ L65-72 verbatim
theorem jet_eq_of_field_eq (A B : SmoothTimeField K E V)
    (h : ∀ t x, A.field t x = B.field t x) (n : ℕ) : A.jet n = B.jet n := by
  apply ContinuousMap.ext
  intro t
  apply BoundedContinuousFunction.ext
  intro x
  rw [A.jet_eq, B.jet_eq]
  exact congrArg (fun f : E → V => iteratedFDeriv ℝ n f x) (funext (h t))


-- @@ L74-74 verbatim
end SmoothTimeField


-- @@ L76-76 verbatim
namespace SmoothTimeField


-- @@ L78-78 verbatim
open Set


-- @@ L80-82 verbatim
variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {T : ℝ} {hT : 0 ≤ T}


-- @@ L84-89 verbatim
theorem TimeDerivative.add
    {A A₁ B B₁ : SmoothTimeField (Icc (0 : ℝ) T) E V}
    (hA : TimeDerivative T hT A A₁) (hB : TimeDerivative T hT B B₁) :
    TimeDerivative T hT (A.add B) (A₁.add B₁) := by
  intro t x
  exact (hA t x).add (hB t x)


-- @@ L91-91 verbatim
end SmoothTimeField
