/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothBanachFlow
import Mathlib.Analysis.Calculus.Deriv.Add


-- @@ L12-13 verbatim
/-! Odd prescribed velocity gives an odd actual Picard flow and inverse.
The symmetry is proved by uniqueness of the genuine ODE solution. -/


-- @@ L15-15 verbatim
@[expose] public section



-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-20 verbatim
namespace EulerBoundedLipschitzFlow.Data


-- @@ L22-23 verbatim
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (V : EulerBoundedLipschitzFlow.Data E)


-- @@ L25-32 verbatim
theorem flow_odd (ho : ∀ t, Function.Odd (V.velocity t)) (s t : ℝ) : Function.Odd (V.flow s t) := by
  intro x
  have he := V.flow_unique s (-x) (fun r => -V.flow s r x)
    (fun r => by
      rw [ho r]
      exact (V.flow_hasDerivAt s r x).neg)
    (by rw [V.flow_initial])
  exact (congrFun he t).symm


-- @@ L34-35 verbatim
theorem forward_odd (ho : ∀ t, Function.Odd (V.velocity t)) (t : ℝ) :
    Function.Odd (V.forward t) := V.flow_odd ho 0 t


-- @@ L37-38 verbatim
theorem backward_odd (ho : ∀ t, Function.Odd (V.velocity t)) (t : ℝ) :
    Function.Odd (V.backward t) := V.flow_odd ho t 0


-- @@ L40-40 verbatim
end EulerBoundedLipschitzFlow.Data


-- @@ L42-42 verbatim
namespace EulerSmoothBanachFlow


-- @@ L44-44 verbatim
open Set


-- @@ L46-47 verbatim
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (T : ℝ) (hT : 0 ≤ T) (A : SmoothTimeField (Icc (0 : ℝ) T) E E)


-- @@ L49-51 verbatim
theorem forward_odd (ho : ∀ t, Function.Odd (A.field t : E → E)) (t : ℝ) :
    Function.Odd ((flowData T hT A).forward t) :=
  (flowData T hT A).forward_odd (fun r => ho (projIcc 0 T hT r)) t


-- @@ L53-55 verbatim
theorem backward_odd (ho : ∀ t, Function.Odd (A.field t : E → E)) (t : ℝ) :
    Function.Odd ((flowData T hT A).backward t) :=
  (flowData T hT A).backward_odd (fun r => ho (projIcc 0 T hT r)) t


-- @@ L57-57 verbatim
end EulerSmoothBanachFlow
