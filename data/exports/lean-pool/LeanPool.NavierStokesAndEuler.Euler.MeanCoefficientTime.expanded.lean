/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

import LeanPool.NavierStokesAndEuler.ForMathlib.StronglyMeasurable

public import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientMultipliers
public import LeanPool.NavierStokesAndEuler.Euler.VolterraConvolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus


-- @@ L15-19 verbatim
/-!
Pointwise time differentiation of actual matrix fields yields differentiation
of their L² multiplication operators. The bridge is proved by evaluating the
Bochner fundamental theorem of calculus, not by assuming operator derivatives.
-/


-- @@ L21-21 verbatim
@[expose] public section



-- @@ L24-24 verbatim
noncomputable section


-- @@ L26-26 verbatim
namespace EulerMeanCoefficients


-- @@ L28-29 verbatim
open MeasureTheory InnerProductSpace Set EulerSmoothLimit EulerMeanSolenoidal
    EulerVolterraConvolution

-- @@ L30-30 verbatim
open scoped BoundedContinuousFunction


-- @@ L32-33 verbatim
/-- Cache the standard `NormedAddCommGroup Field` instance to shorten typeclass synthesis. -/
local instance instMeanCoefficientTime1 : NormedAddCommGroup Field := inferInstance

-- @@ L34-35 verbatim
/-- Cache the standard `NormedSpace ℝ Field` instance to shorten typeclass synthesis. -/
local instance instMeanCoefficientTime2 : NormedSpace ℝ Field := inferInstance

-- @@ L36-38 verbatim
/-- Cache the standard `NormedAddCommGroup (L2 →L[ℝ] L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanCoefficientTime3 : NormedAddCommGroup (L2 →L[ℝ] L2) := inferInstance

-- @@ L39-40 verbatim
/-- Cache the standard `NormedSpace ℝ (L2 →L[ℝ] L2)` instance to shorten typeclass synthesis. -/
local instance instMeanCoefficientTime4 : NormedSpace ℝ (L2 →L[ℝ] L2) := inferInstance


-- @@ L42-46 verbatim
/-- Operator path, given by `⟨fun t => multiplierMap (A t), multiplierMap.continuous.comp
A.continuous⟩`. -/
def operatorPath (T : ℝ) (A : C(Icc (0 : ℝ) T, Field)) :
    C(Icc (0 : ℝ) T, L2 →L[ℝ] L2) :=
  ⟨fun t => multiplierMap (A t), multiplierMap.continuous.comp A.continuous⟩


-- @@ L48-74 verbatim
theorem field_integral_eq_sub (T : ℝ) (hT : 0 ≤ T)
    (A A' : C(Icc (0 : ℝ) T, Field))
    (hpoint : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space,
      HasDerivWithinAt (fun s => extendPath (Y := Field) T hT A s x)
        (extendPath (Y := Field) T hT A' t x) (Icc (0 : ℝ) T) t)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    (∫ s in (0 : ℝ)..t, extendPath (Y := Field) T hT A' s) =
      extendPath (Y := Field) T hT A t - extendPath (Y := Field) T hT A 0 := by
  apply BoundedContinuousFunction.ext
  intro x
  let ev : Field →L[ℝ] (Space →L[ℝ] Space) := BoundedContinuousFunction.evalCLM ℝ x
  have hcA := ev.continuous.comp (extendPath_continuous (Y := Field) T hT A)
  have hcA' := ev.continuous.comp (extendPath_continuous (Y := Field) T hT A')
  calc
    (∫ s in (0 : ℝ)..t, extendPath (Y := Field) T hT A' s) x =
        ∫ s in (0 : ℝ)..t, extendPath (Y := Field) T hT A' s x := by
      change ev (∫ s in (0 : ℝ)..t, extendPath (Y := Field) T hT A' s) =
        ∫ s in (0 : ℝ)..t, ev (extendPath (Y := Field) T hT A' s)
      exact (ContinuousLinearMap.intervalIntegral_comp_comm (𝕜 := ℝ) (E := Field)
        (F := Space →L[ℝ] Space) (μ := volume) ev
        ((extendPath_continuous (Y := Field) T hT A').intervalIntegrable 0 t)).symm
    _ = extendPath (Y := Field) T hT A t x - extendPath (Y := Field) T hT A 0 x := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hcA.continuousOn
        ?_ (hcA'.intervalIntegrable 0 t)
      intro s hs
      have hsT : s < T := hs.2.trans_le ht.2
      exact (hpoint s ⟨hs.1.le, hsT.le⟩ x).hasDerivAt (Icc_mem_nhds hs.1 hsT)


-- @@ L76-91 verbatim
/-- Pointwise matrix derivatives and sup-norm continuity of the derivative are sufficient. -/
theorem field_hasDerivWithinAt (T : ℝ) (hT : 0 ≤ T)
    (A A' : C(Icc (0 : ℝ) T, Field))
    (hpoint : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space,
      HasDerivWithinAt (fun s => extendPath (Y := Field) T hT A s x)
        (extendPath (Y := Field) T hT A' t x) (Icc (0 : ℝ) T) t)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath (Y := Field) T hT A) (extendPath (Y := Field) T hT A' t) (Icc (0 :
        ℝ) T) t := by
  have hc := extendPath_continuous (Y := Field) T hT A'
  have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable_of_secondCountable.stronglyMeasurableAtFilter hc.continuousAt
  apply (hd.const_add (extendPath (Y := Field) T hT A 0)).hasDerivWithinAt.congr_of_mem ?_ ht
  intro s hs
  rw [field_integral_eq_sub T hT A A' hpoint s hs]
  abel


-- @@ L93-115 verbatim
/-- The operator-valued derivative used by the mean solver follows from the matrix-field derivative.
-/
theorem operatorPath_hasDerivWithinAt (T : ℝ) (hT : 0 ≤ T)
    (A A' : C(Icc (0 : ℝ) T, Field))
    (hpoint : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space,
      HasDerivWithinAt (fun s => extendPath (Y := Field) T hT A s x)
        (extendPath (Y := Field) T hT A' t x) (Icc (0 : ℝ) T) t) :
    ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT (operatorPath T A)) (operatorPath T A' t)
        (Icc (0 : ℝ) T) t := by
  intro t
  have hlinear : HasFDerivAt (fun A : Field => multiplierMap A) multiplierMap
      (extendPath (Y := Field) T hT A t) :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := Field) (F := L2 →L[ℝ] L2) multiplierMap
  have hfield := field_hasDerivWithinAt T hT A A' hpoint t t.property
  have hd : HasDerivWithinAt (fun s => multiplierMap (extendPath (Y := Field) T hT A s))
      (multiplierMap (extendPath (Y := Field) T hT A' t)) (Icc (0 : ℝ) T) t :=
    hlinear.comp_hasDerivWithinAt (t : ℝ) hfield
  change HasDerivWithinAt (fun s => multiplierMap (A (projIcc 0 T hT s)))
    (multiplierMap (A' t)) (Icc (0 : ℝ) T) t
  change HasDerivWithinAt (fun s => multiplierMap (A (projIcc 0 T hT s)))
    (multiplierMap (A' (projIcc 0 T hT t))) (Icc (0 : ℝ) T) t at hd
  rwa [projIcc_of_mem hT t.property] at hd


-- @@ L117-121 verbatim
theorem operatorPath_inverse (T : ℝ) (A B : C(Icc (0 : ℝ) T, Field))
    (hAB : ∀ t x v, A t x (B t x v) = v) :
    ∀ t (u : L2), operatorPath T A t (operatorPath T B t u) = u := by
  intro t u
  exact multiplier_inverse (A t) (B t) (hAB t) u


-- @@ L123-127 verbatim
theorem operatorPath_quadratic_upper (T : ℝ) (A : C(Icc (0 : ℝ) T, Field)) (K : ℝ)
    (hA : ∀ t x v, ⟪A t x v, v⟫_ℝ ≤ K * ‖v‖ ^ 2) :
    ∀ t (u : L2), ⟪operatorPath T A t u, u⟫_ℝ ≤ K * ‖u‖^2 := by
  intro t u
  exact multiplier_quadratic_upper (A t) K (hA t) u


-- @@ L129-129 verbatim
end EulerMeanCoefficients
