module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

import SpherePacking.ForMathlib.GaussianRexpIntegral


-- @@ L8-13 verbatim
/-!
# Integrability of Gaussian `rexp`

This file proves integrability of the real Gaussian `x ↦ exp (-π * ‖x‖^2 / s)` on `ℝ^(2k)` for
`s > 0`, and records the specialization to `ℝ⁸` used in the dimension-8 development.
-/


-- @@ L15-15 verbatim
namespace SpherePacking.ForMathlib


-- @@ L17-17 verbatim
open Real MeasureTheory


-- @@ L19-19 verbatim
local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)


-- @@ L21-27 verbatim
/-- The real Gaussian `x ↦ exp (-π * ‖x‖^2 / s)` is integrable on `ℝ^(2k)` for `s > 0`. -/
public lemma integrable_gaussian_rexp_even (k : ℕ) (s : ℝ) (hs : 0 < s) :
    Integrable (fun x : EuclideanSpace ℝ (Fin (2 * k)) ↦ rexp (-π * (‖x‖ ^ 2) / s))
      (volume : Measure (EuclideanSpace ℝ (Fin (2 * k)))) := by
  refine MeasureTheory.Integrable.of_integral_ne_zero (μ := volume) ?_
  rw [integral_gaussian_rexp_even (k := k) (s := s) hs]
  exact pow_ne_zero k hs.ne'


-- @@ L29-32 verbatim
/-- The real Gaussian `x ↦ exp (-π * ‖x‖^2 / s)` is integrable on `ℝ⁸` for `s > 0`. -/
public lemma integrable_gaussian_rexp (s : ℝ) (hs : 0 < s) :
    Integrable (fun x : ℝ⁸ ↦ rexp (-π * (‖x‖ ^ 2) / s)) (volume : Measure ℝ⁸) := by
  simpa using integrable_gaussian_rexp_even (k := 4) s hs


-- @@ L34-34 verbatim
end SpherePacking.ForMathlib
