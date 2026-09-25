module
public import SpherePacking.Dim24.MagicFunction.A.Defs
public import SpherePacking.Dim24.MagicFunction.B.Defs.Eigenfunction
public import SpherePacking.ForMathlib.Fourier
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier



-- @@ L8-20 verbatim
/-!
# Definitions of `f` and `scaledF`

This file defines the auxiliary Schwartz function `f` and its scaled version `scaledF`, used in
the dimension-24 LP bound.

## Main definitions
* `f`
* `scaledF`

## References
`dim_24.tex`, Section 4 (`sec:proof`).
-/


-- @@ L22-22 verbatim
open scoped FourierTransform ENNReal SchwartzMap


-- @@ L24-24 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L26-26 verbatim
namespace SpherePacking.Dim24


-- @@ L28-31 expanded
/-- The auxiliary function `f` (called `f` in `dim_24.tex`). -/
@[expose]
public noncomputable def f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ) :=
  (-((Real.pi : ℂ) * Complex.I) / (113218560 : ℂ)) • a -
    (Complex.I / ((262080 : ℂ) * (Real.pi : ℂ))) • b


-- @@ L33-40 expanded
/-- A scaled version of `f` satisfying the radius-1 Cohn-Elkies hypotheses.

We take `scaledF(x) = f(2 • x)`.
-/
@[expose]
public noncomputable def scaledF : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ) :=
  let c : ℝ := 2
  let A : EuclideanSpace ℝ (Fin 24) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 24) :=
    LinearEquiv.smulOfNeZero (K := ℝ) (M := EuclideanSpace ℝ (Fin 24)) c two_ne_zero
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv f


-- @@ L42-42 verbatim
end SpherePacking.Dim24
