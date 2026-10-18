/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.API.Eval


-- @@ L8-14 verbatim
/-!
# Checked backend-native evaluation

These APIs are for clients that need a backend's native result type. They keep
the same checked failure behavior and box semantics as `LeanCert.evalInterval`.
Ordinary clients should prefer the backend-independent public façade.
-/


-- @@ L16-16 verbatim
namespace LeanCert.Backend


-- @@ L18-18 verbatim
open LeanCert

-- @@ L19-19 verbatim
open LeanCert.Core

-- @@ L20-20 verbatim
open LeanCert.Engine

-- @@ L21-21 verbatim
open LeanCert.Engine.Affine


-- @@ L23-23 verbatim
namespace Rational


-- @@ L25-27 verbatim
/-- Evaluate with the checked rational backend and retain its native interval. -/
def eval (e : Expr) (box : List IntervalRat) : EvalResult IntervalRat :=
  evalIntervalChecked e (intervalEnvOfList box)


-- @@ L29-33 verbatim
/-- Successful native rational evaluation encloses every point of the box. -/
theorem eval_correct {e : Expr} {box : List IntervalRat} {result : IntervalRat}
    (hsuccess : eval e box = .ok result) {rho : Nat → ℝ}
    (hrho : BoxEnvMem rho box) : Expr.eval rho e ∈ result := by
  exact evalIntervalChecked_correct e (intervalEnvOfList box) result hsuccess rho hrho


-- @@ L35-35 verbatim
end Rational


-- @@ L37-37 verbatim
namespace Dyadic


-- @@ L39-51 verbatim
/-- Evaluate with the checked dyadic backend and retain its native interval. -/
def eval (e : Expr) (box : List IntervalRat)
    (precision : PrecisionOptions := {}) : EvalResult IntervalDyadic :=
  if precision.dyadicExponent > 0 then
    .error (.invalidConfiguration
      "dyadicExponent must be nonpositive for certified outward rounding")
  else
    let cfg : DyadicConfig := {
      precision := precision.dyadicExponent
      taylorDepth := precision.taylorDepth
    }
    evalIntervalDyadicChecked e
      (toDyadicEnv (intervalEnvOfList box) precision.dyadicExponent) cfg


-- @@ L53-72 verbatim
/-- Successful native dyadic evaluation encloses every point of the box. -/
theorem eval_correct {e : Expr} {box : List IntervalRat}
    {precision : PrecisionOptions} {result : IntervalDyadic}
    (hsuccess : eval e box precision = .ok result) {rho : Nat → ℝ}
    (hrho : BoxEnvMem rho box) : Expr.eval rho e ∈ result := by
  have hprec : precision.dyadicExponent ≤ 0 := by
    by_contra h
    have hpos : precision.dyadicExponent > 0 := lt_of_not_ge h
    simp [eval, hpos] at hsuccess
  let cfg : DyadicConfig := {
    precision := precision.dyadicExponent
    taylorDepth := precision.taylorDepth
  }
  let rhoDyadic := toDyadicEnv (intervalEnvOfList box) precision.dyadicExponent
  have hrhoDyadic : envMemDyadic rho rhoDyadic := by
    intro i
    exact IntervalDyadic.mem_ofIntervalRat (hrho i) precision.dyadicExponent hprec
  apply evalIntervalDyadicChecked_correct e rho rhoDyadic hrhoDyadic cfg hprec result
  simpa [eval, cfg, rhoDyadic, show ¬precision.dyadicExponent > 0 from not_lt.mpr hprec]
    using hsuccess


-- @@ L74-74 verbatim
end Dyadic


-- @@ L76-76 verbatim
namespace Affine


-- @@ L78-85 verbatim
/-- Evaluate with the checked affine backend and retain its native form. -/
def eval (e : Expr) (box : List IntervalRat)
    (precision : PrecisionOptions := {}) : EvalResult AffineForm :=
  let cfg : AffineConfig := {
    taylorDepth := precision.taylorDepth
    maxNoiseSymbols := precision.maxNoiseSymbols
  }
  evalIntervalAffineChecked e (toAffineEnv box) cfg


-- @@ L87-101 verbatim
/-- Successful native affine evaluation encloses every point of the box after
conversion to an ordinary rational interval. -/
theorem eval_correct {e : Expr} {box : List IntervalRat}
    {precision : PrecisionOptions} {result : AffineForm}
    (hsuccess : eval e box precision = .ok result) {rho : Nat → ℝ}
    (hrho : BoxEnvMem rho box) : Expr.eval rho e ∈ result.toInterval := by
  obtain ⟨eps, hvalid, henv⟩ := exists_noise_toAffineEnv box rho
    (fun i hi => hrho.get i hi) (fun i hi => hrho.eq_zero i hi)
  let cfg : AffineConfig := {
    taylorDepth := precision.taylorDepth
    maxNoiseSymbols := precision.maxNoiseSymbols
  }
  have hnative := evalIntervalAffineChecked_correct e rho (toAffineEnv box) eps
    hvalid henv cfg result (by simpa [eval, cfg] using hsuccess)
  exact AffineForm.mem_toInterval_weak hvalid hnative


-- @@ L103-103 verbatim
end Affine


-- @@ L105-105 verbatim
end LeanCert.Backend
