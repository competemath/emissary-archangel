/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.API.Eval
import LeanCert.Engine.AD.Dyadic
import LeanCert.Engine.Optimization.Gradient


-- @@ L10-17 verbatim
/-!
# Public checked automatic differentiation

This module is the backend-independent boundary for checked derivatives and
gradients. Rational and Dyadic computations return the same public result
shape, retain the requested and selected backend, and share one soundness
contract. Affine AD is deliberately reported as unsupported.
-/


-- @@ L19-19 verbatim
namespace LeanCert


-- @@ L21-21 verbatim
open LeanCert.Core

-- @@ L22-22 verbatim
open LeanCert.Engine


-- @@ L24-30 verbatim
/-- Controls relevant to checked AD. Backend-specific fields are rejected when
an explicitly selected backend cannot honor them. -/
structure ADOptions where
  backend : BackendChoice := .auto
  taylorDepth : Nat := 10
  dyadicPrecision : Int := -53
  deriving Repr, DecidableEq, Inhabited


-- @@ L32-38 verbatim
/-- Backend-independent value-and-derivative result. -/
structure DerivativeOutcome where
  value : IntervalRat
  derivative : IntervalRat
  requested : BackendChoice
  backend : ConcreteBackend
  deriving Repr, DecidableEq


-- @@ L40-45 verbatim
/-- Backend-independent checked gradient result. -/
structure GradientOutcome where
  gradient : List IntervalRat
  requested : BackendChoice
  backend : ConcreteBackend
  deriving Repr, DecidableEq


-- @@ L47-54 verbatim
/-- AD uses Rational for ordinary algebraic expressions and Dyadic for
transcendentals or expressions at risk of exact-denominator growth. -/
def selectAutomaticADBackend (e : Expr) : ConcreteBackend :=
  let stats := automaticIntervalStats e
  if stats.hasNonlinear || stats.denominatorBits > automaticIntervalDenominatorBudget then
    .dyadic
  else
    .rational


-- @@ L56-62 verbatim
private def rationalADConfig (requested : BackendChoice) (options : ADOptions) :
    EvalResult EvalConfig :=
  if requested != .rational || options.dyadicPrecision = -53 then
    .ok { taylorDepth := options.taylorDepth }
  else
    .error (.invalidConfiguration
      "dyadicPrecision is only meaningful for the Dyadic AD backend")


-- @@ L64-68 verbatim
private def dyadicADConfig (options : ADOptions) : EvalResult DyadicConfig :=
  if options.dyadicPrecision ≤ 0 then
    .ok { precision := options.dyadicPrecision, taylorDepth := options.taylorDepth }
  else
    .error (.invalidConfiguration "Dyadic AD precision must be nonpositive")


-- @@ L70-77 verbatim
private theorem dyadicADConfig_precision {options : ADOptions} {cfg : DyadicConfig}
    (hcfg : dyadicADConfig options = .ok cfg) : cfg.precision ≤ 0 := by
  unfold dyadicADConfig at hcfg
  split at hcfg
  · rename_i hprec
    cases hcfg
    exact hprec
  · contradiction


-- @@ L79-91 verbatim
private def evalWithDerivativeRational (e : Expr) (box : List IntervalRat) (idx : Nat)
    (requested : BackendChoice) (options : ADOptions) : EvalResult DerivativeOutcome :=
  match rationalADConfig requested options with
  | .error err => .error err
  | .ok cfg =>
      match evalWithDerivChecked e (intervalEnvOfList box) idx cfg with
      | .error err => .error err
      | .ok result => .ok {
          value := result.val
          derivative := result.der
          requested := requested
          backend := .rational
        }


-- @@ L93-106 verbatim
private def evalWithDerivativeDyadic (e : Expr) (box : List IntervalRat) (idx : Nat)
    (requested : BackendChoice) (options : ADOptions) : EvalResult DerivativeOutcome :=
  match dyadicADConfig options with
  | .error err => .error err
  | .ok cfg =>
      match evalWithDerivDyadicChecked e
          (toDyadicEnv (intervalEnvOfList box) cfg.precision) idx cfg with
      | .error err => .error err
      | .ok result => .ok {
          value := result.val.toIntervalRat
          derivative := result.der.toIntervalRat
          requested := requested
          backend := .dyadic
        }


-- @@ L108-119 verbatim
/-- Checked value and partial derivative over a rational box. -/
def evalWithDerivative (e : Expr) (box : List IntervalRat) (idx : Nat)
    (options : ADOptions := {}) : EvalResult DerivativeOutcome :=
  match options.backend with
  | .auto =>
      match selectAutomaticADBackend e with
      | .rational => evalWithDerivativeRational e box idx .auto options
      | .dyadic => evalWithDerivativeDyadic e box idx .auto options
      | .affine => .error (.unsupportedBackend "checked automatic differentiation with Affine")
  | .rational => evalWithDerivativeRational e box idx .rational options
  | .dyadic => evalWithDerivativeDyadic e box idx .dyadic options
  | .affine => .error (.unsupportedBackend "checked automatic differentiation with Affine")


-- @@ L121-123 verbatim
/-- Checked partial derivative. The value enclosure is retained because it is
often required by downstream monotonicity and Newton workflows. -/
def evalDerivative := evalWithDerivative


-- @@ L125-154 verbatim
private theorem evalWithDerivativeRational_correct {e : Expr} {box : List IntervalRat}
    {idx : Nat} {requested : BackendChoice} {options : ADOptions}
    {outcome : DerivativeOutcome}
    (hsuccess : evalWithDerivativeRational e box idx requested options = .ok outcome)
    {rho : Nat → ℝ} (hrho : BoxEnvMem rho box) {x : ℝ}
    (hx : x ∈ intervalEnvOfList box idx) :
    Expr.eval rho e ∈ outcome.value ∧
      deriv (Expr.evalAlong e rho idx) x ∈ outcome.derivative := by
  unfold evalWithDerivativeRational at hsuccess
  cases hcfg : rationalADConfig requested options with
  | error err => simp [hcfg] at hsuccess
  | ok cfg =>
    simp only [hcfg] at hsuccess
    cases hdual : evalWithDerivChecked e (intervalEnvOfList box) idx cfg with
    | error err => simp [hdual] at hsuccess
    | ok result =>
      simp only [hdual, Except.ok.injEq] at hsuccess
      subst outcome
      have henv : ∀ i, rho i ∈ intervalEnvOfList box i := hrho
      constructor
      · apply evalDualChecked_val_correct e rho
          (mkDualEnv (intervalEnvOfList box) idx) cfg result
        · intro i
          by_cases hi : i = idx
          · subst i
            simpa [mkDualEnv, DualInterval.varActive] using henv idx
          · simpa [mkDualEnv, hi, DualInterval.varPassive] using henv i
        · simpa [evalWithDerivChecked] using hdual
      · exact evalWithDerivChecked_der_correct e rho (intervalEnvOfList box) idx cfg
          result x hx henv hdual


-- @@ L156-193 verbatim
private theorem evalWithDerivativeDyadic_correct {e : Expr} {box : List IntervalRat}
    {idx : Nat} {requested : BackendChoice} {options : ADOptions}
    {outcome : DerivativeOutcome}
    (hsuccess : evalWithDerivativeDyadic e box idx requested options = .ok outcome)
    {rho : Nat → ℝ} (hrho : BoxEnvMem rho box) {x : ℝ}
    (hx : x ∈ intervalEnvOfList box idx) :
    Expr.eval rho e ∈ outcome.value ∧
      deriv (Expr.evalAlong e rho idx) x ∈ outcome.derivative := by
  unfold evalWithDerivativeDyadic at hsuccess
  cases hcfg : dyadicADConfig options with
  | error err => simp [hcfg] at hsuccess
  | ok cfg =>
    simp only [hcfg] at hsuccess
    let rhoD := toDyadicEnv (intervalEnvOfList box) cfg.precision
    cases hdual : evalWithDerivDyadicChecked e rhoD idx cfg with
    | error err => simp [rhoD, hdual] at hsuccess
    | ok result =>
      simp only [rhoD, hdual, Except.ok.injEq] at hsuccess
      subst outcome
      have hprec := dyadicADConfig_precision hcfg
      have henv : ∀ i, rho i ∈ intervalEnvOfList box i := hrho
      have henvD : ∀ i, rho i ∈ rhoD i := fun i =>
        IntervalDyadic.mem_ofIntervalRat (henv i) cfg.precision hprec
      have hxD : x ∈ rhoD idx :=
        IntervalDyadic.mem_ofIntervalRat hx cfg.precision hprec
      constructor
      · apply IntervalDyadic.mem_toIntervalRat.mpr
        apply evalDualDyadicChecked_val_correct e rho
          (mkDualDyadicEnv rhoD idx) cfg result
        · intro i
          by_cases hi : i = idx
          · subst i
            simpa [mkDualDyadicEnv, DualIntervalDyadic.varActive] using henvD idx
          · simpa [mkDualDyadicEnv, hi, DualIntervalDyadic.varPassive] using henvD i
        · simpa [evalWithDerivDyadicChecked] using hdual
      · apply IntervalDyadic.mem_toIntervalRat.mpr
        exact evalWithDerivDyadicChecked_der_correct e rho rhoD idx cfg result
          x hxD henvD hdual


-- @@ L195-222 verbatim
/-- A successful public checked AD computation encloses both the expression
value and the selected true partial derivative. -/
theorem evalWithDerivative_correct {e : Expr} {box : List IntervalRat} {idx : Nat}
    {options : ADOptions} {outcome : DerivativeOutcome}
    (hsuccess : evalWithDerivative e box idx options = .ok outcome)
    {rho : Nat → ℝ} (hrho : BoxEnvMem rho box) {x : ℝ}
    (hx : x ∈ intervalEnvOfList box idx) :
    Expr.eval rho e ∈ outcome.value ∧
      deriv (Expr.evalAlong e rho idx) x ∈ outcome.derivative := by
  unfold evalWithDerivative at hsuccess
  cases hchoice : options.backend with
  | auto =>
    simp only [hchoice] at hsuccess
    cases hselected : selectAutomaticADBackend e with
    | rational =>
      simp only [hselected] at hsuccess
      exact evalWithDerivativeRational_correct hsuccess hrho hx
    | dyadic =>
      simp only [hselected] at hsuccess
      exact evalWithDerivativeDyadic_correct hsuccess hrho hx
    | affine => simp [hselected] at hsuccess
  | rational =>
    simp only [hchoice] at hsuccess
    exact evalWithDerivativeRational_correct hsuccess hrho hx
  | dyadic =>
    simp only [hchoice] at hsuccess
    exact evalWithDerivativeDyadic_correct hsuccess hrho hx
  | affine => simp [hchoice] at hsuccess


-- @@ L224-231 verbatim
private def evalGradientRational (e : Expr) (box : List IntervalRat)
    (requested : BackendChoice) (options : ADOptions) : EvalResult GradientOutcome :=
  match rationalADConfig requested options with
  | .error err => .error err
  | .ok cfg =>
      match Optimization.gradientIntervalChecked e box cfg with
      | .error err => .error err
      | .ok gradient => .ok { gradient, requested, backend := .rational }


-- @@ L233-244 verbatim
private def evalGradientDyadic (e : Expr) (box : List IntervalRat)
    (requested : BackendChoice) (options : ADOptions) : EvalResult GradientOutcome :=
  match dyadicADConfig options with
  | .error err => .error err
  | .ok cfg =>
      match gradientIntervalDyadicCheckedOfRat e (intervalEnvOfList box) box.length cfg with
      | .error err => .error err
      | .ok gradient => .ok {
          gradient := gradient.map IntervalDyadic.toIntervalRat
          requested := requested
          backend := .dyadic
        }


-- @@ L246-257 verbatim
/-- Compute all partial derivatives corresponding to the supplied box. -/
def evalGradient (e : Expr) (box : List IntervalRat)
    (options : ADOptions := {}) : EvalResult GradientOutcome :=
  match options.backend with
  | .auto =>
      match selectAutomaticADBackend e with
      | .rational => evalGradientRational e box .auto options
      | .dyadic => evalGradientDyadic e box .auto options
      | .affine => .error (.unsupportedBackend "checked automatic differentiation with Affine")
  | .rational => evalGradientRational e box .rational options
  | .dyadic => evalGradientDyadic e box .dyadic options
  | .affine => .error (.unsupportedBackend "checked automatic differentiation with Affine")


-- @@ L259-280 verbatim
private theorem evalGradientRational_correct {e : Expr} {box : List IntervalRat}
    {requested : BackendChoice} {options : ADOptions} {outcome : GradientOutcome}
    (hsuccess : evalGradientRational e box requested options = .ok outcome)
    {rho : Nat → ℝ} (hrho : BoxEnvMem rho box) :
    List.Forall₂ (fun i dI => deriv (Expr.evalAlong e rho i) (rho i) ∈ dI)
      (List.range box.length) outcome.gradient := by
  unfold evalGradientRational at hsuccess
  cases hcfg : rationalADConfig requested options with
  | error err => simp [hcfg] at hsuccess
  | ok cfg =>
    simp only [hcfg] at hsuccess
    cases hgradient : Optimization.gradientIntervalChecked e box cfg with
    | error err => simp [hgradient] at hsuccess
    | ok gradient =>
      simp only [hgradient, Except.ok.injEq] at hsuccess
      subst outcome
      apply Optimization.gradientIntervalChecked_correct e box cfg rho
      · intro i
        exact hrho.get i.val i.isLt
      · intro i hi
        exact hrho.eq_zero i hi
      · exact hgradient


-- @@ L282-302 verbatim
private theorem evalGradientDyadic_correct {e : Expr} {box : List IntervalRat}
    {requested : BackendChoice} {options : ADOptions} {outcome : GradientOutcome}
    (hsuccess : evalGradientDyadic e box requested options = .ok outcome)
    {rho : Nat → ℝ} (hrho : BoxEnvMem rho box) :
    List.Forall₂ (fun i dI => deriv (Expr.evalAlong e rho i) (rho i) ∈ dI)
      (List.range box.length) outcome.gradient := by
  unfold evalGradientDyadic at hsuccess
  cases hcfg : dyadicADConfig options with
  | error err => simp [hcfg] at hsuccess
  | ok cfg =>
    simp only [hcfg] at hsuccess
    cases hgradient : gradientIntervalDyadicCheckedOfRat e
        (intervalEnvOfList box) box.length cfg with
    | error err => simp [hgradient] at hsuccess
    | ok gradient =>
      simp only [hgradient, Except.ok.injEq] at hsuccess
      subst outcome
      have hnative := gradientIntervalDyadicCheckedOfRat_correct e rho
        (intervalEnvOfList box) box.length cfg (fun i => hrho i) gradient hgradient
      rw [List.forall₂_map_right_iff]
      exact hnative.imp fun _ _ hmem => IntervalDyadic.mem_toIntervalRat.mpr hmem


-- @@ L304-330 verbatim
/-- A successful public gradient computation encloses the corresponding true
partial derivative in each coordinate. -/
theorem evalGradient_correct {e : Expr} {box : List IntervalRat}
    {options : ADOptions} {outcome : GradientOutcome}
    (hsuccess : evalGradient e box options = .ok outcome)
    {rho : Nat → ℝ} (hrho : BoxEnvMem rho box) :
    List.Forall₂ (fun i dI => deriv (Expr.evalAlong e rho i) (rho i) ∈ dI)
      (List.range box.length) outcome.gradient := by
  unfold evalGradient at hsuccess
  cases hchoice : options.backend with
  | auto =>
    simp only [hchoice] at hsuccess
    cases hselected : selectAutomaticADBackend e with
    | rational =>
      simp only [hselected] at hsuccess
      exact evalGradientRational_correct hsuccess hrho
    | dyadic =>
      simp only [hselected] at hsuccess
      exact evalGradientDyadic_correct hsuccess hrho
    | affine => simp [hselected] at hsuccess
  | rational =>
    simp only [hchoice] at hsuccess
    exact evalGradientRational_correct hsuccess hrho
  | dyadic =>
    simp only [hchoice] at hsuccess
    exact evalGradientDyadic_correct hsuccess hrho
  | affine => simp [hchoice] at hsuccess


-- @@ L332-332 verbatim
end LeanCert
