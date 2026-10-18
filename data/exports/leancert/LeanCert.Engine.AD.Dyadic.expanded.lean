/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Engine.AD.DomainChecked
import LeanCert.Engine.IntervalEvalDyadic


-- @@ L9-21 verbatim
/-!
# Domain-aware automatic differentiation with Dyadic intervals

This module is the bounded-denominator counterpart of `AD.DomainChecked`.
Polynomial dual arithmetic is performed with Dyadic endpoints and outward
rounding after every addition and multiplication.  Transcendental values use
the same verified rational Taylor kernels as the Dyadic value evaluator and
are rounded back to Dyadic endpoints.

The public entry points are checked: unsupported syntax, invalid reciprocal or
logarithm domains, and positive rounding precisions return `EvalError` rather
than a finite interval.
-/


-- @@ L23-23 verbatim
namespace LeanCert.Engine


-- @@ L25-25 verbatim
open LeanCert.Core


-- @@ L27-31 verbatim
/-- A value interval and one directional derivative interval, both Dyadic. -/
structure DualIntervalDyadic where
  val : IntervalDyadic
  der : IntervalDyadic
  deriving Repr


-- @@ L33-34 verbatim
instance : Inhabited DualIntervalDyadic where
  default := ⟨default, default⟩


-- @@ L36-37 verbatim
/-- An environment of Dyadic dual intervals. -/
abbrev DualDyadicEnv := Nat → DualIntervalDyadic


-- @@ L39-39 verbatim
namespace DualIntervalDyadic


-- @@ L41-41 verbatim
private def zero : IntervalDyadic := IntervalDyadic.singleton Core.Dyadic.zero

-- @@ L42-42 verbatim
private def one : IntervalDyadic := IntervalDyadic.singleton (Core.Dyadic.ofInt 1)


-- @@ L44-45 verbatim
def const (q : ℚ) (cfg : DyadicConfig := {}) : DualIntervalDyadic :=
  ⟨IntervalDyadic.ofIntervalRat (IntervalRat.singleton q) cfg.precision, zero⟩


-- @@ L47-47 verbatim
def varActive (I : IntervalDyadic) : DualIntervalDyadic := ⟨I, one⟩

-- @@ L48-48 verbatim
def varPassive (I : IntervalDyadic) : DualIntervalDyadic := ⟨I, zero⟩


-- @@ L50-52 verbatim
def add (a b : DualIntervalDyadic) (cfg : DyadicConfig := {}) : DualIntervalDyadic :=
  ⟨IntervalDyadic.addRounded a.val b.val cfg.precision,
   IntervalDyadic.addRounded a.der b.der cfg.precision⟩


-- @@ L54-59 verbatim
def mul (a b : DualIntervalDyadic) (cfg : DyadicConfig := {}) : DualIntervalDyadic :=
  ⟨IntervalDyadic.mulRounded a.val b.val cfg.precision,
   IntervalDyadic.addRounded
     (IntervalDyadic.mulRounded a.der b.val cfg.precision)
     (IntervalDyadic.mulRounded a.val b.der cfg.precision)
     cfg.precision⟩


-- @@ L61-62 verbatim
def neg (a : DualIntervalDyadic) : DualIntervalDyadic :=
  ⟨IntervalDyadic.neg a.val, IntervalDyadic.neg a.der⟩


-- @@ L64-67 verbatim
def inv (a : DualIntervalDyadic) (cfg : DyadicConfig := {}) : DualIntervalDyadic :=
  let invVal := invIntervalDyadic a.val cfg
  let invSq := IntervalDyadic.mulRounded invVal invVal cfg.precision
  ⟨invVal, IntervalDyadic.neg (IntervalDyadic.mulRounded a.der invSq cfg.precision)⟩


-- @@ L69-71 verbatim
def exp (a : DualIntervalDyadic) (cfg : DyadicConfig := {}) : DualIntervalDyadic :=
  let value := expIntervalDyadic a.val cfg
  ⟨value, IntervalDyadic.mulRounded value a.der cfg.precision⟩


-- @@ L73-75 verbatim
def sin (a : DualIntervalDyadic) (cfg : DyadicConfig := {}) : DualIntervalDyadic :=
  ⟨sinIntervalDyadic a.val cfg,
   IntervalDyadic.mulRounded (cosIntervalDyadic a.val cfg) a.der cfg.precision⟩


-- @@ L77-80 verbatim
def cos (a : DualIntervalDyadic) (cfg : DyadicConfig := {}) : DualIntervalDyadic :=
  ⟨cosIntervalDyadic a.val cfg,
   IntervalDyadic.mulRounded (IntervalDyadic.neg (sinIntervalDyadic a.val cfg))
     a.der cfg.precision⟩


-- @@ L82-84 verbatim
def log (a : DualIntervalDyadic) (cfg : DyadicConfig := {}) : DualIntervalDyadic :=
  ⟨logIntervalDyadic a.val cfg,
   IntervalDyadic.mulRounded (invIntervalDyadic a.val cfg) a.der cfg.precision⟩


-- @@ L86-86 verbatim
end DualIntervalDyadic

-- @@ L87-87 verbatim
end LeanCert.Engine


-- @@ L89-89 verbatim
namespace LeanCert.Internal.AD.Dyadic


-- @@ L91-91 verbatim
open LeanCert.Core LeanCert.Engine


-- @@ L93-108 verbatim
/-- Total computational kernel.  Sound public use goes through the checked
entry points below. -/
def evalTotal (e : Expr) (rho : DualDyadicEnv) (cfg : DyadicConfig := {}) :
    DualIntervalDyadic :=
  match e with
  | .const q => DualIntervalDyadic.const q cfg
  | .var i => rho i
  | .add a b => DualIntervalDyadic.add (evalTotal a rho cfg) (evalTotal b rho cfg) cfg
  | .mul a b => DualIntervalDyadic.mul (evalTotal a rho cfg) (evalTotal b rho cfg) cfg
  | .neg a => DualIntervalDyadic.neg (evalTotal a rho cfg)
  | .inv a => DualIntervalDyadic.inv (evalTotal a rho cfg) cfg
  | .exp a => DualIntervalDyadic.exp (evalTotal a rho cfg) cfg
  | .sin a => DualIntervalDyadic.sin (evalTotal a rho cfg) cfg
  | .cos a => DualIntervalDyadic.cos (evalTotal a rho cfg) cfg
  | .log a => DualIntervalDyadic.log (evalTotal a rho cfg) cfg
  | _ => default


-- @@ L110-110 verbatim
end LeanCert.Internal.AD.Dyadic


-- @@ L112-112 verbatim
namespace LeanCert.Engine


-- @@ L114-114 verbatim
open LeanCert.Core


-- @@ L116-117 verbatim
/-- Value projection of a Dyadic dual environment. -/
def DualDyadicEnv.values (rho : DualDyadicEnv) : IntervalDyadicEnv := fun i => (rho i).val


-- @@ L119-122 verbatim
/-- Dual environment selecting coordinate `idx`. -/
def mkDualDyadicEnv (rho : IntervalDyadicEnv) (idx : Nat) : DualDyadicEnv :=
  fun i => if i = idx then DualIntervalDyadic.varActive (rho i)
    else DualIntervalDyadic.varPassive (rho i)


-- @@ L124-129 verbatim
@[simp] theorem mkDualDyadicEnv_values (rho : IntervalDyadicEnv) (idx : Nat) :
    (mkDualDyadicEnv rho idx).values = rho := by
  funext i
  by_cases hi : i = idx <;>
    simp [mkDualDyadicEnv, DualDyadicEnv.values, hi,
      DualIntervalDyadic.varActive, DualIntervalDyadic.varPassive]


-- @@ L131-136 verbatim
/-- The deliberately small v1 Dyadic AD fragment. -/
def checkDyadicADFragment : Expr → Bool
  | .const _ | .var _ => true
  | .add a b | .mul a b => checkDyadicADFragment a && checkDyadicADFragment b
  | .neg a | .inv a | .exp a | .sin a | .cos a | .log a => checkDyadicADFragment a
  | _ => false


-- @@ L138-140 verbatim
/-- Box-dependent domain check for the Dyadic AD kernel. -/
def checkDyadicADDomain (e : Expr) (rho : DualDyadicEnv) (cfg : DyadicConfig := {}) : Bool :=
  checkDyadicADFragment e && (LeanCert.Internal.Dyadic.evalCached e rho.values cfg).2


-- @@ L142-148 verbatim
/-- Explain the first failed support or domain check. -/
def diagnoseDyadicADFailure (e : Expr) (rho : DualDyadicEnv)
    (cfg : DyadicConfig := {}) : EvalError :=
  if !checkDyadicADFragment e then
    .unsupportedFeature "Dyadic automatic differentiation"
  else
    diagnoseEvalIntervalDyadicFailure e rho.values cfg


-- @@ L150-159 verbatim
/-- Checked Dyadic dual evaluation. -/
def evalDualDyadicChecked (e : Expr) (rho : DualDyadicEnv) (cfg : DyadicConfig := {}) :
    EvalResult DualIntervalDyadic :=
  if cfg.precision ≤ 0 then
    if checkDyadicADDomain e rho cfg then
      .ok (LeanCert.Internal.AD.Dyadic.evalTotal e rho cfg)
    else
      .error (diagnoseDyadicADFailure e rho cfg)
  else
    .error (.invalidConfiguration "Dyadic AD precision must be nonpositive")


-- @@ L161-164 verbatim
/-- Checked value-and-derivative evaluation along coordinate `idx`. -/
def evalWithDerivDyadicChecked (e : Expr) (rho : IntervalDyadicEnv) (idx : Nat)
    (cfg : DyadicConfig := {}) : EvalResult DualIntervalDyadic :=
  evalDualDyadicChecked e (mkDualDyadicEnv rho idx) cfg


-- @@ L166-169 verbatim
/-- Checked Dyadic derivative enclosure along coordinate `idx`. -/
def derivIntervalDyadicChecked (e : Expr) (rho : IntervalDyadicEnv) (idx : Nat)
    (cfg : DyadicConfig := {}) : EvalResult IntervalDyadic :=
  return (← evalWithDerivDyadicChecked e rho idx cfg).der


-- @@ L171-174 verbatim
/-- Checked Dyadic derivative enclosure for a single-variable expression. -/
def derivIntervalDyadicChecked1 (e : Expr) (I : IntervalDyadic)
    (cfg : DyadicConfig := {}) : EvalResult IntervalDyadic :=
  derivIntervalDyadicChecked e (fun _ => I) 0 cfg


-- @@ L176-182 verbatim
/-- Convenience boundary for callers whose boxes use rational endpoints. -/
def derivIntervalDyadicCheckedOfRat (e : Expr) (rho : IntervalEnv) (idx : Nat)
    (cfg : DyadicConfig := {}) : EvalResult IntervalDyadic :=
  if cfg.precision ≤ 0 then
    derivIntervalDyadicChecked e (toDyadicEnv rho cfg.precision) idx cfg
  else
    .error (.invalidConfiguration "Dyadic AD precision must be nonpositive")


-- @@ L184-187 verbatim
/-- Single-variable rational-input convenience boundary. -/
def derivIntervalDyadicChecked1OfRat (e : Expr) (I : IntervalRat)
    (cfg : DyadicConfig := {}) : EvalResult IntervalDyadic :=
  derivIntervalDyadicCheckedOfRat e (fun _ => I) 0 cfg


-- @@ L189-210 verbatim
/-- The value projection of the dual kernel is exactly the ordinary Dyadic
value kernel. -/
theorem evalTotalDyadic_val_of_fragment (e : Expr) (rho : DualDyadicEnv)
    (cfg : DyadicConfig) (hsupp : checkDyadicADFragment e = true) :
    (LeanCert.Internal.AD.Dyadic.evalTotal e rho cfg).val =
      LeanCert.Internal.Dyadic.evalUnchecked e rho.values cfg := by
  induction e with
  | const | var =>
      simp [LeanCert.Internal.AD.Dyadic.evalTotal, LeanCert.Internal.Dyadic.evalUnchecked,
        DualIntervalDyadic.const, DualDyadicEnv.values]
  | add a b iha ihb | mul a b iha ihb =>
      simp only [checkDyadicADFragment, Bool.and_eq_true] at hsupp
      simp [LeanCert.Internal.AD.Dyadic.evalTotal, LeanCert.Internal.Dyadic.evalUnchecked,
        DualIntervalDyadic.add, DualIntervalDyadic.mul, IntervalDyadic.addRounded,
        IntervalDyadic.mulRounded, iha hsupp.1, ihb hsupp.2]
  | neg a ih | inv a ih | exp a ih | sin a ih | cos a ih | log a ih =>
      simp only [checkDyadicADFragment] at hsupp
      simp [LeanCert.Internal.AD.Dyadic.evalTotal, LeanCert.Internal.Dyadic.evalUnchecked,
        DualIntervalDyadic.neg, DualIntervalDyadic.inv, DualIntervalDyadic.exp,
        DualIntervalDyadic.sin, DualIntervalDyadic.cos, DualIntervalDyadic.log, ih hsupp]
  | atan | arsinh | atanh | sinc | erf | sinh | cosh | tanh | sqrt | namedConst =>
      simp [checkDyadicADFragment] at hsupp


-- @@ L212-233 verbatim
private theorem evalDualDyadicChecked_facts {e : Expr} {rho : DualDyadicEnv}
    {cfg : DyadicConfig} {D : DualIntervalDyadic}
    (hok : evalDualDyadicChecked e rho cfg = .ok D) :
    cfg.precision ≤ 0 ∧ checkDyadicADFragment e = true ∧
      evalDomainValidDyadic e rho.values cfg ∧
      D = LeanCert.Internal.AD.Dyadic.evalTotal e rho cfg := by
  simp only [evalDualDyadicChecked] at hok
  split at hok
  · rename_i hprec
    split at hok
    · rename_i hcheck
      have hparts : checkDyadicADFragment e = true ∧
          (LeanCert.Internal.Dyadic.evalCached e rho.values cfg).2 = true := by
        simpa only [checkDyadicADDomain, Bool.and_eq_true] using hcheck
      have hdomainCheck : checkDomainValidDyadic e rho.values cfg = true := by
        rw [← evalIntervalDyadicCached_snd e rho.values cfg]
        exact hparts.2
      exact ⟨hprec, hparts.1,
        checkDomainValidDyadic_correct e rho.values cfg hdomainCheck,
        (Except.ok.inj hok).symm⟩
    · contradiction
  · contradiction


-- @@ L235-242 verbatim
private theorem evalTotalDyadic_val_correct_of_facts (e : Expr)
    (rhoReal : Nat → ℝ) (rho : DualDyadicEnv) (cfg : DyadicConfig)
    (hprec : cfg.precision ≤ 0) (hsupp : checkDyadicADFragment e = true)
    (hdom : evalDomainValidDyadic e rho.values cfg)
    (hrho : ∀ i, rhoReal i ∈ (rho i).val) :
    Expr.eval rhoReal e ∈ (LeanCert.Internal.AD.Dyadic.evalTotal e rho cfg).val := by
  rw [evalTotalDyadic_val_of_fragment e rho cfg hsupp]
  exact evalIntervalDyadic_correct_of_domain e rhoReal rho.values hrho cfg hprec hdom


-- @@ L244-251 verbatim
/-- Golden theorem for successful checked Dyadic dual evaluation. -/
theorem evalDualDyadicChecked_val_correct (e : Expr)
    (rhoReal : Nat → ℝ) (rho : DualDyadicEnv) (cfg : DyadicConfig)
    (D : DualIntervalDyadic) (hrho : ∀ i, rhoReal i ∈ (rho i).val)
    (hok : evalDualDyadicChecked e rho cfg = .ok D) :
    Expr.eval rhoReal e ∈ D.val := by
  obtain ⟨hprec, hsupp, hdom, rfl⟩ := evalDualDyadicChecked_facts hok
  exact evalTotalDyadic_val_correct_of_facts e rhoReal rho cfg hprec hsupp hdom hrho


-- @@ L253-261 verbatim
private theorem updateVar_mem_mkDualDyadicEnv_val
    (rhoReal : Nat → ℝ) (rho : IntervalDyadicEnv) (idx : Nat)
    (x : ℝ) (hx : x ∈ rho idx) (hrho : ∀ i, rhoReal i ∈ rho i) :
    ∀ i, Expr.updateVar rhoReal idx x i ∈ (mkDualDyadicEnv rho idx i).val := by
  intro i
  by_cases hi : i = idx
  · subst i
    simpa [Expr.updateVar, mkDualDyadicEnv, DualIntervalDyadic.varActive] using hx
  · simpa [Expr.updateVar, mkDualDyadicEnv, hi, DualIntervalDyadic.varPassive] using hrho i


-- @@ L263-336 verbatim
private theorem evalAlong_differentiableAt_of_dyadic_facts (e : Expr)
    (rhoReal : Nat → ℝ) (rho : IntervalDyadicEnv) (idx : Nat) (cfg : DyadicConfig)
    (x : ℝ) (hx : x ∈ rho idx) (hrho : ∀ i, rhoReal i ∈ rho i)
    (hprec : cfg.precision ≤ 0) (hsupp : checkDyadicADFragment e = true)
    (hdom : evalDomainValidDyadic e rho cfg) :
    DifferentiableAt ℝ (Expr.evalAlong e rhoReal idx) x := by
  have hmem := updateVar_mem_mkDualDyadicEnv_val rhoReal rho idx x hx hrho
  have hmemValue : envMemDyadic (Expr.updateVar rhoReal idx x) rho := by
    intro i
    by_cases hi : i = idx
    · subst i
      simpa [Expr.updateVar] using hx
    · simpa [Expr.updateVar, hi] using hrho i
  induction e with
  | const => exact differentiableAt_const _
  | var i =>
      by_cases hi : i = idx
      · subst i
        simpa only [Expr.evalAlong_var_active] using differentiableAt_id
      · simpa only [Expr.evalAlong_var_passive _ _ _ hi] using
          differentiableAt_const (c := rhoReal i)
  | add a b iha ihb =>
      simp only [checkDyadicADFragment, Bool.and_eq_true] at hsupp
      simp only [evalDomainValidDyadic] at hdom
      simpa only [Expr.evalAlong_add_pi] using
        (iha hsupp.1 hdom.1).add (ihb hsupp.2 hdom.2)
  | mul a b iha ihb =>
      simp only [checkDyadicADFragment, Bool.and_eq_true] at hsupp
      simp only [evalDomainValidDyadic] at hdom
      simpa only [Expr.evalAlong_mul_pi] using
        (iha hsupp.1 hdom.1).mul (ihb hsupp.2 hdom.2)
  | neg a ih =>
      simp only [checkDyadicADFragment] at hsupp
      simp only [evalDomainValidDyadic] at hdom
      simpa only [Expr.evalAlong_neg_pi] using (ih hsupp hdom).neg
  | inv a ih =>
      simp only [checkDyadicADFragment] at hsupp
      simp only [evalDomainValidDyadic] at hdom
      have hval := evalIntervalDyadic_correct_of_domain a
        (Expr.updateVar rhoReal idx x) rho hmemValue cfg hprec hdom.1
      have hne : Expr.evalAlong a rhoReal idx x ≠ 0 := by
        rw [Expr.evalAlong_eq]
        intro hz
        rw [hz] at hval
        rcases hdom.2 with hpos | hneg
        · exact (not_lt_of_ge (IntervalDyadic.mem_toIntervalRat.mp hval).1)
            (by exact_mod_cast hpos)
        · exact (not_lt_of_ge (IntervalDyadic.mem_toIntervalRat.mp hval).2)
            (by exact_mod_cast hneg)
      exact DifferentiableAt.inv (ih hsupp hdom.1) hne
  | exp a ih =>
      simp only [checkDyadicADFragment] at hsupp
      simp only [evalDomainValidDyadic] at hdom
      exact Real.differentiableAt_exp.comp x (ih hsupp hdom)
  | sin a ih =>
      simp only [checkDyadicADFragment] at hsupp
      simp only [evalDomainValidDyadic] at hdom
      exact Real.differentiableAt_sin.comp x (ih hsupp hdom)
  | cos a ih =>
      simp only [checkDyadicADFragment] at hsupp
      simp only [evalDomainValidDyadic] at hdom
      exact Real.differentiableAt_cos.comp x (ih hsupp hdom)
  | log a ih =>
      simp only [checkDyadicADFragment] at hsupp
      simp only [evalDomainValidDyadic] at hdom
      have hval := evalIntervalDyadic_correct_of_domain a
        (Expr.updateVar rhoReal idx x) rho hmemValue cfg hprec hdom.1
      have hpos : 0 < Expr.evalAlong a rhoReal idx x := by
        rw [Expr.evalAlong_eq]
        exact lt_of_lt_of_le (by exact_mod_cast hdom.2)
          (IntervalDyadic.mem_toIntervalRat.mp hval).1
      exact (Real.differentiableAt_log (ne_of_gt hpos)).comp x (ih hsupp hdom.1)
  | atan | arsinh | atanh | sinc | erf | sinh | cosh | tanh | sqrt | namedConst =>
      simp [checkDyadicADFragment] at hsupp


-- @@ L338-348 verbatim
/-- Successful checked Dyadic indexed AD proves differentiability throughout
the selected input interval. -/
theorem evalWithDerivDyadicChecked_differentiableAt (e : Expr)
    (rhoReal : Nat → ℝ) (rho : IntervalDyadicEnv) (idx : Nat) (cfg : DyadicConfig)
    (D : DualIntervalDyadic) (x : ℝ) (hx : x ∈ rho idx)
    (hrho : ∀ i, rhoReal i ∈ rho i)
    (hok : evalWithDerivDyadicChecked e rho idx cfg = .ok D) :
    DifferentiableAt ℝ (Expr.evalAlong e rhoReal idx) x := by
  obtain ⟨hprec, hsupp, hdom, _⟩ := evalDualDyadicChecked_facts hok
  exact evalAlong_differentiableAt_of_dyadic_facts e rhoReal rho idx cfg x hx hrho
    hprec hsupp (by simpa using hdom)


-- @@ L350-549 verbatim
set_option maxHeartbeats 800000 in
private theorem evalTotalDyadic_der_correct_of_facts (e : Expr)
    (rhoReal : Nat → ℝ) (rho : IntervalDyadicEnv) (idx : Nat) (cfg : DyadicConfig)
    (x : ℝ) (hx : x ∈ rho idx) (hrho : ∀ i, rhoReal i ∈ rho i)
    (hprec : cfg.precision ≤ 0) (hsupp : checkDyadicADFragment e = true)
    (hdom : evalDomainValidDyadic e rho cfg) :
    deriv (Expr.evalAlong e rhoReal idx) x ∈
      (LeanCert.Internal.AD.Dyadic.evalTotal e (mkDualDyadicEnv rho idx) cfg).der := by
  have hmemValue : envMemDyadic (Expr.updateVar rhoReal idx x) rho := by
    intro i
    by_cases hi : i = idx
    · subst i
      simpa [Expr.updateVar] using hx
    · simpa [Expr.updateVar, hi] using hrho i
  induction e with
  | const q =>
      simp only [Expr.evalAlong_const', deriv_const, LeanCert.Internal.AD.Dyadic.evalTotal,
        DualIntervalDyadic.const]
      norm_num [DualIntervalDyadic.zero, IntervalDyadic.mem_def, IntervalDyadic.singleton,
        Core.Dyadic.zero, Core.Dyadic.toRat]
  | var i =>
      by_cases hi : i = idx
      · subst i
        simp only [Expr.evalAlong_var_active, deriv_id, LeanCert.Internal.AD.Dyadic.evalTotal,
          mkDualDyadicEnv, ↓reduceIte, DualIntervalDyadic.varActive]
        simpa [DualIntervalDyadic.one, Core.Dyadic.toRat_ofInt] using
          IntervalDyadic.mem_singleton (Core.Dyadic.ofInt 1)
      · simp only [Expr.evalAlong_var_passive _ _ _ hi, deriv_const,
          LeanCert.Internal.AD.Dyadic.evalTotal, mkDualDyadicEnv, ite_eq_right hi,
          DualIntervalDyadic.varPassive]
        norm_num [DualIntervalDyadic.zero, IntervalDyadic.mem_def, IntervalDyadic.singleton,
          Core.Dyadic.zero, Core.Dyadic.toRat]
  | add a b iha ihb =>
      simp only [checkDyadicADFragment, Bool.and_eq_true] at hsupp
      simp only [evalDomainValidDyadic] at hdom
      have hda := evalAlong_differentiableAt_of_dyadic_facts a rhoReal rho idx cfg x hx hrho
        hprec hsupp.1 hdom.1
      have hdb := evalAlong_differentiableAt_of_dyadic_facts b rhoReal rho idx cfg x hx hrho
        hprec hsupp.2 hdom.2
      simp only [Expr.evalAlong_add_pi, deriv_add hda hdb,
        LeanCert.Internal.AD.Dyadic.evalTotal, DualIntervalDyadic.add,
        IntervalDyadic.addRounded]
      exact IntervalDyadic.roundOut_contains
        (IntervalDyadic.mem_add (iha hsupp.1 hdom.1) (ihb hsupp.2 hdom.2)) cfg.precision
  | mul a b iha ihb =>
      simp only [checkDyadicADFragment, Bool.and_eq_true] at hsupp
      simp only [evalDomainValidDyadic] at hdom
      have hda := evalAlong_differentiableAt_of_dyadic_facts a rhoReal rho idx cfg x hx hrho
        hprec hsupp.1 hdom.1
      have hdb := evalAlong_differentiableAt_of_dyadic_facts b rhoReal rho idx cfg x hx hrho
        hprec hsupp.2 hdom.2
      have hmemDual := updateVar_mem_mkDualDyadicEnv_val rhoReal rho idx x hx hrho
      have hva := evalTotalDyadic_val_correct_of_facts a
        (Expr.updateVar rhoReal idx x) (mkDualDyadicEnv rho idx) cfg hprec hsupp.1
        (by simpa using hdom.1) hmemDual
      have hvb := evalTotalDyadic_val_correct_of_facts b
        (Expr.updateVar rhoReal idx x) (mkDualDyadicEnv rho idx) cfg hprec hsupp.2
        (by simpa using hdom.2) hmemDual
      have hleft := IntervalDyadic.roundOut_contains
        (IntervalDyadic.mem_mul (iha hsupp.1 hdom.1) hvb) cfg.precision
      have hright := IntervalDyadic.roundOut_contains
        (IntervalDyadic.mem_mul hva (ihb hsupp.2 hdom.2)) cfg.precision
      simp only [Expr.evalAlong_mul_pi, deriv_mul hda hdb,
        LeanCert.Internal.AD.Dyadic.evalTotal, DualIntervalDyadic.mul,
        IntervalDyadic.mulRounded, IntervalDyadic.addRounded]
      exact IntervalDyadic.roundOut_contains (IntervalDyadic.mem_add hleft hright) cfg.precision
  | neg a ih =>
      simp only [checkDyadicADFragment] at hsupp
      simp only [evalDomainValidDyadic] at hdom
      have hd := evalAlong_differentiableAt_of_dyadic_facts a rhoReal rho idx cfg x hx hrho
        hprec hsupp hdom
      simp only [Expr.evalAlong_neg_pi, deriv.neg, LeanCert.Internal.AD.Dyadic.evalTotal,
        DualIntervalDyadic.neg]
      exact IntervalDyadic.mem_neg (ih hsupp hdom)
  | inv a ih =>
      simp only [checkDyadicADFragment] at hsupp
      simp only [evalDomainValidDyadic] at hdom
      have hval := evalIntervalDyadic_correct_of_domain a
        (Expr.updateVar rhoReal idx x) rho hmemValue cfg hprec hdom.1
      have hval' : Expr.evalAlong a rhoReal idx x ∈
          LeanCert.Internal.Dyadic.evalUnchecked a rho cfg := by
        simpa only [Expr.evalAlong_eq] using hval
      have hne : Expr.evalAlong a rhoReal idx x ≠ 0 := by
        intro hz
        rw [hz] at hval'
        rcases hdom.2 with hpos | hneg
        · exact (not_lt_of_ge (IntervalDyadic.mem_toIntervalRat.mp hval').1)
            (by exact_mod_cast hpos)
        · exact (not_lt_of_ge (IntervalDyadic.mem_toIntervalRat.mp hval').2)
            (by exact_mod_cast hneg)
      have hd := evalAlong_differentiableAt_of_dyadic_facts a rhoReal rho idx cfg x hx hrho
        hprec hsupp hdom.1
      rw [Expr.evalAlong_inv]
      have hcomp : (fun t => (Expr.evalAlong a rhoReal idx t)⁻¹) =
          (fun y : ℝ => y⁻¹) ∘ Expr.evalAlong a rhoReal idx := rfl
      rw [hcomp, deriv_comp x (hasDerivAt_inv hne).differentiableAt hd]
      simp only [(hasDerivAt_inv hne).deriv, LeanCert.Internal.AD.Dyadic.evalTotal,
        DualIntervalDyadic.inv]
      rw [evalTotalDyadic_val_of_fragment a (mkDualDyadicEnv rho idx) cfg hsupp]
      simp only [mkDualDyadicEnv_values]
      have hrat := IntervalDyadic.mem_toIntervalRat.mp hval'
      have hinvRat := mem_invInterval_nonzero hrat hdom.2
      have hinv : (Expr.evalAlong a rhoReal idx x)⁻¹ ∈
          invIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked a rho cfg) cfg := by
        exact IntervalDyadic.mem_ofIntervalRat hinvRat cfg.precision hprec
      have hinvSq := IntervalDyadic.roundOut_contains
        (IntervalDyadic.mem_mul hinv hinv) cfg.precision
      have hprod := IntervalDyadic.roundOut_contains
        (IntervalDyadic.mem_mul (ih hsupp hdom.1) hinvSq) cfg.precision
      have hneg := IntervalDyadic.mem_neg hprod
      simpa [IntervalDyadic.mulRounded, pow_two, mul_assoc, mul_comm, mul_left_comm] using hneg
  | exp a ih =>
      simp only [checkDyadicADFragment] at hsupp
      simp only [evalDomainValidDyadic] at hdom
      have hd := evalAlong_differentiableAt_of_dyadic_facts a rhoReal rho idx cfg x hx hrho
        hprec hsupp hdom
      have hval := evalIntervalDyadic_correct_of_domain a
        (Expr.updateVar rhoReal idx x) rho hmemValue cfg hprec hdom
      have hexpRat := IntervalRat.mem_expComputable
        (IntervalDyadic.mem_toIntervalRat.mp hval) cfg.taylorDepth
      have hexp : Real.exp (Expr.evalAlong a rhoReal idx x) ∈
          expIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked a rho cfg) cfg := by
        simpa [Expr.evalAlong_eq, expIntervalDyadic] using
          (IntervalDyadic.mem_ofIntervalRat hexpRat cfg.precision hprec)
      simp only [Expr.evalAlong_exp, deriv_exp hd, LeanCert.Internal.AD.Dyadic.evalTotal,
        DualIntervalDyadic.exp, IntervalDyadic.mulRounded]
      rw [evalTotalDyadic_val_of_fragment a (mkDualDyadicEnv rho idx) cfg hsupp]
      simp only [mkDualDyadicEnv_values]
      exact IntervalDyadic.roundOut_contains
        (IntervalDyadic.mem_mul hexp (ih hsupp hdom)) cfg.precision
  | sin a ih =>
      simp only [checkDyadicADFragment] at hsupp
      simp only [evalDomainValidDyadic] at hdom
      have hd := evalAlong_differentiableAt_of_dyadic_facts a rhoReal rho idx cfg x hx hrho
        hprec hsupp hdom
      have hval := evalIntervalDyadic_correct_of_domain a
        (Expr.updateVar rhoReal idx x) rho hmemValue cfg hprec hdom
      have hcosRat := IntervalRat.mem_cosComputable
        (IntervalDyadic.mem_toIntervalRat.mp hval) cfg.taylorDepth
      have hcos : Real.cos (Expr.evalAlong a rhoReal idx x) ∈
          cosIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked a rho cfg) cfg := by
        simpa [Expr.evalAlong_eq, cosIntervalDyadic] using
          (IntervalDyadic.mem_ofIntervalRat hcosRat cfg.precision hprec)
      simp only [Expr.evalAlong_sin, deriv_sin hd, LeanCert.Internal.AD.Dyadic.evalTotal,
        DualIntervalDyadic.sin, IntervalDyadic.mulRounded]
      rw [evalTotalDyadic_val_of_fragment a (mkDualDyadicEnv rho idx) cfg hsupp]
      simp only [mkDualDyadicEnv_values]
      exact IntervalDyadic.roundOut_contains
        (IntervalDyadic.mem_mul hcos (ih hsupp hdom)) cfg.precision
  | cos a ih =>
      simp only [checkDyadicADFragment] at hsupp
      simp only [evalDomainValidDyadic] at hdom
      have hd := evalAlong_differentiableAt_of_dyadic_facts a rhoReal rho idx cfg x hx hrho
        hprec hsupp hdom
      have hval := evalIntervalDyadic_correct_of_domain a
        (Expr.updateVar rhoReal idx x) rho hmemValue cfg hprec hdom
      have hsinRat := IntervalRat.mem_sinComputable
        (IntervalDyadic.mem_toIntervalRat.mp hval) cfg.taylorDepth
      have hsin : Real.sin (Expr.evalAlong a rhoReal idx x) ∈
          sinIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked a rho cfg) cfg := by
        simpa [Expr.evalAlong_eq, sinIntervalDyadic] using
          (IntervalDyadic.mem_ofIntervalRat hsinRat cfg.precision hprec)
      simp only [Expr.evalAlong_cos, deriv_cos hd, LeanCert.Internal.AD.Dyadic.evalTotal,
        DualIntervalDyadic.cos, IntervalDyadic.mulRounded]
      rw [evalTotalDyadic_val_of_fragment a (mkDualDyadicEnv rho idx) cfg hsupp]
      simp only [mkDualDyadicEnv_values]
      exact IntervalDyadic.roundOut_contains
        (IntervalDyadic.mem_mul (IntervalDyadic.mem_neg hsin) (ih hsupp hdom)) cfg.precision
  | log a ih =>
      simp only [checkDyadicADFragment] at hsupp
      simp only [evalDomainValidDyadic] at hdom
      have hval := evalIntervalDyadic_correct_of_domain a
        (Expr.updateVar rhoReal idx x) rho hmemValue cfg hprec hdom.1
      have hval' : Expr.evalAlong a rhoReal idx x ∈
          LeanCert.Internal.Dyadic.evalUnchecked a rho cfg := by
        simpa only [Expr.evalAlong_eq] using hval
      have hpos : 0 < Expr.evalAlong a rhoReal idx x :=
        lt_of_lt_of_le (by exact_mod_cast hdom.2)
          (IntervalDyadic.mem_toIntervalRat.mp hval').1
      have hd := evalAlong_differentiableAt_of_dyadic_facts a rhoReal rho idx cfg x hx hrho
        hprec hsupp hdom.1
      rw [Expr.evalAlong_log]
      have hcomp : (fun t => Real.log (Expr.evalAlong a rhoReal idx t)) =
          Real.log ∘ Expr.evalAlong a rhoReal idx := rfl
      rw [hcomp, deriv_comp x (Real.differentiableAt_log (ne_of_gt hpos)) hd]
      simp only [Real.deriv_log, LeanCert.Internal.AD.Dyadic.evalTotal,
        DualIntervalDyadic.log, IntervalDyadic.mulRounded]
      rw [evalTotalDyadic_val_of_fragment a (mkDualDyadicEnv rho idx) cfg hsupp]
      simp only [mkDualDyadicEnv_values]
      have hnz : (LeanCert.Internal.Dyadic.evalUnchecked a rho cfg).toIntervalRat.lo > 0 ∨
          (LeanCert.Internal.Dyadic.evalUnchecked a rho cfg).toIntervalRat.hi < 0 := Or.inl hdom.2
      have hinvRat := mem_invInterval_nonzero
        (IntervalDyadic.mem_toIntervalRat.mp hval') hnz
      have hinv : (Expr.evalAlong a rhoReal idx x)⁻¹ ∈
          invIntervalDyadic (LeanCert.Internal.Dyadic.evalUnchecked a rho cfg) cfg :=
        IntervalDyadic.mem_ofIntervalRat hinvRat cfg.precision hprec
      exact IntervalDyadic.roundOut_contains
        (IntervalDyadic.mem_mul hinv (ih hsupp hdom.1)) cfg.precision
  | atan | arsinh | atanh | sinc | erf | sinh | cosh | tanh | sqrt | namedConst =>
      simp [checkDyadicADFragment] at hsupp


-- @@ L551-561 verbatim
/-- Golden theorem: successful checked Dyadic indexed AD encloses the true
partial derivative. -/
theorem evalWithDerivDyadicChecked_der_correct (e : Expr)
    (rhoReal : Nat → ℝ) (rho : IntervalDyadicEnv) (idx : Nat) (cfg : DyadicConfig)
    (D : DualIntervalDyadic) (x : ℝ) (hx : x ∈ rho idx)
    (hrho : ∀ i, rhoReal i ∈ rho i)
    (hok : evalWithDerivDyadicChecked e rho idx cfg = .ok D) :
    deriv (Expr.evalAlong e rhoReal idx) x ∈ D.der := by
  obtain ⟨hprec, hsupp, hdom, rfl⟩ := evalDualDyadicChecked_facts hok
  exact evalTotalDyadic_der_correct_of_facts e rhoReal rho idx cfg x hx hrho hprec hsupp
    (by simpa using hdom)


-- @@ L563-577 verbatim
/-- Golden theorem for the derivative-only Dyadic API. -/
theorem derivIntervalDyadicChecked_correct (e : Expr)
    (rhoReal : Nat → ℝ) (rho : IntervalDyadicEnv) (idx : Nat) (cfg : DyadicConfig)
    (dI : IntervalDyadic) (x : ℝ) (hx : x ∈ rho idx)
    (hrho : ∀ i, rhoReal i ∈ rho i)
    (hok : derivIntervalDyadicChecked e rho idx cfg = .ok dI) :
    deriv (Expr.evalAlong e rhoReal idx) x ∈ dI := by
  simp only [derivIntervalDyadicChecked, bind, Except.bind] at hok
  cases hdual : evalWithDerivDyadicChecked e rho idx cfg with
  | error err => simp [hdual] at hok
  | ok D =>
      rw [hdual] at hok
      simp only [pure, Except.pure, Except.ok.injEq] at hok
      subst dI
      exact evalWithDerivDyadicChecked_der_correct e rhoReal rho idx cfg D x hx hrho hdual


-- @@ L579-595 verbatim
/-- Golden theorem for rational input boxes converted to the Dyadic backend. -/
theorem derivIntervalDyadicCheckedOfRat_correct (e : Expr)
    (rhoReal : Nat → ℝ) (rho : IntervalEnv) (idx : Nat) (cfg : DyadicConfig)
    (dI : IntervalDyadic) (x : ℝ) (hx : x ∈ rho idx)
    (hrho : ∀ i, rhoReal i ∈ rho i)
    (hok : derivIntervalDyadicCheckedOfRat e rho idx cfg = .ok dI) :
    deriv (Expr.evalAlong e rhoReal idx) x ∈ dI := by
  simp only [derivIntervalDyadicCheckedOfRat] at hok
  split at hok
  · rename_i hprec
    apply derivIntervalDyadicChecked_correct e rhoReal
      (toDyadicEnv rho cfg.precision) idx cfg dI x
    · exact IntervalDyadic.mem_ofIntervalRat hx cfg.precision hprec
    · intro i
      exact IntervalDyadic.mem_ofIntervalRat (hrho i) cfg.precision hprec
    · exact hok
  · contradiction


-- @@ L597-603 verbatim
/-- Compute the first `n` partial derivatives with the checked Dyadic backend. -/
def gradientIntervalDyadicChecked (e : Expr) (rho : IntervalDyadicEnv) (n : Nat)
    (cfg : DyadicConfig := {}) : EvalResult (List IntervalDyadic) :=
  if cfg.precision ≤ 0 then
    (List.range n).mapM fun i => derivIntervalDyadicChecked e rho i cfg
  else
    .error (.invalidConfiguration "Dyadic AD precision must be nonpositive")


-- @@ L605-611 verbatim
/-- Rational-input convenience boundary for the first `n` Dyadic partials. -/
def gradientIntervalDyadicCheckedOfRat (e : Expr) (rho : IntervalEnv) (n : Nat)
    (cfg : DyadicConfig := {}) : EvalResult (List IntervalDyadic) :=
  if cfg.precision ≤ 0 then
    gradientIntervalDyadicChecked e (toDyadicEnv rho cfg.precision) n cfg
  else
    .error (.invalidConfiguration "Dyadic AD precision must be nonpositive")


-- @@ L613-646 verbatim
private theorem derivIntervalsDyadicChecked_correct (e : Expr)
    (rhoReal : Nat → ℝ) (rho : IntervalDyadicEnv) (cfg : DyadicConfig)
    (hrho : ∀ i, rhoReal i ∈ rho i) (indices : List Nat)
    (gradient : List IntervalDyadic)
    (hok : indices.mapM (fun i => derivIntervalDyadicChecked e rho i cfg) = .ok gradient) :
    List.Forall₂ (fun i dI => deriv (Expr.evalAlong e rhoReal i) (rhoReal i) ∈ dI)
      indices gradient := by
  induction indices generalizing gradient with
  | nil =>
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hok
      subst gradient
      exact .nil
  | cons i indices ih =>
      simp only [List.mapM_cons] at hok
      cases hdi : derivIntervalDyadicChecked e rho i cfg with
      | error err =>
          rw [hdi] at hok
          simp only [bind, Except.bind] at hok
          cases hok
      | ok dI =>
          rw [hdi] at hok
          simp only [bind, Except.bind] at hok
          cases htail : indices.mapM (fun j => derivIntervalDyadicChecked e rho j cfg) with
          | error err =>
              rw [htail] at hok
              cases hok
          | ok tail =>
              rw [htail] at hok
              simp only [pure, Except.pure, Except.ok.injEq] at hok
              subst gradient
              exact .cons
                (derivIntervalDyadicChecked_correct e rhoReal rho i cfg dI
                  (rhoReal i) (hrho i) hrho hdi)
                (ih tail htail)


-- @@ L648-659 verbatim
/-- Golden theorem for the checked Dyadic gradient API. -/
theorem gradientIntervalDyadicChecked_correct (e : Expr)
    (rhoReal : Nat → ℝ) (rho : IntervalDyadicEnv) (n : Nat) (cfg : DyadicConfig)
    (hrho : ∀ i, rhoReal i ∈ rho i) (gradient : List IntervalDyadic)
    (hok : gradientIntervalDyadicChecked e rho n cfg = .ok gradient) :
    List.Forall₂ (fun i dI => deriv (Expr.evalAlong e rhoReal i) (rhoReal i) ∈ dI)
      (List.range n) gradient := by
  simp only [gradientIntervalDyadicChecked] at hok
  split at hok
  · exact derivIntervalsDyadicChecked_correct e rhoReal rho cfg hrho
      (List.range n) gradient hok
  · contradiction


-- @@ L661-676 verbatim
/-- Golden theorem for checked Dyadic gradients over rational input boxes. -/
theorem gradientIntervalDyadicCheckedOfRat_correct (e : Expr)
    (rhoReal : Nat → ℝ) (rho : IntervalEnv) (n : Nat) (cfg : DyadicConfig)
    (hrho : ∀ i, rhoReal i ∈ rho i) (gradient : List IntervalDyadic)
    (hok : gradientIntervalDyadicCheckedOfRat e rho n cfg = .ok gradient) :
    List.Forall₂ (fun i dI => deriv (Expr.evalAlong e rhoReal i) (rhoReal i) ∈ dI)
      (List.range n) gradient := by
  simp only [gradientIntervalDyadicCheckedOfRat] at hok
  split at hok
  · rename_i hprec
    apply gradientIntervalDyadicChecked_correct e rhoReal
      (toDyadicEnv rho cfg.precision) n cfg
    · intro i
      exact IntervalDyadic.mem_ofIntervalRat (hrho i) cfg.precision hprec
    · exact hok
  · contradiction


-- @@ L678-678 verbatim
end LeanCert.Engine
