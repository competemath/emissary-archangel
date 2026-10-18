/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic


-- @@ L8-22 verbatim
/-!
# Trust-mode regression tests (`leancert.trust`)

Guards the verification choke point (`LeanCert.Tactic.closeCertificateGoalTyped`)
behind `interval_decide`:

* default (native) behavior is unchanged;
* `set_option leancert.trust "kernel"` closes certificates by kernel
  reduction only — the axiom pins below fail if `Lean.ofReduceBool` (or a
  `*.native_decide.ax_*` auxiliary) ever sneaks back in;
* `"auto"` stays foundational on goals the kernel can handle.

Earlier kernel-only tactic paths rotted because no test exercised strict kernel
verification. These pins are the guard against a repeat.
-/


-- @@ L24-24 verbatim
open Lean Meta Elab Tactic


-- @@ L26-43 verbatim
private def closeAndExpectVerificationEvent
    (cfg : LeanCert.Tactic.VerificationConfig)
    (requested : LeanCert.Tactic.VerificationMode)
    (used : LeanCert.Tactic.VerificationUsed)
    (cause : LeanCert.Tactic.VerificationCause) : TacticM Unit := do
  let goal ← getMainGoal
  let event ←
    match ← LeanCert.Tactic.closeCertificateGoalTyped cfg goal
        "trust telemetry test" with
    | .accepted event => pure event
    | .rejected => throwError "trust telemetry certificate was rejected"
    | .failed failure => throwError (failure.message "trust telemetry test")
  unless event.requested == requested do
    throwError "wrong requested verification mode: {repr event}"
  unless event.used == used do
    throwError "wrong observed verification route: {repr event}"
  unless event.cause == cause do
    throwError "wrong verification cause: {repr event}"


-- @@ L45-47 verbatim
elab "close_expect_native_event" : tactic =>
  closeAndExpectVerificationEvent { mode := .native }
    .native .native .explicitNative


-- @@ L49-51 verbatim
elab "close_expect_kernel_event" : tactic =>
  closeAndExpectVerificationEvent { mode := .kernel }
    .kernel .kernel .explicitKernel


-- @@ L53-55 verbatim
elab "close_expect_auto_kernel_event" : tactic =>
  closeAndExpectVerificationEvent { mode := .auto }
    .auto .kernel .autoKernel


-- @@ L57-57 verbatim
example : true = true := by close_expect_native_event

-- @@ L58-58 verbatim
example : true = true := by close_expect_kernel_event

-- @@ L59-59 verbatim
example : true = true := by close_expect_auto_kernel_event

-- @@ L60-60 verbatim
example : 0 < 1 := by close_expect_kernel_event


-- @@ L62-78 verbatim
private def expectTypedRejection
    (cfg : LeanCert.Tactic.VerificationConfig) : TacticM Unit := do
  let callerGoals ← getGoals
  let envSizeBefore := (← getEnv).constants.toList.length
  let certType ← mkEq (toExpr false) (toExpr true)
  let certGoal ← mkFreshExprMVar certType
  match ← LeanCert.Tactic.closeCertificateGoalTyped cfg certGoal.mvarId!
      "typed rejection test" with
  | .rejected => pure ()
  | result => throwError "expected typed certificate rejection, got {repr result}"
  unless (← getGoals) == callerGoals do
    throwError "typed certificate rejection changed the caller's goal list"
  unless (← getEnv).constants.toList.length == envSizeBefore do
    throwError "typed certificate rejection leaked an environment declaration"
  unless !(← certGoal.mvarId!.isAssigned) do
    throwError "typed certificate rejection assigned the certificate goal"
  evalTactic (← `(tactic| trivial))


-- @@ L80-81 verbatim
elab "expect_native_rejection" : tactic =>
  expectTypedRejection { mode := .native }


-- @@ L83-84 verbatim
elab "expect_kernel_rejection" : tactic =>
  expectTypedRejection { mode := .kernel }


-- @@ L86-87 verbatim
elab "expect_auto_rejection" : tactic =>
  expectTypedRejection { mode := .auto }


-- @@ L89-89 verbatim
example : True := by expect_native_rejection

-- @@ L90-90 verbatim
example : True := by expect_kernel_rejection

-- @@ L91-91 verbatim
example : True := by expect_auto_rejection


-- @@ L93-102 verbatim
elab "expect_malformed_certificate_failure" : tactic => do
  let callerGoals ← getGoals
  let malformed ← mkFreshExprMVar (mkConst ``Bool)
  match ← LeanCert.Tactic.closeCertificateGoalTyped { mode := .native }
      malformed.mvarId! "malformed certificate test" with
  | .failed (.malformedCertificateGoal _) => pure ()
  | result => throwError "expected malformed-certificate failure, got {repr result}"
  unless (← getGoals) == callerGoals do
    throwError "malformed certificate failure changed the caller's goal list"
  evalTactic (← `(tactic| trivial))


-- @@ L104-104 verbatim
example : True := by expect_malformed_certificate_failure


-- @@ L106-122 verbatim
elab "expect_free_variable_certificate_failure" : tactic => do
  let callerGoals ← getGoals
  let mainGoal ← getMainGoal
  mainGoal.withContext do
    let some fvar := (← getLCtx).getFVarIds.back?
      | throwError "expected a local Boolean variable"
    let certType ← mkEq (mkFVar fvar) (toExpr true)
    let certGoal ← mkFreshExprMVar certType
    match ← LeanCert.Tactic.closeCertificateGoalTyped { mode := .native }
        certGoal.mvarId! "free-variable certificate test" with
    | .failed (.malformedCertificateGoal _) => pure ()
    | result => throwError "expected malformed free-variable certificate, got {repr result}"
    unless (← getGoals) == callerGoals do
      throwError "free-variable certificate failure changed the caller's goal list"
    unless !(← certGoal.mvarId!.isAssigned) do
      throwError "free-variable certificate failure assigned the certificate goal"
  evalTactic (← `(tactic| trivial))


-- @@ L124-124 verbatim
example (_b : Bool) : True := by expect_free_variable_certificate_failure


-- @@ L126-135 verbatim
elab "expect_outer_boundary_failure" : tactic => do
  let callerGoals ← getGoals
  let invalidGoal := MVarId.mk `LeanCert.Test.missingCertificateGoal
  match ← LeanCert.Tactic.closeCertificateGoalTyped { mode := .native }
      invalidGoal "outer boundary failure test" with
  | .failed (.internalError _) => pure ()
  | result => throwError "expected internal boundary failure, got {repr result}"
  unless (← getGoals) == callerGoals do
    throwError "outer verification failure changed the caller's goal list"
  evalTactic (← `(tactic| trivial))


-- @@ L137-137 verbatim
example : True := by expect_outer_boundary_failure


-- @@ L139-140 verbatim
noncomputable def verificationOpaqueBool : Bool :=
  Classical.choice ⟨true⟩


-- @@ L142-143 verbatim
def verificationExpensiveBool : Bool :=
  (List.range 10000).length == 10000


-- @@ L145-161 verbatim
elab "expect_failed_auto_fallback_is_silent" : tactic => do
  let callerGoals ← getGoals
  let messagesBefore := (← Core.getMessageLog).toList.length
  let certType ← mkEq (mkConst ``verificationOpaqueBool) (toExpr true)
  let certGoal ← mkFreshExprMVar certType
  match ← LeanCert.Tactic.closeCertificateGoalTyped
      { mode := .auto, kernelHeartbeats := 1 } certGoal.mvarId!
      "failed auto fallback test" with
  | .failed (.nativeFailure _) => pure ()
  | result => throwError "expected failed native fallback, got {repr result}"
  unless (← Core.getMessageLog).toList.length == messagesBefore do
    throwError "failed auto fallback emitted a successful-verification notice"
  unless (← getGoals) == callerGoals do
    throwError "failed auto fallback changed the caller's goal list"
  unless !(← certGoal.mvarId!.isAssigned) do
    throwError "failed auto fallback assigned the certificate goal"
  evalTactic (← `(tactic| trivial))


-- @@ L163-163 verbatim
example : True := by expect_failed_auto_fallback_is_silent


-- @@ L165-175 verbatim
elab "expect_successful_auto_fallback_notice" : tactic => do
  let certType ← mkEq (mkConst ``verificationExpensiveBool) (toExpr true)
  let certGoal ← mkFreshExprMVar certType
  match ← LeanCert.Tactic.closeCertificateGoalTyped
      { mode := .auto, kernelHeartbeats := 1 } certGoal.mvarId!
      "successful auto fallback test" with
  | .accepted event =>
      unless event.used == .native && event.cause == .autoNativeFallback do
        throwError "expected native auto fallback, got {repr event}"
  | result => throwError "expected successful auto fallback, got {repr result}"
  evalTactic (← `(tactic| trivial))


-- @@ L177-177 verbatim
example : True := by expect_successful_auto_fallback_notice


-- @@ L179-179 verbatim
/-! ### Default mode: native (behavior preserved) -/


-- @@ L181-184 verbatim
theorem trustDefaultNative : Real.log 2 < 7/10 := by interval_decide

-- native_decide mints a per-declaration auxiliary axiom; its presence here
-- confirms the default route is unchanged.

-- @@ L185-194 verbatim
open Lean in
run_meta do
  let axs ← collectAxioms ``trustDefaultNative
  let isNativeAux (a : Name) : Bool :=
    match a with
    | .str (.str _ "native_decide") _ => true
    | _ => false
  unless axs.any isNativeAux || axs.contains ``Lean.ofReduceBool do
    throwError "expected trustDefaultNative to be native_decide-verified \
      (default mode changed?); axioms: {axs.toList}"


-- @@ L196-196 verbatim
/-! ### Kernel mode: foundational axioms only, never falls back -/


-- @@ L198-199 verbatim
set_option leancert.trust "kernel" in
theorem trustKernelLogUpper : Real.log 2 < 7/10 := by interval_decide


-- @@ L201-202 verbatim
set_option leancert.trust "kernel" in
theorem trustKernelLogLower : (69 : ℝ)/100 < Real.log 2 := by interval_decide


-- @@ L204-205 verbatim
set_option leancert.trust "kernel" in
theorem trustKernelExp : Real.exp 1 ≤ 2.72 := by interval_decide


-- @@ L207-209 verbatim
/-- info: 'trustKernelLogUpper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trustKernelLogUpper


-- @@ L211-213 verbatim
/-- info: 'trustKernelLogLower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trustKernelLogLower


-- @@ L215-217 verbatim
/-- info: 'trustKernelExp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trustKernelExp


-- @@ L219-219 verbatim
/-! ### Kernel mode: quantified bounds (`certify_bound`, Phase 2 migration) -/


-- @@ L221-223 verbatim
set_option leancert.trust "kernel" in
theorem trustKernelBoundExp : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 2.72 := by
  certify_bound


-- @@ L225-227 verbatim
/-- info: 'trustKernelBoundExp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trustKernelBoundExp


-- @@ L229-229 verbatim
/-! ### Auto mode: kernel-capable goals stay foundational -/


-- @@ L231-232 verbatim
set_option leancert.trust "auto" in
theorem trustAutoLog : Real.log 2 < 7/10 := by interval_decide


-- @@ L234-236 verbatim
/-- info: 'trustAutoLog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trustAutoLog


-- @@ L238-238 verbatim
/-! ### Public per-invocation syntax: `(trust := …)` (Phase 3) -/


-- @@ L240-241 verbatim
theorem trustSyntaxKernel : Real.log 2 < 7/10 := by
  interval_decide (trust := kernel)


-- @@ L243-244 verbatim
theorem trustSyntaxKernelDepth : Real.log 2 < 7/10 := by
  interval_decide 20 (trust := kernel)


-- @@ L246-247 verbatim
theorem trustSyntaxBound : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 2.72 := by
  certify_bound (trust := kernel)


-- @@ L249-250 verbatim
theorem trustSyntaxAuto : ∀ x ∈ Set.Icc (0 : ℝ) 1, Real.exp x ≤ 2.72 := by
  interval_auto (trust := kernel)


-- @@ L252-253 verbatim
theorem trustSyntaxRouter : Real.log 2 < 7/10 := by
  leancert (trust := kernel)


-- @@ L255-255 verbatim
/-! ### Kernel mode: discovery Set.Icc branches (embedded certificate terms) -/


-- @@ L257-259 verbatim
set_option leancert.trust "kernel" in
theorem trustKernelRoots : ∃ x ∈ Set.Icc (0 : ℝ) 2, x * x - 2 = 0 := by
  interval_roots


-- @@ L261-263 verbatim
set_option leancert.trust "kernel" in
theorem trustKernelUniqueRoot : ∃! x, x ∈ Set.Icc (1 : ℝ) 2 ∧ x * x - 2 = 0 := by
  interval_unique_root


-- @@ L265-269 verbatim
/-! ### Auto-mode cost gate (calibrated thresholds; see scripts/bench-trust) -/

-- Unit test with *resolved* checker names: if a checker is renamed, this
-- breaks CI instead of silently disabling the gate (whose own references
-- are unresolved Name literals to keep Verification.lean import-free).

-- @@ L270-295 verbatim
open Lean Meta LeanCert.Tactic in
run_meta do
  let body ← mkAppM ``LeanCert.Core.Expr.var #[toExpr (0 : Nat)]
  let mkSumCheck (a b : Nat) : MetaM Lean.Expr := do
    let app ← mkAppM ``LeanCert.Engine.checkFinSumUpperBoundFull
      #[body, toExpr a, toExpr b, toExpr (0 : ℚ)]
    mkEq app (toExpr true)
  let opts ← getOptions
  let bigTy ← mkSumCheck 1 5000
  let expected :=
    "finite sum with 5000 terms exceeds autoMaxSumTerms=2000"
  let actual := autoGateReason? opts bigTy
  unless actual == some expected do
    throwError "auto gate reason mismatch: expected {expected}, got {repr actual}"
  let smallTy ← mkSumCheck 1 100
  unless (autoGateReason? opts smallTy).isNone do
    throwError "auto gate wrongly fired on a 100-term finite sum"
  -- disabling the gate must disable the skip
  let noGate := leancert.trust.autoGate.set opts false
  unless (autoGateReason? noGate bigTy).isNone do
    throwError "auto gate fired despite leancert.trust.autoGate=false"

-- End-to-end: past the crossover, auto routes to native (the `native` pin
-- would fail with a tighten-to-kernel hint if the gate stopped working).
-- The body must use the index: constant-body sums are closed by a
-- non-certificate arithmetic strategy and never reach the gate.

-- @@ L296-299 verbatim
set_option leancert.trust "auto" in
theorem trustAutoGatedSum :
    ∑ k ∈ Finset.Icc (1 : ℕ) 5000, (↑k : ℝ) ≤ 12502500 := by
  finsum_bound


-- @@ L301-303 verbatim
#assert_trust native trustAutoGatedSum

-- …while small sums still get kernel verification.

-- @@ L304-307 verbatim
set_option leancert.trust "auto" in
theorem trustAutoSmallSum :
    ∑ k ∈ Finset.Icc (1 : ℕ) 100, (↑k : ℝ) ≤ 5050 := by
  finsum_bound


-- @@ L309-312 verbatim
#assert_trust kernel trustAutoSmallSum

-- Partition integration certifies the retained fixed partition candidate
-- through the same trust boundary.

-- @@ L313-316 verbatim
set_option leancert.trust "kernel" in
theorem trustKernelPartitionIntegral :
    (∫ x in (0 : ℝ)..1, Real.exp x) ≤ 2 := by
  leancert


-- @@ L318-321 verbatim
set_option leancert.trust "auto" in
theorem trustAutoPartitionIntegral :
    (∫ x in (0 : ℝ)..1, Real.exp x) ≤ 2 := by
  leancert


-- @@ L323-323 verbatim
#assert_trust kernel trustKernelPartitionIntegral

-- @@ L324-324 verbatim
#assert_trust kernel trustAutoPartitionIntegral


-- @@ L326-326 verbatim
/-! ### `#assert_trust`: the CI manifest command -/


-- @@ L328-328 verbatim
#assert_trust kernel trustSyntaxKernel

-- @@ L329-329 verbatim
#assert_trust kernel trustSyntaxKernelDepth

-- @@ L330-330 verbatim
#assert_trust kernel trustSyntaxBound

-- @@ L331-331 verbatim
#assert_trust kernel trustSyntaxAuto

-- @@ L332-332 verbatim
#assert_trust kernel trustSyntaxRouter

-- @@ L333-333 verbatim
#assert_trust kernel trustKernelLogUpper

-- @@ L334-334 verbatim
#assert_trust kernel trustKernelRoots

-- @@ L335-335 verbatim
#assert_trust kernel trustKernelUniqueRoot

-- @@ L336-339 verbatim
#assert_trust native trustDefaultNative

-- Drift is caught in BOTH directions: pinning `native` on a kernel-clean
-- theorem fails with a tighten-the-manifest hint.

-- @@ L340-346 verbatim
/--
error: #assert_trust native: 'trustSyntaxKernel' has no native-compiler dependency; tighten the manifest to `kernel`
-/
#guard_msgs in
#assert_trust native trustSyntaxKernel

-- Invalid trust mode in the per-invocation syntax errors cleanly.

-- @@ L347-351 verbatim
/--
error: invalid trust mode 'kernle'; expected kernel, native, or auto
-/
#guard_msgs in
example : Real.log 2 < 7/10 := by interval_decide (trust := kernle)


-- @@ L353-353 verbatim
/-! ### Invalid option values error up front -/


-- @@ L355-360 verbatim
/--
error: invalid value 'kernle' for option 'leancert.trust'; expected "native", "kernel", or "auto"
-/
#guard_msgs in
set_option leancert.trust "kernle" in
example : Real.log 2 < 7/10 := by interval_decide
