/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.Extension


-- @@ L8-13 verbatim
/-!
# Downstream enclosure-extension pattern

This module intentionally imports only the extension umbrella.  It models a downstream
package registering a function without editing LeanCert's expression AST or router.
-/


-- @@ L15-15 verbatim
namespace LeanCert.Test.DownstreamPatterns.Extension


-- @@ L17-17 verbatim
open Lean Elab Command

-- @@ L18-18 verbatim
open LeanCert.Core LeanCert.Tactic.Extension


-- @@ L20-20 verbatim
def shifted (x : ℝ) : ℝ := x + 1


-- @@ L22-24 verbatim
def shiftedCandidate (request : UnaryEnclosureRequest) :
    Except EnclosureCandidateFailure IntervalRat :=
  .ok <| IntervalRat.add request.input (IntervalRat.singleton 1)


-- @@ L26-27 verbatim
def checkShifted (request : UnaryEnclosureRequest) (output : IntervalRat) : Bool :=
  decide (output = IntervalRat.add request.input (IntervalRat.singleton 1))


-- @@ L29-38 verbatim
@[leancert_enclosure shiftedCandidate, priority := 1200]
theorem shifted_mem
    {request : UnaryEnclosureRequest} {x : ℝ} {output : IntervalRat}
    (hx : x ∈ request.input)
    (hcheck : checkShifted request output = true) :
    shifted x ∈ output := by
  have hout : output = IntervalRat.add request.input (IntervalRat.singleton 1) := by
    exact of_decide_eq_true hcheck
  rw [hout]
  simpa [shifted] using IntervalRat.mem_add hx (IntervalRat.mem_singleton 1)


-- @@ L40-46 verbatim
@[leancert_enclosure shiftedCandidate, priority := 100]
theorem shifted_mem_fallback
    {request : UnaryEnclosureRequest} {x : ℝ} {output : IntervalRat}
    (hx : x ∈ request.input)
    (hcheck : checkShifted request output = true) :
    shifted x ∈ output := by
  exact shifted_mem hx hcheck


-- @@ L48-50 verbatim
/-- A deliberately non-reifiable downstream function used to exercise the
registered execution path rather than LeanCert's built-in expression bridge. -/
noncomputable def positiveBranch (x : ℝ) : ℝ := if x ≤ 0 then 0 else x


-- @@ L52-55 verbatim
def positiveBranchCandidate (request : UnaryEnclosureRequest) :
    Except EnclosureCandidateFailure IntervalRat :=
  if 0 < request.input.lo then .ok request.input
  else .error <| .domainObstruction "input interval is not strictly positive"


-- @@ L57-58 verbatim
def checkPositiveBranch (request : UnaryEnclosureRequest) (output : IntervalRat) : Bool :=
  decide (0 < request.input.lo) && decide (output = request.input)


-- @@ L60-63 verbatim
/-- A higher-priority bad candidate checks the fallback path to the next
registered rule without weakening the soundness boundary. -/
def rejectedPositiveBranchCandidate (request : UnaryEnclosureRequest) :
    Except EnclosureCandidateFailure IntervalRat := .ok request.input


-- @@ L65-66 verbatim
def rejectPositiveBranch (_request : UnaryEnclosureRequest) (_output : IntervalRat) : Bool :=
  false


-- @@ L68-74 verbatim
@[leancert_enclosure rejectedPositiveBranchCandidate, priority := 1300]
theorem rejected_positiveBranch_mem
    {request : UnaryEnclosureRequest} {x : ℝ} {output : IntervalRat}
    (_hx : x ∈ request.input)
    (hcheck : rejectPositiveBranch request output = true) :
    positiveBranch x ∈ output := by
  simp [rejectPositiveBranch] at hcheck


-- @@ L76-86 verbatim
@[leancert_enclosure positiveBranchCandidate, priority := 1200]
theorem positiveBranch_mem
    {request : UnaryEnclosureRequest} {x : ℝ} {output : IntervalRat}
    (hx : x ∈ request.input)
    (hcheck : checkPositiveBranch request output = true) :
    positiveBranch x ∈ output := by
  simp only [checkPositiveBranch, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨hpositive, rfl⟩
  have hxpositive : 0 < x := by
    exact lt_of_lt_of_le (by exact_mod_cast hpositive) hx.1
  simpa [positiveBranch, not_le.mpr hxpositive] using hx


-- @@ L88-90 verbatim
/-- A deliberately width-sensitive rule used to demonstrate that candidate
rejection on a broad interval can be repaired by checked subdivision. -/
noncomputable def narrowIdentity (x : ℝ) : ℝ := x


-- @@ L92-93 verbatim
def narrowIdentityCandidate (request : UnaryEnclosureRequest) :
    Except EnclosureCandidateFailure IntervalRat := .ok request.input


-- @@ L95-96 verbatim
def checkNarrowIdentity (request : UnaryEnclosureRequest) (output : IntervalRat) : Bool :=
  decide (request.input.hi - request.input.lo ≤ 1) && decide (output = request.input)


-- @@ L98-109 verbatim
@[leancert_enclosure narrowIdentityCandidate]
theorem narrowIdentity_mem
    {request : UnaryEnclosureRequest} {x : ℝ} {output : IntervalRat}
    (hx : x ∈ request.input)
    (hcheck : checkNarrowIdentity request output = true) :
    narrowIdentity x ∈ output := by
  simp only [checkNarrowIdentity, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨_, rfl⟩
  simpa [narrowIdentity] using hx

/- A sound but deliberately widened enclosure. It exercises correlation loss,
subdivision, and domain propagation through a registered atom. -/

-- @@ L110-110 verbatim
noncomputable def fatPositive (x : ℝ) : ℝ := if x ≤ 0 then 0 else x


-- @@ L112-115 verbatim
def fatPositiveOutput (input : IntervalRat) : IntervalRat where
  lo := input.lo - 1 / 10
  hi := input.hi + 1 / 10
  le := by linarith [input.le]


-- @@ L117-120 verbatim
def fatPositiveCandidate (request : UnaryEnclosureRequest) :
    Except EnclosureCandidateFailure IntervalRat :=
  if 0 < request.input.lo then .ok (fatPositiveOutput request.input)
  else .error <| .domainObstruction "input interval is not strictly positive"


-- @@ L122-123 verbatim
def checkFatPositive (request : UnaryEnclosureRequest) (output : IntervalRat) : Bool :=
  decide (0 < request.input.lo) && decide (output = fatPositiveOutput request.input)


-- @@ L125-137 verbatim
@[leancert_enclosure fatPositiveCandidate]
theorem fatPositive_mem
    {request : UnaryEnclosureRequest} {x : ℝ} {output : IntervalRat}
    (hx : x ∈ request.input)
    (hcheck : checkFatPositive request output = true) :
    fatPositive x ∈ output := by
  simp only [checkFatPositive, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨hpositive, rfl⟩
  have hxpositive : 0 < x := lt_of_lt_of_le (by exact_mod_cast hpositive) hx.1
  simp only [fatPositive, ite_eq_right (not_le.mpr hxpositive), IntervalRat.mem_def,
    fatPositiveOutput]
  simp only [IntervalRat.mem_def] at hx
  constructor <;> push_cast <;> linarith [hx.1, hx.2]


-- @@ L139-148 verbatim
run_meta do
  let env ← getEnv
  let rules := getUnaryEnclosureRules env ``shifted
  unless rules.size == 2 do
    throwError "expected two downstream shifted rules, found {rules.size}"
  unless rules[0]!.theoremName == ``shifted_mem && rules[0]!.rulePriority == 1200 do
    throwError "highest-priority downstream rule was not ordered first"
  for moduleName in env.header.moduleNames do
    if (`LeanCert.Tactic.LeanCert.Router).isPrefixOf moduleName then
      throwError "extension-only import leaked router module {moduleName}"


-- @@ L150-150 verbatim
end LeanCert.Test.DownstreamPatterns.Extension
