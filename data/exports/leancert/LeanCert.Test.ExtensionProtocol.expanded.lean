/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Test.DownstreamPatterns.Extension


-- @@ L8-8 verbatim
/-! # Typed enclosure-extension registry tests -/


-- @@ L10-10 verbatim
namespace LeanCert.Test.ExtensionProtocol


-- @@ L12-12 verbatim
open Lean Elab Command

-- @@ L13-13 verbatim
open LeanCert.Core LeanCert.Tactic.Extension

-- @@ L14-14 verbatim
open LeanCert.Test.DownstreamPatterns.Extension


-- @@ L16-23 verbatim
run_meta do
  let rules := getUnaryEnclosureRules (← getEnv) ``shifted
  unless rules.size == 2 do
    throwError "persistent enclosure rules did not survive import"
  unless rules[0]!.candidateName == ``shiftedCandidate &&
      rules[0]!.checkerName == ``checkShifted &&
      rules[0]!.theoremName == ``shifted_mem do
    throwError "registered enclosure metadata did not match its declarations"


-- @@ L25-25 verbatim
#print_leancert_rules shifted


-- @@ L27-27 verbatim
def identity (x : ℝ) : ℝ := x


-- @@ L29-31 verbatim
def identityCandidate (request : UnaryEnclosureRequest) :
    Except EnclosureCandidateFailure IntervalRat :=
  .ok request.input


-- @@ L33-34 verbatim
def checkIdentity (request : UnaryEnclosureRequest) (output : IntervalRat) : Bool :=
  decide (output = request.input)


-- @@ L36-36 verbatim
def wrongCandidate (_request : UnaryEnclosureRequest) : Nat := 0


-- @@ L38-48 verbatim
/-- error: invalid @[leancert_enclosure] candidate `LeanCert.Test.ExtensionProtocol.wrongCandidate`: expected type `UnaryEnclosureCandidate`, found
  UnaryEnclosureRequest → ℕ -/
#guard_msgs in
@[leancert_enclosure wrongCandidate]
theorem rejectsWrongCandidate
    {request : UnaryEnclosureRequest} {x : ℝ} {output : IntervalRat}
    (hx : x ∈ request.input)
    (hcheck : checkIdentity request output = true) :
    identity x ∈ output := by
  have hout : output = request.input := of_decide_eq_true hcheck
  simpa [identity, hout] using hx


-- @@ L50-50 verbatim
def impossibleChecker (_request : UnaryEnclosureRequest) (_output : IntervalRat) : Bool := false


-- @@ L52-60 verbatim
/-- error: invalid @[leancert_enclosure] theorem `LeanCert.Test.ExtensionProtocol.rejectsWrongInput`: input-membership hypothesis must use `request.input` -/
#guard_msgs in
@[leancert_enclosure identityCandidate]
theorem rejectsWrongInput
    {request : UnaryEnclosureRequest} {x : ℝ} {output : IntervalRat}
    (hx : x ∈ output)
    (_hcheck : impossibleChecker request output = true) :
    identity x ∈ output := by
  simpa [identity] using hx


-- @@ L62-62 verbatim
def alwaysTrueChecker (_request : UnaryEnclosureRequest) (_output : IntervalRat) : Bool := true


-- @@ L64-72 verbatim
/-- error: invalid @[leancert_enclosure] theorem `LeanCert.Test.ExtensionProtocol.rejectsFalseComparison`: checker hypothesis must compare against `true` -/
#guard_msgs in
@[leancert_enclosure identityCandidate]
theorem rejectsFalseComparison
    {request : UnaryEnclosureRequest} {x : ℝ} {output : IntervalRat}
    (_hx : x ∈ request.input)
    (hcheck : alwaysTrueChecker request output = false) :
    identity x ∈ output := by
  simp [alwaysTrueChecker] at hcheck


-- @@ L74-83 verbatim
/-- error: invalid @[leancert_enclosure] declaration `LeanCert.Test.ExtensionProtocol.rejectsDefinition`: soundness boundary must be a proved theorem, not an axiom or definition -/
#guard_msgs in
@[leancert_enclosure identityCandidate]
def rejectsDefinition
    {request : UnaryEnclosureRequest} {x : ℝ} {output : IntervalRat}
    (hx : x ∈ request.input)
    (hcheck : checkIdentity request output = true) :
    identity x ∈ output := by
  have hout : output = request.input := of_decide_eq_true hcheck
  simpa [identity, hout] using hx


-- @@ L85-85 verbatim
end LeanCert.Test.ExtensionProtocol
