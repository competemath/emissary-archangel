/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesUtil.Answer
import Lean.Expr


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
section WithAuxiliary


-- @@ L25-25 verbatim
open Google


-- @@ L27-27 verbatim
open Lean Elab Meta


-- @@ L29-29 verbatim
set_option google.answer "with_auxiliary"


-- @@ L31-31 verbatim
open Lean Elab Meta


-- @@ L33-37 verbatim
theorem foo : answer(True) := by
  run_tac Tactic.withMainContext do
    let env ← getEnv
    let some aux := env.find? `foo._answer | throwError "here"
  trivial


-- @@ L39-45 verbatim
theorem bar : 1 = answer(sorry) := by
  run_tac Tactic.withMainContext do
    let env ← getEnv
    let some aux := env.find? `bar._answer | throwError "here"
  -- TODO(Paul-Lez): This will change when I write a delaborator
  guard_target = 1 = bar._answer
  sorry


-- @@ L47-53 verbatim
theorem bar_symm : answer(sorry) = 1 := by
  run_tac Tactic.withMainContext do
    let env ← getEnv
    let some aux := env.find? `bar._answer | throwError "here"
  -- TODO(Paul-Lez): This will change when I write a delaborator
  guard_target = bar_symm._answer = 1
  sorry


-- @@ L55-61 verbatim
theorem bar_symm_explicit : answer(1) = 1 := by
  run_tac Tactic.withMainContext do
    let env ← getEnv
    let some aux := env.find? `bar._answer | throwError "here"
  -- TODO(Paul-Lez): This will change when I write a delaborator
  guard_target = bar_symm_explicit._answer = 1
  sorry


-- @@ L63-65 verbatim
theorem i_have_some_universes.{u, v} (X : Type u) (Y : Type v) : (X × Y) = answer(sorry) := by
  guard_target = (X × Y : Type (max u v)) = i_have_some_universes._answer.{u, v}
  sorry


-- @@ L67-67 verbatim
end WithAuxiliary


-- @@ L69-69 verbatim
section AlwaysTrue


-- @@ L71-71 verbatim
set_option google.answer "always_true"


-- @@ L73-74 verbatim
theorem this_works : (answer(sorry) : Prop) := by
  trivial


-- @@ L76-76 verbatim
end AlwaysTrue


-- @@ L78-78 verbatim
section FindAnswerExprTests


-- @@ L80-80 verbatim
open Google Lean


-- @@ L82-82 verbatim
private abbrev c (n : Name) : Expr := .const n []


-- @@ L84-119 verbatim
#eval do
  -- No annotation → none
  assert! (findAnswerExpr (c `Nat)).isNone
  -- Direct annotation
  assert! findAnswerExpr (mkAnswerAnnotation (c `True))
    == some (c `True)
  -- Nested inside forallE body
  assert! findAnswerExpr
      (.forallE `x (c `Nat)
        (mkAnswerAnnotation (c `True)) .default)
    == some (c `True)
  -- Nested inside app
  assert! findAnswerExpr
      (.app (c `id) (mkAnswerAnnotation (c `False)))
    == some (c `False)
  -- Nested inside lam
  assert! findAnswerExpr
      (.lam `x (c `Nat)
        (mkAnswerAnnotation (c `True)) .default)
    == some (c `True)
  -- Nested inside letE
  assert! findAnswerExpr
      (.letE `x (c `Nat) (c `Nat.zero)
        (mkAnswerAnnotation (c `True)) false)
    == some (c `True)
  -- Annotation in binder type (not body)
  assert! findAnswerExpr
      (.forallE `x (mkAnswerAnnotation (c `Bool))
        (c `True) .default)
    == some (c `Bool)
  -- Two annotations: find? only returns the first one found
  let twoAnswers := Expr.app
    (mkAnswerAnnotation (c `True))
    (mkAnswerAnnotation (c `False))
  assert! findAnswerExpr twoAnswers
    == some (c `True)


-- @@ L121-143 verbatim
#eval do
  -- findAnswerExprs: no annotation → empty
  assert! (findAnswerExprs (c `Nat)).isEmpty
  -- Single annotation
  assert! findAnswerExprs (mkAnswerAnnotation (c `True))
    == #[c `True]
  -- Nested inside forallE body
  assert! findAnswerExprs
      (.forallE `x (c `Nat)
        (mkAnswerAnnotation (c `True)) .default)
    == #[c `True]
  -- Two annotations: both found
  let twoAnswers := Expr.app
    (mkAnswerAnnotation (c `True))
    (mkAnswerAnnotation (c `False))
  assert! findAnswerExprs twoAnswers
    == #[c `True, c `False]
  -- Annotation in both binder type and body
  let bothPositions := Expr.forallE `x
    (mkAnswerAnnotation (c `Bool))
    (mkAnswerAnnotation (c `Nat)) .default
  assert! findAnswerExprs bothPositions
    == #[c `Bool, c `Nat]


-- @@ L145-145 verbatim
end FindAnswerExprTests
