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

public meta import FormalConjecturesUtil.Linters.CategoryAnswerLinter
public import FormalConjecturesUtil.Answer


-- @@ L21-23 verbatim
@[expose] public section

-- Off by default; on here because this file is what tests it.

-- @@ L24-24 verbatim
set_option linter.style.category_answer true


-- @@ L26-26 verbatim
namespace CategoryAnswerLinter


-- @@ L28-37 verbatim
/--
warning: Declarations tagged `@[category research solved]` should not use `answer(sorry)`: the answer should be filled in explicitly, e.g. `answer(True)`.

Note: This linter can be disabled with `set_option linter.style.category_answer false`
-/
#guard_msgs in
/-- A solved problem should not leave its answer unfilled. -/
@[category research solved]
theorem flagged_solved_answer_sorry : answer(sorry) ↔ 1 + 1 = 2 := by
  sorry


-- @@ L39-48 verbatim
/--
warning: Declarations tagged `@[category research solved]` should not use `answer(sorry)`: the answer should be filled in explicitly, e.g. `answer(True)`.

Note: This linter can be disabled with `set_option linter.style.category_answer false`
-/
#guard_msgs in
/-- The `sorry` is still a placeholder when it carries a type ascription. -/
@[category research solved]
theorem flagged_ascribed_answer_sorry : answer((sorry : Nat)) = 2 := by
  sorry


-- @@ L50-61 verbatim
/--
warning: Declarations tagged `@[category research solved]` should not use `answer(sorry)`: the answer should be filled in explicitly, e.g. `answer(True)`.

Note: This linter can be disabled with `set_option linter.style.category_answer false`
-/
#guard_msgs in
/-- An answer bound by a `let` is flagged too. -/
@[category research solved]
theorem flagged_let_answer_sorry :
    let c : Nat := answer(sorry)
    0 < c := by
  sorry


-- @@ L63-67 verbatim
#guard_msgs in
/-- A solved problem with an explicit answer is fine. -/
@[category research solved]
theorem not_flagged_explicit_answer : answer(True) ↔ 1 + 1 = 2 := by
  simp


-- @@ L69-73 verbatim
#guard_msgs in
/-- An open problem may leave its answer unfilled. -/
@[category research open]
theorem not_flagged_open_answer_sorry : answer(sorry) ↔ 1 + 1 = 2 := by
  sorry


-- @@ L75-75 verbatim
end CategoryAnswerLinter
