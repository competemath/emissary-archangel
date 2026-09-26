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


-- @@ L28-33 verbatim
/--
warning: Declarations tagged `@[category research solved]` should not use `answer(sorry)`: the answer should be filled in explicitly, e.g. `answer(True)`.

Note: This linter can be disabled with `set_option linter.style.category_answer false`
-/
#guard_msgs in

-- @@ L34-35 verbatim
/-- A solved problem should not leave its answer unfilled. -/
@[category research solved]

-- @@ L36-37 verbatim
theorem flagged_solved_answer_sorry : answer(sorry) ↔ 1 + 1 = 2 := by
  sorry


-- @@ L39-44 verbatim
/--
warning: Declarations tagged `@[category research solved]` should not use `answer(sorry)`: the answer should be filled in explicitly, e.g. `answer(True)`.

Note: This linter can be disabled with `set_option linter.style.category_answer false`
-/
#guard_msgs in

-- @@ L45-46 verbatim
/-- The `sorry` is still a placeholder when it carries a type ascription. -/
@[category research solved]

-- @@ L47-48 verbatim
theorem flagged_ascribed_answer_sorry : answer((sorry : Nat)) = 2 := by
  sorry


-- @@ L50-55 verbatim
/--
warning: Declarations tagged `@[category research solved]` should not use `answer(sorry)`: the answer should be filled in explicitly, e.g. `answer(True)`.

Note: This linter can be disabled with `set_option linter.style.category_answer false`
-/
#guard_msgs in

-- @@ L56-57 verbatim
/-- An answer bound by a `let` is flagged too. -/
@[category research solved]

-- @@ L58-63 verbatim
theorem flagged_let_answer_sorry :
    let c : Nat := answer(sorry)
    0 < c := by
  sorry

#guard_msgs in

-- @@ L64-65 verbatim
/-- A solved problem with an explicit answer is fine. -/
@[category research solved]

-- @@ L66-69 verbatim
theorem not_flagged_explicit_answer : answer(True) ↔ 1 + 1 = 2 := by
  simp

#guard_msgs in

-- @@ L70-71 verbatim
/-- An open problem may leave its answer unfilled. -/
@[category research 
-- @@ L71-71 verbatim
open]

-- @@ L72-73 verbatim
theorem not_flagged_open_answer_sorry : answer(sorry) ↔ 1 + 1 = 2 := by
  sorry


-- @@ L75-75 verbatim
end CategoryAnswerLinter
