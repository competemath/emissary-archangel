/-
Copyright 2025 The Formal Conjectures Authors.

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

public meta import FormalConjecturesUtil.Linters.CategoryLinter


-- @@ L20-22 verbatim
@[expose] public section

-- Off by default; on here because this file is what tests it.

-- @@ L23-23 verbatim
set_option linter.style.category_attribute true


-- @@ L25-27 verbatim
namespace CategoryLinter

-- Definitions aren't required to have a category attribute

-- @@ L28-29 verbatim
#guard_msgs in
def foo : Nat := 1


-- @@ L31-39 verbatim
/--
warning: Missing problem category attribute

Note: This linter can be disabled with `set_option linter.style.category_attribute false`
-/
#guard_msgs in
/-- A highly non-trivial theorem -/
theorem test_theorem : 1 + 1 = 2 := by
  rfl


-- @@ L41-49 verbatim
/--
warning: Missing problem category attribute

Note: This linter can be disabled with `set_option linter.style.category_attribute false`
-/
#guard_msgs in
/-- A highly non-trivial theorem with a helpful hypothesis -/
theorem test_theorem_with_hypothesis (_ : True) : 1 + 1 = 2 := by
  rfl


-- @@ L51-59 verbatim
/--
warning: Missing problem category attribute

Note: This linter can be disabled with `set_option linter.style.category_attribute false`
-/
#guard_msgs in
/-- A highly non-trivial theorem with two helpful hypotheses -/
theorem test_theorem_with_hypotheses (_ : True) (_ : False): 1 + 1 = 2 := by
  rfl



-- @@ L62-69 verbatim
/--
warning: Missing problem category attribute

Note: This linter can be disabled with `set_option linter.style.category_attribute false`
-/
#guard_msgs in
lemma test_lemma : 1 + 1 = 2 := by
  rfl


-- @@ L71-78 verbatim
/--
warning: Missing problem category attribute

Note: This linter can be disabled with `set_option linter.style.category_attribute false`
-/
#guard_msgs in
example : 1 + 1 = 2 := by
  rfl


-- @@ L80-89 verbatim
/--
warning: If a problem has a sorry-free proof, it should not be categorised as `open`.

Note: This linter can be disabled with `set_option linter.style.category_attribute false`
-/
#guard_msgs in
/-- A highly non-trivial theorem with a helpful hypothesis -/
@[category research open]
theorem test_theorem_with_docstring : 1 + 1 = 2 := by
  rfl


-- @@ L91-103 verbatim
/--
warning: If a problem has a sorry-free proof, it should not be categorised as `open`.

Note: This linter can be disabled with `set_option linter.style.category_attribute false`
-/
#guard_msgs in
@[category research open]
lemma test_lemma_sorry_free : 1 + 1 = 2 := by
  rfl

-- The `category` attribute on an `example` records no tag, and an `example` leaves no
-- declaration to look a proof up under, so the sorry-free check cannot reach it. The
-- attribute check above still applies.

-- @@ L104-107 verbatim
#guard_msgs in
@[category research open]
example : 1 + 1 = 2 := by
  rfl


-- @@ L109-119 verbatim
/--
warning: If a problem has a sorry-free proof, it should not be categorised as `open`.

Note: This linter can be disabled with `set_option linter.style.category_attribute false`
-/
#guard_msgs in
@[category research open]
private theorem test_private_sorry_free : 1 + 1 = 2 := by
  rfl

-- A proof given by match alternatives rather than `:=` is still a `declVal`.

-- @@ L120-129 verbatim
/--
warning: Missing problem category attribute

Note: This linter can be disabled with `set_option linter.style.category_attribute false`
-/
#guard_msgs in
/-- A highly non-trivial theorem proved by cases -/
theorem test_theorem_match : ∀ l : List Nat, l = l
  | [] => rfl
  | _ :: _ => rfl


-- @@ L131-136 verbatim
#guard_msgs in
@[category research open]
theorem test_2 : 1 + 1 = 3 := by
  sorry

-- The linter is compatible with theorems having other attributes.

-- @@ L137-142 verbatim
#guard_msgs in
@[simp, category research open]
theorem test_1 : 1 + 1 = 3 := by
  sorry

-- The order of attributes is irrelevant.

-- @@ L143-146 verbatim
#guard_msgs in
@[category research open, simp]
theorem test_3 : 1 + 1 = 3 := by
  sorry


-- @@ L148-156 verbatim
/--
warning: Duplicate category attribute. There should be only one category attribute per declaration

Note: This linter can be disabled with `set_option linter.style.category_attribute false`
-/
#guard_msgs in
@[category research solved, category test]
theorem test_duplicate_category : 1 + 1 = 2 := by
  rfl


-- @@ L158-158 verbatim
end CategoryLinter
