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

public meta import FormalConjecturesUtil.Linters.AMSLinter


-- @@ L20-22 verbatim
@[expose] public section

-- Off by default; on here because this file is what tests it.

-- @@ L23-23 verbatim
set_option linter.style.ams_attribute true


-- @@ L25-27 verbatim
namespace AMSLinter

-- Definitions aren't required to have an AMS attribute

-- @@ L28-29 verbatim
#guard_msgs in
def foo : Nat := 1


-- @@ L31-39 verbatim
/--
warning: Missing AMS attribute.

Note: This linter can be disabled with `set_option linter.style.ams_attribute false`
-/
#guard_msgs in
/-- A highly non-trivial theorem -/
theorem test_theorem : 1 + 1 = 2 := by
  rfl


-- @@ L41-49 verbatim
/--
warning: Missing AMS attribute.

Note: This linter can be disabled with `set_option linter.style.ams_attribute false`
-/
#guard_msgs in
/-- A highly non-trivial theorem with a helpful hypothesis -/
theorem test_theorem_with_hypothesis (_ : True) : 1 + 1 = 2 := by
  rfl


-- @@ L51-59 verbatim
/--
warning: Missing AMS attribute.

Note: This linter can be disabled with `set_option linter.style.ams_attribute false`
-/
#guard_msgs in
/-- A highly non-trivial theorem with two helpful hypotheses -/
theorem test_theorem_with_hypotheses (_ : True) (_ : False): 1 + 1 = 2 := by
  rfl



-- @@ L62-69 verbatim
/--
warning: Missing AMS attribute.

Note: This linter can be disabled with `set_option linter.style.ams_attribute false`
-/
#guard_msgs in
lemma test_lemma : 1 + 1 = 2 := by
  rfl


-- @@ L71-78 verbatim
/--
warning: Missing AMS attribute.

Note: This linter can be disabled with `set_option linter.style.ams_attribute false`
-/
#guard_msgs in
example : 1 + 1 = 2 := by
  rfl


-- @@ L80-89 verbatim
/--
warning: The AMS tag should be formatted as AMS 1 3 rather than AMS 1, AMS 3

Note: This linter can be disabled with `set_option linter.style.ams_attribute false`
-/
#guard_msgs in
/-- A highly non-trivial theorem with a helpful hypothesis -/
@[AMS 1, AMS 3]
theorem test_theorem_with_docstring : 1 + 1 = 2 := by
  rfl


-- @@ L91-97 verbatim
#guard_msgs in
/-- A highly non-trivial theorem with a helpful hypothesis -/
@[AMS 1 3]
example: 1 + 1 = 2 := by
  rfl

-- The linter is compatible with theorems having other attributes.

-- @@ L98-103 verbatim
#guard_msgs in
@[simp, AMS 1]
theorem test_1 : 1 + 1 = 2 := by
  rfl

-- The order of attributes is irrelevant.

-- @@ L104-107 verbatim
#guard_msgs in
@[AMS 1, simp]
theorem test_3 : 1 + 1 = 2 := by
  rfl


-- @@ L109-117 verbatim
/--
warning: The AMS tags should be ordered as AMS 1 3

Note: This linter can be disabled with `set_option linter.style.ams_attribute false`
-/
#guard_msgs in
@[AMS 3 1]
theorem test_out_of_order : 1 + 1 = 2 := by
  rfl


-- @@ L119-127 verbatim
/--
warning: AMS tags contain duplicates. This should be AMS 3

Note: This linter can be disabled with `set_option linter.style.ams_attribute false`
-/
#guard_msgs in
@[AMS 3 3]
theorem test_dup : 1 + 1 = 2 := by
  rfl


-- @@ L129-129 verbatim
end AMSLinter
