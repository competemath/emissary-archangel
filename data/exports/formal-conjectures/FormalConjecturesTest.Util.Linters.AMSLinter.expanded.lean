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


-- @@ L25-28 verbatim
namespace AMSLinter

-- Definitions aren't required to have an AMS attribute
#guard_msgs in

-- @@ L29-29 verbatim
def foo : Nat := 1


-- @@ L31-36 verbatim
/--
warning: Missing AMS attribute.

Note: This linter can be disabled with `set_option linter.style.ams_attribute false`
-/
#guard_msgs in

-- @@ L37-39 verbatim
/-- A highly non-trivial theorem -/
theorem test_theorem : 1 + 1 = 2 := by
  rfl


-- @@ L41-46 verbatim
/--
warning: Missing AMS attribute.

Note: This linter can be disabled with `set_option linter.style.ams_attribute false`
-/
#guard_msgs in

-- @@ L47-49 verbatim
/-- A highly non-trivial theorem with a helpful hypothesis -/
theorem test_theorem_with_hypothesis (_ : True) : 1 + 1 = 2 := by
  rfl


-- @@ L51-56 verbatim
/--
warning: Missing AMS attribute.

Note: This linter can be disabled with `set_option linter.style.ams_attribute false`
-/
#guard_msgs in

-- @@ L57-59 verbatim
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


-- @@ L71-76 verbatim
/--
warning: Missing AMS attribute.

Note: This linter can be disabled with `set_option linter.style.ams_attribute false`
-/
#guard_msgs in

-- @@ L77-78 verbatim
example : 1 + 1 = 2 := by
  rfl


-- @@ L80-85 verbatim
/--
warning: The AMS tag should be formatted as AMS 1 3 rather than AMS 1, AMS 3

Note: This linter can be disabled with `set_option linter.style.ams_attribute false`
-/
#guard_msgs in

-- @@ L86-91 verbatim
/-- A highly non-trivial theorem with a helpful hypothesis -/
@[AMS 1, AMS 3]
theorem test_theorem_with_docstring : 1 + 1 = 2 := by
  rfl

#guard_msgs in

-- @@ L92-93 verbatim
/-- A highly non-trivial theorem with a helpful hypothesis -/
@[AMS 1 3]

-- @@ L94-98 verbatim
example: 1 + 1 = 2 := by
  rfl

-- The linter is compatible with theorems having other attributes.
#guard_msgs in

-- @@ L99-104 verbatim
@[simp, AMS 1]
theorem test_1 : 1 + 1 = 2 := by
  rfl

-- The order of attributes is irrelevant.
#guard_msgs in

-- @@ L105-107 verbatim
@[AMS 1, simp]
theorem test_3 : 1 + 1 = 2 := by
  rfl


-- @@ L109-114 verbatim
/--
warning: The AMS tags should be ordered as AMS 1 3

Note: This linter can be disabled with `set_option linter.style.ams_attribute false`
-/
#guard_msgs in

-- @@ L115-115 verbatim
@[AMS 3 1]

-- @@ L116-117 verbatim
theorem test_out_of_order : 1 + 1 = 2 := by
  rfl


-- @@ L119-124 verbatim
/--
warning: AMS tags contain duplicates. This should be AMS 3

Note: This linter can be disabled with `set_option linter.style.ams_attribute false`
-/
#guard_msgs in

-- @@ L125-125 verbatim
@[AMS 3 3]

-- @@ L126-127 verbatim
theorem test_dup : 1 + 1 = 2 := by
  rfl


-- @@ L129-129 verbatim
end AMSLinter
