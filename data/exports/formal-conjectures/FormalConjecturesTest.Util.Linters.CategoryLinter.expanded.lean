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


-- @@ L25-28 verbatim
namespace CategoryLinter

-- Definitions aren't required to have a category attribute
#guard_msgs in

-- @@ L29-29 verbatim
def foo : Nat := 1


-- @@ L31-36 verbatim
/--
warning: Missing problem category attribute

Note: This linter can be disabled with `set_option linter.style.category_attribute false`
-/
#guard_msgs in

-- @@ L37-39 verbatim
/-- A highly non-trivial theorem -/
theorem test_theorem : 1 + 1 = 2 := by
  rfl


-- @@ L41-46 verbatim
/--
warning: Missing problem category attribute

Note: This linter can be disabled with `set_option linter.style.category_attribute false`
-/
#guard_msgs in

-- @@ L47-49 verbatim
/-- A highly non-trivial theorem with a helpful hypothesis -/
theorem test_theorem_with_hypothesis (_ : True) : 1 + 1 = 2 := by
  rfl


-- @@ L51-56 verbatim
/--
warning: Missing problem category attribute

Note: This linter can be disabled with `set_option linter.style.category_attribute false`
-/
#guard_msgs in

-- @@ L57-59 verbatim
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


-- @@ L71-76 verbatim
/--
warning: Missing problem category attribute

Note: This linter can be disabled with `set_option linter.style.category_attribute false`
-/
#guard_msgs in

-- @@ L77-78 verbatim
example : 1 + 1 = 2 := by
  rfl


-- @@ L80-85 verbatim
/--
warning: If a problem has a sorry-free proof, it should not be categorised as `open`.

Note: This linter can be disabled with `set_option linter.style.category_attribute false`
-/
#guard_msgs in

-- @@ L86-87 verbatim
/-- A highly non-trivial theorem with a helpful hypothesis -/
@[category research 
-- @@ L87-87 verbatim
open]

-- @@ L88-89 verbatim
theorem test_theorem_with_docstring : 1 + 1 = 2 := by
  rfl


-- @@ L91-96 verbatim
/--
warning: If a problem has a sorry-free proof, it should not be categorised as `open`.

Note: This linter can be disabled with `set_option linter.style.category_attribute false`
-/
#guard_msgs in

-- @@ L97-97 verbatim
@[category research 
-- @@ L97-104 verbatim
open]
lemma test_lemma_sorry_free : 1 + 1 = 2 := by
  rfl

-- The `category` attribute on an `example` records no tag, and an `example` leaves no
-- declaration to look a proof up under, so the sorry-free check cannot reach it. The
-- attribute check above still applies.
#guard_msgs in

-- @@ L105-105 verbatim
@[category research 
-- @@ L105-105 verbatim
open]

-- @@ L106-107 verbatim
example : 1 + 1 = 2 := by
  rfl


-- @@ L109-114 verbatim
/--
warning: If a problem has a sorry-free proof, it should not be categorised as `open`.

Note: This linter can be disabled with `set_option linter.style.category_attribute false`
-/
#guard_msgs in

-- @@ L115-115 verbatim
@[category research 
-- @@ L115-115 verbatim
open]

-- @@ L116-119 verbatim
private theorem test_private_sorry_free : 1 + 1 = 2 := by
  rfl

-- A proof given by match alternatives rather than `:=` is still a `declVal`.

-- @@ L120-125 verbatim
/--
warning: Missing problem category attribute

Note: This linter can be disabled with `set_option linter.style.category_attribute false`
-/
#guard_msgs in

-- @@ L126-131 verbatim
/-- A highly non-trivial theorem proved by cases -/
theorem test_theorem_match : ∀ l : List Nat, l = l
  | [] => rfl
  | _ :: _ => rfl

#guard_msgs in

-- @@ L132-132 verbatim
@[category research 
-- @@ L132-132 verbatim
open]

-- @@ L133-137 verbatim
theorem test_2 : 1 + 1 = 3 := by
  sorry

-- The linter is compatible with theorems having other attributes.
#guard_msgs in

-- @@ L138-138 verbatim
@[simp, category research 
-- @@ L138-138 verbatim
open]

-- @@ L139-143 verbatim
theorem test_1 : 1 + 1 = 3 := by
  sorry

-- The order of attributes is irrelevant.
#guard_msgs in

-- @@ L144-144 verbatim
@[category research 
-- @@ L144-144 verbatim
open, simp]

-- @@ L145-146 verbatim
theorem test_3 : 1 + 1 = 3 := by
  sorry


-- @@ L148-153 verbatim
/--
warning: Duplicate category attribute. There should be only one category attribute per declaration

Note: This linter can be disabled with `set_option linter.style.category_attribute false`
-/
#guard_msgs in

-- @@ L154-154 verbatim
@[category research solved, category test]

-- @@ L155-156 verbatim
theorem test_duplicate_category : 1 + 1 = 2 := by
  rfl


-- @@ L158-158 verbatim
end CategoryLinter
