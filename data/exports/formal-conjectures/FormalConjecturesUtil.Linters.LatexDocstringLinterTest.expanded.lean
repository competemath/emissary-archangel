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

public import FormalConjecturesUtil.Linters.LatexDocstringLinter


-- @@ L20-25 verbatim
/-!
# Tests for the LaTeX docstring linter

This file contains test cases for the `LatexDocstringLinter`, verifying that
docstrings with backslash-bracket, backslash-parenthesis, or legacy URL links are flagged.
-/


-- @@ L27-27 verbatim
@[expose] public section


-- @@ L29-29 verbatim
namespace LatexDocstringLinter



-- @@ L32-37 verbatim
/--
warning: Docstrings should use `$ $` or `$$ $$` for math formulas instead of `\[ \]` or `\( \)`.

Note: This linter can be disabled with `set_option linter.style.latex_docstring false`
-/
#guard_msgs in

-- @@ L38-40 verbatim
/-- This is a bad docstring with \[ math \]. -/
theorem flagged_with_bracket_math : True := by
  trivial


-- @@ L42-47 verbatim
/--
warning: Docstrings should use `$ $` or `$$ $$` for math formulas instead of `\[ \]` or `\( \)`.

Note: This linter can be disabled with `set_option linter.style.latex_docstring false`
-/
#guard_msgs in

-- @@ L48-52 verbatim
/-- This is a bad docstring with \( math \). -/
theorem flagged_with_paren_math : True := by
  trivial

#guard_msgs in

-- @@ L53-55 verbatim
/-- This is a good docstring with $$ math $$. -/
theorem not_flagged_with_good_math : True := by
  trivial


-- @@ L57-62 verbatim
/--
warning: Docstring URLs should use `[label](https://...)`, not `[label][https://...]`.

Note: This linter can be disabled with `set_option linter.style.latex_docstring false`
-/
#guard_msgs in

-- @@ L63-67 verbatim
/-- This is a bad link: [example][https://example.com]. -/
theorem flagged_with_legacy_url_link : True := by
  trivial

#guard_msgs in

-- @@ L68-70 verbatim
/-- This is a good link: [example](https://example.com). -/
theorem not_flagged_with_inline_url_link : True := by
  trivial


-- @@ L72-72 verbatim
end LatexDocstringLinter
