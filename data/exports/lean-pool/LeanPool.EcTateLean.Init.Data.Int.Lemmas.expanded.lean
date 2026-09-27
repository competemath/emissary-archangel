/-
Copyright (c) 2023 Alex J. Best and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
module

import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Lemma


-- @@ L11-15 verbatim
/-!
# LeanPool.EcTateLean.Init.Data.Int.Lemmas

Imported Lean Pool material for `LeanPool.EcTateLean.Init.Data.Int.Lemmas`.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
lemma mod_neg_right (m k : Int) : m % (-k) = m % k := by simp

-- @@ L20-20 verbatim
lemma div_neg_right (m k : Int) : m / (-k) = -(m / k) := by simp



-- @@ L23-23 verbatim
namespace Int


-- @@ L25-25 verbatim
@[simp] lemma ofNat_zero_eq_zero : ofNat Nat.zero = 0 := rfl


-- @@ L27-27 verbatim
end Int
