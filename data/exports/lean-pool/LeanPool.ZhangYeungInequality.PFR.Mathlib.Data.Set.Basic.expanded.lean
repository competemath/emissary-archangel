/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.ToDual
import Mathlib.Data.Set.Basic


-- @@ L13-17 verbatim
/-!
# LeanPool.ZhangYeungInequality.PFR.Mathlib.Data.Set.Basic

Imported Lean Pool material for `LeanPool.ZhangYeungInequality.PFR.Mathlib.Data.Set.Basic`.
-/


-- @@ L19-19 verbatim
public section


-- @@ L21-21 verbatim
namespace Set

-- @@ L22-24 verbatim
variable {α : Type*} {s t : Set α}

-- TODO: Rename `inter_eq_left` to `inter_eq_left_iff`

-- @@ L25-25 verbatim
@[simp] alias ⟨_, inter_eq_left'⟩ := inter_eq_left

-- @@ L26-26 verbatim
@[simp] alias ⟨_, inter_eq_right'⟩ := inter_eq_right


-- @@ L28-28 verbatim
end Set
