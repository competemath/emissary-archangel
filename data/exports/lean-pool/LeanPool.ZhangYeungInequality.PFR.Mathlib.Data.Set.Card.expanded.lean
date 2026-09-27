/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import Mathlib.Data.Set.Card
import LeanPool.ZhangYeungInequality.PFR.Mathlib.Data.Set.Basic


-- @@ L12-16 verbatim
/-!
# LeanPool.ZhangYeungInequality.PFR.Mathlib.Data.Set.Card

Imported Lean Pool material for `LeanPool.ZhangYeungInequality.PFR.Mathlib.Data.Set.Card`.
-/


-- @@ L18-18 verbatim
public section


-- @@ L20-20 verbatim
namespace Set

-- @@ L21-23 verbatim
variable {α : Type*}

-- TODO: Rename `ncard_singleton_inter` to `ncard_singleton_inter_le_one`


-- @@ L25-27 verbatim
lemma ncard_singleton_inter' (a : α) (s : Set α) [Decidable (a ∈ s)] :
    ({a} ∩ s).ncard = if a ∈ s then 1 else 0 := by
  split_ifs <;> simp [*]


-- @@ L29-31 verbatim
lemma ncard_inter_singleton (a : α) (s : Set α) [Decidable (a ∈ s)] :
    (s ∩ {a}).ncard = if a ∈ s then 1 else 0 := by
  split_ifs <;> simp [*]


-- @@ L33-33 verbatim
end Set
