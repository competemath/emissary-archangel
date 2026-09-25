module

public import Mathlib.Data.Set.Basic


-- @@ L5-5 verbatim
public section


-- @@ L7-7 verbatim
namespace Set

-- @@ L8-10 verbatim
variable {α : Type*} {s t : Set α}

-- TODO: Rename `inter_eq_left` to `inter_eq_left_iff`

-- @@ L11-11 verbatim
@[simp] alias ⟨_, inter_eq_left'⟩ := inter_eq_left

-- @@ L12-12 verbatim
@[simp] alias ⟨_, inter_eq_right'⟩ := inter_eq_right


-- @@ L14-14 verbatim
@[simp] lemma ne_empty_iff_nonempty : s ≠ ∅ ↔ s.Nonempty := nonempty_iff_ne_empty.symm


-- @@ L16-16 verbatim
end Set
