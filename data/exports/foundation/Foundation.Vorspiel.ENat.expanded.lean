module

public import Mathlib.Data.ENat.Basic



-- @@ L6-7 verbatim
@[expose]
public section


-- @@ L9-9 verbatim
namespace ENat


-- @@ L11-11 verbatim
open Classical


-- @@ L13-13 verbatim
noncomputable def find (P : ℕ → Prop) : ℕ∞ := if h : ∃ x : ℕ, P x then Nat.find h else ⊤


-- @@ L15-15 verbatim
variable (P : ℕ → Prop)


-- @@ L17-20 verbatim
theorem lt_find (n : ℕ) (h : ∀ m ≤ n, ¬P m) : (n : ℕ∞) < find P := by
  by_cases h : ∃ x : ℕ, P x
  · simpa [find, h]
  · simp [find, h]


-- @@ L22-24 verbatim
theorem exists_of_find_le (n : ℕ) (h : find P ≤ (n : ENat)) : ∃ m ≤ n, P m := by
  by_contra A
  exact Std.Irrefl.irrefl _ <| lt_of_le_of_lt h <| lt_find P n (by simpa using A)


-- @@ L26-26 verbatim
lemma find_eq_top_iff : find P = ⊤ ↔ ∀ (n : ℕ), ¬P n := by simp [find]


-- @@ L28-30 verbatim
lemma find_le (n : ℕ) (h : P n) : find P ≤ ↑n := by
  suffices ∃ m ≤ n, P m by simpa [show ∃ x, P x from ⟨n, h⟩, find]
  exact ⟨n, by rfl, h⟩


-- @@ L32-32 verbatim
end ENat


-- @@ L34-34 verbatim
end
