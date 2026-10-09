import OAI.Combinatorics.ExpectationThreshold.SelectorDefinitions


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
/-! Elementary bounds on the literal truncation scales. -/


-- @@ L7-7 verbatim
namespace TalagrandThreshold.Selector


-- @@ L9-10 verbatim
theorem dscale_pos {s : ℕ} (i : Fin s) : 0 < dscale i := by
  exact inv_pos.mpr (pow_pos (by norm_num : (0 : ℝ) < 2) _)


-- @@ L12-13 verbatim
theorem dscale_nonneg {s : ℕ} (i : Fin s) : 0 ≤ dscale i :=
  (dscale_pos i).le


-- @@ L15-17 verbatim
theorem dscale_lt_one {s : ℕ} (i : Fin s) : dscale i < 1 := by
  exact inv_lt_one_of_one_lt₀
    (one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) (Nat.succ_ne_zero i.val))


-- @@ L19-19 verbatim
end TalagrandThreshold.Selector


-- @@ L21-21 verbatim
end OAI
