import OAI.Combinatorics.SphericalRamsey.Parameter
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith


-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
namespace GrahamSpherical


-- @@ L11-11 verbatim
theorem parameter_den_pos : 0 < 1 + parameter ^ 2 := by positivity


-- @@ L13-16 verbatim
theorem u_sq_add_v_sq : u ^ 2 + v ^ 2 = 1 := by
  unfold u v
  field_simp [ne_of_gt parameter_den_pos]
  ring


-- @@ L18-20 verbatim
theorem v_pos : 0 < v := by
  have ht : 0 < parameter := by linarith [parameter_bounds.1]
  exact div_pos (mul_pos (by norm_num) ht) parameter_den_pos


-- @@ L22-27 verbatim
theorem v_lt_u : v < u := by
  apply (div_lt_div_iff_of_pos_right parameter_den_pos).2
  have ht := parameter_bounds
  have hprod : 0 ≤ (12 / 100 - parameter) * (12 / 100 + parameter) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith


-- @@ L29-33 verbatim
theorem u_lt_one : u < 1 := by
  change (1 - parameter ^ 2) / (1 + parameter ^ 2) < 1
  apply (div_lt_one parameter_den_pos).2
  have ht : 0 < parameter := by linarith [parameter_bounds.1]
  nlinarith [sq_pos_of_pos ht]


-- @@ L35-35 verbatim
theorem u_pos : 0 < u := lt_trans v_pos v_lt_u


-- @@ L37-37 verbatim
end GrahamSpherical


-- @@ L39-39 verbatim
end


-- @@ L41-41 verbatim
end OAI
