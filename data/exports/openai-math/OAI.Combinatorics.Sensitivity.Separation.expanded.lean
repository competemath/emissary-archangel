import OAI.Combinatorics.Sensitivity.SeedAmplification


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
/-! Quantitative, unbounded quadratic, and fixed-power separations of sensitivity. -/


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped Classical


-- @@ L10-10 verbatim
namespace Paper320


-- @@ L12-21 verbatim
theorem quantitative_separation (d : ℕ) (hd : 1 ≤ d) :
    ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      0 < n ∧ f (fun _ => false) = false ∧
      (∃ x y : Fin n → Bool, f x ≠ f y) ∧
      (2 : ℝ) ^ d / (4 * ((d : ℝ) + 2) ^ 2) ≤
        (blockSensitivity f : ℝ) / (sensitivity f : ℝ) ^ 2 := by
  let M : ℕ := 9 ^ (d + 1)
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨f, hn, hf, hnc, hs, hb⟩ := exists_constructed_seed d M hd (by rfl)
  exact ⟨_, f, hn, hf, hnc, quantitative_ratio_of_bounds f d M hM hnc hs hb⟩


-- @@ L23-34 verbatim
theorem unbounded_quadratic_separation (C : ℝ) (hC : 0 < C) :
    ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      0 < n ∧ f (fun _ => false) = false ∧
      (∃ x y : Fin n → Bool, f x ≠ f y) ∧
      C * (sensitivity f : ℝ) ^ 2 < (blockSensitivity f : ℝ) := by
  obtain ⟨d, hd, hlarge⟩ := ((Filter.eventually_ge_atTop (1 : ℕ)).and
    (quantitative_ratio_tendsto.eventually_gt_atTop (max C 0))).exists
  rw [max_eq_left hC.le] at hlarge
  obtain ⟨n, f, hn, hf, hnc, hratio⟩ := quantitative_separation d hd
  have hs : (0 : ℝ) < sensitivity f := by
    exact_mod_cast sensitivity_pos_of_nonconstant f hnc
  exact ⟨n, f, hn, hf, hnc, (lt_div_iff₀ (pow_pos hs 2)).mp (hlarge.trans_le hratio)⟩


-- @@ L36-51 verbatim
theorem fixed_power_separation :
    ∃ α : ℝ, 2 < α ∧
      ∃ (n : ℕ → ℕ) (F : ∀ m : ℕ, (Fin (n m) → Bool) → Bool),
        (∀ m : ℕ, 1 ≤ m →
          0 < n m ∧ F m (fun _ => false) = false ∧
          (∃ x y : Fin (n m) → Bool, F m x ≠ F m y) ∧
          (sensitivity (F m) : ℝ) ^ α ≤
            (blockSensitivityAt (F m) (fun _ => false) : ℝ)) ∧
        Filter.Tendsto
          (fun m : ℕ => (blockSensitivityAt (F m) (fun _ => false) : ℝ))
          Filter.atTop Filter.atTop := by
  obtain ⟨α, hα, n, F, hall, hlim⟩ := constructed_power_family
  refine ⟨α, hα, n, F, ?_, hlim⟩
  intro m _
  obtain ⟨hn, hf, hnc, hpow, _⟩ := hall m
  exact ⟨hn, hf, hnc, hpow⟩


-- @@ L53-53 verbatim
end Paper320


-- @@ L55-55 verbatim
end


-- @@ L57-57 verbatim
end OAI
