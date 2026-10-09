import OAI.Combinatorics.Sensitivity.Construction
import OAI.Combinatorics.Sensitivity.Labeling
import OAI.Combinatorics.Sensitivity.ParameterBounds
import OAI.Combinatorics.Sensitivity.Iterates


-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-8 verbatim
/-! All construction parameters and labels are supplied unconditionally. -/


-- @@ L10-10 verbatim
noncomputable section

-- @@ L11-11 verbatim
open scoped Classical


-- @@ L13-13 verbatim
namespace Paper320


-- @@ L15-22 verbatim
theorem construction_label_count_pos {M : ℕ} (hM : 0 < M) :
    0 < Nat.ceil (Real.sqrt (M : ℝ)) := by
  have h := le_ceil_sqrt_sq M
  by_contra hn
  have he : Nat.ceil (Real.sqrt (M : ℝ)) = 0 := by omega
  rw [he] at h
  norm_num at h
  omega


-- @@ L24-41 verbatim
theorem exists_constructed_seed (d M : ℕ) (hd : 1 ≤ d) (hM : 9 ^ (d + 1) ≤ M) :
    ∃ f : (Fin (constructionDimension d M (Nat.ceil (Real.sqrt (M : ℝ)))) → Bool) → Bool,
      0 < constructionDimension d M (Nat.ceil (Real.sqrt (M : ℝ))) ∧
      f (fun _ => false) = false ∧ (∃ x y, f x ≠ f y) ∧
      sensitivity f ≤ 2 * (d + 2) * M ^ (d + 1) ∧
      M ^ 2 * (2 * M ^ 2 + 1) ^ d ≤ blockSensitivityAt f (fun _ => false) := by
  have h81 := parameter_ge_eighty_one hd hM
  have hMp : 0 < M := by omega
  have hr := construction_label_count_pos hMp
  obtain ⟨A⟩ := regular_goodLabeling_exists (show 3 ≤ M by omega)
  let f := finalWitness d (regularCyclicTournament M) A
  have hs := finalWitness_sensitivity d (regularCyclicTournament M) A hMp hr
    (parameter_epsilon_budget hd hM)
  have hb := finalWitness_blockSensitivity d (regularCyclicTournament M) A hr
  have hbp : 0 < M ^ 2 * (2 * M ^ 2 + 1) ^ d := by positivity
  have hnc := nonconstant_of_blockSensitivityAt_pos f (fun _ => false) (hbp.trans_le hb)
  exact ⟨f, constructionDimension_pos hMp hr,
    finalWitness_zero d (regularCyclicTournament M) A hr, hnc, hs, hb⟩


-- @@ L43-43 verbatim
end Paper320


-- @@ L45-45 verbatim
end


-- @@ L47-47 verbatim
end OAI
