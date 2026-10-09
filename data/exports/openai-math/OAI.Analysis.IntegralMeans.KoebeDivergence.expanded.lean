import OAI.Analysis.IntegralMeans.AffineArea
import OAI.Analysis.IntegralMeans.KoebePolar
import OAI.Analysis.IntegralMeans.SectorDivergence


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open Set MeasureTheory

-- @@ L9-9 verbatim
open scoped ENNReal

-- @@ L10-10 verbatim
namespace Brennan.Sharp


-- @@ L12-24 verbatim
lemma koebe_negative_endpoint_area : areaMoment koebeMap disk (-2) = ⊤ := by
  have h := Sector.lintegral_eq_top_of_sector_lower_bound
    (fun w => disk.indicator
      (fun z => ENNReal.ofReal (‖deriv koebeMap z‖ ^ (-2 : ℝ))) (-1 + w))
    (1 / 2) (-(Real.pi / 3)) (Real.pi / 3) 1
    (by norm_num) (by linarith [Real.pi_pos]) (by norm_num)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    (by
      intro r hr θ hθ
      rw [Set.indicator_of_mem (polar_left_mem_disk hr hθ)]
      exact ENNReal.ofReal_le_ofReal (koebe_polar_left_lower hr hθ))
  rw [lintegral_left_disk_indicator] at h
  exact h


-- @@ L26-38 verbatim
lemma koebe_positive_endpoint_area : areaMoment koebeMap disk (2 / 3) = ⊤ := by
  have h := Sector.lintegral_eq_top_of_sector_lower_bound
    (fun w => disk.indicator
      (fun z => ENNReal.ofReal (‖deriv koebeMap z‖ ^ (2 / 3 : ℝ))) (1 - w))
    (1 / 2) (-(Real.pi / 3)) (Real.pi / 3) 1
    (by norm_num) (by linarith [Real.pi_pos]) (by norm_num)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    (by
      intro r hr θ hθ
      rw [Set.indicator_of_mem (polar_right_mem_disk hr hθ)]
      exact ENNReal.ofReal_le_ofReal (koebe_polar_right_lower hr hθ))
  rw [lintegral_right_disk_indicator] at h
  exact h


-- @@ L40-40 verbatim
end Brennan.Sharp


-- @@ L42-42 verbatim
end


-- @@ L44-44 verbatim
end OAI
