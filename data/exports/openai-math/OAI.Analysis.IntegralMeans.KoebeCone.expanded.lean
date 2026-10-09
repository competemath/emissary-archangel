import OAI.Analysis.IntegralMeans.KoebeReduction


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
namespace Brennan.Sharp


-- @@ L9-19 verbatim
lemma right_cone_mem_disk {w : ℂ}
    (h0 : 0 < ‖w‖) (hsmall : ‖w‖ < 1 / 2)
    (hcone : ‖w‖ / 2 ≤ w.re) : 1 - w ∈ disk := by
  have hsq : ‖1 - w‖ ^ 2 = 1 - 2 * w.re + ‖w‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  have hsmall' : ‖w‖ ^ 2 < ‖w‖ := by nlinarith
  have hnorm : ‖1 - w‖ < 1 := by
    nlinarith [norm_nonneg (1 - w)]
  simpa only [disk, Metric.mem_ball, dist_zero_right] using hnorm


-- @@ L21-26 verbatim
lemma left_cone_mem_disk {w : ℂ}
    (h0 : 0 < ‖w‖) (hsmall : ‖w‖ < 1 / 2)
    (hcone : ‖w‖ / 2 ≤ w.re) : -1 + w ∈ disk := by
  have hr := right_cone_mem_disk h0 hsmall hcone
  have hid : (-1 : ℂ) + w = -(1 - w) := by ring
  simpa only [disk, Metric.mem_ball, dist_zero_right, hid, norm_neg] using hr


-- @@ L28-31 verbatim
lemma norm_rpow_neg_two (w : ℂ) :
    ‖w‖ ^ (-2 : ℝ) = 1 / ‖w‖ ^ 2 := by
  simpa only [Real.rpow_two, one_div] using
    Real.rpow_neg (norm_nonneg w) (2 : ℝ)


-- @@ L33-38 verbatim
lemma koebe_left_cone_lower {w : ℂ}
    (h0 : 0 < ‖w‖) (hsmall : ‖w‖ < 1 / 2)
    (hcone : ‖w‖ / 2 ≤ w.re) :
    1 / ‖w‖ ^ 2 ≤ ‖deriv koebeMap (-1 + w)‖ ^ (-2 : ℝ) := by
  rw [← norm_rpow_neg_two]
  exact koebe_negative_endpoint_lower (left_cone_mem_disk h0 hsmall hcone) hsmall


-- @@ L40-45 verbatim
lemma koebe_right_cone_lower {w : ℂ}
    (h0 : 0 < ‖w‖) (hsmall : ‖w‖ < 1 / 2)
    (hcone : ‖w‖ / 2 ≤ w.re) :
    1 / ‖w‖ ^ 2 ≤ ‖deriv koebeMap (1 - w)‖ ^ (2 / 3 : ℝ) := by
  rw [← norm_rpow_neg_two]
  exact koebe_positive_endpoint_lower (right_cone_mem_disk h0 hsmall hcone) h0 hsmall


-- @@ L47-47 verbatim
end Brennan.Sharp


-- @@ L49-49 verbatim
end


-- @@ L51-51 verbatim
end OAI
