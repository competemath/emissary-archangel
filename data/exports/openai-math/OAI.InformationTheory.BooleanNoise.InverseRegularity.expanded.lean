import OAI.InformationTheory.BooleanNoise.InverseScalars
import OAI.InformationTheory.BooleanNoise.EndpointLimits
import OAI.InformationTheory.BooleanNoise.ArtanhBounds


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
open Set Filter

-- @@ L10-10 verbatim
open scoped Topology


-- @@ L12-12 verbatim
namespace LeanBlast.CourtadeKumar


-- @@ L14-16 verbatim
theorem psi_pos_of_pos {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) : 0 < psi u := by
  simpa only [psi_zero] using
    strictMonoOn_psi (show (0 : ℝ) ∈ Icc 0 1 by norm_num) ⟨hu.le, hu1⟩ hu


-- @@ L18-21 verbatim
theorem rDeriv_psi {u : ℝ} (hu : u ∈ Ioo 0 1) :
    rDeriv (psi u) = 1 + u / ((1 - u ^ 2) * Real.artanh u) := by
  simp only [rDeriv, ite_eq_right (not_le.mpr (psi_pos_of_pos hu.1 hu.2.le)),
    psiInv_psi ⟨hu.1.le, hu.2.le⟩]


-- @@ L23-27 verbatim
theorem rSecondDeriv_psi {u : ℝ} (hu : u ∈ Ioo 0 1) :
    rSecondDeriv (psi u) = ((1 + u ^ 2) * Real.artanh u - u) /
      ((1 - u ^ 2) ^ 2 * (Real.artanh u) ^ 3) := by
  simp only [rSecondDeriv, ite_eq_right (not_le.mpr (psi_pos_of_pos hu.1 hu.2.le)),
    psiInv_psi ⟨hu.1.le, hu.2.le⟩]


-- @@ L29-41 verbatim
theorem hasDerivAt_rDerivativeFormula {u : ℝ} (hu : u ∈ Ioo 0 1) :
    HasDerivAt (fun v => 1 + v / ((1 - v ^ 2) * Real.artanh v))
      (((1 + u ^ 2) * Real.artanh u - u) /
        ((1 - u ^ 2) ^ 2 * (Real.artanh u) ^ 2)) u := by
  have ht : Real.artanh u ≠ 0 := (Real.artanh_pos hu).ne'
  have hq : 1 - u ^ 2 ≠ 0 := by nlinarith [hu.1, hu.2]
  have hd := (((hasDerivAt_id u).pow 2).const_sub 1).mul
    (hasDerivAt_artanh ⟨by linarith [hu.1], hu.2⟩)
  have h := ((hasDerivAt_id u).div hd (mul_ne_zero hq ht)).const_add 1
  convert! h using 1
  dsimp
  field_simp [hq, ht]
  ring


-- @@ L43-55 verbatim
theorem hasDerivAt_rDeriv {s : ℝ} (hs : s ∈ Ioo 0 ell) :
    HasDerivAt rDeriv (rSecondDeriv s) s := by
  have hu := psiInv_mem_Ioo hs
  have h := (hasDerivAt_rDerivativeFormula hu).comp s (hasDerivAt_psiInv hs)
  have he : rDeriv =ᶠ[𝓝 s]
      (fun z => 1 + psiInv z / ((1 - (psiInv z) ^ 2) * Real.artanh (psiInv z))) := by
    filter_upwards [Ioi_mem_nhds hs.1] with z hz
    simp only [rDeriv, ite_eq_right (not_le.mpr (show 0 < z from hz))]
  apply (h.congr_of_eventuallyEq he).congr_deriv
  have ht : Real.artanh (psiInv s) ≠ 0 := (Real.artanh_pos hu).ne'
  have hq : 1 - (psiInv s) ^ 2 ≠ 0 := by nlinarith [hu.1, hu.2]
  simp only [rSecondDeriv, ite_eq_right (not_le.mpr hs.1)]
  field_simp [hq, ht]


-- @@ L57-58 verbatim
theorem continuousOn_rGap : ContinuousOn rGap (Ico 0 ell) :=
  continuousOn_r.sub (continuous_const.mul continuous_id).continuousOn


-- @@ L60-63 verbatim
theorem hasDerivAt_rGap {s : ℝ} (hs : s ∈ Ioo 0 ell) :
    HasDerivAt rGap (rDeriv s - 2) s := by
  convert! (hasDerivAt_r hs).sub ((hasDerivAt_id s).const_mul 2) using 1
  simp


-- @@ L65-70 verbatim
theorem L_ell_sub {s : ℝ} (hs : 0 ≤ s) (hsell : s < ell) :
    L (ell - s) = r s - 2 * s := by
  rcases hs.eq_or_lt with rfl | hs
  · simp [L]
  · have hx : 0 < ell - s ∧ ell - s < ell := by constructor <;> linarith
    simp only [L, ite_eq_left hx, rGap, sub_sub_cancel]


-- @@ L72-74 verbatim
theorem L_entropy {u : ℝ} (hu : u ∈ Ioo (-1) 1) :
    L (entropy u) = r (psi u) - 2 * psi u :=
  L_ell_sub (psi_nonneg u) (psi_lt_ell hu)


-- @@ L76-82 verbatim
theorem LDeriv_entropy {u : ℝ} (hu : u ∈ Ioo 0 1) :
    LDeriv (entropy u) = 2 - rDeriv (psi u) := by
  have hp := psi_pos_of_pos hu.1 hu.2.le
  have hpl := psi_lt_ell (show u ∈ Ioo (-1) 1 by constructor <;> linarith [hu.1, hu.2])
  have hx : 0 < entropy u ∧ entropy u < ell := by unfold entropy; constructor <;> linarith
  rw [LDeriv, ite_eq_left hx]
  simp only [entropy, sub_sub_cancel]


-- @@ L84-93 verbatim
theorem hasDerivAt_L_of_lt {x : ℝ} (hx : x ∈ Ioo 0 ell) :
    HasDerivAt L (LDeriv x) x := by
  have hs : ell - x ∈ Ioo 0 ell := by constructor <;> linarith [hx.1, hx.2]
  have h := (hasDerivAt_rGap hs).comp x ((hasDerivAt_id x).const_sub ell)
  have he : L =ᶠ[𝓝 x] (fun z => rGap (ell - z)) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with z hz
    exact L_eq_rGap hz
  apply (h.congr_of_eventuallyEq he).congr_deriv
  rw [LDeriv, ite_eq_left (show 0 < x ∧ x < ell from hx)]
  ring


-- @@ L95-103 verbatim
theorem hasDerivAt_LDeriv_of_lt {x : ℝ} (hx : x ∈ Ioo 0 ell) :
    HasDerivAt LDeriv (rSecondDeriv (ell - x)) x := by
  have hs : ell - x ∈ Ioo 0 ell := by constructor <;> linarith [hx.1, hx.2]
  have h := ((hasDerivAt_rDeriv hs).comp x ((hasDerivAt_id x).const_sub ell)).const_sub 2
  have he : LDeriv =ᶠ[𝓝 x] (fun z => 2 - rDeriv (ell - z)) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with z hz
    exact ite_eq_left hz
  apply (h.congr_of_eventuallyEq he).congr_deriv
  ring


-- @@ L105-116 verbatim
theorem rDeriv_ge_two {s : ℝ} (hs : 0 ≤ s) (hsell : s < ell) : 2 ≤ rDeriv s := by
  rcases hs.eq_or_lt with rfl | hs
  · simp
  · have hu := psiInv_mem_Ioo ⟨hs, hsell⟩
    have hq : 0 < 1 - (psiInv s) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hu.2) (show 0 < 1 + psiInv s by linarith [hu.1])]
    have ht := Real.artanh_pos hu
    have hb := one_sub_sq_mul_artanh_le_self ⟨hu.1.le, hu.2⟩
    have hd : 1 ≤ psiInv s / ((1 - (psiInv s) ^ 2) * Real.artanh (psiInv s)) :=
      (le_div_iff₀ (mul_pos hq ht)).mpr (by simpa using hb)
    simp only [rDeriv, ite_eq_right (not_le.mpr hs)]
    linarith


-- @@ L118-127 verbatim
theorem rSecondDeriv_pos {s : ℝ} (hs : s ∈ Ioo 0 ell) : 0 < rSecondDeriv s := by
  have hu := psiInv_mem_Ioo hs
  have hq : 0 < 1 - (psiInv s) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hu.2) (show 0 < 1 + psiInv s by linarith [hu.1])]
  have ht := Real.artanh_pos hu
  have hb := self_le_artanh ⟨hu.1.le, hu.2⟩
  have hn : 0 < (1 + (psiInv s) ^ 2) * Real.artanh (psiInv s) - psiInv s := by
    nlinarith [mul_pos (sq_pos_of_pos hu.1) ht]
  simp only [rSecondDeriv, ite_eq_right (not_le.mpr hs.1)]
  exact div_pos hn (mul_pos (sq_pos_of_pos hq) (pow_pos ht 3))


-- @@ L129-133 verbatim
theorem rSecondDeriv_nonneg {s : ℝ} (hs : 0 ≤ s) (hsell : s < ell) :
    0 ≤ rSecondDeriv s := by
  rcases hs.eq_or_lt with rfl | hs
  · norm_num
  · exact (rSecondDeriv_pos ⟨hs, hsell⟩).le


-- @@ L135-143 verbatim
theorem convexOn_r : ConvexOn ℝ (Ico 0 ell) r := by
  refine convexOn_of_hasDerivWithinAt2_nonneg
    (f' := rDeriv) (f'' := rSecondDeriv) (convex_Ico 0 ell) continuousOn_r ?_ ?_ ?_
  · intro s hs
    exact (hasDerivAt_r (by simpa using hs)).hasDerivWithinAt
  · intro s hs
    exact (hasDerivAt_rDeriv (by simpa using hs)).hasDerivWithinAt
  · intro s hs
    exact (rSecondDeriv_pos (by simpa using hs)).le


-- @@ L145-155 verbatim
theorem convexOn_rGap : ConvexOn ℝ (Ico 0 ell) rGap := by
  refine convexOn_of_hasDerivWithinAt2_nonneg
    (f' := fun s => rDeriv s - 2) (f'' := rSecondDeriv)
    (convex_Ico 0 ell) continuousOn_rGap ?_ ?_ ?_
  · intro s hs
    exact (hasDerivAt_rGap (by simpa using hs)).hasDerivWithinAt
  · intro s hs
    simpa only [sub_zero] using
      ((hasDerivAt_rDeriv (by simpa using hs)).sub_const 2).hasDerivWithinAt
  · intro s hs
    exact (rSecondDeriv_pos (by simpa using hs)).le


-- @@ L157-164 verbatim
theorem monotoneOn_rGap : MonotoneOn rGap (Ico 0 ell) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun s => rDeriv s - 2)
    (convex_Ico 0 ell) continuousOn_rGap ?_ ?_
  · intro s hs
    exact (hasDerivAt_rGap (by simpa using hs)).hasDerivWithinAt
  · intro s hs
    have hs' : s ∈ Ioo 0 ell := by simpa using hs
    exact sub_nonneg.mpr (rDeriv_ge_two hs'.1.le hs'.2)


-- @@ L166-167 verbatim
theorem rGap_nonneg {s : ℝ} (hs : 0 ≤ s) (hsell : s < ell) : 0 ≤ rGap s := by
  simpa only [rGap_zero] using monotoneOn_rGap ⟨le_rfl, ell_pos⟩ ⟨hs, hsell⟩ hs


-- @@ L169-181 verbatim
theorem monotoneOn_rDeriv : MonotoneOn rDeriv (Ico 0 ell) := by
  have hm : MonotoneOn rDeriv (Ioo 0 ell) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := rSecondDeriv)
      (convex_Ioo 0 ell) ?_ ?_ ?_
    · exact fun s hs => (hasDerivAt_rDeriv hs).continuousAt.continuousWithinAt
    · intro s hs
      exact (hasDerivAt_rDeriv (by simpa using hs)).hasDerivWithinAt
    · intro s hs
      exact (rSecondDeriv_pos (by simpa using hs)).le
  intro s hs t ht hst
  rcases hs.1.eq_or_lt with rfl | hs0
  · simpa only [rDeriv_zero] using rDeriv_ge_two ht.1 ht.2
  · exact hm ⟨hs0, hs.2⟩ ⟨lt_of_lt_of_le hs0 hst, ht.2⟩ hst


-- @@ L183-189 verbatim
theorem tendsto_psiInv_zero_right : Tendsto psiInv (𝓝[>] 0) (𝓝[>] 0) := by
  have hc : Tendsto psiInv (𝓝[≥] 0) (𝓝 0) := by
    simpa only [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE ell_pos, psiInv_zero] using
      continuousOn_psiInv 0 ⟨le_rfl, ell_pos.le⟩
  refine tendsto_nhdsWithin_iff.mpr ⟨hc.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self), ?_⟩
  filter_upwards [Ioo_mem_nhdsGT ell_pos] with s hs
  exact (psiInv_mem_Ioo hs).1


-- @@ L191-194 verbatim
theorem tendsto_rDeriv_zero_right : Tendsto rDeriv (𝓝[>] 0) (𝓝 2) := by
  apply (tendsto_entropy_inverse_derivative_zero_right.comp tendsto_psiInv_zero_right).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Function.comp_apply, rDeriv, ite_eq_right (not_le.mpr (show 0 < s from hs))]


-- @@ L196-199 verbatim
theorem tendsto_rSecondDeriv_zero_right : Tendsto rSecondDeriv (𝓝[>] 0) (𝓝 (4 / 3 : ℝ)) := by
  apply (tendsto_entropy_inverse_second_derivative_zero_right.comp tendsto_psiInv_zero_right).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Function.comp_apply, rSecondDeriv, ite_eq_right (not_le.mpr (show 0 < s from hs))]


-- @@ L201-211 verbatim
theorem continuousOn_rDeriv : ContinuousOn rDeriv (Ico 0 ell) := by
  intro s hs
  rcases hs.1.eq_or_lt with rfl | hs0
  · have hright : ContinuousWithinAt rDeriv (Ioi 0) 0 := by
      simpa only [ContinuousWithinAt, rDeriv_zero] using tendsto_rDeriv_zero_right
    apply hright.insert.mono
    intro s hs
    rcases hs.1.eq_or_lt with h | h
    · exact Or.inl h.symm
    · exact Or.inr h
  · exact (hasDerivAt_rDeriv ⟨hs0, hs.2⟩).continuousAt.continuousWithinAt


-- @@ L213-217 verbatim
theorem tendsto_r_div_zero_right :
    Tendsto (fun s : ℝ => r s / s) (𝓝[>] 0) (𝓝 2) := by
  apply (tendsto_artanh_mul_id_div_psi_zero_right.comp tendsto_psiInv_zero_right).congr'
  filter_upwards [Ioo_mem_nhdsGT ell_pos] with s hs
  simp only [Function.comp_apply, r, psi_psiInv hs.1.le hs.2]


-- @@ L219-225 verbatim
theorem hasDerivWithinAt_r_zero : HasDerivWithinAt r 2 (Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope, Ici_sdiff_left]
  have he : slope r 0 = fun s : ℝ => r s / s := by
    ext s
    simp only [slope_def_field, r_zero, sub_zero]
  rw [he]
  exact tendsto_r_div_zero_right


-- @@ L227-230 verbatim
theorem hasDerivWithinAt_rGap_zero : HasDerivWithinAt rGap 0 (Ici 0) 0 := by
  convert! hasDerivWithinAt_r_zero.sub
    (((hasDerivAt_id (0 : ℝ)).const_mul 2).hasDerivWithinAt) using 1
  simp


-- @@ L232-236 verbatim
theorem monotoneOn_r : MonotoneOn r (Ico 0 ell) := by
  intro s hs t ht hst
  have h := monotoneOn_rGap hs ht hst
  unfold rGap at h
  linarith


-- @@ L238-258 verbatim
theorem hasDerivWithinAt_rDeriv_zero :
    HasDerivWithinAt rDeriv (4 / 3 : ℝ) (Ici 0) 0 := by
  have hlim : Tendsto (fun s : ℝ => (rDeriv s - 2) / s)
      (𝓝[>] 0) (𝓝 (4 / 3 : ℝ)) := by
    apply HasDerivAt.lhopital_zero_right_on_Ioo
      (f' := rSecondDeriv) (g' := fun _ => 1) ell_pos
    · intro s hs
      exact (hasDerivAt_rDeriv hs).sub_const 2
    · intro s _
      exact hasDerivAt_id s
    · intro s _
      norm_num
    · simpa using tendsto_rDeriv_zero_right.sub (tendsto_const_nhds (x := (2 : ℝ)))
    · exact tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    · simpa using tendsto_rSecondDeriv_zero_right
  rw [hasDerivWithinAt_iff_tendsto_slope, Ici_sdiff_left]
  have he : slope rDeriv 0 = fun s : ℝ => (rDeriv s - 2) / s := by
    ext s
    simp only [slope_def_field, rDeriv_zero, sub_zero]
  rw [he]
  exact hlim


-- @@ L260-260 verbatim
end LeanBlast.CourtadeKumar


-- @@ L262-262 verbatim
end


-- @@ L264-264 verbatim
end OAI
