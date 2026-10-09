import OAI.MeasureTheory.SelfSimilar.RadiusGrowth


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
section

-- @@ L6-6 verbatim
open scoped BigOperators ENNReal

-- @@ L7-7 verbatim
open MeasureTheory

-- @@ L8-8 verbatim
open MeasureTheory Metric Set Filter

-- @@ L9-9 verbatim
open scoped Topology ENNReal

-- @@ L10-10 verbatim
open MeasureTheory Filter Set ProbabilityTheory

-- @@ L11-11 verbatim
open scoped Topology

-- @@ L12-12 verbatim
open MeasureTheory Metric Set Filter

-- @@ L13-13 verbatim
open scoped ENNReal Topology

-- @@ L14-14 verbatim
open MeasureTheory Filter Set

-- @@ L15-15 verbatim
open scoped Topology BigOperators

-- @@ L16-16 verbatim
open Set Filter

-- @@ L17-17 verbatim
open scoped Topology


-- @@ L19-19 verbatim
namespace EntropyRateDimension

-- @@ L20-20 verbatim
namespace Interpolation


-- @@ L22-103 verbatim
theorem tendsto_div_of_bounded_gaps {F : ℝ → ℝ} {t : ℕ → ℝ} {C d : ℝ}
    (hF : Monotone F) (ht : Monotone t) (ht0 : t 0 = 0)
    (hstep : ∀ n, t (n+1) ≤ t n+C) (htop : Tendsto t atTop atTop)
    (hlim : Tendsto (fun n => F (t n) / t n) atTop (𝓝 d)) :
    Tendsto (fun s => F s / s) atTop (𝓝 d) := by
  have hex : ∀ s : ℝ, ∃ n : ℕ, s < t n := fun s =>
    (htop.eventually (eventually_gt_atTop s)).exists
  let I : ℝ → ℕ := fun s => Nat.find (hex s)
  have hI : ∀ s, s < t (I s) := fun s => Nat.find_spec (hex s)
  have hItop : Tendsto I atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro N
    filter_upwards [eventually_ge_atTop (t N)] with s hs
    by_contra hn
    have hm := ht (le_of_not_ge hn)
    linarith [hI s]
  have hPtop : Tendsto (fun s => I s-1) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro N
    filter_upwards [(Filter.tendsto_atTop.mp hItop) (N+1)] with s hs
    omega
  have hbracket : ∀ s : ℝ, 0 ≤ s →
      t (I s-1) ≤ s ∧ s < t (I s) ∧ t (I s) ≤ s+C ∧ s-C ≤ t (I s-1) := by
    intro s hs
    have hi : 0 < I s := by
      by_contra hn
      have hz : I s = 0 := by omega
      have hh := hI s
      rw [hz,ht0] at hh
      linarith
    have hprev : t (I s-1) ≤ s := by
      exact le_of_not_gt (Nat.find_min (hex s) (by change I s-1 < I s; omega))
    have hst := hstep (I s-1)
    rw [Nat.sub_add_cancel hi] at hst
    exact ⟨hprev,hI s,by linarith,by linarith [hI s]⟩
  have hsmall : Tendsto (fun s : ℝ => C/s) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hUdiff : Tendsto (fun s : ℝ => t (I s)/s-1) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hsmall
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
      exact sub_nonneg.mpr ((le_div_iff₀ hs).mpr (by simpa using (hI s).le))
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
      have hh := (div_le_div_of_nonneg_right (hbracket s hs.le).2.2.1 hs.le)
      rw [add_div,div_self hs.ne'] at hh
      linarith
  have hU : Tendsto (fun s : ℝ => t (I s)/s) atTop (𝓝 1) := by
    have hh := hUdiff.add_const 1
    simpa only [sub_add_cancel,zero_add] using hh
  have hLdiff : Tendsto (fun s : ℝ => 1-t (I s-1)/s) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hsmall
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
      exact sub_nonneg.mpr ((div_le_one hs).mpr (hbracket s hs.le).1)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
      have hh := div_le_div_of_nonneg_right (hbracket s hs.le).2.2.2 hs.le
      rw [sub_div,div_self hs.ne'] at hh
      linarith
  have hL : Tendsto (fun s : ℝ => t (I s-1)/s) atTop (𝓝 1) := by
    have hh := (tendsto_const_nhds (x := (1 : ℝ))).sub hLdiff
    simpa only [sub_sub_cancel,sub_zero] using hh
  have hUF : Tendsto (fun s : ℝ => F (t (I s))/s) atTop (𝓝 d) := by
    have hh := (hlim.comp hItop).mul hU
    rw [mul_one] at hh
    apply hh.congr'
    filter_upwards [(htop.comp hItop).eventually (eventually_gt_atTop (0 : ℝ))] with s hs
    have htne := hs.ne'
    dsimp [Function.comp_def] at htne
    dsimp only [Function.comp_def]
    field_simp
  have hLF : Tendsto (fun s : ℝ => F (t (I s-1))/s) atTop (𝓝 d) := by
    have hh := (hlim.comp hPtop).mul hL
    rw [mul_one] at hh
    apply hh.congr'
    filter_upwards [(htop.comp hPtop).eventually (eventually_gt_atTop (0 : ℝ))] with s hs
    have htne := hs.ne'
    dsimp [Function.comp_def] at htne
    dsimp only [Function.comp_def]
    field_simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hLF hUF
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    exact div_le_div_of_nonneg_right (hF (hbracket s hs.le).1) hs.le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    exact div_le_div_of_nonneg_right (hF (hI s).le) hs.le


-- @@ L105-105 verbatim
end Interpolation

-- @@ L106-106 verbatim
end EntropyRateDimension


-- @@ L108-108 verbatim
end


-- @@ L110-110 verbatim
end OAI
