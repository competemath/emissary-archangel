import OAI.MeasureTheory.SelfSimilar.TriangularAverages


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
namespace EntropyRateDimension.BallRatios

-- @@ L17-17 verbatim
open MeasureTheory Metric Set Filter

-- @@ L18-18 verbatim
open scoped Topology BigOperators


-- @@ L20-23 verbatim
theorem information_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ] (x r : ℝ) :
    0 ≤ information μ x r := by
  unfold information
  exact neg_nonneg.mpr (Real.log_nonpos ENNReal.toReal_nonneg (measureReal_le_one))


-- @@ L25-30 verbatim
theorem information_antitone (μ : Measure ℝ) [IsProbabilityMeasure μ] {x r s : ℝ}
    (hx : x ∈ μ.support) (hr : 0 < r) (hrs : r ≤ s) :
    information μ x s ≤ information μ x r := by
  apply neg_le_neg
  apply Real.log_le_log (massReal_pos μ hx hr)
  exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (closedBall_subset_closedBall hrs))


-- @@ L32-55 verbatim
theorem information_one_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hK : IsCompact μ.support) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ μ.support, information μ x 1 ≤ C := by
  classical
  obtain ⟨t,ht⟩ := hK.elim_finite_subcover (fun x : μ.support => ball (x : ℝ) (1/2))
    (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x,hx⟩,mem_ball_self (by norm_num)⟩)
  refine ⟨∑ z ∈ t, information μ z.val (1/2),
    Finset.sum_nonneg (fun _ _ => information_nonneg _ _ _),?_⟩
  intro x hx
  obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp (ht hx)
  have hsub : closedBall y.val (1/2) ⊆ closedBall x 1 := by
    intro z hz
    have hzy : dist z y.val ≤ 1/2 := mem_closedBall.mp hz
    have hyx : dist y.val x < 1/2 := by simpa only [dist_comm] using mem_ball.mp hxy
    apply mem_closedBall.mpr
    calc
      dist z x ≤ dist z y.val + dist y.val x := dist_triangle _ _ _
      _ ≤ 1 := by linarith
  have hh : information μ x 1 ≤ information μ y.val (1/2) := by
    apply neg_le_neg
    exact Real.log_le_log (massReal_pos μ y.property (by norm_num))
      (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub))
  exact hh.trans (Finset.single_le_sum (fun z _ => information_nonneg μ z.val (1/2)) hy)


-- @@ L57-57 verbatim
end EntropyRateDimension.BallRatios


-- @@ L59-59 verbatim
end


-- @@ L61-61 verbatim
end OAI
