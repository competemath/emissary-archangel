import OAI.Analysis.Littlewood.Curvature


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-6 verbatim
/-! Smooth cutoffs of nearly full squared mass, required by both the spreading
and sampling constructions. -/

-- @@ L7-7 verbatim
namespace AsymptoticallyMinimalLittlewood

-- @@ L8-8 verbatim
namespace Cutoff

-- @@ L9-9 verbatim
noncomputable section

-- @@ L10-10 verbatim
open MeasureTheory Set

-- @@ L11-11 verbatim
open scoped Topology ContDiff


-- @@ L13-33 verbatim
lemma bump_mass (g : ContDiffBump (0 : ℝ)) :
    2*g.rIn ≤ ∫ x : ℝ, g x ^ 2 := by
  have hs : HasCompactSupport (fun x : ℝ ↦ g x ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using
      (g.hasCompactSupport.mul_right (f' := (g : ℝ → ℝ)))
  have hi : Integrable (fun x : ℝ ↦ g x ^ 2) :=
    ((show ContDiff ℝ ∞ g from g.contDiff).continuous.pow 2).integrable_of_hasCompactSupport hs
  have hmono : (∫ x in Icc (-g.rIn) g.rIn, g x ^ 2) ≤ ∫ x : ℝ, g x ^ 2 :=
    setIntegral_le_integral hi (Filter.Eventually.of_forall (fun x ↦ sq_nonneg _))
  have hone : (∫ x in Icc (-g.rIn) g.rIn, g x ^ 2) = 2*g.rIn := by
    calc
      _ = ∫ _ : ℝ in Icc (-g.rIn) g.rIn, (1 : ℝ) := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro x hx
        have hx' : x ∈ Metric.closedBall (0 : ℝ) g.rIn := by
          simpa [Metric.mem_closedBall, Real.dist_eq, abs_le] using hx
        simp only [g.one_of_mem_closedBall hx', one_pow]
      _ = 2*g.rIn := by
        simp [sub_neg_eq_add, g.rIn_pos.le]
        ring
  rwa [hone] at hmono


-- @@ L35-53 verbatim
theorem unit_cutoff {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      (∃ α : ℝ, 0 < α ∧ α < 1/2 ∧ tsupport g ⊆ Icc (-α) α) ∧
      (∀ x, 0 ≤ g x ∧ g x ≤ 1) ∧
      1-ε < ∫ x : ℝ, g x ^ 2 := by
  obtain ⟨a,ha0,ha1⟩ := exists_between (show max (0:ℝ) ((1-ε)/2) < 1/2 by
    rw [max_lt_iff]; constructor <;> linarith)
  have ha : 0<a := lt_of_le_of_lt (le_max_left _ _) ha0
  have ham : (1-ε)/2<a := lt_of_le_of_lt (le_max_right _ _) ha0
  obtain ⟨b,hab,hb⟩ := exists_between ha1
  let g : ContDiffBump (0 : ℝ) := ⟨a,b,ha,hab⟩
  refine ⟨g,g.contDiff,g.hasCompactSupport,⟨b,ha.trans hab,hb,?_⟩,
    fun x ↦ ⟨g.nonneg,g.le_one⟩,?_⟩
  · rw [g.tsupport_eq]
    intro x hx
    simpa [Metric.mem_closedBall, Real.dist_eq, abs_le, g] using hx
  · have h := bump_mass g
    change 2*a ≤ _ at h
    linarith


-- @@ L55-55 verbatim
end

-- @@ L56-56 verbatim
end Cutoff

-- @@ L57-57 verbatim
end AsymptoticallyMinimalLittlewood


-- @@ L59-59 verbatim
end OAI
