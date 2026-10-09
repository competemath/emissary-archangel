import OAI.Analysis.Daugavet.LimitingSlices


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L7-7 verbatim
open scoped ENNReal NNReal Topology BigOperators


-- @@ L9-9 verbatim
namespace ExactModuli


-- @@ L11-16 verbatim
theorem kadets_werner_existence :
    ∃ E : Submodule ℝ (Lp ℝ 1 kwMeasure),
      IsClosed (E : Set (Lp ℝ 1 kwMeasure)) ∧ (¬ FiniteDimensional ℝ E) ∧
      MeasurePrecompactBall kwMeasure E ∧ UnitSliceProperty E ∧ Daugavet E := by
  exact ⟨KW.constructedSpace, KW.constructedSpace_closed, KW.constructedSpace_infiniteDimensional,
    KW.constructedSpace_measurePrecompact, KW.constructedSpace_unitSlice, KW.constructedSpace_daugavet⟩


-- @@ L18-18 verbatim
end ExactModuli


-- @@ L20-20 verbatim
namespace ExactModuli


-- @@ L22-36 verbatim
theorem exact_example :
    ∃ E : Submodule ℝ (Lp ℝ 1 kwMeasure),
      IsClosed (E : Set (Lp ℝ 1 kwMeasure)) ∧ (¬ FiniteDimensional ℝ E) ∧
      MeasurePrecompactBall kwMeasure E ∧ UnitSliceProperty E ∧ Daugavet E ∧
      (∀ (x : E), ‖x‖ = 1 → ∀ t : ℝ, 0 < t →
        H (normSeminorm ℝ E) x t = max (t / 2) (t - 1) ∧
        D (normSeminorm ℝ E) x t = max 0 (t - 2)) ∧
      (∀ t : ℝ, 0 < t →
        averagedModulus (normSeminorm ℝ E) t = max (t / 2) (t - 1) ∧
        oneSidedModulus (normSeminorm ℝ E) t = max 0 (t - 2)) ∧
      (∀ N : Seminorm ℝ E, EquivalentNorm N → ¬ AUC N) := by
  let := KW.kwMeasure_probability
  obtain ⟨E,hclosed,hdim,hcompact,hslice,hdaugavet⟩ := kadets_werner_existence
  obtain ⟨hpoint,hcenters,hrenorm⟩ := exact_main kwMeasure E hclosed hdim hcompact hdaugavet
  exact ⟨E,hclosed,hdim,hcompact,hslice,hdaugavet,hpoint,hcenters,hrenorm⟩


-- @@ L38-38 verbatim
end ExactModuli


-- @@ L40-40 verbatim
end


-- @@ L42-42 verbatim
end OAI
