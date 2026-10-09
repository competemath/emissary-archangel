import OAI.Geometry.QuadricBundles.Ampleness


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
namespace QuadricCounterexample

-- @@ L8-8 verbatim
noncomputable section


-- @@ L10-28 verbatim
theorem main_theorem : SourceMainTheorem := by
  let G := sourceGraphScalars.equalizerData.bundle
  let E : ℕ → AlgebraicRankTwoBundle := fun m ↦
    if hm : 0 < m then powerPullbackTwist G m hm else G
  refine ⟨G,E,?_,?_,?_⟩
  · intro m hm
    dsimp [E]
    rw [dite_eq_left hm]
    exact powerPullbackTwist_spec G m hm
  · intro m hm
    dsimp [E]
    rw [dite_eq_left hm]
    exact sourceGraphScalars.equalizerData.powerTwist_ample m hm
  · obtain ⟨m₀,h₀,h⟩ := source_eventually_no_positive_metric
    refine ⟨m₀,h₀,fun m hmi ↦ ?_⟩
    have hm : 0 < m := h₀.trans_le hmi
    dsimp [E]
    rw [dite_eq_left hm]
    exact h m hm hmi


-- @@ L30-30 verbatim
end

-- @@ L31-31 verbatim
end QuadricCounterexample


-- @@ L33-33 verbatim
end


-- @@ L35-35 verbatim
end OAI
