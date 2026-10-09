import OAI.Geometry.QuadricBundles.Embedding


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
namespace QuadricCounterexample

-- @@ L8-8 verbatim
noncomputable section


-- @@ L10-18 verbatim
theorem EqualizerData.powerTwist_ample (D : EqualizerData) (m : ℕ) (hm : 0 < m) :
    IsAmple (powerPullbackTwist D.bundle m hm) := by
  let t := 3*m+1
  let e := 2*t-1
  have he : 3*m≤e := by dsimp [e,t]; omega
  have hen : e+1=2*t := by dsimp [e,t]; omega
  have hn : 0<2*t := by dsimp [t]; omega
  let S := D.ampleSystem m hm e t he hen
  exact ⟨2*t,hn,_,S.sections,S.closedEmbedding hn⟩


-- @@ L20-20 verbatim
end

-- @@ L21-21 verbatim
end QuadricCounterexample


-- @@ L23-23 verbatim
end


-- @@ L25-25 verbatim
end OAI
