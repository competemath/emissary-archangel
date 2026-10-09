import OAI.Geometry.PolarProducts.UpperBound


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace SymmetricPolar


-- @@ L7-15 verbatim
theorem symmetric_polar_main {n : ℕ} (hn : 2 ≤ n)
    (K : Set (Position n)) (hK : IsSymmetricConvexBody K) :
    gromovWidth (polarProduct K) = 4 ∧
      ∀ c : ℝ, 0 < c → c < 4 →
        HasSymplecticEmbedding (capacityBall n c) (polarProduct K) := by
  refine ⟨le_antisymm (gromovWidth_polarProduct_le_four hK (by omega))
    (four_le_gromovWidth_polarProduct hK), ?_⟩
  intro c hc hc4
  exact symmetric_polar_embedding hK hc hc4


-- @@ L17-17 verbatim
end SymmetricPolar


-- @@ L19-19 verbatim
end OAI
