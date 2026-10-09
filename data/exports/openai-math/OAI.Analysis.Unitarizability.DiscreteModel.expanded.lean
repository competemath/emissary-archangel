import OAI.Analysis.Unitarizability.Model


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
namespace Dixmier

-- @@ L7-7 verbatim
universe u v


-- @@ L9-16 verbatim
def CurrentMainTheorem : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [DiscreteTopology G],
    (Amenable G ↔ Unitarizable.{u, max u v} G) ∧
    ∀ (ε : ℝ), 0 < ε → ¬ Amenable G →
      ∃ (H : Type (max u v)) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
        (_ : CompleteSpace H) (π : G →* (H →L[ℂ] H)),
        (Countable G → TopologicalSpace.SeparableSpace H) ∧
        (∀ g, ‖π g‖ ≤ 1 + ε) ∧ ¬ SimilarToUnitary π


-- @@ L18-18 verbatim
end Dixmier

-- @@ L19-19 verbatim
end


-- @@ L21-21 verbatim
end OAI
