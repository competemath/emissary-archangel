import OAI.Analysis.TreePotential.UniformAverages


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u


-- @@ L7-7 verbatim
namespace BoundedTreePotentials.TreeCalculus


-- @@ L9-25 verbatim
/-- Every root convention and quadratic budget gives a complete separable
infinite-dimensional space with a positive real averaged midpoint modulus,
but no continuously linearly equivalent space has an AUC norm. -/
theorem main_counterexample (r : Bool) (k : QuadraticKind) :
    (CompleteSpace (TestCompletion (treeTestFamily r k)) ∧
      TopologicalSpace.SeparableSpace (TestCompletion (treeTestFamily r k)) ∧
      ¬Module.Finite ℝ (TestCompletion (treeTestFamily r k))) ∧
    (∀ t : ℝ, 0 < t → t < 1 →
      Real.sqrt (1 + t ^ 2 / 4) - 1 ≤
        averagedModulusReal (TestCompletion (treeTestFamily r k)) t) ∧
    (∀ (Y : Type u) [NormedAddCommGroup Y] [NormedSpace ℝ Y],
      (TestCompletion (treeTestFamily r k) ≃L[ℝ] Y) → ¬IsAUCReal Y) := by
  refine ⟨four_completed_space r k, ?_, ?_⟩
  · intro t ht ht1
    exact four_averaged_modulus_real r k ht ht1
  · intro Y _ _ equivalence
    exact four_no_equivalent_AUC_real r k equivalence


-- @@ L27-27 verbatim
end BoundedTreePotentials.TreeCalculus


-- @@ L29-29 verbatim
end OAI
