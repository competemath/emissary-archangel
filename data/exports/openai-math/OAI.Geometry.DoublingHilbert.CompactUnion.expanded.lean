import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
open Set Metric

-- @@ L6-6 verbatim
open scoped BigOperators

-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
namespace CompactBanach


-- @@ L10-38 verbatim
theorem compact_shrinking_union {B : Type*} [MetricSpace B]
    (o : B) (C : ℕ → Finset B)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j ≥ N, ∀ z ∈ C j, dist z o < ε) :
    IsCompact ({o} ∪ ⋃ j : ℕ, (C j : Set B)) := by
  classical
  apply isCompact_of_finite_subcover
  intro ι U hU hcov
  obtain ⟨i₀, hi₀⟩ := mem_iUnion.mp (hcov (by simp : o ∈ {o} ∪ ⋃ j : ℕ, (C j : Set B)))
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp (hU i₀) o hi₀
  obtain ⟨N, hN⟩ := hsmall ε hε
  let F : Finset B := (Finset.range N).biUnion C
  have hFK : (F : Set B) ⊆ {o} ∪ ⋃ j : ℕ, (C j : Set B) := by
    intro z hz
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hz
    exact Or.inr (mem_iUnion.mpr ⟨j, hj⟩)
  obtain ⟨t, ht⟩ := F.finite_toSet.isCompact.elim_finite_subcover U hU (hFK.trans hcov)
  refine ⟨insert i₀ t, ?_⟩
  intro z hz
  rcases hz with hz | hz
  · rcases Set.mem_singleton_iff.mp hz with rfl
    exact mem_iUnion.mpr ⟨i₀, mem_iUnion.mpr ⟨by simp, hi₀⟩⟩
  · obtain ⟨j, hj⟩ := mem_iUnion.mp hz
    by_cases hjN : j < N
    · have hzF : z ∈ F := Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hjN, hj⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp (ht hzF)
      obtain ⟨hit, hzi⟩ := mem_iUnion.mp hi
      exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨Finset.mem_insert_of_mem hit, hzi⟩⟩
    · have hzi : z ∈ U i₀ := hεU (hN j (by omega) z hj)
      exact mem_iUnion.mpr ⟨i₀, mem_iUnion.mpr ⟨by simp, hzi⟩⟩


-- @@ L40-40 verbatim
end CompactBanach

-- @@ L41-41 verbatim
end


-- @@ L43-43 verbatim
end OAI
