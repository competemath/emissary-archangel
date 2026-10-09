import OAI.Analysis.MetricEntropy.CommonIndex
import OAI.Analysis.MetricEntropy.GreedyPivots
import OAI.Analysis.MetricEntropy.PartitionGraph


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
universe uX uY uLabel


-- @@ L9-16 verbatim
/-!
# A common index and greedy pivots at every profile level

The retained index is chosen once from the column weights. At each level,
the bounded greedy construction is applied to the actual retained graph
balls. All assignments and residual bounds below are consequently proved
for the actual partition graphs.
-/


-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-20 verbatim
namespace MetricEntropyDuality


-- @@ L22-22 verbatim
open scoped BigOperators Classical


-- @@ L24-57 verbatim
/-- One common retained index and an actual bounded pivot assignment at each
of the finitely many profile levels. -/
theorem exists_profile_pivots {X : Type uX} {Y : Type uY}
    [Fintype X] [Nonempty X] [Fintype Y]
    {u : ℕ} {Label : Fin u → Type uLabel}
    (L : (i : Fin u) → X → Label i) (v : Y → X) (T : Y → Finset (Fin u))
    (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y) (hmass : ∑ y, μ y ≤ 1)
    (hu : 0 < u) (θ : ℝ) (hθ : 0 < θ) (s : ℕ) (hs : 1 ≤ (s : ℝ) * θ)
    (hcomp : ∀ y, ((Finset.univ \ T y).card : ℝ) ≤ θ * (u : ℝ)) (h : ℕ) :
    ∃ i : Fin u, ∃ centers : Fin h → Fin s → X,
      ∃ assigned : Fin h → Y → Option (Fin s),
        (∑ y ∈ Finset.univ.filter (fun y => i ∉ T y), μ y) ≤ θ ∧
        (∀ j y k, assigned j y = some k →
          i ∈ T y ∧ PartitionGraph.near L (T y) j.val (centers j k) (v y)) ∧
        (∀ j x, (∑ y ∈ Finset.univ.filter (fun y =>
          i ∈ T y ∧ PartitionGraph.near L (T y) j.val x (v y) ∧
            assigned j y = none), μ y) ≤ θ) := by
  classical
  obtain ⟨i, hi⟩ := exists_common_index hu T μ hμ hmass hθ.le hcomp
  let incidence : Fin h → X → Finset Y := fun j x =>
    Finset.univ.filter (fun y => i ∈ T y ∧ PartitionGraph.near L (T y) j.val x (v y))
  have hgreedy (j : Fin h) :=
    exists_greedy_pivots μ (incidence j) hμ hmass θ hθ s hs
  let centers : Fin h → Fin s → X := fun j => (hgreedy j).choose
  let assigned : Fin h → Y → Option (Fin s) := fun j => (hgreedy j).choose_spec.choose
  refine ⟨i, centers, assigned, hi, ?_, ?_⟩
  · intro j y k hy
    have hyI : y ∈ incidence j (centers j k) :=
      (hgreedy j).choose_spec.choose_spec.1 y k hy
    exact (Finset.mem_filter.mp hyI).2
  · intro j x
    have hres : (∑ y ∈ (incidence j x).filter (fun y => assigned j y = none), μ y) ≤ θ :=
      (hgreedy j).choose_spec.choose_spec.2.2 x
    simpa only [incidence, Finset.filter_filter, and_assoc] using hres


-- @@ L59-59 verbatim
end MetricEntropyDuality


-- @@ L61-61 verbatim
end


-- @@ L63-63 verbatim
end OAI
