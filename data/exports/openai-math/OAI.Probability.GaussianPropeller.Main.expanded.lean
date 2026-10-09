import OAI.Probability.GaussianPropeller.Elimination


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
open MeasureTheory ProbabilityTheory

-- @@ L6-6 verbatim
open scoped ENNReal

-- @@ L7-7 verbatim
open scoped RealInnerProductSpace

-- @@ L8-8 verbatim
open scoped RealInnerProductSpace

-- @@ L9-9 verbatim
open MeasureTheory ProbabilityTheory Set

-- @@ L10-10 verbatim
open scoped ENNReal RealInnerProductSpace

-- @@ L11-11 verbatim
open Filter

-- @@ L12-12 verbatim
open scoped Topology

-- @@ L13-13 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L14-14 verbatim
open scoped Topology

-- @@ L15-15 verbatim
open scoped RealInnerProductSpace

-- @@ L16-16 verbatim
open Set Filter

-- @@ L17-17 verbatim
open scoped Topology RealInnerProductSpace

-- @@ L18-18 verbatim
open scoped NNReal

-- @@ L19-19 verbatim
open Set Filter

-- @@ L20-20 verbatim
open scoped Topology RealInnerProductSpace NNReal

-- @@ L21-21 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L22-22 verbatim
open scoped Topology RealInnerProductSpace

-- @@ L23-23 verbatim
open MeasureTheory Set Filter

-- @@ L24-24 verbatim
open scoped Topology BigOperators

-- @@ L25-25 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L26-26 verbatim
open scoped RealInnerProductSpace Topology

-- @@ L27-27 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L28-28 verbatim
open scoped RealInnerProductSpace Topology ENNReal

-- @@ L29-29 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L30-30 verbatim
open scoped RealInnerProductSpace Topology ENNReal

-- @@ L31-31 verbatim
open Metric

-- @@ L32-32 verbatim
open MeasureTheory ProbabilityTheory Set

-- @@ L33-33 verbatim
open scoped RealInnerProductSpace ENNReal

-- @@ L34-34 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L35-35 verbatim
open scoped ENNReal RealInnerProductSpace


-- @@ L37-37 verbatim
namespace GaussianPropeller.Reduction


-- @@ L39-68 verbatim
theorem all_partition_bound (d:ℕ) (hd:0<d) :
    ∀ k (A:Fin k→Set (Space d)), IsPartition A → value A≤9/(8*Real.pi) := by
  classical
  let : NeZero d := ⟨by omega⟩
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro A hA
    by_cases hk:k≤3
    · exact partition_bound_small hk hA
    let : NeZero k := ⟨by omega⟩
    obtain ⟨B,hB⟩:=exists_minimal_optimal (d:=d) (k:=k)
    suffices hb:value B≤9/(8*Real.pi) from (hB.1.2 _ hA).trans hb
    by_contra hn
    have hC:9/(8*Real.pi)<value B := lt_of_not_ge hn
    by_cases hall:∀ j,gaussian d (B j)≠0
    · obtain ⟨D⟩:=exists_configuration (by omega) hB hC hall
      by_cases hk4:k=4
      · subst k
        exact D.impossible_four
      · exact D.impossible_five_or_more (by omega)
    · push Not at hall
      obtain ⟨i,hi⟩:=hall
      cases k with
      | zero => omega
      | succ m =>
        have hp:=remove_null_partition hB.1.1 i hi
        have hv:=ih m (by omega) (fun j=>B (i.succAbove j)) hp
        rw [remove_null_value i hi] at hv
        exact (not_le_of_gt hC) hv


-- @@ L70-70 verbatim
end GaussianPropeller.Reduction


-- @@ L72-72 verbatim
namespace GaussianPropeller


-- @@ L74-76 verbatim
theorem main_bound : MainBound := by
  intro n hn A hA
  exact Reduction.all_partition_bound n (by omega) (n+1) A hA


-- @@ L78-82 verbatim
theorem all_partitions : AllPartitions := by
  constructor
  · intro d k hd hk A hA
    exact Reduction.all_partition_bound d hd k A hA
  · exact Reduction.propeller_attainment


-- @@ L84-84 verbatim
end GaussianPropeller


-- @@ L86-86 verbatim
namespace GaussianPropeller


-- @@ L88-103 verbatim
theorem all_partition_bound_nullMeasurable {d k : ℕ} (hd : 0 < d)
    (A : Fin k → Set (Space d))
    (hA : ∀ i, NullMeasurableSet (A i) (gaussian d))
    (hp : ∀ᵐ x ∂gaussian d, ∃! i, x ∈ A i) :
    value A ≤ 9 / (8 * Real.pi) := by
  let B : Fin k → Set (Space d) := fun i => toMeasurable (gaussian d) (A i)
  have he : ∀ i, B i =ᵐ[gaussian d] A i := fun i => (hA i).toMeasurable_ae_eq
  have hB : IsPartition B := by
    refine ⟨fun i => measurableSet_toMeasurable _ _, ?_⟩
    have hh := ae_all_iff.mpr he
    filter_upwards [hp,hh] with x hx heq
    change ∀ i, (x ∈ B i) = (x ∈ A i) at heq
    obtain ⟨i,hi,hu⟩ := hx
    exact ⟨i,Eq.mpr (heq i) hi,fun j hj => hu j (Eq.mp (heq j) hj)⟩
  rw [←Reduction.value_congr_ae he]
  exact Reduction.all_partition_bound d hd k B hB


-- @@ L105-110 verbatim
theorem main_bound_nullMeasurable (n : ℕ) (hn : 4 ≤ n)
    (A : Fin (n+1) → Set (Space n))
    (hA : ∀ i, NullMeasurableSet (A i) (gaussian n))
    (hp : ∀ᵐ x ∂gaussian n, ∃! i, x ∈ A i) :
    value A ≤ 9 / (8 * Real.pi) :=
  all_partition_bound_nullMeasurable (by omega) A hA hp


-- @@ L112-112 verbatim
end GaussianPropeller


-- @@ L114-114 verbatim
end OAI
