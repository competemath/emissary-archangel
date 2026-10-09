import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
open MeasureTheory ProbabilityTheory

-- @@ L6-6 verbatim
open scoped ENNReal


-- @@ L8-8 verbatim
namespace GaussianPropeller


-- @@ L10-10 verbatim
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)


-- @@ L12-12 verbatim
noncomputable def gaussian (d : ℕ) : Measure (Space d) := stdGaussian (Space d)


-- @@ L14-15 verbatim
def IsPartition {d k : ℕ} (A : Fin k → Set (Space d)) : Prop :=
  (∀ i, MeasurableSet (A i)) ∧ ∀ᵐ x ∂gaussian d, ∃! i, x ∈ A i


-- @@ L17-18 verbatim
noncomputable def centroid {d : ℕ} (A : Set (Space d)) : Space d :=
  ∫ x in A, x ∂gaussian d


-- @@ L20-21 verbatim
noncomputable def value {d k : ℕ} (A : Fin k → Set (Space d)) : ℝ :=
  ∑ i, ‖centroid (A i)‖ ^ 2


-- @@ L23-24 verbatim
def coord {d : ℕ} (j : ℕ) (x : Space d) : ℝ :=
  if h : j < d then x ⟨j, h⟩ else 0


-- @@ L26-30 verbatim
noncomputable def propeller (d k : ℕ) (i : Fin k) : Set (Space d) :=
  if i.val = 0 then {x | |coord 1 x| ≤ Real.sqrt 3 * coord 0 x}
  else if i.val = 1 then {x | 0 ≤ coord 1 x ∧ Real.sqrt 3 * coord 0 x ≤ coord 1 x}
  else if i.val = 2 then {x | coord 1 x ≤ 0 ∧ Real.sqrt 3 * coord 0 x ≤ -coord 1 x}
  else ∅


-- @@ L32-36 verbatim
def AllPartitions : Prop :=
  (∀ (d k : ℕ), 0 < d → 0 < k → ∀ A : Fin k → Set (Space d),
    IsPartition A → value A ≤ 9 / (8 * Real.pi)) ∧
  (∀ (d k : ℕ), 2 ≤ d → 3 ≤ k →
    IsPartition (propeller d k) ∧ value (propeller d k) = 9 / (8 * Real.pi))


-- @@ L38-38 verbatim
end GaussianPropeller


-- @@ L40-40 verbatim
end OAI
