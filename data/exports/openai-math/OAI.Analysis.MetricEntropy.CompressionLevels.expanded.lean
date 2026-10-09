import OAI.Analysis.MetricEntropy.PartitionGraph
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith


-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-8 verbatim
universe uX uY uK uι uLabel


-- @@ L10-17 verbatim
/-!
# Graph-ball comparison at one compression level

Columns omitted by the common index and retained columns left uncovered
each contribute at most `θ`. Assigned columns are compared using the actual
partition graph and replacement pivots with the same selected label.
Graph distances remain extended distances throughout.
-/


-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
namespace MetricEntropyDuality.CompressionLevels


-- @@ L23-23 verbatim
open scoped BigOperators Classical


-- @@ L25-25 verbatim
variable {X : Type uX} {Y : Type uY} {K : Type uK} {ι : Type uι} {Label : ι → Type uLabel}


-- @@ L27-29 verbatim
/-- The real indicator of a finite-radius ball in the actual partition graph. -/
def ballIndicator (L : (i : ι) → X → Label i) (T : Finset ι) (j : ℕ)
    (x v : X) : ℝ := if PartitionGraph.near L T j x v then 1 else 0


-- @@ L31-34 verbatim
theorem ballIndicator_nonneg (L : (i : ι) → X → Label i) (T : Finset ι)
    (j : ℕ) (x v : X) : 0 ≤ ballIndicator L T j x v := by
  unfold ballIndicator
  split_ifs <;> simp


-- @@ L36-39 verbatim
theorem ballIndicator_le_one (L : (i : ι) → X → Label i) (T : Finset ι)
    (j : ℕ) (x v : X) : ballIndicator L T j x v ≤ 1 := by
  unfold ballIndicator
  split_ifs <;> simp


-- @@ L41-46 verbatim
/-- Unassigned columns contribute zero; assigned columns use replacement pivots. -/
def assignedIndicator (L : (i : ι) → X → Label i) (T : Y → Finset ι)
    (rep : K → X) (assignment : Y → Option K) (j : ℕ) (x : X) (y : Y) : ℝ :=
  match assignment y with
  | none => 0
  | some k => ballIndicator L (T y) (2 * j + 1) x (rep k)


-- @@ L48-54 verbatim
theorem assignedIndicator_nonneg (L : (i : ι) → X → Label i) (T : Y → Finset ι)
    (rep : K → X) (assignment : Y → Option K) (j : ℕ) (x : X) (y : Y) :
    0 ≤ assignedIndicator L T rep assignment j x y := by
  unfold assignedIndicator
  cases assignment y with
  | none => exact le_rfl
  | some k => exact ballIndicator_nonneg _ _ _ _ _


-- @@ L56-82 verbatim
/-- Pointwise accounting for assigned, omitted, and uncovered columns. -/
theorem ballIndicator_le_assignedIndicator_add
    (L : (i : ι) → X → Label i) (v : Y → X) (T : Y → Finset ι)
    (i : ι) (j : ℕ) (centers rep : K → X) (assignment : Y → Option K)
    (hassign : ∀ y k, assignment y = some k →
      i ∈ T y ∧ PartitionGraph.near L (T y) j (centers k) (v y))
    (hrep : ∀ k, L i (rep k) = L i (centers k)) (x : X) (y : Y) :
    ballIndicator L (T y) j x (v y) ≤
      assignedIndicator L T rep assignment j x y +
        (if i ∉ T y then 1 else 0) +
        (if i ∈ T y ∧ PartitionGraph.near L (T y) j x (v y) ∧
          assignment y = none then 1 else 0) := by
  have ha := assignedIndicator_nonneg L T rep assignment j x y
  by_cases hx : PartitionGraph.near L (T y) j x (v y)
  · by_cases hi : i ∈ T y
    · cases hass : assignment y with
      | none => simp [ballIndicator, assignedIndicator, hx, hi, hass]
      | some k =>
          have hk := hassign y k hass
          have hf := PartitionGraph.pivot_forward L (T y) hk.1 (hrep k)
            (PartitionGraph.near_symm L (T y) hk.2) hx
          simp [ballIndicator, assignedIndicator, hx, hi, hass, hf]
    · simp only [ballIndicator, ite_eq_left hx, hi, not_false_eq_true, ite_true,
        false_and, ite_false]
      linarith
  · simp only [ballIndicator, hx, and_false, false_and, ite_false]
    split_ifs <;> linarith


-- @@ L84-104 verbatim
/-- Every assigned replacement ball lies in the original ball of radius `3*j+2`. -/
theorem assignedIndicator_le_ballIndicator
    (L : (i : ι) → X → Label i) (v : Y → X) (T : Y → Finset ι)
    (i : ι) (j : ℕ) (centers rep : K → X) (assignment : Y → Option K)
    (hassign : ∀ y k, assignment y = some k →
      i ∈ T y ∧ PartitionGraph.near L (T y) j (centers k) (v y))
    (hrep : ∀ k, L i (rep k) = L i (centers k)) (x : X) (y : Y) :
    assignedIndicator L T rep assignment j x y ≤
      ballIndicator L (T y) (3 * j + 2) x (v y) := by
  cases hass : assignment y with
  | none =>
      simpa [assignedIndicator, hass] using
        ballIndicator_nonneg L (T y) (3 * j + 2) x (v y)
  | some k =>
      by_cases hx : PartitionGraph.near L (T y) (2 * j + 1) x (rep k)
      · have hk := hassign y k hass
        have hb := PartitionGraph.pivot_backward L (T y) hk.1 (hrep k)
          (PartitionGraph.near_symm L (T y) hk.2) hx
        simp [assignedIndicator, hass, ballIndicator, hx, hb]
      · simpa [assignedIndicator, hass, ballIndicator, hx] using
          ballIndicator_nonneg L (T y) (3 * j + 2) x (v y)


-- @@ L106-106 verbatim
section Weighted


-- @@ L108-108 verbatim
variable [Fintype Y]


-- @@ L110-113 verbatim
/-- The original mixture at one ball radius. -/
def levelValue (L : (i : ι) → X → Label i) (v : Y → X) (T : Y → Finset ι)
    (μ : Y → ℝ) (j : ℕ) (x : X) : ℝ :=
  ∑ y, μ y * ballIndicator L (T y) j x (v y)


-- @@ L115-118 verbatim
/-- The assigned mixture after pivot replacement. -/
def assignedValue (L : (i : ι) → X → Label i) (T : Y → Finset ι)
    (rep : K → X) (assignment : Y → Option K) (μ : Y → ℝ) (j : ℕ) (x : X) : ℝ :=
  ∑ y, μ y * assignedIndicator L T rep assignment j x y


-- @@ L120-148 verbatim
/-- The lower comparison loses only omitted mass and uncovered retained mass. -/
theorem levelValue_sub_two_mul_le_assignedValue
    (L : (i : ι) → X → Label i) (v : Y → X) (T : Y → Finset ι)
    (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y) (i : ι) (j : ℕ)
    (centers rep : K → X) (assignment : Y → Option K)
    (hassign : ∀ y k, assignment y = some k →
      i ∈ T y ∧ PartitionGraph.near L (T y) j (centers k) (v y))
    (hrep : ∀ k, L i (rep k) = L i (centers k)) {θ : ℝ}
    (homit : (∑ y ∈ Finset.univ.filter (fun y => i ∉ T y), μ y) ≤ θ)
    (hrem : ∀ x, (∑ y ∈ Finset.univ.filter (fun y =>
      i ∈ T y ∧ PartitionGraph.near L (T y) j x (v y) ∧
        assignment y = none), μ y) ≤ θ) (x : X) :
    levelValue L v T μ j x - 2 * θ ≤ assignedValue L T rep assignment μ j x := by
  have hsum : levelValue L v T μ j x ≤ assignedValue L T rep assignment μ j x +
      (∑ y ∈ Finset.univ.filter (fun y => i ∉ T y), μ y) +
      (∑ y ∈ Finset.univ.filter (fun y =>
        i ∈ T y ∧ PartitionGraph.near L (T y) j x (v y) ∧
          assignment y = none), μ y) := by
    calc
      _ ≤ ∑ y, μ y * (assignedIndicator L T rep assignment j x y +
          (if i ∉ T y then 1 else 0) +
          (if i ∈ T y ∧ PartitionGraph.near L (T y) j x (v y) ∧
            assignment y = none then 1 else 0)) := by
        exact Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left
          (ballIndicator_le_assignedIndicator_add L v T i j centers rep assignment
            hassign hrep x y) (hμ y)
      _ = _ := by
        simp [assignedValue, mul_add, Finset.sum_add_distrib, Finset.sum_filter, mul_ite]
  linarith [hrem x]


-- @@ L150-161 verbatim
/-- The upper comparison uses the genuine radius `3*j+2` in each column graph. -/
theorem assignedValue_le_levelValue
    (L : (i : ι) → X → Label i) (v : Y → X) (T : Y → Finset ι)
    (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y) (i : ι) (j : ℕ)
    (centers rep : K → X) (assignment : Y → Option K)
    (hassign : ∀ y k, assignment y = some k →
      i ∈ T y ∧ PartitionGraph.near L (T y) j (centers k) (v y))
    (hrep : ∀ k, L i (rep k) = L i (centers k)) (x : X) :
    assignedValue L T rep assignment μ j x ≤ levelValue L v T μ (3 * j + 2) x := by
  exact Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left
    (assignedIndicator_le_ballIndicator L v T i j centers rep assignment
      hassign hrep x y) (hμ y)


-- @@ L163-163 verbatim
end Weighted


-- @@ L165-165 verbatim
end MetricEntropyDuality.CompressionLevels


-- @@ L167-167 verbatim
end


-- @@ L169-169 verbatim
end OAI
