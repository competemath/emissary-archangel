import OAI.Combinatorics.ExpectationThreshold.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring


-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-15 verbatim
/-!
# Concrete rounding masses

Each nonempty subset's fractional weight is split equally among its members.
Normalizing by the total nonempty-subset weight gives the probability mass used
by the common selector. Both normalization and the mean identity are finite
double-sum calculations.
-/


-- @@ L17-17 verbatim
namespace TalagrandThreshold


-- @@ L19-19 verbatim
open scoped BigOperators


-- @@ L21-21 verbatim
variable {α : Type*} [Fintype α] [DecidableEq α]


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
def nonemptySubsets (H : Finset α) : Finset (Finset α) := H.powerset.erase ∅


-- @@ L27-28 verbatim
def memberMass (g : Finset α → ℝ) (H : Finset α) : ℝ :=
  ∑ S ∈ nonemptySubsets H, g S


-- @@ L30-31 verbatim
def subsetAverage (a : α → ℝ) (S : Finset α) : ℝ :=
  (∑ x ∈ S, a x) / (S.card : ℝ)


-- @@ L33-35 verbatim
def roundingMass (g : Finset α → ℝ) (H : Finset α) (x : α) : ℝ :=
  (∑ S ∈ nonemptySubsets H, if x ∈ S then g S / (S.card : ℝ) else 0) /
    memberMass g H


-- @@ L37-40 verbatim
omit [Fintype α] in
@[simp] theorem mem_nonemptySubsets {S H : Finset α} :
    S ∈ nonemptySubsets H ↔ S ≠ ∅ ∧ S ⊆ H := by
  simp only [nonemptySubsets, Finset.mem_erase, Finset.mem_powerset]


-- @@ L42-45 verbatim
omit [Fintype α] in
theorem memberMass_add_empty (g : Finset α → ℝ) (H : Finset α) :
    memberMass g H + g ∅ = ∑ S ∈ H.powerset, g S := by
  exact Finset.sum_erase_add H.powerset g (Finset.empty_mem_powerset H)


-- @@ L47-50 verbatim
omit [Fintype α] in
theorem memberMass_nonneg {g : Finset α → ℝ} (hg : ∀ S, 0 ≤ g S)
    (H : Finset α) : 0 ≤ memberMass g H :=
  Finset.sum_nonneg (fun S _ => hg S)


-- @@ L52-56 verbatim
omit [DecidableEq α] in
theorem empty_weight_le_half {r : ℝ} {g : Finset α → ℝ}
    (hr : 0 ≤ r) (hg : ∀ S, 0 ≤ g S) (hcost : fracCost r g ≤ 1 / 2) :
    g ∅ ≤ 1 / 2 :=
  (empty_weight_le_fracCost hr hg).trans hcost


-- @@ L58-65 verbatim
theorem memberMass_ge_half {F : Family α} {g : Finset α → ℝ}
    {H : Finset α} {r : ℝ} (hcover : FractionalCover F g) (hH : H ∈ F)
    (hr : 0 ≤ r) (hcost : fracCost r g ≤ 1 / 2) :
    1 / 2 ≤ memberMass g H := by
  have hcoverage := hcover.2 H hH
  have hempty := empty_weight_le_half hr hcover.nonneg hcost
  have hsplit := memberMass_add_empty g H
  linarith


-- @@ L67-72 verbatim
theorem memberMass_pos_of_fractionalCover {F : Family α} {g : Finset α → ℝ}
    {H : Finset α} {r : ℝ} (hcover : FractionalCover F g) (hH : H ∈ F)
    (hr : 0 ≤ r) (hcost : fracCost r g ≤ 1 / 2) :
    0 < memberMass g H := by
  have hmass := memberMass_ge_half hcover hH hr hcost
  linarith


-- @@ L74-77 verbatim
omit [Fintype α] [DecidableEq α] in
theorem subsetAverage_nonneg {a : α → ℝ} (ha : ∀ x, 0 ≤ a x)
    (S : Finset α) : 0 ≤ subsetAverage a S :=
  div_nonneg (Finset.sum_nonneg (fun x _ => ha x)) (Nat.cast_nonneg _)


-- @@ L79-88 verbatim
omit [Fintype α] in
theorem roundingMass_nonneg (g : Finset α → ℝ) (H : Finset α)
    (hg : ∀ S, 0 ≤ g S) (hM : 0 < memberMass g H) (x : α) :
    0 ≤ roundingMass g H x := by
  apply div_nonneg _ hM.le
  apply Finset.sum_nonneg
  intro S _
  split_ifs
  · exact div_nonneg (hg S) (Nat.cast_nonneg _)
  · exact le_rfl


-- @@ L90-100 verbatim
omit [Fintype α] in
theorem roundingMass_eq_zero_of_not_mem (g : Finset α → ℝ) (H : Finset α)
    {x : α} (hx : x ∉ H) : roundingMass g H x = 0 := by
  have hsum :
      (∑ S ∈ nonemptySubsets H, if x ∈ S then g S / (S.card : ℝ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro S hS
    have hxS : x ∉ S := fun h => hx ((mem_nonemptySubsets.mp hS).2 h)
    simp only [ite_eq_right hxS]
  unfold roundingMass
  rw [hsum, zero_div]


-- @@ L102-110 verbatim
/-- A nonempty set distributes exactly its original weight. -/
theorem sum_uniform_subset_weight (g : Finset α → ℝ) (S : Finset α)
    (hS : S ≠ ∅) :
    (∑ x : α, if x ∈ S then g S / (S.card : ℝ) else 0) = g S := by
  have hcard : (S.card : ℝ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr
      (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hS))
  rw [Finset.sum_ite_mem_eq, Finset.sum_const, nsmul_eq_mul]
  exact mul_div_cancel₀ (g S) hcard


-- @@ L112-119 verbatim
/-- Counting each set's members evaluates the full double sum. -/
theorem sum_rounding_numerator (g : Finset α → ℝ) (H : Finset α) :
    (∑ x : α, ∑ S ∈ nonemptySubsets H,
      if x ∈ S then g S / (S.card : ℝ) else 0) = memberMass g H := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  exact sum_uniform_subset_weight g S (mem_nonemptySubsets.mp hS).1


-- @@ L121-124 verbatim
theorem roundingMass_sum (g : Finset α → ℝ) (H : Finset α)
    (hM : 0 < memberMass g H) : (∑ x : α, roundingMass g H x) = 1 := by
  simp only [roundingMass, ← Finset.sum_div]
  rw [sum_rounding_numerator, div_self hM.ne']


-- @@ L126-134 verbatim
/-- Averaging one set's distributed weight gives its subset average. -/
theorem sum_weighted_uniform_subset_weight (g : Finset α → ℝ)
    (S : Finset α) (a : α → ℝ) :
    (∑ x : α, a x * (if x ∈ S then g S / (S.card : ℝ) else 0)) =
      g S * subsetAverage a S := by
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_mem_eq, ← Finset.sum_mul]
  unfold subsetAverage
  ring


-- @@ L136-146 verbatim
theorem roundingMass_mean (g : Finset α → ℝ) (H : Finset α) (a : α → ℝ) :
    (∑ x : α, a x * roundingMass g H x) =
      (∑ S ∈ nonemptySubsets H, g S * subsetAverage a S) / memberMass g H := by
  unfold roundingMass
  simp only [← mul_div_assoc, ← Finset.sum_div]
  congr 1
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  exact sum_weighted_uniform_subset_weight g S a


-- @@ L148-148 verbatim
end

-- @@ L149-149 verbatim
end TalagrandThreshold


-- @@ L151-151 verbatim
end OAI
