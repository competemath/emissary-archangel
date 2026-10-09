import OAI.Combinatorics.GraphThreshold.FiniteProbability
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Tactic.FieldSimp


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
open scoped BigOperators

-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L11-11 verbatim
namespace LeanBlast.SecondKahnKalai


-- @@ L13-13 verbatim
variable {X : Type*} [Fintype X] [DecidableEq X]


-- @@ L15-17 verbatim
theorem bernoulliExpectation_congr (p : ℝ) {f g : Finset X → ℝ}
    (h : ∀ W, f W = g W) : bernoulliExpectation p f = bernoulliExpectation p g := by
  exact Finset.sum_congr rfl fun W _ => congrArg (fun z => bernoulliWeight p W * z) (h W)


-- @@ L19-21 verbatim
@[simp] theorem bernoulliExpectation_const (p c : ℝ) :
    bernoulliExpectation p (fun _ : Finset X => c) = c := by
  rw [bernoulliExpectation, ← Finset.sum_mul, bernoulliWeight_sum, one_mul]


-- @@ L23-26 verbatim
theorem bernoulliExpectation_add (p : ℝ) (f g : Finset X → ℝ) :
    bernoulliExpectation p (fun W => f W + g W) =
      bernoulliExpectation p f + bernoulliExpectation p g := by
  simp [bernoulliExpectation, mul_add, Finset.sum_add_distrib]


-- @@ L28-30 verbatim
theorem bernoulliExpectation_smul (p c : ℝ) (f : Finset X → ℝ) :
    bernoulliExpectation p (fun W => c * f W) = c * bernoulliExpectation p f := by
  simp [bernoulliExpectation, Finset.mul_sum, mul_left_comm]


-- @@ L32-36 verbatim
theorem bernoulliExpectation_sum {ι : Type*} [Fintype ι] (p : ℝ)
    (f : ι → Finset X → ℝ) :
    bernoulliExpectation p (fun W => ∑ i, f i W) = ∑ i, bernoulliExpectation p (f i) := by
  simp only [bernoulliExpectation, Finset.mul_sum]
  exact Finset.sum_comm


-- @@ L38-40 verbatim
theorem bernoulliExpectation_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {f : Finset X → ℝ} (hf : ∀ W, 0 ≤ f W) : 0 ≤ bernoulliExpectation p f :=
  (bernoulliLaw p hp0 hp1).expectation_nonneg hf


-- @@ L42-45 verbatim
theorem bernoulliExpectation_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {f g : Finset X → ℝ} (hfg : ∀ W, f W ≤ g W) :
    bernoulliExpectation p f ≤ bernoulliExpectation p g :=
  (bernoulliLaw p hp0 hp1).expectation_mono hfg


-- @@ L47-53 verbatim
theorem finset_eq_indicator_product (U V : Finset X) :
    (if U = V then (1 : ℝ) else 0) =
      ∏ x, if (x ∈ U ↔ x ∈ V) then (1 : ℝ) else 0 := by
  rw [Fintype.prod_boole]
  have h : (∀ x : X, x ∈ U ↔ x ∈ V) ↔ U = V :=
    ⟨Finset.ext, fun h => by subst V; simp⟩
  simp only [h]


-- @@ L55-69 verbatim
theorem bernoulliExpectation_pushforward (p : ℝ) (T : Finset X → Finset X)
    (F : Finset X → ℝ) :
    bernoulliExpectation p (fun W => F (T W)) =
      ∑ Y : Finset X, bernoulliExpectation p (fun W => if T W = Y then 1 else 0) * F Y := by
  unfold bernoulliExpectation
  calc
    (∑ W : Finset X, bernoulliWeight p W * F (T W)) =
        ∑ W : Finset X, ∑ Y : Finset X,
          (bernoulliWeight p W * (if T W = Y then 1 else 0)) * F Y := by
      apply Finset.sum_congr rfl
      intro W _
      simp [mul_ite, ite_mul]
    _ = ∑ Y : Finset X, ∑ W : Finset X,
          (bernoulliWeight p W * (if T W = Y then 1 else 0)) * F Y := Finset.sum_comm
    _ = _ := by simp only [Finset.sum_mul]


-- @@ L71-84 verbatim
theorem bernoulli_union_fixed_mass (p : ℝ) (A Y : Finset X) :
    bernoulliExpectation p (fun W => if W ∪ A = Y then 1 else 0) =
      ∏ x, if x ∈ A then (if x ∈ Y then (1 : ℝ) else 0)
        else (if x ∈ Y then p else 1 - p) := by
  let f : X → Bool → ℝ := fun x b =>
    if (b = true ∨ x ∈ A) ↔ x ∈ Y then 1 else 0
  have hf : (fun W : Finset X => if W ∪ A = Y then (1 : ℝ) else 0) =
      (fun W => ∏ x, f x (decide (x ∈ W))) := by
    funext W
    simpa [f] using finset_eq_indicator_product (W ∪ A) Y
  rw [hf, bernoulliExpectation_product]
  apply Finset.prod_congr rfl
  intro x _
  by_cases ha : x ∈ A <;> by_cases hy : x ∈ Y <;> simp [f, ha, hy]


-- @@ L86-107 verbatim
theorem bernoulli_union_fixed_mass_mul (p : ℝ) (A Y : Finset X) :
    p ^ A.card * bernoulliExpectation p (fun W => if W ∪ A = Y then 1 else 0) =
      if A ⊆ Y then bernoulliWeight p Y else 0 := by
  rw [bernoulli_union_fixed_mass]
  by_cases hAY : A ⊆ Y
  · rw [ite_eq_left hAY]
    have hp : p ^ A.card = ∏ x : X, if x ∈ A then p else 1 := by
      rw [Fintype.prod_ite_mem]
      simp
    rw [hp, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro x _
    by_cases ha : x ∈ A
    · simp [ha, hAY ha]
    · simp [ha]
  · rw [ite_eq_right hAY]
    obtain ⟨x, hxa, hxy⟩ := Finset.not_subset.mp hAY
    have hz : (∏ x, if x ∈ A then (if x ∈ Y then (1 : ℝ) else 0)
        else (if x ∈ Y then p else 1 - p)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ x)
      simp [hxa, hxy]
    rw [hz, mul_zero]


-- @@ L109-113 verbatim
theorem bernoulli_union_fixed_mass_div (p : ℝ) (hp : p ≠ 0) (A Y : Finset X) :
    bernoulliExpectation p (fun W => if W ∪ A = Y then 1 else 0) =
      (if A ⊆ Y then bernoulliWeight p Y else 0) / p ^ A.card := by
  apply (eq_div_iff (pow_ne_zero _ hp)).2
  simpa only [mul_comm] using bernoulli_union_fixed_mass_mul p A Y


-- @@ L115-127 verbatim
/-- Forcing all coordinates of `A` to be present gives the literal Bernoulli
law conditioned on containing `A`. -/
theorem bernoulliExpectation_union_fixed (p : ℝ) (hp : p ≠ 0)
    (A : Finset X) (F : Finset X → ℝ) :
    bernoulliExpectation p (fun W => F (W ∪ A)) =
      bernoulliExpectation p (fun Y => if A ⊆ Y then F Y / p ^ A.card else 0) := by
  rw [bernoulliExpectation_pushforward]
  unfold bernoulliExpectation
  apply Finset.sum_congr rfl
  intro Y _
  rw [← bernoulliExpectation, bernoulli_union_fixed_mass_div p hp A Y]
  by_cases hAY : A ⊆ Y <;> simp [hAY]
  ring


-- @@ L129-129 verbatim
end LeanBlast.SecondKahnKalai


-- @@ L131-131 verbatim
end


-- @@ L133-133 verbatim
end OAI
