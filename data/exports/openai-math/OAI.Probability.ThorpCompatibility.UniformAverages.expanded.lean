import Mathlib
import OAI.Probability.ThorpCompatibility.Model
import OAI.Probability.ThorpCompatibility.PermutationProbability


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
open scoped Classical

-- @@ L8-8 verbatim
namespace ThorpCompatibility

-- @@ L9-9 verbatim
open Finset

-- @@ L10-10 verbatim
open Finset


-- @@ L12-14 verbatim
lemma uniformMean_mono {α : Type*} [Fintype α] {f g : α → ℝ} (h : ∀ x, f x ≤ g x) :
    uniformMean f ≤ uniformMean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => h x) (by positivity)


-- @@ L16-19 verbatim
lemma uniformMean_sum {α β : Type*} [Fintype α] [Fintype β] (f : α → β → ℝ) :
    uniformMean (fun x => ∑ y, f x y) = ∑ y, uniformMean (fun x => f x y) := by
  simp only [uniformMean]
  rw [Finset.sum_comm, Finset.sum_div]


-- @@ L21-23 verbatim
lemma uniformMean_const_mul {α : Type*} [Fintype α] (a : ℝ) (f : α → ℝ) :
    uniformMean (fun x => a * f x) = a * uniformMean f := by
  simp only [uniformMean, ← Finset.mul_sum, mul_div_assoc]


-- @@ L25-28 verbatim
lemma uniformMean_indicator {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] :
    uniformMean (fun x => if P x then 1 else 0) = uniformProbability P := by
  rw [uniformProbability_def]
  simp [uniformMean]


-- @@ L30-30 verbatim
end ThorpCompatibility


-- @@ L32-32 verbatim
end OAI
