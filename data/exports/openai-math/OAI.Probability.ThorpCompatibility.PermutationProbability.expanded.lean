import Mathlib
import OAI.Probability.ThorpCompatibility.PermutationCount
import OAI.Probability.ThorpCompatibility.FactorialBounds
import OAI.Probability.ThorpCompatibility.Entropy


-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-8 verbatim
open scoped Classical

-- @@ L9-9 verbatim
namespace ThorpCompatibility

-- @@ L10-10 verbatim
open Finset

-- @@ L11-11 verbatim
open Finset

-- @@ L12-36 verbatim
lemma prescribed_function_probability_le {α : Type*} [Fintype α] [DecidableEq α]
    (hn : 0 < Fintype.card α) (s : Finset α) (f : α → α) :
    ((Finset.univ.filter (fun τ : Equiv.Perm α => ∀ x ∈ s, τ x = f x)).card : ℝ) /
      Fintype.card (Equiv.Perm α) ≤ (Real.exp 1 / Fintype.card α) ^ s.card := by
  have hs : s.card ≤ Fintype.card α := Finset.card_le_univ s
  have hcard := prescribed_function_card_le s f
  have hfac : (0 : ℝ) < (Fintype.card α).factorial := by positivity
  have hdesc : (0 : ℝ) < (Fintype.card α).descFactorial s.card := by
    exact_mod_cast Nat.descFactorial_pos.mpr hs
  have hn' : (0 : ℝ) < Fintype.card α := by exact_mod_cast hn
  have hbase : 0 < ((Fintype.card α : ℝ) / Real.exp 1) ^ s.card := by positivity
  have hmul : ((Fintype.card α - s.card).factorial : ℝ) *
      (Fintype.card α).descFactorial s.card = (Fintype.card α).factorial := by
    exact_mod_cast Nat.factorial_mul_descFactorial hs
  rw [Fintype.card_perm]
  calc
    _ ≤ ((Fintype.card α - s.card).factorial : ℝ) / (Fintype.card α).factorial :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcard) hfac.le
    _ = 1 / ((Fintype.card α).descFactorial s.card : ℝ) := by
      apply (div_eq_div_iff hfac.ne' hdesc.ne').mpr
      simpa using hmul
    _ ≤ 1 / (((Fintype.card α : ℝ) / Real.exp 1) ^ s.card) :=
      one_div_le_one_div_of_le hbase (descFactorial_exponential_lower _ _ hs)
    _ = (Real.exp 1 / Fintype.card α) ^ s.card := by
      rw [← one_div_pow, one_div_div]


-- @@ L38-40 verbatim
noncomputable def uniformProbability {α : Type*} [Fintype α] (P : α → Prop) : ℝ := by
  classical
  exact (Finset.univ.filter P).card / (Fintype.card α : ℝ)


-- @@ L42-46 verbatim
lemma uniformProbability_def {α : Type*} [Fintype α] (P : α → Prop)
    [DecidablePred P] :
    uniformProbability P = ((Finset.univ.filter P).card : ℝ) / Fintype.card α := by
  unfold uniformProbability
  congr


-- @@ L48-51 verbatim
lemma uniformProbability_nonneg {α : Type*} [Fintype α] (P : α → Prop) :
    0 ≤ uniformProbability P := by
  unfold uniformProbability
  positivity


-- @@ L53-57 verbatim
lemma uniformProbability_eq_zero {α : Type*} [Fintype α] (P : α → Prop)
    (h : ¬ ∃ x, P x) : uniformProbability P = 0 := by
  classical
  have hP : ∀ x, ¬ P x := fun x hx => h ⟨x, hx⟩
  simp [uniformProbability, hP]


-- @@ L59-72 verbatim
lemma uniformProbability_all {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]
    (P : ι → α → Prop) :
    uniformProbability (fun f : ι → α => ∀ i, P i (f i)) =
      ∏ i, uniformProbability (P i) := by
  classical
  rw [uniformProbability_def]
  have hset : Finset.univ.filter (fun f : ι → α => ∀ i, P i (f i)) =
      Fintype.piFinset (fun i => Finset.univ.filter (P i)) := by
    ext f
    simp
  rw [show (Finset.univ.filter (fun f : ι → α => ∀ i, P i (f i))).card =
      ∏ i, (Finset.univ.filter (P i)).card by
    rw [hset, Fintype.card_piFinset]]
  simp only [uniformProbability, Fintype.card_pi, Nat.cast_prod, Finset.prod_div_distrib]


-- @@ L74-74 verbatim
end ThorpCompatibility


-- @@ L76-76 verbatim
end OAI
