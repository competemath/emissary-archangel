import OAI.Combinatorics.DiscreteConvexity.FiniteProbability
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-11 verbatim
/-!
# Marginals and pushforwards of finite product laws

All identities below follow from the weights of the actual finite laws.
-/


-- @@ L13-13 verbatim
open scoped BigOperators

-- @@ L14-14 verbatim
noncomputable section

-- @@ L15-15 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L17-17 verbatim
namespace TalagrandDiscreteConvexity.FiniteLaw


-- @@ L19-19 verbatim
section ProductCoordinates


-- @@ L21-22 verbatim
variable {I : Type*} [Fintype I] [DecidableEq I]
  {A : I → Type*} [∀ i, Fintype (A i)]


-- @@ L24-32 verbatim
/-- Product observables factor under the product of the given finite laws. -/
theorem expectation_pi_product (μ : ∀ i, FiniteLaw (A i))
    (f : ∀ i, A i → ℝ) :
    (pi μ).expectation (fun ω => ∏ i, f i (ω i)) =
      ∏ i, (μ i).expectation (f i) := by
  classical
  simp only [expectation, pi_weight]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => (μ i).weight a * f i a)).symm


-- @@ L34-55 verbatim
/-- A coordinate of the product law has exactly its prescribed marginal. -/
theorem expectation_pi_coordinate (μ : ∀ i, FiniteLaw (A i))
    (i : I) (f : A i → ℝ) :
    (pi μ).expectation (fun ω => f (ω i)) = (μ i).expectation f := by
  classical
  let g : ∀ j, A j → ℝ := fun j a => if h : j = i then f (h ▸ a) else 1
  have hg (ω : ∀ j, A j) : (∏ j, g j (ω j)) = f (ω i) := by
    dsimp only [g]
    simp only [Fintype.prod_dite_eq']
  have he (j : I) : (μ j).expectation (g j) =
      if h : j = i then (μ i).expectation f else 1 := by
    by_cases h : j = i
    · subst j
      simp [g]
    · simp [g, h, expectation_const]
  calc
    _ = (pi μ).expectation (fun ω => ∏ j, g j (ω j)) := by
      congr 1
      funext ω
      exact (hg ω).symm
    _ = ∏ j, (μ j).expectation (g j) := expectation_pi_product μ g
    _ = _ := by simp_rw [he]; simp


-- @@ L57-63 verbatim
/-- Events depending on one coordinate have their original probabilities. -/
theorem prob_pi_coordinate (μ : ∀ i, FiniteLaw (A i))
    (i : I) (P : A i → Prop) :
    (pi μ).prob (fun ω => P (ω i)) = (μ i).prob P := by
  classical
  rw [prob_eq_expectation, prob_eq_expectation]
  exact expectation_pi_coordinate μ i (fun a => if P a then 1 else 0)


-- @@ L65-82 verbatim
/-- A cylinder event has the product of its coordinate probabilities. -/
theorem prob_pi (μ : ∀ i, FiniteLaw (A i)) (P : ∀ i, A i → Prop) :
    (pi μ).prob (fun ω => ∀ i, P i (ω i)) = ∏ i, (μ i).prob (P i) := by
  classical
  rw [prob_eq_expectation]
  calc
    _ = (pi μ).expectation (fun ω => ∏ i, if P i (ω i) then 1 else 0) := by
      congr 1
      funext ω
      symm
      by_cases h : ∀ i, P i (ω i)
      · simpa only [ite_eq_left h] using
          (Fintype.prod_boole (p := fun i => P i (ω i)) (M₀ := ℝ))
      · simpa only [ite_eq_right h] using
          (Fintype.prod_boole (p := fun i => P i (ω i)) (M₀ := ℝ))
    _ = ∏ i, (μ i).expectation (fun a => if P i a then 1 else 0) :=
      expectation_pi_product μ (fun i a => if P i a then 1 else 0)
    _ = _ := by simp_rw [prob_eq_expectation]


-- @@ L84-84 verbatim
end ProductCoordinates


-- @@ L86-86 verbatim
variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]


-- @@ L88-104 verbatim
/-- Rectangle events factor under the binary product law. -/
theorem prob_prod (μ : FiniteLaw Ω) (ν : FiniteLaw Γ)
    (P : Ω → Prop) (Q : Γ → Prop) :
    (μ.prod ν).prob (fun z => P z.1 ∧ Q z.2) = μ.prob P * ν.prob Q := by
  classical
  simp only [prob, prod, Fintype.sum_prod_type]
  calc
    _ = ∑ ω, ∑ γ,
        (if P ω then μ.weight ω else 0) * (if Q γ then ν.weight γ else 0) := by
      apply Finset.sum_congr rfl
      intro ω _
      apply Finset.sum_congr rfl
      intro γ _
      by_cases hp : P ω <;> by_cases hq : Q γ <;> simp [hp, hq]
    _ = _ := by
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]


-- @@ L106-115 verbatim
/-- Pushforward by summing the source weights in each fiber. -/
def map (μ : FiniteLaw Ω) (f : Ω → Γ) : FiniteLaw Γ where
  weight γ := ∑ ω, if f ω = γ then μ.weight ω else 0
  nonneg γ := Finset.sum_nonneg fun ω _ => by
    split_ifs
    · exact μ.nonneg ω
    · exact le_rfl
  total := by
    rw [Finset.sum_comm]
    simpa using μ.total


-- @@ L117-118 verbatim
@[simp] theorem map_weight (μ : FiniteLaw Ω) (f : Ω → Γ) (γ : Γ) :
    (map μ f).weight γ = ∑ ω, if f ω = γ then μ.weight ω else 0 := rfl


-- @@ L120-121 verbatim
theorem map_weight_eq_prob (μ : FiniteLaw Ω) (f : Ω → Γ) (γ : Γ) :
    (map μ f).weight γ = μ.prob (fun ω => f ω = γ) := rfl


-- @@ L123-131 verbatim
/-- Observables of a pushed law are evaluated along the defining map. -/
theorem expectation_map (μ : FiniteLaw Ω) (f : Ω → Γ) (g : Γ → ℝ) :
    (map μ f).expectation g = μ.expectation (fun ω => g (f ω)) := by
  unfold expectation
  simp only [map_weight, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp [ite_mul]


-- @@ L133-136 verbatim
/-- The probability of an event under a pushed law is its preimage probability. -/
theorem prob_map (μ : FiniteLaw Ω) (f : Ω → Γ) (P : Γ → Prop) :
    (map μ f).prob P = μ.prob (fun ω => P (f ω)) := by
  rw [prob_eq_expectation, expectation_map, prob_eq_expectation]


-- @@ L138-138 verbatim
end TalagrandDiscreteConvexity.FiniteLaw


-- @@ L140-140 verbatim
end


-- @@ L142-142 verbatim
end OAI
