import OAI.Combinatorics.ExpectationThreshold.ProbabilityProduct


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-11 verbatim
/-!
# Moments of products on a subset of coordinates

Under the actual product law, observables supported on a finite subset
factor into their coordinate expectations. Extending the factors by one
outside the subset reduces this to the full product moment identity.
-/


-- @@ L13-13 verbatim
open scoped BigOperators

-- @@ L14-14 verbatim
noncomputable section


-- @@ L16-16 verbatim
namespace TalagrandThreshold.FiniteLaw


-- @@ L18-19 verbatim
variable {I : Type*} [Fintype I] [DecidableEq I]
  {A : I → Type*} [∀ i, Fintype (A i)]


-- @@ L21-42 verbatim
/-- A product on a subset has the product of its actual coordinate means. -/
theorem expectation_pi_subset_product (μ : ∀ i, FiniteLaw (A i))
    (S : Finset I) (f : ∀ i, A i → ℝ) :
    (pi μ).expectation (fun ω => ∏ i ∈ S, f i (ω i)) =
      ∏ i ∈ S, (μ i).expectation (f i) := by
  classical
  let g : ∀ i, A i → ℝ := fun i a => if i ∈ S then f i a else 1
  have hg (ω : ∀ i, A i) : (∏ i, g i (ω i)) = ∏ i ∈ S, f i (ω i) := by
    simpa only [g] using Fintype.prod_ite_mem S (fun i => f i (ω i))
  have he (i : I) : (μ i).expectation (g i) =
      if i ∈ S then (μ i).expectation (f i) else 1 := by
    by_cases hi : i ∈ S
    · simp only [g, ite_eq_left hi]
    · simp only [g, ite_eq_right hi, expectation_const]
  calc
    _ = (pi μ).expectation (fun ω => ∏ i, g i (ω i)) := by
      congr 1
      funext ω
      exact (hg ω).symm
    _ = ∏ i, (μ i).expectation (g i) := expectation_pi_product μ g
    _ = ∏ i ∈ S, (μ i).expectation (f i) := by
      simp only [he, Finset.prod_ite_mem_eq]


-- @@ L44-53 verbatim
/-- Equal coordinate means give the corresponding power of the subset size. -/
theorem expectation_pi_subset_product_of_mean (μ : ∀ i, FiniteLaw (A i))
    (S : Finset I) (f : ∀ i, A i → ℝ) (a : ℝ)
    (hmean : ∀ i ∈ S, (μ i).expectation (f i) = a) :
    (pi μ).expectation (fun ω => ∏ i ∈ S, f i (ω i)) = a ^ S.card := by
  rw [expectation_pi_subset_product]
  calc
    (∏ i ∈ S, (μ i).expectation (f i)) = ∏ _i ∈ S, a :=
      Finset.prod_congr rfl hmean
    _ = a ^ S.card := Finset.prod_const a


-- @@ L55-60 verbatim
/-- Identically distributed coordinates give a power of their common mean. -/
theorem expectation_pi_subset_product_const {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (S : Finset I) (f : Ω → ℝ) :
    (pi (fun _ : I => μ)).expectation (fun ω => ∏ i ∈ S, f (ω i)) =
      (μ.expectation f) ^ S.card := by
  rw [expectation_pi_subset_product, Finset.prod_const]


-- @@ L62-62 verbatim
end TalagrandThreshold.FiniteLaw


-- @@ L64-64 verbatim
end


-- @@ L66-66 verbatim
end OAI
