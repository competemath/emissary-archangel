import OAI.Probability.GaussianPropeller.Model


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uF


-- @@ L7-7 verbatim
open MeasureTheory ProbabilityTheory

-- @@ L8-8 verbatim
open scoped ENNReal

-- @@ L9-9 verbatim
namespace GaussianPropeller


-- @@ L11-13 verbatim
def MainBound : Prop :=
  ∀ (n : ℕ), 4 ≤ n → ∀ A : Fin (n + 1) → Set (Space n),
    IsPartition A → value A ≤ 9 / (8 * Real.pi)


-- @@ L15-17 verbatim
def MainAttainment : Prop :=
  ∀ (n : ℕ), 4 ≤ n →
    IsPartition (propeller n (n + 1)) ∧ value (propeller n (n + 1)) = 9 / (8 * Real.pi)


-- @@ L19-19 verbatim
open scoped RealInnerProductSpace


-- @@ L21-23 verbatim
theorem integrable_id_gaussian (d : ℕ) :
    Integrable (fun x : Space d => x) (gaussian d) := by
  exact IsGaussian.integrable_id (μ := stdGaussian (Space d))


-- @@ L25-27 verbatim
theorem integrable_id_restrict (d : ℕ) (A : Set (Space d)) :
    Integrable (fun x : Space d => x) ((gaussian d).restrict A) :=
  (integrable_id_gaussian d).restrict


-- @@ L29-30 verbatim
@[simp] theorem centroid_empty (d : ℕ) : centroid (∅ : Set (Space d)) = 0 := by
  simp [centroid]


-- @@ L32-33 verbatim
theorem value_nonneg {d k : ℕ} (A : Fin k → Set (Space d)) : 0 ≤ value A := by
  exact Finset.sum_nonneg (fun i _ => sq_nonneg ‖centroid (A i)‖)


-- @@ L35-45 verbatim
theorem sum_indicator_eq {d k : ℕ} {A : Fin k → Set (Space d)} (hA : IsPartition A)
    {F : Type uF} [AddCommMonoid F] (f : Space d → F) :
    (fun x => ∑ i, (A i).indicator f x) =ᵐ[gaussian d] f := by
  classical
  filter_upwards [hA.2] with x hx
  obtain ⟨i, hi, huniq⟩ := hx
  rw [Finset.sum_eq_single i]
  · exact Set.indicator_of_mem hi f
  · intro j _ hji
    exact Set.indicator_of_notMem (fun hj => hji (huniq j hj)) f
  · simp


-- @@ L47-59 verbatim
theorem sum_centroid_eq_zero {d k : ℕ} {A : Fin k → Set (Space d)}
    (hA : IsPartition A) : ∑ i, centroid (A i) = 0 := by
  have hi (i : Fin k) : Integrable ((A i).indicator (fun x => x)) (gaussian d) :=
    (integrable_id_gaussian d).indicator (hA.1 i)
  calc
    ∑ i, centroid (A i) = ∑ i, ∫ x, (A i).indicator (fun x => x) x ∂gaussian d := by
      apply Finset.sum_congr rfl
      intro i _
      exact (integral_indicator (hA.1 i)).symm
    _ = ∫ x, ∑ i, (A i).indicator (fun x => x) x ∂gaussian d :=
      (integral_finsetSum _ (fun i _ => hi i)).symm
    _ = ∫ x, x ∂gaussian d := integral_congr_ae (sum_indicator_eq hA (fun x => x))
    _ = 0 := integral_id_stdGaussian


-- @@ L61-61 verbatim
end GaussianPropeller


-- @@ L63-63 verbatim
end OAI
