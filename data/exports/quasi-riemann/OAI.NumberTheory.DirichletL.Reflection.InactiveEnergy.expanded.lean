import OAI.NumberTheory.DirichletL.Reflection.InactiveAggregation


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace SevenEighths.InverseReflectedPhase

-- @@ L6-6 verbatim
open scoped Classical BigOperators

-- @@ L7-7 verbatim
open ActualEisensteinCubic CanonicalQuadraticSieve

-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L11-24 verbatim
lemma weighted_finite_row_energy {ι κ : Type*} (L : Finset ι) (rows : Finset κ)
    (w : ι→ℂ) (f : ι→κ→ℂ) :
    (∑ k∈rows, ‖∑ i∈L, w i*f i k‖^2)≤
      (∑ i∈L, ‖w i‖)*∑ i∈L, ‖w i‖*(∑ k∈rows, ‖f i k‖^2) := by
  calc
    _ ≤ ∑ k∈rows, (∑ i∈L, ‖w i‖*‖f i k‖^2)*(∑ i∈L, ‖w i‖) := by
      apply Finset.sum_le_sum
      intro k hk
      simpa only [star_one,mul_one,norm_one,one_pow] using
        DescentWeightedCauchy.weighted_cauchy_sq L w (fun i => f i k) (fun _ => 1)
    _ = _ := by
      rw [← Finset.sum_mul,Finset.sum_comm]
      simp only [← Finset.mul_sum]
      ring


-- @@ L26-35 verbatim
lemma weighted_finite_row_energy_uniform {ι κ : Type*} (L : Finset ι) (rows : Finset κ)
    (w : ι→ℂ) (f : ι→κ→ℂ) (B : ℝ)
    (hf : ∀ i∈L, (∑ k∈rows, ‖f i k‖^2)≤B) :
    (∑ k∈rows, ‖∑ i∈L, w i*f i k‖^2)≤(∑ i∈L, ‖w i‖)^2*B := by
  apply (weighted_finite_row_energy L rows w f).trans
  calc
    _ ≤ (∑ i∈L, ‖w i‖)*∑ i∈L, ‖w i‖*B := by
      apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun i hi => norm_nonneg _))
      exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hf i hi) (norm_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; ring


-- @@ L37-50 verbatim
theorem inactive_slot_energy {ι κ : Type*} [Fintype ι] (P : PrimeFamily ι)
    (hinj : Function.Injective P.ideal) (L : Finset ι) (rows : Finset κ) (H B : ℝ)
    (hB : 0≤B) (hH : ∀ i∈L, (Ideal.absNorm (P.ideal i):ℝ)≤H)
    (a : ι→ℂ) (ha : ∀ i∈L, ‖a i‖≤1) (f : ι→κ→ℂ)
    (hf : ∀ i∈L, (∑ k∈rows, ‖f i k‖^2)≤B) :
    (∑ k∈rows, ‖∑ i∈L, (Ideal.absNorm (P.ideal i):ℂ)⁻¹*a i*f i k‖^2)≤
      (256*(columnDyadicLength H+1:ℝ))^2*B := by
  have hm : (∑ i∈L, ‖(Ideal.absNorm (P.ideal i):ℂ)⁻¹*a i‖)≤256*(columnDyadicLength H+1:ℝ) := by
    apply (Finset.sum_le_sum (fun i hi => ?_)).trans (inactive_slot_mass P hinj L H hH)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (ha i hi)
  apply (weighted_finite_row_energy_uniform L rows (fun i => (Ideal.absNorm (P.ideal i):ℂ)⁻¹*a i) f B hf).trans
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun i hi => norm_nonneg _)) hm 2) hB

-- @@ L51-51 verbatim
end

-- @@ L52-52 verbatim
end SevenEighths.InverseReflectedPhase


-- @@ L54-54 verbatim
end OAI
