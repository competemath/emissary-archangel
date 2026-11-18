import OAI.NumberTheory.DirichletL.Reflection.SourceCost


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace SevenEighths.InverseReflectedPhase

-- @@ L6-6 verbatim
open scoped Classical BigOperators

-- @@ L7-7 verbatim
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve

-- @@ L8-8 verbatim
noncomputable section

-- @@ L9-9 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L11-34 verbatim
theorem original_source_cost_budget {χ : Type*} [Fintype χ]
    (rmax : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {σ : Type*} [Fintype σ] (H : σ→ℝ),
      Fintype.card σ≤rmax → (∀ i,1≤H i) →
    ∀ (J Q Q₀ : Ideal Eis),J≠0 → Q≠0 → ∀ (Z Lpool Lslot loss : ℝ),1<Z →
      (Ideal.absNorm (J*Q):ℝ)≤Z^Lpool → (∏ i,H i)≤Z^Lslot → ε*(Lpool+Lslot)≤loss →
      (Fintype.card (χ×(Finset (FreeReflection.pool J Q Q₀)×Finset σ)):ℝ)^2*
        (∏ i,256*(columnDyadicLength (H i)+1:ℝ))^2≤C*Z^loss := by
  obtain ⟨C,hC,hb⟩ := original_source_cost (χ:=χ) rmax ε hε
  refine ⟨C,hC,?_⟩
  intro σ _ H hcard hH J Q Q₀ hJ hQ Z Lpool Lslot loss hZ hpool hslot hloss
  have hz : 0<Z := lt_trans zero_lt_one hZ
  apply (hb H hcard hH J Q Q₀ hJ hQ).trans
  calc
    _ ≤ C*(Z^Lpool)^ε*(Z^Lslot)^ε := by
      have hp := Real.rpow_le_rpow (Nat.cast_nonneg (Ideal.absNorm (J*Q))) hpool hε.le
      have hs := Real.rpow_le_rpow (Finset.prod_nonneg (fun i _ => zero_le_one.trans (hH i))) hslot hε.le
      exact mul_le_mul (mul_le_mul_of_nonneg_left hp hC.le) hs
        (Real.rpow_nonneg (Finset.prod_nonneg (fun i _ => zero_le_one.trans (hH i))) _) (by positivity)
    _ = C*Z^(ε*(Lpool+Lslot)) := by
      rw [←Real.rpow_mul hz.le,←Real.rpow_mul hz.le,mul_assoc,←Real.rpow_add hz]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le hloss) hC.le

-- @@ L35-35 verbatim
end

-- @@ L36-36 verbatim
end SevenEighths.InverseReflectedPhase


-- @@ L38-38 verbatim
end OAI
