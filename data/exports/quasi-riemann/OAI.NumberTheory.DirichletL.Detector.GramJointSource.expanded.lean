import OAI.NumberTheory.DirichletL.Detector.GramJoint


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical

-- @@ L7-7 verbatim
namespace SevenEighths.ProbeGramCommon

-- @@ L8-8 verbatim
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion

-- @@ L9-9 verbatim
open CenteredMomentSupportedCorrelation CenteredMomentCorrelation

-- @@ L10-10 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L11-11 verbatim
local notation "Id" => Ideal O

-- @@ L12-12 verbatim
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

-- @@ L13-13 verbatim
variable {ι : Type*} [Fintype ι]


-- @@ L15-35 verbatim
theorem jointExtension_source (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (hC : Supported (Ideal.span {C}))
    (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (hpr : λ₀^2∣r-1) (hk : k=u.val*λ₀^a*(2:O)^b*r)
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ)
    (hc : ∀i,1≤c i) (hcop : Pairwise (Function.onFun IsCoprime P))
    (he : Ideal.span {C}=∏i,P i^c i)
    [Fintype (O⧸∏i,P i^c i)] [∀i,Fintype (O⧸P i^c i)]
    (n₁ n₂ : O) (h₁ : Supported (Ideal.span {n₁})) (h₂ : Supported (Ideal.span {n₂}))
    (hp₁ : λ₀^2∣n₁-1) (hp₂ : λ₀^2∣n₂-1) (hn : IsCoprime n₁ n₂) :
    jointExtension S hS σ C k u a b r hr P hg c n₁ n₂=
      primaryCoefficient S hS σ (C*n₁)*star (primaryCoefficient S hS σ (C*n₂))*
        actualCorrelation (C*n₁) (C*n₂) (supported_mul_elements C n₁ hC h₁)
          (supported_mul_elements C n₂ hC h₂) (C*k) := by
  rw [actual_common_lift C n₁ n₂ k hC h₁ h₂ hp₁ hp₂ hn,
    actualCommon_eq_globalExtension C hC P hg c hc hcop he n₁ n₂ k hn,
    ←numeratorExtension_primary u a b r k n₁ hr hpr hk h₁ hp₁,
    ←numeratorExtension_neg_primary u a b r k n₂ hr hpr hk h₂ hp₂]
  simp only [jointExtension,jointFixed,numeratorExtension,MonoidHom.mul_apply,
    movingNumeratorRow,MonoidHom.coe_mk,OneHom.coe_mk,star_mul]
  ring


-- @@ L37-44 verbatim
lemma lowGramCoefficient_eq_primary (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (s : {I : Id // Supported I}) :
    lowGramCoefficient (calibrationForSet S hS) σ s=
      primaryCoefficient S hS σ (primaryGenerator s.val) := by
  have hp : λ₀^2∣primaryGenerator s.val-1 := (primaryGenerator_spec s.val
    (supported_primaryGenerator_ne_zero s.val s.property)).2
  rw [primaryCoefficient,ite_eq_left hp]
  exact lowGramCoefficient_eq_extension S hS hbad σ s


-- @@ L46-46 verbatim
end SevenEighths.ProbeGramCommon

-- @@ L47-47 verbatim
end


-- @@ L49-49 verbatim
end OAI
