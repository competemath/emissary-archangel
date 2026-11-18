import OAI.NumberTheory.DirichletL.Moments.AmplificationActiveFactor


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators Classical SchwartzMap


-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentAmplificationActiveFamily

-- @@ L9-9 verbatim
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion

-- @@ L10-10 verbatim
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion

-- @@ L11-11 verbatim
open CenteredMomentAmplificationShortening CenteredMomentAmplificationActiveFactor

-- @@ L12-12 verbatim
open CenteredMomentAmplificationFamilyEnergy CenteredMomentAmplificationSourceDomain

-- @@ L13-13 verbatim
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow CenteredMomentChildRows

-- @@ L14-14 verbatim
open CenteredMomentSourceRow CenteredMomentOriginalChildEnergy CenteredMomentGaussEnergy

-- @@ L15-15 verbatim
local notation "O" => ActualEisensteinCubic.O

 
-- @@ L17-29 verbatim
theorem actual_error_energy_active (S : Finset (Ideal O)) (p : O) (hp : Prime p)
    (hs : Supported (Ideal.span {p})) (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6)
    (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceGaussEnergy (residualColumns S p hp (n+1)) c
      (fun I => residualCharacter p (n+1) (primaryGenerator I)) W K=
    sourceGaussEnergy (residualColumns S p hp (n+1)) c
      (fun I => residualCharacter p (errorMovingExponent n) (primaryGenerator I)) W K := by
  let Q := residualColumns S p hp (n+1)
  apply congrArg (fun f : supportedColumns Q → ℂ =>
    gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q) f W K)
  funext I
  dsimp only
  rw [residual_column_active S p hp hs n hn I (Finset.mem_filter.mp I.property).1]


-- @@ L31-52 verbatim
theorem exists_actual_error_family (η : Character) (m p : O)
    (hm : m≠0) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (hpp : goodLambda^2 ∣ p-1) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    ∃ τ : RayCharacter → Character,
      (∀ χ,(τ χ).modulus.absNorm≤rowConductorBound (childCharacter η χ) m 1
        (p^(2*errorMovingExponent n))) ∧
      ∀ (S : Finset (Ideal O)) (C : Ideal O),C≠0 → ∀ (β : Ideal O → ℂ) (t : ℝ)
        (W : 𝓢(ℝ,ℂ)) (K : ℝ),0<K →
      (∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      (sourceGaussEnergy (residualColumns S p hp (n+1))
        (fun I => β (C*I)*rowWeight η m 1 1 t (C*I))
        (fun I => residualCharacter p (n+1) (primaryGenerator I)) W K).re≤
        16*∑ χ : RayCharacter,
          (sourceGaussEnergy (residualColumns S p hp (n+1))
            (fun I => β (C*I)) (heightCoeff (τ χ) t) W K).re := by
  obtain ⟨τ,hN,hτ⟩ := exists_amplification_energy_family η m p hm hp.ne_zero hs hpp hmLam hm2
    (errorMovingExponent n)
  refine ⟨τ,hN,?_⟩
  intro S C hC β t W K hK hW
  rw [actual_error_energy_active S p hp hs n hn]
  exact hτ (residualColumns S p hp (n+1)) C hC β t W K hK hW


-- @@ L54-54 verbatim
end SevenEighths.CenteredMomentAmplificationActiveFamily


-- @@ L56-56 verbatim
end


-- @@ L58-58 verbatim
end OAI
