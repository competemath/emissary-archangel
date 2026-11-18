import OAI.NumberTheory.DirichletL.Moments.AmplificationSourceError
import OAI.NumberTheory.DirichletL.Moments.SecondChildProfile
import OAI.NumberTheory.DirichletL.Moments.FirstTailAggregate


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped BigOperators Classical


-- @@ L10-10 verbatim
namespace SevenEighths.CenteredMomentAmplificationFamily

-- @@ L11-11 verbatim
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion

-- @@ L12-12 verbatim
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion

-- @@ L13-13 verbatim
open CenteredMomentAmplificationShortening CenteredMomentFixedRay

-- @@ L14-14 verbatim
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow

-- @@ L15-15 verbatim
open CenteredMomentSecondChildProfile CenteredMomentSourceRow CenteredMomentChildRows

-- @@ L16-16 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L18-20 verbatim
def amplificationPhase (p : O) (k : ℕ) (r : RayRing) : ℂ :=
  (QuadraticAllOddCRT.quadraticRaySign (ActualEisensteinCoordinates.residue p)
    (QuadraticGaussRay.residueQuotientFour r):ℂ)^k


-- @@ L22-24 verbatim
theorem amplificationPhase_mk (p u : O) (k : ℕ) :
    amplificationPhase p k (Ideal.Quotient.mk _ u)=sexticReciprocityPhase p u^k := by
  simp only [amplificationPhase,QuadraticGaussRay.residueQuotientFour_mk,sexticReciprocityPhase]


-- @@ L26-29 verbatim
theorem amplificationPhase_norm (p : O) (k : ℕ) (r : RayRing) :
    ‖amplificationPhase p k r‖≤1 := by
  unfold amplificationPhase QuadraticAllOddCRT.quadraticRaySign
  split_ifs <;> cases k <;> simp


-- @@ L31-34 verbatim
theorem amplificationPhase_mass (p : O) (k : ℕ) :
    (∑ χ : RayCharacter,‖phaseCoeff (amplificationPhase p k) χ‖)≤16 := by
  simpa only [mul_one] using phaseCoeff_sum_norm_le (amplificationPhase p k) 1
    (fun u => amplificationPhase_norm p k u)


-- @@ L36-41 verbatim
theorem amplificationPhase_expansion (p u : O) (k : ℕ)
    (hu : Supported (Ideal.span {u})) :
    sexticReciprocityPhase p u^k=
      ∑ χ : RayCharacter,phaseCoeff (amplificationPhase p k) χ*rayCharacter χ u := by
  have he := phase_expansion (amplificationPhase p k) u
  simpa only [supported_rayMask u hu,one_mul,amplificationPhase_mk] using he


-- @@ L43-64 verbatim
theorem exists_amplification_family (η : Character) (m p : O)
    (hm : m≠0) (hp : p≠0) (hs : Supported (Ideal.span {p}))
    (hpp : goodLambda^2 ∣ p-1) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) (k : ℕ) :
    ∃ τ : RayCharacter → Character,
      (∀ χ, (τ χ).modulus.absNorm≤rowConductorBound (childCharacter η χ) m 1 (p^(2*k))) ∧
      ∀ I : Ideal O,Supported I → ∀ t : ℝ,
        rowWeight η m 1 1 t I*residualCharacter p k (primaryGenerator I)=
          ∑ χ : RayCharacter,phaseCoeff (amplificationPhase p k) χ*heightCoeff (τ χ) t I := by
  choose τ hN hτ using fun χ : RayCharacter =>
    exists_second_height_character η χ m (p^(2*k)) hm (pow_ne_zero _ hp) hmLam hm2
  refine ⟨τ,hN,?_⟩
  intro I hI t
  have hn := supported_primaryGenerator_ne_zero I hI
  have hgen : Supported (Ideal.span {primaryGenerator I}) := by
    rw [primary_span_supported I hI];exact hI
  rw [residualCharacter_moving p _ k hs hgen hpp (primaryGenerator_spec I hn).2,
    primary_span_supported I hI,amplificationPhase_expansion p _ k hgen]
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [hτ χ I hI t]
  ring


-- @@ L66-79 verbatim
theorem original_column_family (η : Character) (m p : O) (k : ℕ)
    (τ : RayCharacter → Character)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      rowWeight η m 1 1 t I*residualCharacter p k (primaryGenerator I)=
        ∑ χ : RayCharacter,phaseCoeff (amplificationPhase p k) χ*heightCoeff (τ χ) t I)
    (C I : Ideal O) (hI : Supported I) (β : Ideal O → ℂ) (t : ℝ) :
    (β (C*I)*rowWeight η m 1 1 t (C*I))*residualCharacter p k (primaryGenerator I)=
      rowWeight η m 1 1 t C *
        ∑ χ : RayCharacter,phaseCoeff (amplificationPhase p k) χ*(β (C*I)*heightCoeff (τ χ) t I) := by
  rw [map_mul]
  calc
    _ = rowWeight η m 1 1 t C *
      (β (C*I)*(rowWeight η m 1 1 t I*residualCharacter p k (primaryGenerator I))) := by ring
    _ = _ := by rw [hτ I hI t,Finset.mul_sum];congr 1;apply Finset.sum_congr rfl;intro χ hχ;ring


-- @@ L81-81 verbatim
end SevenEighths.CenteredMomentAmplificationFamily


-- @@ L83-83 verbatim
end


-- @@ L85-85 verbatim
end OAI
