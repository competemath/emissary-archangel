import OAI.NumberTheory.DirichletL.Moments.SecondChildProfile


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators Classical


-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentSecondHeightFamily

-- @@ L9-9 verbatim
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss

-- @@ L10-10 verbatim
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentHeckeExpansion

-- @@ L11-11 verbatim
open CenteredMomentSecondChildProfile CenteredMomentChildRows CenteredMomentChildAssembly

-- @@ L12-12 verbatim
open CenteredMomentSecondScaled RayFourExpansion ConcretePrimeRowBridge ActualEisensteinCubic

-- @@ L13-13 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L15-15 verbatim
def fixedBadMask : O := goodLambda*2


-- @@ L17-18 verbatim
theorem fixedBadMask_ne_zero : fixedBadMask≠0 :=
  mul_ne_zero PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero (by norm_num)


-- @@ L20-27 verbatim
theorem fixedBadMask_coprime (n : O) (hn : Supported (Ideal.span {n})) :
    IsCoprime fixedBadMask n := by
  have hl := PrimaryIdealUnitReindex.lambda_prime_actual.irreducible.coprime_iff_not_dvd.mpr
    ((supported_span_iff n).mp hn).1
  have h2 := negative_two_prime.irreducible.coprime_iff_not_dvd.mpr
    (by simpa only [neg_dvd] using ((supported_span_iff n).mp hn).2)
  have htwo : IsCoprime (2:O) n := h2.of_isCoprime_of_dvd_left ⟨-1,by ring⟩
  exact hl.mul_left htwo


-- @@ L29-39 verbatim
theorem heightCoeff_eq_fixed_rowWeight (τ : Character) (t : ℝ)
    (I : Ideal O) (hI : Supported I) :
    heightCoeff τ t I=rowWeight τ fixedBadMask 1 1 t I := by
  have hc : IsCoprime (Ideal.span {fixedBadMask}) I := by
    rw [←primary_span_supported I hI,Ideal.isCoprime_span_singleton_iff]
    exact fixedBadMask_coprime _ ((supported_span_primaryGenerator_iff I).mpr hI)
  have hs := idealRowHom_sixth_mask fixedBadMask I hI
  rw [ite_eq_left hc.symm] at hs
  change idealCoeff τ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
    ((idealCoeff τ I*idealRowHom (fixedBadMask^6*(1*1)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t))
  simp only [mul_one,hs]


-- @@ L41-51 verbatim
theorem exists_second_family (η : Character) (χ : RayCharacter) (A : O) (hA : A≠0) :
    ∃ τ : Character,
      τ.modulus.absNorm≤HeckeRowClosure.rowConductorBound (childCharacter η χ) fixedBadMask 1 A ∧
      ∀ I : Ideal O,Supported I → ∀ t : ℝ,
        heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*
          rayCharacter χ (primaryGenerator I) := by
  obtain ⟨τ,hN,hτ⟩ := exists_second_height_character η χ fixedBadMask A fixedBadMask_ne_zero hA
    (by exact dvd_mul_right goodLambda (2:O)) (by exact dvd_mul_left (2:O) goodLambda)
  refine ⟨τ,hN,?_⟩
  intro I hI t
  rw [hτ I hI t,←heightCoeff_eq_fixed_rowWeight η t I hI]


-- @@ L53-62 verbatim
theorem second_height_divisor_column (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (L I : Ideal O) (hI : Supported I) (β : Ideal O → ℂ) (t : ℝ) :
    divisorCoefficient L (fun J : Ideal O => primaryGenerator J)
      (movingCoefficient A (fun J : Ideal O => primaryGenerator J)
        (fun J => β J*heightCoeff η t J)) χ I=
      (if L∣I then β I else 0)*heightCoeff τ t I := by
  rw [divisorCoefficient,movingCoefficient,primary_span_supported I hI,hτ I hI t]
  split_ifs <;> ring


-- @@ L64-64 verbatim
end SevenEighths.CenteredMomentSecondHeightFamily


-- @@ L66-66 verbatim
end


-- @@ L68-68 verbatim
end OAI
