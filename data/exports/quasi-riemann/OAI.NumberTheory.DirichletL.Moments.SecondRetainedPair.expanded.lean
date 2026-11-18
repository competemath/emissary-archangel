import OAI.NumberTheory.DirichletL.Moments.SecondSectorRetained


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators Classical SchwartzMap


-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentSecondRetainedPair

-- @@ L9-9 verbatim
open CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT EisensteinSchwartzPoisson

-- @@ L10-10 verbatim
open CenteredMomentSecondSectorRetained CenteredMomentSupport CenteredMomentSupportedCorrelation

-- @@ L11-11 verbatim
open CenteredMomentSecondWholeKernel CenteredMomentFirstLocalization CenteredMomentSectorLocalization

-- @@ L12-12 verbatim
open CenteredMomentSecondLocalization CenteredMomentSourceRow

-- @@ L13-13 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L15-36 verbatim
theorem physical_pair_summable (C D I J : Ideal O) (hI : Supported (C*I)) (hJ : Supported (D*J))
    (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K) :
    Summable (fun j : O=>idealCorrelation (C*I) (D*J) hI hJ j*physicalKernel C D W K R j I J) := by
  have hk : 0<K/((Ideal.absNorm (C*I):ℝ)*Ideal.absNorm (D*J)) :=
    div_pos hK (mul_pos (CenteredMomentFirstScale.norm_pos _ hI.1) (CenteredMomentFirstScale.norm_pos _ hJ.1))
  have hc (j : O) : ‖idealCorrelation (C*I) (D*J) hI hJ j‖≤
      (Ideal.absNorm (C*I):ℝ)*Ideal.absNorm (D*J) := by
    have hh := CenteredMomentTail.actualCorrelation_norm_le _ _
      ((supported_span_primaryGenerator_iff _).mpr hI) ((supported_span_primaryGenerator_iff _).mpr hJ) j
    simpa only [idealCorrelation,primary_span_supported _ hI,primary_span_supported _ hJ] using hh
  have hs := weighted_fourier_summable W _ hk (fun j=>idealCorrelation (C*I) (D*J) hI hJ j)
    (fun j=>(retainedWeight R (normValue j):ℂ)) _ hc (fun j=>retained_complex_norm R _)
  have he (j : O) : K*‖eisEmbedding j‖^2/‖eisEmbedding (primaryGenerator (C*I)*primaryGenerator (D*J))‖^2=
      (K/((Ideal.absNorm (C*I):ℝ)*Ideal.absNorm (D*J)))*normValue j := by
    rw [map_mul,norm_mul,mul_pow,primary_norm_sq _ hI,primary_norm_sq _ hJ,normValue_eq_embedding]
    ring
  convert hs.mul_left
    ((K:ℂ)/((Real.sqrt (Ideal.absNorm (C*I):ℝ):ℂ)*(Real.sqrt (Ideal.absNorm (D*J):ℝ):ℂ))) using 1
  funext j
  dsimp only [physicalKernel]
  rw [he]
  ring


-- @@ L38-53 verbatim
theorem retainedPair_positive_frequency (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) :
    secondRetainedPair I J hI hJ W K Tsec Z ξ=
      ∑' j : O,idealCorrelation I J hI hJ j*physicalKernel 1 1 W K (frequencyRadius Tsec Z ξ) j I J := by
  have he := (Equiv.neg O).tsum_eq (fun j : O=>idealCorrelation I J hI hJ j*
    physicalKernel 1 1 W K (frequencyRadius Tsec Z ξ) j I J)
  simp only [Equiv.neg_apply,physicalKernel,one_mul,map_neg,norm_neg,
    normValue_eq_embedding] at he
  simp only [physicalKernel,one_mul,normValue_eq_embedding]
  rw [←he]
  unfold secondRetainedPair
  rw [←tsum_mul_left]
  apply tsum_congr
  intro j
  simp only [idealCorrelation,normValue_eq_embedding]
  ring


-- @@ L55-55 verbatim
end SevenEighths.CenteredMomentSecondRetainedPair


-- @@ L57-57 verbatim
end


-- @@ L59-59 verbatim
end OAI
