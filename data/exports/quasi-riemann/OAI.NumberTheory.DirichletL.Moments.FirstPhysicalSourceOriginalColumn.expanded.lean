import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceOriginalData
import OAI.NumberTheory.DirichletL.Moments.SecondSectorColumns


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentFirstPhysicalSource

-- @@ L10-10 verbatim
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow

-- @@ L11-11 verbatim
open CenteredMomentSecondSectorColumns CenteredMomentFirstSectorTransform IdealMobiusDivisorSum

-- @@ L12-12 verbatim
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors CenteredMomentLiveDomain

-- @@ L13-13 verbatim
open CenteredMomentGaussEnergy CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily

-- @@ L14-14 verbatim
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentChildAssembly

-- @@ L15-15 verbatim
local notation "O"=>ActualEisensteinCubic.O


-- @@ L17-36 verbatim
theorem columns_gauss_polynomial (C:Ideal O)(hC:Supported C)(S:Finset (Ideal O))
    (f:Ideal O→ℂ)(z:O):
    gaussPolynomial Finset.univ (element C C hC.1 S) (element_supported C C hC.1 S)
      (fun a=>f a) z=
    gaussPolynomial Finset.univ (sourceGenerator (residualPool C hC.1 S))
      (sourceGenerator_supported _) (fun I=>if IsCoprime C (I:Ideal O) then f I else 0) z:=by
  rw [source_gaussPolynomial (residualPool C hC.1 S)
    (fun I=>if IsCoprime C I then f I else 0) z,supported_residualPool C hC S]
  have he (a:columns C C hC.1 S):
      gaussRow (element C C hC.1 S a) (element_supported C C hC.1 S a) z=
        primaryGaussRow a z:=by
    rw [primaryGaussRow,dite_eq_left (column_supported C C hC.1 S a)]
    rfl
  simp only [gaussPolynomial,he]
  rw [Finset.sum_coe_sort (columns C C hC.1 S) (fun I=>f I*primaryGaussRow I z)]
  unfold columns
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  split_ifs <;> simp


-- @@ L38-57 verbatim
theorem columns_gauss_polynomial_filter (Q C:Ideal O)(hC:Supported C)(S:Finset (Ideal O))
    (f:Ideal O→ℂ)(z:O):
    gaussPolynomial Finset.univ (element Q C hC.1 S) (element_supported Q C hC.1 S)
      (fun a=>f a) z=
    gaussPolynomial Finset.univ (sourceGenerator (residualPool C hC.1 S))
      (sourceGenerator_supported _) (fun I=>if IsCoprime Q (I:Ideal O) then f I else 0) z:=by
  rw [source_gaussPolynomial (residualPool C hC.1 S)
    (fun I=>if IsCoprime Q I then f I else 0) z,supported_residualPool C hC S]
  have he (a:columns Q C hC.1 S):
      gaussRow (element Q C hC.1 S a) (element_supported Q C hC.1 S a) z=
        primaryGaussRow a z:=by
    rw [primaryGaussRow,dite_eq_left (column_supported Q C hC.1 S a)]
    rfl
  simp only [gaussPolynomial,he]
  rw [Finset.sum_coe_sort (columns Q C hC.1 S) (fun I=>f I*primaryGaussRow I z)]
  unfold columns
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  split_ifs <;> simp


-- @@ L59-59 verbatim
variable {ι:Type*}[Fintype ι]

-- @@ L60-60 verbatim
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _


-- @@ L62-84 verbatim
theorem first_column_original_data (D:OriginalData ι)
    (hS:∀i,∀I∈D.S i,I≠0)(hp:∀i,∀I∈D.S (Sum.inl i),Prime I)
    (C:Ideal O)(hC:Supported C)(hseed:D.s∣C)(τ:Character)(t T:ℝ)(L:Ideal O)
    (a:columns C C hC.1 D.columns→ℂ)
    (ha:∀I:columns C C hC.1 D.columns,
      a I=(if L∣(I:Ideal O) then D.beta (C*I) else 0)*heightCoeff τ t I)(z:O):
    (Real.sqrt T:ℂ)⁻¹*gaussPolynomial Finset.univ (element C C hC.1 D.columns)
      (element_supported C C hC.1 D.columns) a z=
      ∑B:actualAllocations D.S C,frozenCoefficient B.val C D.R D.nu D.slot D.lengths*
        gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
          (sourceGenerator_supported (allocatedData D C L B).columns)
          ((allocatedData D C L B).coefficient τ fixedBadMask t T) z:=by
  rw [funext ha,columns_gauss_polynomial C hC D.columns
    (fun I=>(if L∣I then D.beta (C*I) else 0)*heightCoeff τ t I) z]
  have he:(fun I:supportedColumns (residualPool C hC.1 D.columns)=>
      if IsCoprime C (I:Ideal O) then
        (if L∣(I:Ideal O) then D.beta (C*I) else 0)*heightCoeff τ t I else 0)=
      (fun I:supportedColumns (residualPool C hC.1 D.columns)=>
        (if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then D.beta (C*I) else 0)*heightCoeff τ t I):=by
    funext I
    by_cases hc:IsCoprime C (I:Ideal O) <;> by_cases hl:L∣(I:Ideal O) <;> simp [hc,hl]
  rw [he]
  exact normalized_common_gauss_allocation D hS hp C hC hseed τ t T L z


-- @@ L86-110 verbatim
theorem first_column_original_data_filter (D:OriginalData ι)
    (hS:∀i,∀I∈D.S i,I≠0)(hp:∀i,∀I∈D.S (Sum.inl i),Prime I)
    (Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)(hQC:primeSupport Q=primeSupport C)
    (hseed:D.s∣C)(τ:Character)(t T:ℝ)(L:Ideal O)
    (a:columns Q C hC.1 D.columns→ℂ)
    (ha:∀I:columns Q C hC.1 D.columns,
      a I=(if L∣(I:Ideal O) then D.beta (C*I) else 0)*heightCoeff τ t I)(z:O):
    (Real.sqrt T:ℂ)⁻¹*gaussPolynomial Finset.univ (element Q C hC.1 D.columns)
      (element_supported Q C hC.1 D.columns) a z=
      ∑B:actualAllocations D.S C,frozenCoefficient B.val C D.R D.nu D.slot D.lengths*
        gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
          (sourceGenerator_supported (allocatedData D C L B).columns)
          ((allocatedData D C L B).coefficient τ fixedBadMask t T) z:=by
  rw [funext ha,columns_gauss_polynomial_filter Q C hC D.columns
    (fun I=>(if L∣I then D.beta (C*I) else 0)*heightCoeff τ t I) z]
  have he:(fun I:supportedColumns (residualPool C hC.1 D.columns)=>
      if IsCoprime Q (I:Ideal O) then
        (if L∣(I:Ideal O) then D.beta (C*I) else 0)*heightCoeff τ t I else 0)=
      (fun I:supportedColumns (residualPool C hC.1 D.columns)=>
        (if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then D.beta (C*I) else 0)*heightCoeff τ t I):=by
    funext I
    rw [coprime_of_same_support Q C I hQ hC.1 (Finset.mem_filter.mp I.property).2.1 hQC]
    by_cases hc:IsCoprime C (I:Ideal O) <;> by_cases hl:L∣(I:Ideal O) <;> simp [hc,hl]
  rw [he]
  exact normalized_common_gauss_allocation D hS hp C hC hseed τ t T L z


-- @@ L112-112 verbatim
end SevenEighths.CenteredMomentFirstPhysicalSource


-- @@ L114-114 verbatim
end


-- @@ L116-116 verbatim
end OAI
