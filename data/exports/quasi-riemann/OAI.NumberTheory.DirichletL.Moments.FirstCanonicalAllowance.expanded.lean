import OAI.NumberTheory.DirichletL.Moments.CommonAllowance
import OAI.NumberTheory.DirichletL.Moments.SecondCanonical
import OAI.NumberTheory.DirichletL.Moments.FirstCanonicalFamily


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped BigOperators Classical

-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentFirstCanonicalAllowance

-- @@ L10-10 verbatim
open ActualEisensteinCubic CanonicalQuadraticSieve ConcreteTraceCRT

-- @@ L11-11 verbatim
open CenteredMomentActive CenteredMomentCanonicalFirst CenteredMomentCompleteCommon

-- @@ L12-12 verbatim
open CenteredMomentSecondCanonical CenteredMomentFirstCanonicalFamily

-- @@ L13-13 verbatim
open CenteredMomentRankinRadical CenteredMomentCommonAllowance

-- @@ L14-14 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L16-22 verbatim
theorem activeConductor_span_product (I J : Ideal O) :
    Ideal.span {activeConductor I J} =
      ∏ P ∈ activeSupport (Finset.univ : Finset (CommonIndex I J))
        (leftExponent I J) (rightExponent I J), P.val := by
  rw [activeConductor, span_finitePrimeModulus]
  exact Finset.prod_coe_sort (s := ActiveIndex I J)
    (f := fun P : CommonIndex I J => P.val)


-- @@ L24-29 verbatim
theorem active_generator_ideal_product (I J : Ideal O) (hI : Supported I) :
    (∏ P ∈ activeSupport (Finset.univ : Finset (CommonIndex I J))
      (leftExponent I J) (rightExponent I J), Ideal.span {commonPrime I J P}) =
      Ideal.span {activeConductor I J} := by
  simp_rw [commonPrime_span I J hI]
  exact (activeConductor_span_product I J).symm


-- @@ L31-33 verbatim
theorem common_ideal_product (I J : Ideal O) :
    (∏ P : CommonIndex I J, P.val) = commonRadical I J := by
  exact Finset.prod_coe_sort (s := commonSupport I J) (f := fun P : Ideal O => P)


-- @@ L35-38 verbatim
theorem common_generator_ideal_product (I J : Ideal O) (hI : Supported I) :
    (∏ P : CommonIndex I J, Ideal.span {commonPrime I J P}) = commonRadical I J := by
  simp_rw [commonPrime_span I J hI]
  exact common_ideal_product I J


-- @@ L40-48 verbatim
theorem commonRadical_active_principal (I J : Ideal O) :
    commonRadical I J = Ideal.span {activeConductor I J} *
      ∏ P ∈ principalSupport (Finset.univ : Finset (CommonIndex I J))
        (leftExponent I J) (rightExponent I J), P.val := by
  rw [← common_ideal_product, activeConductor_span_product]
  simpa only [CenteredMomentActive.activeSupport, CenteredMomentActive.principalSupport, not_not] using
    (Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun P : CommonIndex I J => netExponent (leftExponent I J P) (rightExponent I J P) ≠ 0)
    (fun P => P.val)).symm


-- @@ L50-65 verbatim
theorem actual_canonical_common_support_allowance
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C = CompletedGauss.primeSupport D)
    (Z : ℝ) (hZ : 1 < Z) :
    let c := Real.logb Z (C.absNorm : ℝ)
    let d := Real.logb Z (D.absNorm : ℝ)
    let p := Real.logb Z ((commonRadical C D).absNorm : ℝ)
    let r := Real.logb Z ((Ideal.span {activeConductor C D}).absNorm : ℝ)
    max (3*c-5*d-r) 0/6 + max (3*d-5*c-r) 0/6 ≤ c+d-2*p-r := by
  have h := actual_common_support_allowance (commonPrime C D)
    (commonPrime_supported C D hC) (leftExponent C D) (rightExponent C D)
    (leftExponent_pos C D) (rightExponent_pos C D) Z hZ
  dsimp only at h ⊢
  rw [left_ideal_product C D hC hCD, right_ideal_product C D hC hD hCD,
    common_generator_ideal_product C D hC, active_generator_ideal_product C D hC] at h
  exact h


-- @@ L67-76 verbatim
theorem activeConductor_span_filter (I J : Ideal O) :
    Ideal.span {activeConductor I J} =
      ∏ P ∈ (commonSupport I J).filter (fun P =>
        netExponent (CenteredExceptionalCount.valuation I P)
          (CenteredExceptionalCount.valuation J P) ≠ 0), P := by
  rw [activeConductor_span_product]
  simp only [CenteredMomentActive.activeSupport, Finset.prod_filter]
  exact Finset.prod_coe_sort (s := commonSupport I J)
    (f := fun P : Ideal O => if netExponent (CenteredExceptionalCount.valuation I P)
      (CenteredExceptionalCount.valuation J P) ≠ 0 then P else 1)


-- @@ L78-92 verbatim
theorem extracted_activeConductor_span (I J : Ideal O) :
    Ideal.span {activeConductor (commonPart I J) (commonPart J I)} =
      Ideal.span {activeConductor I J} := by
  have hs : commonSupport (commonPart I J) (commonPart J I) = commonSupport I J := by
    unfold commonSupport
    rw [commonPart_support, commonPart_support, commonSupport_comm J I, Finset.inter_self]
    rfl
  rw [activeConductor_span_filter, activeConductor_span_filter, hs]
  apply Finset.prod_congr
  · apply Finset.filter_congr
    intro P hP
    rw [commonPart_valuation, commonPart_valuation, commonSupport_comm J I,
      ite_eq_left hP, ite_eq_left hP]
  · intro P _
    rfl


-- @@ L94-106 verbatim
theorem actual_extracted_common_support_allowance
    (I J : Ideal O) (hI : Supported I) (hJ : Supported J) (Z : ℝ) (hZ : 1 < Z) :
    let c := Real.logb Z ((commonPart I J).absNorm : ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm : ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm : ℝ)
    let r := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm : ℝ)
    max (3*c-5*d-r) 0/6 + max (3*d-5*c-r) 0/6 ≤ c+d-2*p-r := by
  have h := actual_canonical_common_support_allowance
    (commonPart I J) (commonPart J I) (commonPart_supported I J hI)
    (commonPart_supported J I hJ) (commonParts_equal_support I J) Z hZ
  dsimp only at h ⊢
  rw [extracted_commonRadical, extracted_activeConductor_span] at h
  exact h


-- @@ L108-108 verbatim
end SevenEighths.CenteredMomentFirstCanonicalAllowance


-- @@ L110-110 verbatim
end


-- @@ L112-112 verbatim
end OAI
