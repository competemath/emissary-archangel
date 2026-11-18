import OAI.NumberTheory.DirichletL.Moments.FirstActiveFourier
import OAI.NumberTheory.DirichletL.Moments.CompleteCommon


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped BigOperators Classical SchwartzMap


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentCanonicalFirst

-- @@ L10-10 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson

-- @@ L11-11 verbatim
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredExceptionalCount

-- @@ L12-12 verbatim
open CenteredMomentCommonSupport CenteredMomentFourier CenteredMomentSupportedCorrelation

-- @@ L13-13 verbatim
open CenteredMomentFirstReduced CenteredMomentFirstActiveFourier CenteredMomentActive

-- @@ L14-14 verbatim
open CenteredMomentCompleteCommon UniqueFactorizationMonoid

-- @@ L15-15 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L17-17 verbatim
abbrev CommonIndex (I J : Ideal O) := {P : Ideal O // P∈commonSupport I J}

-- @@ L18-20 verbatim
instance commonIndexMaximal (I J : Ideal O) (P : CommonIndex I J) : P.val.IsMaximal := by
  have hp := prime_of_normalized_factor P.val (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1)
  exact (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero


-- @@ L22-22 verbatim
def leftExponent (I J : Ideal O) (P : CommonIndex I J) := valuation I P.val

-- @@ L23-23 verbatim
def rightExponent (I J : Ideal O) (P : CommonIndex I J) := valuation J P.val


-- @@ L25-27 verbatim
theorem common_good (I J : Ideal O) (hI : Supported I) (P : CommonIndex I J) :
    ConcretePrimeRowBridge.goodLambda ∉ P.val :=
  (supported_factors_good I hI P.val (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1)).2.1


-- @@ L29-31 verbatim
theorem common_odd (I J : Ideal O) (hI : Supported I) (P : CommonIndex I J) :
    ringChar (O ⧸ P.val)≠2 :=
  (supported_factors_good I hI P.val (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1)).2.2


-- @@ L33-34 verbatim
theorem leftExponent_pos (I J : Ideal O) (P : CommonIndex I J) : 0<leftExponent I J P :=
  (common_valuations_pos I J P.val P.property).1


-- @@ L36-37 verbatim
theorem rightExponent_pos (I J : Ideal O) (P : CommonIndex I J) : 0<rightExponent I J P :=
  (common_valuations_pos I J P.val P.property).2


-- @@ L39-41 verbatim
theorem commonPart_left_product (I J : Ideal O) :
    commonPart I J=∏ P : CommonIndex I J,P.val^leftExponent I J P := by
  exact (Finset.prod_coe_sort (s:=commonSupport I J) (f:=fun P => P^valuation I P)).symm


-- @@ L43-47 verbatim
theorem commonPart_right_product (I J : Ideal O) :
    commonPart J I=∏ P : CommonIndex I J,P.val^rightExponent I J P := by
  unfold commonPart
  rw [commonSupport_comm J I]
  exact (Finset.prod_coe_sort (s:=commonSupport I J) (f:=fun P => P^valuation J P)).symm


-- @@ L49-50 verbatim
abbrev ActiveIndex (I J : Ideal O) :=
  activeSupport (Finset.univ : Finset (CommonIndex I J)) (leftExponent I J) (rightExponent I J)

-- @@ L51-51 verbatim
def activePrime (I J : Ideal O) (P : ActiveIndex I J) : Ideal O := P.val.val

-- @@ L52-53 verbatim
instance activePrimeMaximal (I J : Ideal O) (P : ActiveIndex I J) : (activePrime I J P).IsMaximal :=
  commonIndexMaximal I J P.val


-- @@ L55-55 verbatim
def activeConductor (I J : Ideal O) : O := finitePrimeModulus (activePrime I J)

-- @@ L56-57 verbatim
def activeExponent (I J : Ideal O) (P : ActiveIndex I J) :=
  netExponent (leftExponent I J P.val) (rightExponent I J P.val)

-- @@ L58-59 verbatim
theorem activeGood (I J : Ideal O) (hI : Supported I) (P : ActiveIndex I J) :
    ConcretePrimeRowBridge.goodLambda ∉ activePrime I J P := common_good I J hI P.val


-- @@ L61-63 verbatim
theorem activeCoprime (I J : Ideal O) : Pairwise (Function.onFun IsCoprime (activePrime I J)) :=
  activePrimes_pairwise_coprime (fun P : CommonIndex I J => P.val) Subtype.val_injective
    Finset.univ (leftExponent I J) (rightExponent I J)


-- @@ L65-67 verbatim
def activeFunction (I J : Ideal O) (hI : Supported I) : Residue (activeConductor I J) → ℂ :=
  principalSexticRow (activePrime I J) (activeCoprime I J) (activeGood I J hI)
    (activeExponent I J) (activeConductor I J) (span_finitePrimeModulus _)


-- @@ L69-69 verbatim
def residualGenerator (I J : Ideal O) : O := CompletedGauss.primaryGenerator (residualPart I J)


-- @@ L71-73 verbatim
theorem residualGenerator_span (I J : Ideal O) (hI : Supported I) :
    Ideal.span {residualGenerator I J}=residualPart I J :=
  (CompletedGauss.primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ (residualPart_supported I J hI))).1


-- @@ L75-78 verbatim
theorem residualGenerator_supported (I J : Ideal O) (hI : Supported I) :
    Supported (Ideal.span {residualGenerator I J}) := by
  rw [residualGenerator_span I J hI]
  exact residualPart_supported I J hI


-- @@ L80-81 verbatim
def residualCharacter (I J : Ideal O) (hI : Supported I) : MulChar (Residue (residualGenerator I J)) ℂ :=
  supportedModulusCharacter _ (residualGenerator_supported I J hI)


-- @@ L83-85 verbatim
@[simp] theorem residualCharacter_mk (I J : Ideal O) (hI : Supported I) (z : O) :
    residualCharacter I J hI (Ideal.Quotient.mk _ z)=idealRowHom z (residualPart I J) := by
  rw [residualCharacter,supportedModulusCharacter_mk,residualGenerator_span I J hI]


-- @@ L87-100 verbatim
theorem original_pair_factor (I J : Ideal O) (hI : Supported I) (hJ : Supported J) (z : O) :
    idealRowHom z I*star (idealRowHom z J)=
      residualCharacter I J hI (Ideal.Quotient.mk _ z)*
        (residualCharacter J I hJ)⁻¹ (Ideal.Quotient.mk _ z)*
        (idealRowHom z (∏ P : CommonIndex I J,P.val^leftExponent I J P)*
          star (idealRowHom z (∏ P : CommonIndex I J,P.val^rightExponent I J P))) := by
  let := finite_quotient_span (supported_element_ne_zero _ (residualGenerator_supported J I hJ))
  rw [← MulChar.star_apply',residualCharacter_mk,residualCharacter_mk,
    ← commonPart_left_product,← commonPart_right_product]
  have hi := congrArg (idealRowHom z) (reconstruct I J hI.1)
  have hj := congrArg (idealRowHom z) (reconstruct J I hJ.1)
  simp only [map_mul] at hi hj
  rw [hi,hj,star_mul]
  ring


-- @@ L102-116 verbatim
def reducedFirstSum (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑ E ∈ (principalSupport (Finset.univ : Finset (CommonIndex I J)) (leftExponent I J) (rightExponent I J)).powerset,
    let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
    let k := K/‖eisEmbedding e‖^2
    let a := residualGenerator I J
    let b := residualGenerator J I
    let r := activeConductor I J
    (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
      tripleRow a b r (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e*
      (((k/‖eisEmbedding (a*(b*r))‖^2:ℝ):ℂ)*∑' h : O,
        tripleFourier a b r (supported_element_ne_zero _ (residualGenerator_supported I J hI))
          (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) (finitePrimeModulus_ne_zero _)
          (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) h*
          paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (a*(b*r))‖^2))


-- @@ L118-129 verbatim
theorem canonical_pair_reduced_poisson (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (∑' z : O,(idealRowHom z I*star (idealRowHom z J))*W (‖eisEmbedding z‖^2/K))=
      reducedFirstSum I J hI hJ W K := by
  simp_rw [original_pair_factor I J hI hJ]
  exact common_residual_reduced_poisson (fun P : CommonIndex I J => P.val) Subtype.val_injective
    (common_good I J hI) (common_odd I J hI) Finset.univ (leftExponent I J) (rightExponent I J)
    (fun P _ => ne_of_gt (leftExponent_pos I J P)) (fun P _ => ne_of_gt (rightExponent_pos I J P))
    (residualGenerator I J) (residualGenerator J I)
    (supported_element_ne_zero _ (residualGenerator_supported I J hI))
    (supported_element_ne_zero _ (residualGenerator_supported J I hJ))
    (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ W K hK


-- @@ L131-141 verbatim
theorem activeConductor_span_dvd (I J : Ideal O) :
    Ideal.span {activeConductor I J} ∣ commonPart I J := by
  rw [activeConductor,span_finitePrimeModulus]
  change (∏ P : ActiveIndex I J,P.val.val) ∣ commonPart I J
  rw [Finset.prod_coe_sort]
  refine (Finset.prod_dvd_prod_of_subset _ Finset.univ
    (fun P : CommonIndex I J => P.val) (Finset.subset_univ _)).trans ?_
  rw [commonPart_left_product]
  apply Finset.prod_dvd_prod_of_dvd
  intro P hP
  simpa only [pow_one] using pow_dvd_pow P.val (leftExponent_pos I J P)


-- @@ L143-147 verbatim
theorem residual_active_coprime (I J : Ideal O) (hI : Supported I) :
    IsCoprime (residualGenerator I J) (activeConductor I J) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [residualGenerator_span I J hI]
  exact (commonPart_own_residual_coprime I J).symm.of_isCoprime_of_dvd_right (activeConductor_span_dvd I J)


-- @@ L149-153 verbatim
theorem opposite_residual_active_coprime (I J : Ideal O) (hJ : Supported J) :
    IsCoprime (residualGenerator J I) (activeConductor I J) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [residualGenerator_span J I hJ]
  exact (commonPart_residualPart_coprime I J).symm.of_isCoprime_of_dvd_right (activeConductor_span_dvd I J)


-- @@ L155-159 verbatim
theorem residual_generators_coprime (I J : Ideal O) (hI : Supported I) (hJ : Supported J) :
    IsCoprime (residualGenerator I J) (residualGenerator J I) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [residualGenerator_span I J hI,residualGenerator_span J I hJ]
  exact residualParts_coprime I J


-- @@ L161-178 verbatim
theorem canonical_tripleFourier_norm_le (I J : Ideal O) (hI : Supported I) (hJ : Supported J) (h : O) :
    ‖tripleFourier (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
      (supported_element_ne_zero _ (residualGenerator_supported I J hI))
      (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) (finitePrimeModulus_ne_zero _)
      (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) h‖ ≤
      ‖eisEmbedding (activeConductor I J)‖*
        ‖residueGauss (residualGenerator I J) (supported_element_ne_zero _ (residualGenerator_supported I J hI))
          (residualCharacter I J hI) (Ideal.Quotient.mk _ h)‖*
        ‖residueGauss (residualGenerator J I) (supported_element_ne_zero _ (residualGenerator_supported J I hJ))
          (residualCharacter J I hJ)⁻¹ (Ideal.Quotient.mk _ h)‖ := by
  exact tripleFourier_active_norm_le (activePrime I J) (activeCoprime I J) (activeGood I J hI)
    (fun P => common_odd I J hI P.val) (activeExponent I J)
    (netExponent_ne_zero _ _ _) (fun P => netExponent_lt_six _ _)
    (residualGenerator I J) (residualGenerator J I)
    (supported_element_ne_zero _ (residualGenerator_supported I J hI))
    (supported_element_ne_zero _ (residualGenerator_supported J I hJ))
    ((residual_generators_coprime I J hI hJ).mul_right (residual_active_coprime I J hI))
    (opposite_residual_active_coprime I J hJ) _ _ h


-- @@ L180-180 verbatim
end SevenEighths.CenteredMomentCanonicalFirst


-- @@ L182-182 verbatim
end


-- @@ L184-184 verbatim
end OAI
