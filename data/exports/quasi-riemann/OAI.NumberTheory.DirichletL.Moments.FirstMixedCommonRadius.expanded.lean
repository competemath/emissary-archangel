import OAI.NumberTheory.DirichletL.Moments.FirstMixedAllowance
import OAI.NumberTheory.DirichletL.Moments.CommonRadiusSaving


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentFirstMixedCommonRadius

-- @@ L10-10 verbatim
open HeckeFamily CanonicalQuadraticSieve CompletedGauss

-- @@ L11-11 verbatim
open CenteredMomentDescentLedger CenteredMomentFirstAmplificationChoice

-- @@ L12-12 verbatim
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization

-- @@ L13-13 verbatim
open CenteredMomentCompleteCommon CenteredMomentCanonicalFirst

-- @@ L14-14 verbatim
open CenteredMomentFirstCanonicalAllowance CenteredMomentFirstCanonicalFamily

-- @@ L15-15 verbatim
open CenteredMomentRankinRadical ConcreteTraceCRT ActualEisensteinCubic

-- @@ L16-16 verbatim
open CenteredMomentFirstMixedAllowance CenteredMomentCommonRadiusSaving

-- @@ L17-17 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L19-39 verbatim
theorem column_saving_gates (η τ : Character) (m : O)
    (I J : Ideal O) (A : Finset (CommonIndex I J)) (Z : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J}) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let q := Real.logb Z (τ.modulus.absNorm:ℝ)
    0≤c ∧ 0≤q ∧ 0≤extractedAllowance I J Z ∧
      3*c-5*d≤6*extractedAllowance I J Z+q := by
  dsimp only
  have hq := canonical_active_log_le η τ m I J A Z hZ hmod
  have hc : 0≤Real.logb Z ((commonPart I J).absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (commonPart_ne_zero I J))
  have hm := le_max_left (3*Real.logb Z ((commonPart I J).absNorm:ℝ)-
    5*Real.logb Z ((commonPart J I).absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) (0:ℝ)
  refine ⟨hc,hq.1,?_,?_⟩
  · unfold extractedAllowance; positivity
  · unfold extractedAllowance; linarith [hq.2]


-- @@ L41-61 verbatim
theorem actual_main_column_saving (η τ : Character) (m : O)
    (I J E : Ideal O) (_hI : Supported I) (_hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J}) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let _p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let _R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    2*c/3-4*sigma/3-5*(delta+reserve)/6≤
      firstSaving c (d+K0-j) 0 (Real.logb Z (τ.modulus.absNorm:ℝ)) 0
        (extractedAllowance I J Z)
        (Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-j) (sigma/3) := by
  dsimp only
  rw [main_radius_gain _ _ _ _ _ _ _ _ hZ]
  obtain ⟨hc,hq,hB,hallow⟩ := column_saving_gates η τ m I J A Z hZ hmod
  convert main_saving_lower _ _ (nominalLog I J E K X Z-j) _ _ sigma delta reserve
    hc hq hB hallow using 1
  congr 1
  ring


-- @@ L63-90 verbatim
theorem actual_error_column_saving (η τ : Character) (m : O)
    (I J E : Ideal O) (_hI : Supported I) (_hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let _p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let _R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    2*(c+errorRemoval p0 Z k)/3-3*sigma/2-5*(delta+reserve)/6≤
      firstSaving c (d+K0-j) (errorRemoval p0 Z k)
        (Real.logb Z (τ.modulus.absNorm:ℝ)) (errorMoving p0 Z k) (extractedAllowance I J Z)
        (Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p0 k)-j) 0 := by
  dsimp only
  rw [error_radius_gain _ _ _ _ _ _ _ _ hZ]
  obtain ⟨hc,hq,hB,hallow⟩ := column_saving_gates η τ m I J A Z hZ hmod
  obtain ⟨hl,hu⟩ := pool_prime_log_range M H Sbad hbad Z sigma hZ p0 hp0
  unfold errorRemoval errorMoving
  convert error_saving_lower _ _ (nominalLog I J E K X Z-j) _ _ sigma delta reserve
    (Real.logb Z (normValue p0)) hc hq hB hallow hl hu k hk using 1
  congr 1
  ring


-- @@ L92-119 verbatim
theorem actual_error_column_saving_refined (η τ : Character) (m : O)
    (I J E : Ideal O) (_hI : Supported I) (_hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let _p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let _R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    2*(c+errorRemoval p0 Z k)/3-errorLoss sigma k-5*(delta+reserve)/6≤
      firstSaving c (d+K0-j) (errorRemoval p0 Z k)
        (Real.logb Z (τ.modulus.absNorm:ℝ)) (errorMoving p0 Z k) (extractedAllowance I J Z)
        (Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p0 k)-j) 0 := by
  dsimp only
  rw [error_radius_gain _ _ _ _ _ _ _ _ hZ]
  obtain ⟨hc,hq,hB,hallow⟩ := column_saving_gates η τ m I J A Z hZ hmod
  obtain ⟨hl,hu⟩ := pool_prime_log_range M H Sbad hbad Z sigma hZ p0 hp0
  unfold errorRemoval errorMoving
  convert error_saving_refined _ _ (nominalLog I J E K X Z-j) _ _ sigma delta reserve
    (Real.logb Z (normValue p0)) hc hq hB hallow hl hu k hk using 1
  congr 1
  ring


-- @@ L121-121 verbatim
end SevenEighths.CenteredMomentFirstMixedCommonRadius


-- @@ L123-123 verbatim
end


-- @@ L125-125 verbatim
end OAI
