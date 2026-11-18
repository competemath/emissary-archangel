import OAI.NumberTheory.DirichletL.Moments.FirstMixedCommonRadius
import OAI.NumberTheory.DirichletL.Moments.FirstExceptionalChildPaid


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentFirstMixedChild

-- @@ L10-10 verbatim
open HeckeFamily CanonicalQuadraticSieve CompletedGauss

-- @@ L11-11 verbatim
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile

-- @@ L12-12 verbatim
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps

-- @@ L13-13 verbatim
open CenteredMomentFirstChildLower CenteredMomentFirstExceptionalChildPaid

-- @@ L14-14 verbatim
open CenteredMomentFirstMixedAllowance CenteredMomentFirstMixedCommonRadius

-- @@ L15-15 verbatim
open CenteredMomentCommonRadiusSaving CenteredMomentFirstAmplificationChoice

-- @@ L16-16 verbatim
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization

-- @@ L17-17 verbatim
open CenteredMomentDescentLedger CenteredMomentCompleteCommon CenteredMomentCanonicalFirst

-- @@ L18-18 verbatim
open CenteredMomentPrimeElements CenteredMomentPrimePool ConcreteTraceCRT

-- @@ L19-19 verbatim
open CenteredMomentRankinRadical ActualEisensteinCubic

-- @@ L20-20 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L21-21 verbatim
variable {ι:Type*}[Fintype ι]

-- @@ L22-22 verbatim
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _


-- @@ L24-49 verbatim
theorem actual_main_child_stage (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (s:Input ι)(Rmask:Ideal O)
    (B:actualAllocations s.pools (commonPart I J))(t parentA parentM:ℝ)
    (hX₁:Z^(parentM/4)≤s.X₁)(hX₂:Z^(parentM/4)≤s.X₂)
    (hY₁:Z^(parentM/4)≤s.Y₁)(hY₂:Z^(parentM/4)≤s.Y₂) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let _p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let _R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    parentA-5*parentM/6-(
      firstSaving c (d+K0-j) 0 (Real.logb Z (τ.modulus.absNorm:ℝ)) 0
        (extractedAllowance I J Z)
        (Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-j) (sigma/3))-2*max (inputCap Z (child s (commonPart I J) Rmask B τ t)) 0/3≤
      parentA-parentM+4*sigma/3+5*(delta+reserve)/6 := by
  have hs:=actual_main_column_saving η τ m I J E hI hJ A K X Z j sigma delta reserve hZ hmod
  have hh:=child_lower s (commonPart I J) Rmask (commonPart_ne_zero I J)
    B τ t Z (parentM/4) hZ hX₁ hX₂ hY₁ hY₂
  have hr:=input_cap_lower Z _ hZ _ hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
  have hm:=le_max_left (inputCap Z (child s (commonPart I J) Rmask B τ t)) (0:ℝ)
  dsimp only at hs hr ⊢
  linarith


-- @@ L51-88 verbatim
theorem actual_error_child_stage (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7)
    (s:Input ι)(Rmask:Ideal O)
    (B:actualAllocations s.pools (commonPart I J))(t parentA parentM:ℝ)
    (Bp:actualAllocations (child s (commonPart I J) Rmask B τ t).pools ((Ideal.span {p0})^k))
    (υ:Character)(v:ℝ)
    (hX₁:Z^(parentM/4)≤s.X₁)(hX₂:Z^(parentM/4)≤s.X₂)
    (hY₁:Z^(parentM/4)≤s.Y₁)(hY₂:Z^(parentM/4)≤s.Y₂) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let _p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let _R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    parentA-5*parentM/6-(
      firstSaving c (d+K0-j) (errorRemoval p0 Z k)
        (Real.logb Z (τ.modulus.absNorm:ℝ)) (errorMoving p0 Z k) (extractedAllowance I J Z)
        (Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p0 k)-j) 0)-2*max (inputCap Z (twiceChild s (commonPart I J) Rmask B τ t (Ideal.span {p0}) k Bp υ v)) 0/3≤
      parentA-parentM+3*sigma/2+5*(delta+reserve)/6 := by
  have hs:=actual_error_column_saving η τ m I J E hI hJ A K X Z j sigma delta reserve hZ hmod M H Sbad hbad p0 hp0 k hk
  have hd := elementPool_data _
    (fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).1)
    (fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).2) p0 hp0
  have hQ:Ideal.span {p0}≠0:=Ideal.span_singleton_eq_bot.not.mpr hd.1.ne_zero
  have hh:=twice_lower s (commonPart I J) Rmask (commonPart_ne_zero I J)
    B τ t (Ideal.span {p0}) hQ k Bp υ v Z (parentM/4) hZ hX₁ hX₂ hY₁ hY₂
  have hr:=input_cap_lower Z _ hZ _ hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
  have hm:=le_max_left (inputCap Z (twiceChild s (commonPart I J) Rmask B τ t (Ideal.span {p0}) k Bp υ v)) (0:ℝ)
  dsimp only at hs hr ⊢
  unfold errorRemoval normValue at hs ⊢
  linarith


-- @@ L90-90 verbatim
end SevenEighths.CenteredMomentFirstMixedChild


-- @@ L92-92 verbatim
end


-- @@ L94-94 verbatim
end OAI
