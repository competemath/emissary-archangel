import OAI.NumberTheory.DirichletL.Moments.CommonRadialData


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators SchwartzMap


-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentCommonRadialSource

-- @@ L9-9 verbatim
open CenteredMomentCommonRadialData CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy

-- @@ L10-10 verbatim
open CenteredMomentSourceRectangle CenteredMomentSourceMass CenteredMomentSourceProfileMass

-- @@ L11-11 verbatim
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentCommonProfile

-- @@ L12-12 verbatim
open CenteredMomentAmplificationLiveMask CenteredMomentAddedZeroUniform CenteredMomentCommonRawScale

-- @@ L13-13 verbatim
open CenteredMomentRestrictedSource CenteredMomentSecondHeightFamily CenteredMomentHeckeColumnWindow

-- @@ L14-14 verbatim
open CenteredMomentFirstSectors ConcretePrimeRowBridge CanonicalQuadraticSieve

-- @@ L15-15 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L16-16 verbatim
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

-- @@ L17-17 verbatim
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

 
-- @@ L19-25 verbatim
def sourceEnergy (s:Input ι) (r:Radial) (C:Ideal O) (hC:Supported C) (R seed L:Ideal O) : ℝ :=
  let Q:=finiteColumns (Fintype.piFinset s.pools)
  let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
  sourceRestrictedEnergy r.keep (residualPool C hC.1 Q)
    (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
    (heightCoeff s.η s.t) r.profile r.scale/(s.X₁*s.X₂*∏i,s.P i)

 
-- @@ L27-29 verbatim
def commonCost (s:Input ι) (C:Ideal O) : ℝ :=
  ((actualAllocations s.pools C).card:ℝ)*
    (((∏i,s.M i)^2*(max 1 s.upper)^Fintype.card ι)/(Ideal.absNorm C:ℝ))


-- @@ L31-34 verbatim
omit [DecidableEq ι] in
lemma commonCost_nonneg (s:Input ι) (C:Ideal O) : 0≤commonCost s C := by
  unfold commonCost
  positivity

 
-- @@ L36-58 verbatim
theorem live_source_eq (s:Input ι) (r:Radial) (C R L:Ideal O) (B:actualAllocations s.pools C) :
    sourceRestrictedEnergy r.keep
      (finiteColumns (liveBox s.pools B.val (alloc_ne s C B)))
      (finiteColumnCoefficient (liveBox s.pools B.val (alloc_ne s C B))
        (maskedLiveProfile B.val C R L s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1))
      (heightCoeff s.η s.t) r.profile r.scale/remainingRaw B.val (s.X₁*s.X₂) s.P=
      energy (commonData s C R B) r L := by
  rw [CenteredMomentCanonicalRetainedSource.liveBox_original_pools]
  have hcov₁:=plainCoverage_residualPool (s.pools (Sum.inr 0)) s.W₁ 1 _
    (alloc_ne s C B (Sum.inr 0)) s.X₁ s.Y₁ s.coverage₁
  have hcov₂:=plainCoverage_residualPool (s.pools (Sum.inr 1)) s.W₂ 1 _
    (alloc_ne s C B (Sum.inr 1)) s.X₂ s.Y₂ s.coverage₂
  simp only [one_mul] at hcov₁ hcov₂
  have hh:=CenteredMomentRadialSourceDictionary.actual_source_energy (commonData s C R B) r
    (residualPool (B.val (Sum.inr 0)) (alloc_ne s C B _) (s.pools (Sum.inr 0)))
    (residualPool (B.val (Sum.inr 1)) (alloc_ne s C B _) (s.pools (Sum.inr 1)))
    (R*C) L (B.val (Sum.inr 0)) (B.val (Sum.inr 1)) s.X₁ s.X₂ s.Y₁ s.Y₂
    rfl rfl rfl rfl rfl rfl hcov₁ hcov₂
  refine Eq.trans ?_ hh
  apply congrArg₂ (fun x y : ℝ => x / y)
  · simp only [maskedLiveProfile,commonData,one_mul,Input.pools,Sum.elim_inl]
  · dsimp only [remainingRaw,plainNorm,commonData]
    ring

 
-- @@ L60-78 verbatim
theorem original_source_common_bound (s:Input ι) (r:Radial) (C:Ideal O) (hC:Supported C)
    (R seed L:Ideal O) (hseed:seed∣C) :
    sourceEnergy s r C hC R seed L≤commonCost s C*
      ∑B:actualAllocations s.pools C,energy (commonData s C R B) r L := by
  have hh:=CenteredMomentSecondSourceCost.source_divisor_common_saving (ι:=ι) s.η s.pools s.pools_ne
    (fun i I hI=>s.prime i I hI) C R seed hC hseed s.ν s.W s.P s.W₁ s.W₂
    s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 L s.t (s.X₁*s.X₂) (mul_pos s.X₁_pos s.X₂_pos)
    s.P_pos s.M s.ν_bound s.W_bound s.M_ge_one s.lower s.upper s.lower_pos s.slot_support
    r.keep r.profile r.scale r.scale_pos r.nonneg
  have hsum:(∑B:actualAllocations s.pools C,
      sourceRestrictedEnergy r.keep
        (finiteColumns (liveBox s.pools B.val (alloc_ne s C B)))
        (finiteColumnCoefficient (liveBox s.pools B.val (alloc_ne s C B))
          (maskedLiveProfile B.val C R L s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1))
        (heightCoeff s.η s.t) r.profile r.scale/remainingRaw B.val (s.X₁*s.X₂) s.P)=
      ∑B:actualAllocations s.pools C,energy (commonData s C R B) r L:=
    Finset.sum_congr rfl (fun B _=>live_source_eq s r C R L B)
  rw [hsum] at hh
  exact hh


-- @@ L80-80 verbatim
end SevenEighths.CenteredMomentCommonRadialSource


-- @@ L82-82 verbatim
end


-- @@ L84-84 verbatim
end OAI
