import OAI.NumberTheory.DirichletL.Moments.CommonLiveFrozen


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators


-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentCommonLiveHeight

-- @@ L9-9 verbatim
open HeckeFamily CenteredMomentCommonRadialSource CenteredMomentCommonRadialData

-- @@ L10-10 verbatim
open CenteredMomentCommonRadialPointwise CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy

-- @@ L11-11 verbatim
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentRestrictedSource

-- @@ L12-12 verbatim
open CenteredMomentSecondHeightFamily CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors

-- @@ L13-13 verbatim
open CenteredMomentCommonAllocationSum CanonicalQuadraticSieve

-- @@ L14-14 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L15-15 verbatim
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

-- @@ L16-16 verbatim
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _


-- @@ L18-18 verbatim
open CenteredMomentCommonHeightEnvelope

-- @@ L19-19 verbatim
open CenteredMomentSourceLiveColumn
 
-- @@ L20-46 verbatim
theorem actual_height_envelope (lo hi:ι→ℝ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C0:ℝ,0<C0 ∧ ∀(s:Input ι),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      ∀(r:Radial) (C:Ideal O) (hC:Supported C) (R seed L:Ideal O),seed∣C → Squarefree L →
      ∀E Z:ℝ,0≤E → 1<Z → (Ideal.absNorm C:ℝ)≤Z^B → (Ideal.absNorm L:ℝ)≤Z^B →
      ∀J:ℕ,∀(τ:Character) (v:ℝ),
      (∀b:actualAllocations s.pools C,frozenCoefficient b.val C R s.ν s.W s.P≠0 → ∀a∈(commonData (withHeight s τ v) C R b).toSource.active L,
        childEnergy (commonData (withHeight s τ v) C R b) r L a≤E*(1+‖v‖)^(2*J)) →
      let Q:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      sourceRestrictedEnergy r.keep (residualPool C hC.1 Q)
        (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
        (heightCoeff τ v) r.profile r.scale≤envelope s C L C0 Z δ E*(1+‖v‖)^(2*J) := by
  obtain ⟨C0,hC0,hbound⟩:=CenteredMomentCommonLiveFrozen.actual_common_source_pointwise lo hi B δ hB hδ
  refine ⟨C0,hC0,?_⟩
  intro s hlo hhi r C hC R seed L hs hL E Z hE hZ hNC hNL J τ v hc
  have hh:=hbound (withHeight s τ v) hlo hhi r C hC R seed L hs hL
    (E*(1+‖v‖)^(2*J)) Z (mul_nonneg hE (by positivity)) hZ hNC hNL hc
  have hraw:0<s.X₁*s.X₂*∏i,s.P i:=mul_pos (mul_pos s.X₁_pos s.X₂_pos)
    (Finset.prod_pos (fun i _=>s.P_pos i))
  unfold sourceEnergy at hh
  have hmul:=(div_le_iff₀ hraw).mp hh
  apply hmul.trans_eq
  change (C0*Z^δ*(profileCost s*(E*(1+‖v‖)^(2*J)))/
      ((Ideal.absNorm C:ℝ)*Ideal.absNorm L))*(s.X₁*s.X₂*∏i,s.P i)=_
  unfold envelope
  ring


-- @@ L48-48 verbatim
end SevenEighths.CenteredMomentCommonLiveHeight


-- @@ L50-50 verbatim
end


-- @@ L52-52 verbatim
end OAI
