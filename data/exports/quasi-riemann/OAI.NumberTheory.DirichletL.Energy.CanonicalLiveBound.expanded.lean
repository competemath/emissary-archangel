import OAI.NumberTheory.DirichletL.Energy.CanonicalChildBound


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators SchwartzMap ContDiff


-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentEnergyCanonicalLiveBound

-- @@ L9-9 verbatim
open HeckeFamily ConcreteTraceCRT

-- @@ L10-10 verbatim
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource

-- @@ L11-11 verbatim
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison

-- @@ L12-12 verbatim
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile

-- @@ L13-13 verbatim
open CenteredMomentRadialEligibleEnergy

-- @@ L14-14 verbatim
local notation "O"=>HeckeFamily.O

-- @@ L15-15 verbatim
variable {α:Type*}[Fintype α][DecidableEq α]


-- @@ L17-22 verbatim
def LiveChild (η:Character)(r:Radial)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2)))(V₁ V₂:Plain)
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(F₁ F₂:Finset (Ideal O))(J:Finset α):Prop:=
  ∃z:O,r.keep z ∧ (r.profile (‖eisEmbedding z‖^2/r.scale)).re≠0 ∧
    child (naturalCharacter η z) D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ F₁ F₂ J≠0


-- @@ L24-43 verbatim
theorem energy_zero_of_not_live (η:Character)(r:Radial)(hz:∀z,r.keep z→z≠0)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2)))(V₁ V₂:Plain)
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)(hP:∀i,0<P i)
    (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(F₁ F₂:Finset (Ideal O))(J:Finset α)
    (hF₁:∀I∈F₁,I≠0)(hF₂:∀I∈F₂,I≠0)
    (hn:¬LiveChild η r D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ F₁ F₂ J):
    allocatedEnergy η r D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ F₁ F₂ J=0:=by
  rw [←child_radial_eq_energy η r hz D a V₁ V₂ pool β P hP t X₁ X₂ hX₁ hX₂ F₁ F₂ J hF₁ hF₂]
  unfold radialEnergy
  apply (tsum_congr (g:=fun _ : O=>(0:ℝ)) ?_).trans (tsum_zero)
  intro z
  by_cases hk:r.keep z
  · rw [ite_eq_left hk]
    by_cases hφ:(r.profile (‖eisEmbedding z‖^2/r.scale)).re=0
    · rw [hφ,mul_zero]
    · have hc:child (naturalCharacter η z) D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ F₁ F₂ J=0:=by
        by_contra hh
        exact hn ⟨z,hk,hφ,hh⟩
      simp only [hc,norm_zero,zero_pow (by decide:2≠0),zero_mul]
  · rw [ite_eq_right hk]


-- @@ L45-45 verbatim
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous

-- @@ L46-46 verbatim
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock

-- @@ L47-47 verbatim
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands

-- @@ L48-48 verbatim
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles

-- @@ L49-49 verbatim
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero

-- @@ L50-50 verbatim
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional

-- @@ L51-51 verbatim
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData

-- @@ L52-52 verbatim
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum

-- @@ L53-53 verbatim
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw

-- @@ L54-54 verbatim
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

-- @@ L55-55 verbatim
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound


-- @@ L57-57 verbatim
open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization

-- @@ L58-58 verbatim
variable (M:Ideal O)[NeZero M]

-- @@ L59-59 verbatim
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

-- @@ L60-60 verbatim
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)


-- @@ L62-149 verbatim
theorem actual_live_canonical_child_bands (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b:ℝ)(haPlain:0<a)(L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀(Q:Ideal O),Q≤M →
    ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),
    0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
      (J:Finset (CenteredMomentCommonProfile.liveIndices B.val)),
    ∀(τ:Character)(dyad:Fin 4→ℤ),∀_hn:1≤CenteredMomentSectorLocalization.dyadicScale (dyad 1),
    Real.logb Z (CenteredMomentSectorLocalization.dyadicScale (dyad 1))+
      Real.logb Z (τ.modulus.absNorm:ℝ)≤Mcap →
    ∀p:Profiles a b,∀X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,X₁≤Z^L → X₂≤Z^L →
    ∀F₁ F₂:Finset (Ideal O),(∀I∈F₁,I≠0) → (∀I∈F₂,I≠0) →
    let d:=commonData (withHeight src τ v) C R B
    ∀Mnom cost:ℝ,
    (LiveChild τ (canonicalRadial τ (internalQ Q η₀) dyad) D alloc
      (sourcePlain a b haPlain (p.profile 0) (p.support 0))
      (sourcePlain a b haPlain (p.profile 1) (p.support 1))
      d.slots d.coefficient d.P v X₁ X₂ hX₁ hX₂ F₁ F₂ J →
      Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ)-Mnom+
        CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
          (length Z (scale D alloc X₁ 0 F₁)) (length Z (scale D alloc X₂ 1 F₂))
          (Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ)) κ/6≤cost) →
    allocatedEnergy τ (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad) D alloc
      (sourcePlain a b haPlain (p.profile 0) (p.support 0))
      (sourcePlain a b haPlain (p.profile 1) (p.support 1))
      d.slots d.coefficient d.P v X₁ X₂ hX₁ hX₂ F₁ F₂ J ≤
      Cc*(C₀+C₁)*diagonalControl (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad).profile*
        (p.control T)^2*
        (1+(|v|+height))^(dc+degree+4*n)*
        Z^(Mnom+εchild+εremove+cost+κ*mesh) := by
  obtain ⟨n,T,dc,Cc,hCc,hbound⟩:=actual_canonical_child_bands (α:=α) M H hH W aslot bslot
    Mcap Lslot εremove lo hi κ a b haPlain L hL degree S ha hWs hW hMcap hLs hε hbeta hκ
  refine ⟨n,T,dc,Cc,hCc,?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J τ dyad hn hwidth p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
  dsimp only
  intro Mnom cost hcost
  have hz:1<Z:=hZ₀.trans_le hZ
  have hz0:0<Z:=zero_lt_one.trans hz
  let d:=commonData (withHeight src τ v) C R B
  let rad:=canonicalRadial τ (internalQ Q η₀) dyad
  let V₁:=sourcePlain a b haPlain (p.profile 0) (p.support 0)
  let V₂:=sourcePlain a b haPlain (p.profile 1) (p.support 1)
  by_cases hne:LiveChild τ rad D alloc V₁ V₂ d.slots d.coefficient d.P
      v X₁ X₂ hX₁ hX₂ F₁ F₂ J
  · have he:=hbound Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
      w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
      src hmatch C R B D alloc J τ dyad hn hwidth p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
    dsimp only at he
    have hnorm:0<(τ.modulus.absNorm:ℝ):=by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot)
    have hpower:Z^(Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ))=
        (τ.modulus.absNorm:ℝ)*dyadicScale (dyad 1):=by
      rw [Real.rpow_add hz0,Real.rpow_logb hz0 hz.ne' (dyadicScale_pos _),
        Real.rpow_logb hz0 hz.ne' hnorm,mul_comm]
    apply he.trans
    rw [←hpower,mul_assoc,←Real.rpow_add hz0]
    apply mul_le_mul_of_nonneg_left _ (by
      have hd:0≤diagonalControl rad.profile:=by unfold diagonalControl;positivity
      have hp:=p.control_nonneg T
      positivity)
    apply Real.rpow_le_rpow_of_exponent_le hz.le
    have hh:=hcost hne
    linarith
  · have he:=energy_zero_of_not_live τ rad (fun z hz=>hz.1) D alloc V₁ V₂
      d.slots d.coefficient d.P d.P_pos v X₁ X₂ hX₁ hX₂ F₁ F₂ J hF₁ hF₂ hne
    change allocatedEnergy τ rad D alloc V₁ V₂ d.slots d.coefficient d.P
      v X₁ X₂ hX₁ hX₂ F₁ F₂ J≤_
    rw [he]
    have hd:0≤diagonalControl rad.profile:=by unfold diagonalControl;positivity
    have hp:=p.control_nonneg T
    positivity


-- @@ L151-151 verbatim
end SevenEighths.CenteredMomentEnergyCanonicalLiveBound


-- @@ L153-153 verbatim
end


-- @@ L155-155 verbatim
end OAI
