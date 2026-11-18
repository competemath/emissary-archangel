import OAI.NumberTheory.DirichletL.Moments.FirstRetainedNorm
import OAI.NumberTheory.DirichletL.Moments.SourceInputFirstRemainder


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators SchwartzMap

-- @@ L8-8 verbatim
open Filter


-- @@ L10-10 verbatim
namespace SevenEighths.CenteredMomentFirstSourceReduction

-- @@ L11-11 verbatim
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData

-- @@ L12-12 verbatim
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow

-- @@ L13-13 verbatim
open CenteredMomentExceptionalAmplitudePair CenteredMomentSourceInputTailUniform

-- @@ L14-14 verbatim
open CenteredMomentSourceInputFirstRemainder CenteredMomentFirstRetainedNorm

-- @@ L15-15 verbatim
open CenteredMomentFirstSectorTransform CenteredMomentFirstSectors CenteredMomentFirstEnergy

-- @@ L16-16 verbatim
open CenteredMomentActiveSource (activeSource)

-- @@ L17-17 verbatim
local notation "O"=>HeckeFamily.O

-- @@ L18-18 verbatim
variable {ι:Type*}[Fintype ι][DecidableEq ι]

-- @@ L19-19 verbatim
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _


-- @@ L21-27 verbatim
def physicalMass (s:Input ι)(R seed:Ideal O)(m A:O)(Φ:𝓢(ℝ,ℂ))(K Z ξ:ℝ):ℝ:=
  let β:=coefficient s R seed
  let T:=activeSource (finiteColumns (Fintype.piFinset s.pools)) β
  ∑p:commonLabels (supportedColumns T) (supportedColumns T),
    sectorMass s R seed m A s.t T p.val.1 p.val.2
      (commonLabels_supported T p).1 (commonLabels_supported T p).2 Φ K
      (volume s.toData) Z ξ

 
-- @@ L29-65 verbatim
theorem original_first_physical_reduction (hi:ι→ℝ)(wlo whi B ε ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hε:0<ε)(hξ:0<ξ):
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0<Cdiag ∧ 0<Ctail ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),
      s.W₁=W₁→s.W₂=W₂→Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→(∀i,s.hi i≤hi i)→
      ∀(m A:O),ConcretePrimeRowBridge.goodLambda∣m→(2:O)∣m→
      ∀(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K:ℝ),0<K→
      volume s.toData≤Z^B→K⁻¹≤Z^B→
      ‖finiteHeckeEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
          (coefficient s R seed) Φ K‖/volume s.toData≤
      physicalMass s R seed m A Φ K Z ξ/volume s.toData+
      Cdiag*(plainControl s W₁ W₂)^2*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^ε+
      Ctail*(plainControl s W₁ W₂)^2*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving):=by
  obtain ⟨Sdiag,Stail,Cdiag,Ctail,hCdiag,hCtail,hrem⟩:=
    original_first_remainder hi wlo whi B ε ξ saving hhi hwlo hwhi hB hε hξ
  refine ⟨Sdiag,Stail,Cdiag,Ctail,hCdiag,hCtail,?_⟩
  filter_upwards [hrem] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A hml hm2 R seed Φ K hK hVcap hKi
  have hz (W:𝓢(ℝ,ℂ))(hs:Function.support (W:ℝ→ℂ)⊆Set.Icc wlo whi):W 0=0:=by
    by_contra hn
    exact (not_le_of_gt hwlo) (hs hn).1
  have hr:=original_retained_norm s R seed (he₁.symm ▸ hz W₁ hs₁) (he₂.symm ▸ hz W₂ hs₂)
    m A s.t (finiteColumns (Fintype.piFinset s.pools)) Φ K (volume s.toData) Z ξ hK
  change ‖CenteredMomentFirstSectorLocalization.retainedEnergy s.η m A s.t
    (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed) Φ K
      (volume s.toData) Z ξ‖≤physicalMass s R seed m A Φ K Z ξ at hr
  have he:=hZ.2 s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A hml hm2 R seed Φ K hK hVcap hKi
  have htri:=norm_le_norm_sub_add
    (finiteHeckeEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed) Φ K)
    (CenteredMomentFirstSectorLocalization.retainedEnergy s.η m A s.t
      (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed) Φ K (volume s.toData) Z ξ)
  have hdiv:=div_le_div_of_nonneg_right htri (volume_pos s).le
  rw [add_div] at hdiv
  have hrdiv:=div_le_div_of_nonneg_right hr (volume_pos s).le
  linarith


-- @@ L67-67 verbatim
end SevenEighths.CenteredMomentFirstSourceReduction


-- @@ L69-69 verbatim
end


-- @@ L71-71 verbatim
end OAI
