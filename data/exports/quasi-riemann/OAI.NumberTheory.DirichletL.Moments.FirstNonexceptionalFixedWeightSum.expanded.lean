import OAI.NumberTheory.DirichletL.Moments.FirstNonexceptionalWeightSum
import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceFixedFamily


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators SchwartzMap

-- @@ L8-8 verbatim
open Filter


-- @@ L10-10 verbatim
namespace SevenEighths.CenteredMomentFirstNonexceptionalFixedWeightSum

-- @@ L11-11 verbatim
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve RayFourExpansion

-- @@ L12-12 verbatim
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalSource

-- @@ L13-13 verbatim
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic

-- @@ L14-14 verbatim
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentCanonicalFirst

-- @@ L15-15 verbatim
open CenteredMomentFirstSectors CenteredMomentActiveSource CenteredMomentSourceRow

-- @@ L16-16 verbatim
open CenteredMomentSourceMass CenteredMomentSupportedCorrelation CenteredMomentSecondRetainedAggregate

-- @@ L17-17 verbatim
local notation "O"=>ActualEisensteinCubic.O

-- @@ L18-18 verbatim
variable {ι:Type*}[Fintype ι][DecidableEq ι]

-- @@ L19-19 verbatim
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _


-- @@ L21-25 verbatim
abbrev Families (s:Input ι)(R seed:Ideal O)(ξ₁ ξ₂:RayCharacter):=
  (p:Labels s R seed)→(E:Finset (CommonIndex p.val.1 p.val.2))→
    FixedPair s.η p.val.1 p.val.2
      (commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
        (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property).1 E ξ₁ ξ₂


-- @@ L27-48 verbatim
theorem original_fixed_weight_sum (B L Cr ε:ℝ)(hB:0≤B)(hL:0≤L)(hCr:0<Cr)(hε:0<ε):
    ∃C₀:ℝ,0<C₀ ∧ ∀ᶠZ:ℝ in atTop,
    ∀(ι:Type*)[Fintype ι][DecidableEq ι](s:Input ι)(R seed:Ideal O),
      Squarefree seed→seed≠0→s.W₁ 0=0→s.W₂ 0=0→0<sourceRadius s→sourceRadius s≤Z^B→
    ∀(m A:O)(t:ℝ)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K a₁ a₂ M:ℝ),
      0<K→0<a₁→0<a₂→
      (∀x,s.W₁ x≠0→a₁≤x)→(∀x,s.W₂ x≠0→a₂≤x)→
      (∀i y,V i y≠0→|y|≤M)→
    ∀(radius:(p:Labels s R seed)→Finset (CommonIndex p.val.1 p.val.2)→ℝ),
      (∀p E,radius p E≤Cr*Z^L)→∀ξ₁ ξ₂:RayCharacter,∀F:Families s R seed ξ₁ ξ₂,
      sumWeight s R seed m A t W V K radius (fun p E=>(F p E).left) (fun p E=>(F p E).right)≤
        ((Real.exp M/((∏i,s.lo i)*a₁*a₂))*fixedPresentationCost*K*(s.η.modulus.absNorm:ℝ))*
          (C₀*Z^ε/(seed.absNorm:ℝ)):=by
  obtain ⟨C₀,hC₀,hbound⟩:=original_weight_sum B L Cr ε hB hL hCr hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hbound] with Z hbound
  intro ι _ _ s R seed hs hs0 hz₁ hz₂ hH hHcap m A t W V K a₁ a₂ M
    hK ha₁ ha₂ hs₁ hs₂ hwin radius hr ξ₁ ξ₂ F
  exact hbound ι s R seed hs hs0 hz₁ hz₂ hH hHcap m A t W V K a₁ a₂ M
    fixedPresentationCost hK ha₁ ha₂ fixedPresentationCost_pos.le hs₁ hs₂ hwin radius
    (fun p E=>(F p E).left) (fun p E=>(F p E).right) hr
    (fun p E=>(F p E).conductor_caps.1) (fun p E=>(F p E).conductor_caps.2)


-- @@ L50-50 verbatim
end SevenEighths.CenteredMomentFirstNonexceptionalFixedWeightSum


-- @@ L52-52 verbatim
end


-- @@ L54-54 verbatim
end OAI
