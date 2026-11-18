import OAI.NumberTheory.DirichletL.Moments.FirstNonexceptionalFixedWeightSum
import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalDyadicCountSource


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators SchwartzMap

-- @@ L8-8 verbatim
open Filter


-- @@ L10-10 verbatim
namespace SevenEighths.CenteredMomentFirstNonexceptionalLocalWeightSum

-- @@ L11-11 verbatim
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve RayFourExpansion

-- @@ L12-12 verbatim
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstNonexceptionalFixedWeightSum

-- @@ L13-13 verbatim
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicCount

-- @@ L14-14 verbatim
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic

-- @@ L15-15 verbatim
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentCanonicalFirst

-- @@ L16-16 verbatim
open CenteredMomentFirstSectors CenteredMomentActiveSource CenteredMomentSourceRow

-- @@ L17-17 verbatim
open CenteredMomentSourceMass CenteredMomentSupportedCorrelation CenteredMomentSecondRetainedAggregate

-- @@ L18-18 verbatim
open CenteredMomentSectorLocalization CenteredMomentFirstScale CenteredMomentExceptionalAmplitudePair

-- @@ L19-19 verbatim
local notation "O"=>ActualEisensteinCubic.O

-- @@ L20-20 verbatim
variable {ι:Type*}[Fintype ι][DecidableEq ι]

-- @@ L21-21 verbatim
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _


-- @@ L23-25 verbatim
def localRadius (s:Input ι)(R seed:Ideal O)(K Z ξ:ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2)):ℝ:=
  frequencyRadius (firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (volume s.toData)) Z ξ


-- @@ L27-55 verbatim
theorem original_local_fixed_weight_sum (hi:ι→ℝ)(b₁ b₂ B ξ ε:ℝ)
    (hB:0≤B)(hξ:0≤ξ)(hε:0<ε):
    ∃C₀:ℝ,0<C₀ ∧ ∀ᶠZ:ℝ in atTop,
    ∀(s:Input ι)(R seed:Ideal O),Squarefree seed→seed≠0→s.W₁ 0=0→s.W₂ 0=0→
      (∀i,|s.hi i|≤hi i)→|s.b₁|≤b₁→|s.b₂|≤b₂→0<sourceRadius s→
    ∀(m A:O)(t:ℝ)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K a₁ a₂ M:ℝ),
      0<K→0<a₁→0<a₂→volume s.toData≤Z^B→K⁻¹≤Z^B→
      (∀x,s.W₁ x≠0→a₁≤x)→(∀x,s.W₂ x≠0→a₂≤x)→
      (∀i y,V i y≠0→|y|≤M)→
    ∀ξ₁ ξ₂:RayCharacter,∀F:Families s R seed ξ₁ ξ₂,
      sumWeight s R seed m A t W V K (localRadius s R seed K Z ξ)
        (fun p E=>(F p E).left) (fun p E=>(F p E).right)≤
      ((Real.exp M/((∏i,s.lo i)*a₁*a₂))*fixedPresentationCost*K*(s.η.modulus.absNorm:ℝ))*
        (C₀*Z^ε/(seed.absNorm:ℝ)):=by
  obtain ⟨C₀,hC₀,hbound⟩:=original_fixed_weight_sum (B+1) (3*B+ξ/2) 1 ε
    (by positivity) (by positivity) (by norm_num) hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (1:ℝ),
    eventually_ge_atTop ((∏i,hi i)*b₁*b₂)] with Z hbound hZ hfixed
  intro s R seed hs hs0 hz₁ hz₂ hhi hb₁ hb₂ hH m A t W V K a₁ a₂ M
    hK ha₁ ha₂ hV hKi hs₁ hs₂ hwin ξ₁ ξ₂ F
  apply hbound ι s R seed hs hs0 hz₁ hz₂ hH
    (input_radius_cap hi b₁ b₂ B Z s hhi hb₁ hb₂ hZ hfixed hV)
    m A t W V K a₁ a₂ M hK ha₁ ha₂ hs₁ hs₂ hwin
    (localRadius s R seed K Z ξ) _ ξ₁ ξ₂ F
  intro p E
  simpa only [localRadius,one_mul] using
    local_frequency_radius_cap p.val.1 p.val.2 E K (volume s.toData) Z B ξ
      hK (volume_pos s.toData).le hZ hV hKi


-- @@ L57-57 verbatim
end SevenEighths.CenteredMomentFirstNonexceptionalLocalWeightSum


-- @@ L59-59 verbatim
end


-- @@ L61-61 verbatim
end OAI
