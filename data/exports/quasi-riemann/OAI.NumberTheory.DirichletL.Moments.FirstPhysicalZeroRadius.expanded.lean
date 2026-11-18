import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalOriginalMask


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators SchwartzMap


-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentFirstPhysicalZeroRadius

-- @@ L9-9 verbatim
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge

-- @@ L10-10 verbatim
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic

-- @@ L11-11 verbatim
open CenteredMomentFirstPhysicalSource CenteredMomentFirstRetainedNorm

-- @@ L12-12 verbatim
open CenteredMomentFirstSourceReduction CenteredMomentCommonSupport

-- @@ L13-13 verbatim
open CenteredMomentCanonicalFirst CenteredMomentFirstSectors

-- @@ L14-14 verbatim
open CenteredMomentOriginalChildEnergy CenteredMomentGaussEnergy

-- @@ L15-15 verbatim
local notation "O" => HeckeFamily.O

-- @@ L16-16 verbatim
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- @@ L17-17 verbatim
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _


-- @@ L19-27 verbatim
omit [DecidableEq ι] in
lemma coefficient_zero (s : Input ι) (R seed : Ideal O)
    (h₁ : s.W₁ 0=0) (h₂ : s.W₂ 0=0) (hH : sourceRadius s≤0) (I : Ideal O) :
    CenteredMomentOriginalCommonHarmonic.coefficient s R seed I=0 := by
  by_contra h
  obtain ⟨hI,hN⟩ := original_column_norm s R seed I h₁ h₂ h
  have hn : 1≤(I.absNorm:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  linarith


-- @@ L29-37 verbatim
omit [DecidableEq ι] in
lemma block_zero (s : Input ι) (R seed : Ideal O)
    (h₁ : s.W₁ 0=0) (h₂ : s.W₂ 0=0) (hH : sourceRadius s≤0)
    (m A : O) (t : ℝ) (S : Finset (Ideal O)) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ) :
    block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
      C D hC hD E rows W V K K₀ H₀ A₀ B₀=0 := by
  simp [block,CenteredMomentFirstPhysicalSource.coefficient,coefficient_zero s R seed h₁ h₂ hH]


-- @@ L39-46 verbatim
omit [DecidableEq ι] in
lemma sectorMass_zero (s : Input ι) (R seed : Ideal O)
    (h₁ : s.W₁ 0=0) (h₂ : s.W₂ 0=0) (hH : sourceRadius s≤0)
    (m A : O) (t : ℝ) (S : Finset (Ideal O)) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    sectorMass s R seed m A t S C D hC hD W K X Z ξ=0 := by
  unfold sectorMass
  simp only [block_zero s R seed h₁ h₂ hH,norm_zero,Finset.sum_const_zero]


-- @@ L48-54 verbatim
omit [DecidableEq ι] in
theorem physicalMass_zero (s : Input ι) (R seed : Ideal O)
    (h₁ : s.W₁ 0=0) (h₂ : s.W₂ 0=0) (hH : sourceRadius s≤0)
    (m A : O) (W : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ) :
    physicalMass s R seed m A W K Z ξ=0 := by
  unfold physicalMass
  simp only [sectorMass_zero s R seed h₁ h₂ hH,Finset.sum_const_zero]


-- @@ L56-61 verbatim
omit [DecidableEq ι] in
theorem sourceGaussEnergy_zero (s : Input ι) (R seed : Ideal O)
    (h₁ : s.W₁ 0=0) (h₂ : s.W₂ 0=0) (hH : sourceRadius s≤0)
    (S : Finset (Ideal O)) (f : Ideal O→ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceGaussEnergy S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed) f W K=0 := by
  simp [sourceGaussEnergy,gaussEnergy,gaussPolynomial,coefficient_zero s R seed h₁ h₂ hH]


-- @@ L63-63 verbatim
end SevenEighths.CenteredMomentFirstPhysicalZeroRadius


-- @@ L65-65 verbatim
end


-- @@ L67-67 verbatim
end OAI
