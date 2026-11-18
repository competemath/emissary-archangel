import OAI.NumberTheory.DirichletL.Energy.FixedRadialSource
import OAI.NumberTheory.DirichletL.Energy.ZeroComparison


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators SchwartzMap


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentEnergyFixedRadialEntry

-- @@ L10-10 verbatim
open ConcretePrimeRowBridge QuadraticInitialBound CenteredMomentSourceMass CenteredMomentSourceRectangleMask

-- @@ L11-11 verbatim
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentEnergyOriginalSource

-- @@ L12-12 verbatim
open CenteredMomentEnergyFixedRadialSource CenteredMomentSourceRow

-- @@ L13-13 verbatim
open CenteredMomentSecondHeightFamily CenteredMomentAmplificationChildInput

-- @@ L14-14 verbatim
open CenteredMomentOriginalCommonHarmonic CenteredMomentRadialEligibleEnergy

-- @@ L15-15 verbatim
open CenteredMomentEnergyZeroComparison CanonicalQuadraticSieve

-- @@ L16-16 verbatim
local notation "O"=>HeckeFamily.O

-- @@ L17-17 verbatim
variable {ι:Type*}[Fintype ι][DecidableEq ι]

-- @@ L18-18 verbatim
local instance : DecidableEq (ι⊕Fin 2):=energyOriginalSourceDecidableSum


-- @@ L20-41 verbatim
theorem original_comparison (b:ℝ)(hb:0<b):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (b+1) ∧
      (∀x,0≤(Ψ x).re) ∧ ∀s:Input ι,∀R:Ideal O,∀r:Radial,
      Function.support (r.profile:ℝ→ℂ)⊆Set.Iic b→
      CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t
        s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.X₁ s.X₂ r.keep r.profile r.scale ≤
      2*QuadraticInitialBound.diagonalControl r.profile*
        ‖finiteHeckeEnergy s.η fixedBadMask 1 s.t
          (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R 1) Ψ r.scale‖/volume s+
      2*CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t
        s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.Y₁ s.Y₂ r.keep r.profile r.scale :=by
  obtain ⟨Ψ,hs,hn,hh⟩:=fixed_source b hb
  refine ⟨Ψ,hs,hn,?_⟩
  intro s R r hr
  apply (positive_energy_comparison s R r).trans
  apply add_le_add _ le_rfl
  apply div_le_div_of_nonneg_right _ (volume_pos s).le
  have h:=mul_le_mul_of_nonneg_left
    (hh r.profile hr s.η fixedBadMask 1 s.t
      (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R 1) r.scale r.scale_pos)
    (by norm_num : (0:ℝ)≤2)
  simpa only [mul_assoc] using h


-- @@ L43-61 verbatim
theorem original_zero_comparison (b:ℝ)(hb:0<b):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (b+1) ∧
      (∀x,0≤(Ψ x).re) ∧ ∀s:Input ι,∀hz₁:s.W₁ 0=0,∀hz₂:s.W₂ 0=0,
      ∀R:Ideal O,∀r:Radial,Function.support (r.profile:ℝ→ℂ)⊆Set.Iic b→
      CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t
        s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.X₁ s.X₂ r.keep r.profile r.scale ≤
      2*QuadraticInitialBound.diagonalControl r.profile*
        ‖finiteHeckeEnergy s.η fixedBadMask 1 s.t
          (finiteColumns (Fintype.piFinset (zeroInput s hz₁ hz₂).pools))
          (coefficient (zeroInput s hz₁ hz₂) R 1) Ψ r.scale‖/volume s :=by
  obtain ⟨Ψ,hs,hn,hh⟩:=original_comparison (ι:=ι) b hb
  refine ⟨Ψ,hs,hn,?_⟩
  intro s hz₁ hz₂ R r hr
  have h:=hh (zeroInput s hz₁ hz₂) R r hr
  change _≤_+2*CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t
    s.W₁ s.W₂ s.slots s.toData.coefficient s.P
    (zeroInput s hz₁ hz₂).Y₁ (zeroInput s hz₁ hz₂).Y₂ r.keep r.profile r.scale at h
  rw [comparison_energy_zero s hz₁ hz₂ R r,mul_zero,add_zero] at h
  exact h

-- @@ L62-62 verbatim
end SevenEighths.CenteredMomentEnergyFixedRadialEntry


-- @@ L64-64 verbatim
end


-- @@ L66-66 verbatim
end OAI
