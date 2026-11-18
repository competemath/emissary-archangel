import OAI.NumberTheory.DirichletL.Moments.FirstRetainedSector
import OAI.NumberTheory.DirichletL.Moments.ActiveSource


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators SchwartzMap


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentFirstRetainedActive

-- @@ L10-10 verbatim
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve

-- @@ L11-11 verbatim
open CenteredMomentFirstRetainedSector CenteredMomentSourceRow CenteredMomentHeckeExpansion

-- @@ L12-12 verbatim
open CenteredMomentFirstSectors CenteredMomentSupportedCorrelation

-- @@ L13-13 verbatim
open CenteredMomentActiveSource (activeSource supportedColumns_active)

-- @@ L14-14 verbatim
local notation "O"=>ActualEisensteinCubic.O

 
-- @@ L16-29 verbatim
theorem retained_energy_sum (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))
    (β:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    CenteredMomentFirstSectorLocalization.retainedEnergy η m A t S β W K X Z ξ=
      ∑I∈supportedColumns S,∑J∈supportedColumns S,
        ((β I*rowWeight η m A 1 t I)*star (β J*rowWeight η m A 1 t J))*
          CenteredMomentFirstRetainedSector.retainedKernel I J W K X Z ξ:=by
  unfold CenteredMomentFirstSectorLocalization.retainedEnergy
  conv_rhs=>rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro I hI
  conv_rhs=>rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [retainedKernel_eq I J (Finset.mem_filter.mp I.property).2 (Finset.mem_filter.mp J.property).2]

 
-- @@ L31-44 verbatim
theorem retained_energy_active (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))
    (β:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    CenteredMomentFirstSectorLocalization.retainedEnergy η m A t (activeSource S β) β W K X Z ξ=
      CenteredMomentFirstSectorLocalization.retainedEnergy η m A t S β W K X Z ξ:=by
  rw [retained_energy_sum,retained_energy_sum,supportedColumns_active]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hi:β I=0
  · simp [hi]
  · rw [ite_eq_left hi]
    apply Finset.sum_congr rfl
    intro J hJ
    by_cases hj:β J=0 <;> simp [hj]


-- @@ L46-46 verbatim
end SevenEighths.CenteredMomentFirstRetainedActive


-- @@ L48-48 verbatim
end


-- @@ L50-50 verbatim
end OAI
