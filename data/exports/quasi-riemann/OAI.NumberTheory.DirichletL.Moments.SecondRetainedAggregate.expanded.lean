import OAI.NumberTheory.DirichletL.Moments.SecondSourceFrequency


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators Classical SchwartzMap


-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentSecondRetainedAggregate

-- @@ L9-9 verbatim
open HeckeFamily CanonicalQuadraticSieve CompletedGauss

-- @@ L10-10 verbatim
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentCanonicalFirst

-- @@ L11-11 verbatim
open CenteredMomentSecondLocalization CenteredMomentSecondSourceRetained CenteredMomentSecondSourceFrequency

-- @@ L12-12 verbatim
open CenteredMomentSecondSectorFrequency CenteredMomentSecondSectorRetained CenteredMomentSectorLocalization

-- @@ L13-13 verbatim
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit

-- @@ L14-14 verbatim
open CenteredMomentHeckeColumnWindow CenteredMomentCompleteCommon

-- @@ L15-15 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L17-24 verbatim
theorem commonLabels_supported (S : Finset (Ideal O)) (C D : Ideal O)
    (h : (C,D)∈commonLabels (supportedColumns S) (supportedColumns S)) :
    Supported C ∧ Supported D := by
  obtain ⟨p,hp,he⟩ := Finset.mem_image.mp h
  rcases Prod.mk.inj he with ⟨rfl,rfl⟩
  have hp' := Finset.mem_product.mp hp
  exact ⟨commonPart_supported _ _ (Finset.mem_filter.mp hp'.1).2,
    commonPart_supported _ _ (Finset.mem_filter.mp hp'.2).2⟩


-- @@ L26-47 verbatim
theorem original_retained_energy_GV (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (W : 𝓢(ℝ,ℂ))
    (K Tsec Z ξ : ℝ) (hK : 0<K) :
    secondRetainedEnergy η t S β W K Tsec Z ξ=
      ∑ p : commonLabels (supportedColumns S) (supportedColumns S),
        heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)*
          ∑ U : Finset (CommonIndex p.val.1 p.val.2),∑' h : O,
            if canonicalPartition p.val.1 p.val.2 U
                (nonunitFrequencyGenerator p.val.1 p.val.2 U*h) then
              sectorFrequency η t S β p.val.1 p.val.2
                (commonLabels_supported S _ _ p.property).1
                (commonLabels_supported S _ _ p.property).2
                (physicalKernel p.val.1 p.val.2 W K (frequencyRadius Tsec Z ξ))
                ((commonFrequencyGenerator p.val.1 p.val.2*
                  nonunitFrequencyGenerator p.val.1 p.val.2 U)*h) else 0 := by
  rw [retainedEnergy_common_sectors]
  rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro p hp
  exact original_retained_sector_GV η t S β p.val.1 p.val.2
    (commonLabels_supported S _ _ p.property).1 (commonLabels_supported S _ _ p.property).2
    (commonLabels_data _ _ _ _ p.property).2.2 W K Tsec Z ξ hK


-- @@ L49-49 verbatim
end SevenEighths.CenteredMomentSecondRetainedAggregate


-- @@ L51-51 verbatim
end


-- @@ L53-53 verbatim
end OAI
