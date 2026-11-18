import OAI.NumberTheory.DirichletL.Moments.FirstRetainedBlock


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators SchwartzMap


-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentFirstRetainedAssembly

-- @@ L9-9 verbatim
open ActualEisensteinCubic ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve

-- @@ L10-10 verbatim
open CenteredMomentFirstRetainedPhysical CenteredMomentFirstRetainedSector

-- @@ L11-11 verbatim
open CenteredMomentFirstRetainedBlock CenteredMomentFirstSectorTransform CenteredMomentFirstSectors

-- @@ L12-12 verbatim
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly

-- @@ L13-13 verbatim
open CenteredMomentSourceRow CenteredMomentCanonicalFirst CenteredMomentFirstReduced CenteredMomentRowNorm

-- @@ L14-14 verbatim
open CenteredMomentCommonSupport CenteredMomentSupportedCorrelation CenteredMomentHeckeExpansion

-- @@ L15-15 verbatim
open CenteredMomentSectorLocalization CenteredMomentFirstScale CenteredMomentLogDyadic

-- @@ L16-16 verbatim
local notation "O"=>ActualEisensteinCubic.O


-- @@ L18-22 verbatim
def infiniteSector (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):ℂ:=
  ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
    retainedInfiniteBlock η m A t S c C D hC hD E W K
      (frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ)


-- @@ L24-43 verbatim
theorem retained_energy_blocks (η:Character)(m A:O)(t:ℝ)
    (S:Finset (Ideal O))(c:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    CenteredMomentFirstSectorLocalization.retainedEnergy η m A t S c W K X Z ξ=
      ∑p:commonLabels (supportedColumns S) (supportedColumns S),
        rowWeight η m A 1 t p.val.1*star (rowWeight η m A 1 t p.val.2)*
          infiniteSector η m A t S c p.val.1 p.val.2
            (commonLabels_supported S p).1 (commonLabels_supported S p).2 W K X Z ξ:=by
  rw [retainedEnergy_common_sectors]
  rw [←Finset.sum_coe_sort _ (fun p:Ideal O×Ideal O=>
    ∑q∈pairSector p.1 p.2 (supportedColumns S) (supportedColumns S),
      ((c q.1*rowWeight η m A 1 t q.1)*star (c q.2*rowWeight η m A 1 t q.2))*
        retainedKernel q.1 q.2 W K X Z ξ)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [original_sector_fixed η m A t S c p.val.1 p.val.2
    (commonLabels_supported S p).1 (commonLabels_supported S p).2
    (commonLabels_data _ _ p.val.1 p.val.2 p.property).2.2 W K X Z ξ]
  exact congrArg (fun z=>rowWeight η m A 1 t p.val.1*star (rowWeight η m A 1 t p.val.2)*z)
    (fixed_sector_blocks η m A t S c p.val.1 p.val.2
      (commonLabels_supported S p).1 (commonLabels_supported S p).2 W K X Z ξ)


-- @@ L45-57 verbatim
def physicalSector {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:CenteredMomentCommonRadialData.Input ι)(Rbad seed:Ideal O)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):ℂ:=
  ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
    let R:=frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ
    ∑n:Blocks (effectiveScale C D E K) R
        (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(C.absNorm:ℝ))
        (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(D.absNorm:ℝ)),
      block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s Rbad seed)
        C D hC hD E (CenteredMomentSecondRetainedRows.retainedRows R 1) W
        (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3))


-- @@ L59-78 verbatim
theorem original_retained_physical
    {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:CenteredMomentCommonRadialData.Input ι)(Rbad seed:Ideal O)
    (hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ)(hK:0<K):
    CenteredMomentFirstSectorLocalization.retainedEnergy s.η m A t S
      (CenteredMomentOriginalCommonHarmonic.coefficient s Rbad seed) W K X Z ξ=
      ∑p:commonLabels (supportedColumns S) (supportedColumns S),
        rowWeight s.η m A 1 t p.val.1*star (rowWeight s.η m A 1 t p.val.2)*
          physicalSector s Rbad seed m A t S p.val.1 p.val.2
            (commonLabels_supported S p).1 (commonLabels_supported S p).2 W K X Z ξ:=by
  rw [retained_energy_blocks]
  apply Finset.sum_congr rfl
  intro p hp
  apply congrArg
  unfold infiniteSector physicalSector
  apply Finset.sum_congr rfl
  intro E hE
  exact original_retained_dyadic s Rbad seed hz₁ hz₂ m A t S p.val.1 p.val.2
    (commonLabels_supported S p).1 (commonLabels_supported S p).2 E W K _ hK


-- @@ L80-80 verbatim
end SevenEighths.CenteredMomentFirstRetainedAssembly


-- @@ L82-82 verbatim
end


-- @@ L84-84 verbatim
end OAI
