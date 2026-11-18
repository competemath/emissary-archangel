import OAI.NumberTheory.DirichletL.Moments.SecondRetainedAggregate
import OAI.NumberTheory.DirichletL.Moments.SecondRetainedRows
import OAI.NumberTheory.DirichletL.Moments.SecondActiveDyadic
import OAI.NumberTheory.DirichletL.Moments.SecondPhysicalBlock
import OAI.NumberTheory.DirichletL.Moments.ActiveSource


-- @@ L7-7 verbatim
namespace OAI


-- @@ L9-9 verbatim
noncomputable section

-- @@ L10-10 verbatim
open scoped BigOperators Classical SchwartzMap


-- @@ L12-12 verbatim
namespace SevenEighths.CenteredMomentSecondBlockAggregate

-- @@ L13-13 verbatim
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge

-- @@ L14-14 verbatim
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentCanonicalFirst

-- @@ L15-15 verbatim
open CenteredMomentSecondLocalization CenteredMomentSecondSectorFrequency

-- @@ L16-16 verbatim
open CenteredMomentSecondSectorRetained CenteredMomentSecondSectorColumns

-- @@ L17-17 verbatim
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency

-- @@ L18-18 verbatim
open CenteredMomentSecondCanonicalNonunit CenteredMomentHeckeColumnWindow

-- @@ L19-19 verbatim
open CenteredMomentSectorLocalization CenteredMomentActiveSource

-- @@ L20-20 verbatim
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondRetainedRows

-- @@ L21-21 verbatim
open CenteredMomentSecondActiveDyadic CenteredMomentSecondDyadicPartition

-- @@ L22-22 verbatim
open CenteredMomentSecondPhysicalWindow CenteredMomentSecondPhysicalBlock CenteredMomentSecondWholeKernel

-- @@ L23-23 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L25-26 verbatim
abbrev ActiveLabel (S : Finset (Ideal O)) (β : Ideal O→ℂ) :=
  ↥(commonLabels (supportedColumns (activeSource S β)) (supportedColumns (activeSource S β)))


-- @@ L28-30 verbatim
abbrev SourceBlocks (C D : Ideal O) (U : Finset (CommonIndex C D)) (K R H : ℝ) :=
  Blocks (sourceLower C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K)
    (sourceUpper C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K R H)


-- @@ L32-35 verbatim
lemma retainedRows_ne_zero (R : ℝ) (A z : O) (hz : z∈retainedRows R A) : z≠0 := by
  have hp := (mem_rowNormDisk.mp hz).1
  intro h
  simp [h] at hp


-- @@ L37-54 verbatim
theorem active_kernel_windows (η : Character)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (H : ℝ)
    (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (I : sectorPool C hC.1 (activeSource S β)) (J : sectorPool D hD.1 (activeSource S β))
    (A h : O) (hA : A≠0) (hh : h≠0) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K) :
    physicalKernel C D W K R (A*h) I J=
      ∑ n : Blocks (sourceLower C D A K) (sourceUpper C D A K R H),
        physicalKernel C D W K R (A*h) I J*
          ((dyadicWeight (n 0) (secondEffectiveScale C D A K)*dyadicWeight (n 1) (normValue h)*
            dyadicWeight (n 2) (Ideal.absNorm (I:Ideal O):ℝ)*
            dyadicWeight (n 3) (Ideal.absNorm (J:Ideal O):ℝ):ℝ):ℂ) := by
  refine (active_physical_kernel_partition η S β H hH C D hC hD I J A h hA W K R hK).trans ?_
  apply Finset.sum_congr rfl
  intro n hn
  exact (physical_kernel_dyadic C D I J hC hD
    (sectorPool_supported C hC.1 _ I) (sectorPool_supported D hD.1 _ J)
    A h hA hh W K R hK (fun i=>n i)).symm


-- @@ L56-86 verbatim
theorem sector_finite_blocks (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (H : ℝ)
    (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K) :
    let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
    (∑h∈retainedRows R A,if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
      sectorFrequency η t (activeSource S β) β C D hC hD (physicalKernel C D W K R) (A*h) else 0)=
      ∑n : SourceBlocks C D U K R H,
        physicalBlock η t (activeSource S β) β C D hC hD U R (retainedRows R A) W K
          (fun i=>(n i:ℤ)) := by
  dsimp only
  have hA : commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U≠0 :=
    mul_ne_zero (commonFrequencyGenerator_ne_zero C D hC)
      (nonunitFrequencyGenerator_ne_zero C D hC U)
  unfold physicalBlock
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  by_cases hp : canonicalPartition C D U (nonunitFrequencyGenerator C D U*h)
  · simp only [hp,ite_true]
    unfold sectorFrequency
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro I hI
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro J hJ
    conv_lhs => rw [active_kernel_windows η S β H hH C D hC hD I J _ h hA
      (retainedRows_ne_zero R _ h hh) W K R hK,Finset.mul_sum]
  · simp only [hp,ite_false,Finset.sum_const_zero]


-- @@ L88-111 verbatim
theorem original_secondRetainedEnergy_blocks (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (W : 𝓢(ℝ,ℂ))
    (K Tsec Z ξ H : ℝ) (hK : 0<K)
    (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H) :
    secondRetainedEnergy η t S β W K Tsec Z ξ=
      ∑p : ActiveLabel S β,heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)*
        ∑U : Finset (CommonIndex p.val.1 p.val.2),
          ∑n : SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
            physicalBlock η t (activeSource S β) β p.val.1 p.val.2
              (commonLabels_supported (activeSource S β) _ _ p.property).1
              (commonLabels_supported (activeSource S β) _ _ p.property).2 U
              (frequencyRadius Tsec Z ξ)
              (retainedRows (frequencyRadius Tsec Z ξ)
                (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U))
              W K (fun i=>(n i:ℤ)) := by
  rw [←secondRetainedEnergy_active η t S β W K Tsec Z ξ,
    original_retained_energy_GV η t (activeSource S β) β W K Tsec Z ξ hK]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  apply Finset.sum_congr rfl
  intro U hU
  rw [actual_GV_finite_rows]
  exact sector_finite_blocks η t S β H hH _ _ _ _ U W K _ hK


-- @@ L113-119 verbatim
lemma common_height_norm_le_one (η : Character) (t : ℝ) (C D : Ideal O)
    (hC : C≠0) (hD : D≠0) :
    ‖heightCoeff η t C*star (heightCoeff η t D)‖≤1 := by
  rw [norm_mul,norm_star]
  have hc := CenteredMomentSourceSecondZeroEnergy.heightCoeff_norm_le_one η t C hC
  have hd := CenteredMomentSourceSecondZeroEnergy.heightCoeff_norm_le_one η t D hD
  nlinarith [norm_nonneg (heightCoeff η t C),norm_nonneg (heightCoeff η t D)]


-- @@ L121-147 verbatim
theorem original_secondRetainedEnergy_norm_le (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (W : 𝓢(ℝ,ℂ))
    (K Tsec Z ξ H : ℝ) (hK : 0<K)
    (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H) :
    ‖secondRetainedEnergy η t S β W K Tsec Z ξ‖≤
      ∑p : ActiveLabel S β,∑U : Finset (CommonIndex p.val.1 p.val.2),
        ∑n : SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
          ‖physicalBlock η t (activeSource S β) β p.val.1 p.val.2
            (commonLabels_supported (activeSource S β) _ _ p.property).1
            (commonLabels_supported (activeSource S β) _ _ p.property).2 U
            (frequencyRadius Tsec Z ξ)
            (retainedRows (frequencyRadius Tsec Z ξ)
              (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U))
            W K (fun i=>(n i:ℤ))‖ := by
  rw [original_secondRetainedEnergy_blocks η t S β W K Tsec Z ξ H hK hH]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  rw [norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _)
    (common_height_norm_le_one η t _ _
      (commonLabels_supported (activeSource S β) _ _ p.property).1.1
      (commonLabels_supported (activeSource S β) _ _ p.property).2.1)).trans
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro U hU
  exact norm_sum_le _ _


-- @@ L149-149 verbatim
end SevenEighths.CenteredMomentSecondBlockAggregate


-- @@ L151-151 verbatim
end


-- @@ L153-153 verbatim
end OAI
