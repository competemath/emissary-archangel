import OAI.NumberTheory.DirichletL.Moments.SecondSourceFrequency


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators Classical SchwartzMap


-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentSecondRetainedRows

-- @@ L9-9 verbatim
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge

-- @@ L10-10 verbatim
open CenteredMomentSecondSectorFrequency CenteredMomentSecondSectorRetained CenteredMomentSectorLocalization

-- @@ L11-11 verbatim
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit

-- @@ L12-12 verbatim
open CenteredMomentCanonicalFirst

-- @@ L13-13 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L15-15 verbatim
def retainedRows (R : ℝ) (A : O) : Finset O := rowNormDisk (Nat.ceil (4*R/normValue A))


-- @@ L17-35 verbatim
theorem retained_mem_rows (R : ℝ) (A h : O) (hA : A≠0)
    (hh : retainedWeight R (normValue (A*h))≠0) : h∈retainedRows R A := by
  have he := retainedWeight_enclosure R _ hh
  have hAh : A*h≠0 := by
    intro hz
    have hn : normValue (A*h)=0 := by simp [hz,normValue]
    linarith [he.1]
  have hh0 : h≠0 := right_ne_zero_of_mul hAh
  apply mem_rowNormDisk.mpr
  constructor
  · have hn := normValue_pos h hh0
    unfold normValue at hn
    exact_mod_cast hn
  · have hbound : normValue h≤4*R/normValue A := by
      apply (le_div_iff₀ (normValue_pos A hA)).mpr
      simpa only [normValue_mul,mul_comm] using he.2
    have hb := hbound.trans (Nat.le_ceil (4*R/normValue A))
    unfold normValue at hb
    exact_mod_cast hb


-- @@ L37-42 verbatim
theorem physical_sector_zero_of_weight (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (j : O)
    (hj : retainedWeight R (normValue j)=0) :
    sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) j=0 := by
  simp only [sectorFrequency,physicalKernel,hj,Complex.ofReal_zero,mul_zero,zero_mul,Finset.sum_const_zero]


-- @@ L44-58 verbatim
theorem physical_partition_finite_rows (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (A : O) (hA : A≠0) (part : O→Prop) :
    (∑' h : O,if part h then
      sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) (A*h) else 0)=
      ∑ h∈retainedRows R A,if part h then
        sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) (A*h) else 0 := by
  apply tsum_eq_sum
  intro h hh
  by_cases hp : part h
  · rw [ite_eq_left hp]
    apply physical_sector_zero_of_weight η t S β C D hC hD W K R (A*h)
    by_contra hn
    exact hh (retained_mem_rows R A h hA hn)
  · rw [ite_eq_right hp]


-- @@ L60-71 verbatim
theorem actual_GV_finite_rows (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) :
    let A := commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
    (∑' h : O,if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
      sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) (A*h) else 0)=
      ∑ h∈retainedRows R A,if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
        sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) (A*h) else 0 := by
  dsimp only
  exact physical_partition_finite_rows η t S β C D hC hD W K R _
    (mul_ne_zero (commonFrequencyGenerator_ne_zero C D hC)
      (nonunitFrequencyGenerator_ne_zero C D hC U)) _


-- @@ L73-73 verbatim
end SevenEighths.CenteredMomentSecondRetainedRows


-- @@ L75-75 verbatim
end


-- @@ L77-77 verbatim
end OAI
