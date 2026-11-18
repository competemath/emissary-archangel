import OAI.NumberTheory.DirichletL.Moments.SecondCanonicalLedger
import OAI.NumberTheory.DirichletL.Moments.SectorLocalization


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped BigOperators Classical


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentSecondCanonicalScalar

-- @@ L10-10 verbatim
open CanonicalQuadraticSieve CompletedGauss

-- @@ L11-11 verbatim
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit

-- @@ L12-12 verbatim
open CenteredMomentCanonicalFirst CenteredMomentPartition CenteredMomentPartitionNorm

-- @@ L13-13 verbatim
open CenteredMomentSectorLocalization CenteredMomentSupport

-- @@ L14-14 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L16-17 verbatim
def normalizer (C D : Ideal O) (U : Finset (CommonIndex C D)) : ℝ :=
  partitionNormalizer (commonPrime C D) (leftExponent C D) (rightExponent C D) U


-- @@ L19-24 verbatim
theorem normalizer_pos (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    0<normalizer C D U := by
  rw [normalizer,partitionNormalizer_eq_norm_ratio _ (commonPrime_supported C D hC) _ _
    (leftExponent_pos C D) (rightExponent_pos C D)]
  exact div_pos (commonIdeal_norm_pos _ (commonPrime_supported C D hC) _ _)
    (unitIdeal_norm_pos _ (commonPrime_supported C D hC) _)


-- @@ L26-28 verbatim
def retainedScalar (C D : Ideal O) (U : Finset (CommonIndex C D)) (R : ℝ) (h : O) : ℂ :=
  canonicalPartitionScalar C D U (nonunitFrequencyGenerator C D U*h)*
    (retainedWeight R (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h)):ℂ)


-- @@ L30-38 verbatim
theorem actual_retained_scalar_norm (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (R : ℝ) (h : O) :
    ‖retainedScalar C D U R h*idealCorrelation C D hC hD
      ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h)‖≤1 := by
  have hs := actual_ideal_partition_scalar C D hC hD hCD U (nonunitFrequencyGenerator C D U*h)
  have hw := retainedWeight_bounds R (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h))
  rw [retainedScalar,mul_right_comm,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hw.1]
  exact (mul_le_of_le_one_left hw.1 (by simpa only [mul_assoc] using hs)).trans hw.2


-- @@ L40-48 verbatim
theorem original_partition_scalar (C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) (R : ℝ) (h : O) (F : ℂ) :
    (if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
      (retainedWeight R (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h)):ℂ)*F else 0)=
      (normalizer C D U:ℂ)*(retainedScalar C D U R h*F) := by
  have hn : (normalizer C D U:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (normalizer_pos C D hC U).ne'
  unfold retainedScalar canonicalPartitionScalar
  change _=(normalizer C D U:ℂ)*((if _ then (normalizer C D U:ℂ)⁻¹ else 0)*_*F)
  split_ifs <;> simp_all [mul_assoc]


-- @@ L50-50 verbatim
end SevenEighths.CenteredMomentSecondCanonicalScalar


-- @@ L52-52 verbatim
end


-- @@ L54-54 verbatim
end OAI
