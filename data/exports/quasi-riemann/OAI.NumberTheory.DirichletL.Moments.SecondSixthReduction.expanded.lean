import OAI.NumberTheory.DirichletL.Moments.SecondMovingSupport
import OAI.NumberTheory.DirichletL.Moments.FixedRowMask


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped BigOperators Classical


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentSecondSixthReduction

-- @@ L10-10 verbatim
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss

-- @@ L11-11 verbatim
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit

-- @@ L12-12 verbatim
open CenteredMomentCanonicalFirst CenteredMomentSecondMovingSupport CenteredMomentFixedRowMask

-- @@ L13-13 verbatim
open CenteredExceptionalProfile CenteredMomentSupportedCorrelation

-- @@ L14-14 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L16-17 verbatim
def reducedNumerator (C D : Ideal O) (U : Finset (CommonIndex C D)) : O :=
  ∏ P : CommonIndex C D,commonPrime C D P^(fixedExponent C D U P%6)


-- @@ L19-20 verbatim
def sixthFactor (C D : Ideal O) (U : Finset (CommonIndex C D)) : O :=
  ∏ P : CommonIndex C D,commonPrime C D P^(fixedExponent C D U P/6)


-- @@ L22-32 verbatim
theorem fixed_numerator_product (C D : Ideal O) (U : Finset (CommonIndex C D)) :
    commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U=
      ∏ P : CommonIndex C D,commonPrime C D P^fixedExponent C D U P := by
  have hv : nonunitFrequencyGenerator C D U=
      ∏ P : CommonIndex C D,if P∈nonunitPartitionSet C D U then commonPrime C D P else 1 := by
    simp only [nonunitFrequencyGenerator,Finset.prod_ite_mem,Finset.univ_inter]
  rw [commonFrequencyGenerator,hv,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P hP
  simp only [fixedExponent,pow_add]
  split_ifs <;> simp


-- @@ L34-42 verbatim
theorem fixed_sixth_factorization (C D : Ideal O) (U : Finset (CommonIndex C D)) :
    commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U=
      reducedNumerator C D U*(sixthFactor C D U)^6 := by
  rw [fixed_numerator_product,reducedNumerator,sixthFactor,←Finset.prod_pow,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P hP
  rw [←pow_mul,←pow_add]
  congr 1
  omega


-- @@ L44-47 verbatim
theorem reducedNumerator_ne_zero (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    reducedNumerator C D U≠0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _=>pow_ne_zero _
    (supported_element_ne_zero _ (commonPrime_supported C D hC P)))


-- @@ L49-52 verbatim
theorem sixthFactor_ne_zero (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    sixthFactor C D U≠0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _=>pow_ne_zero _
    (supported_element_ne_zero _ (commonPrime_supported C D hC P)))


-- @@ L54-63 verbatim
theorem fixed_sixth_row (η : Character) (m h n : O) (C D : Ideal O)
    (U : Finset (CommonIndex C D)) :
    rowTwist (elementHom η) m 1
      ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h) n=
    rowTwist (elementHom η) (m*sixthFactor C D U) 1 (reducedNumerator C D U*h) n := by
  rw [fixed_sixth_factorization]
  have he : m ^ 6 * 1 ^ 4 * ((reducedNumerator C D U * sixthFactor C D U ^ 6) * h) =
      (m * sixthFactor C D U) ^ 6 * 1 ^ 4 * (reducedNumerator C D U * h) := by ring
  exact congrArg
    (fun x => elementHom η n * idealRowHom x (Ideal.span {n})) he


-- @@ L65-78 verbatim
theorem fixed_sixth_inducing_iff (η : Character) (Q : Ideal O) (m h : O)
    (hm : m≠0) (hh : h≠0) (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    FixedInducingRow η Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) h ↔
      FixedInducingRow η Q m (reducedNumerator C D U) h := by
  have he : FixedInducingRow η Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) h ↔
      FixedInducingRow η Q (m*sixthFactor C D U) (reducedNumerator C D U) h := by
    unfold FixedInducingRow
    simp only [fixed_sixth_row]
  exact he.trans (fixedInducingRow_mul_mask_iff η Q m (sixthFactor C D U)
    (reducedNumerator C D U) h hm (sixthFactor_ne_zero C D hC U)
    (reducedNumerator_ne_zero C D hC U) hh hmLam hm2)


-- @@ L80-80 verbatim
end SevenEighths.CenteredMomentSecondSixthReduction


-- @@ L82-82 verbatim
end


-- @@ L84-84 verbatim
end OAI
