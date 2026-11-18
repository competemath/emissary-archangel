import OAI.NumberTheory.DirichletL.Moments.FirstScale
import OAI.NumberTheory.DirichletL.Moments.FirstDiscardedEnergy


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators

-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentSourceInputFirstTailUniform

-- @@ L9-9 verbatim
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstScale

-- @@ L10-10 verbatim
open ActualEisensteinCubic

-- @@ L11-11 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L13-20 verbatim
lemma common_subset_product_dvd_right (I J : Ideal O) (E : Finset (CommonIndex I J)) :
    (∏P∈E,P.val)∣commonPart J I := by
  apply (Finset.prod_dvd_prod_of_subset E Finset.univ
    (fun P : CommonIndex I J=>P.val) (Finset.subset_univ _)).trans
  rw [commonPart_right_product]
  apply Finset.prod_dvd_prod_of_dvd
  intro P hP
  simpa only [pow_one] using pow_dvd_pow P.val (rightExponent_pos I J P)


-- @@ L22-39 verbatim
theorem first_nominal_scale_le (I J : Ideal O) (E : Finset (CommonIndex I J))
    (K X : ℝ) (hK : 0<K) :
    firstNominalScale I J (∏P∈E,P.val) K X≤X^2/K := by
  have hC := norm_pos (commonPart I J) (commonPart_ne_zero I J)
  have hD := norm_pos (commonPart J I) (commonPart_ne_zero J I)
  have hE : (Ideal.absNorm (∏P∈E,P.val):ℝ)≤Ideal.absNorm (commonPart J I) := by
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (commonPart_ne_zero J I)))
      (map_dvd Ideal.absNorm (common_subset_product_dvd_right I J E))
  have hA : (Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)≤Ideal.absNorm (commonPart I J) := by
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (commonPart_ne_zero I J)))
      (map_dvd Ideal.absNorm (activeConductor_span_dvd I J))
  unfold firstNominalScale
  apply (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul hE hA (by positivity) hD.le) (sq_nonneg X))
    (mul_nonneg (mul_nonneg hK.le hC.le) hD.le)).trans_eq
  field_simp


-- @@ L41-41 verbatim
end SevenEighths.CenteredMomentSourceInputFirstTailUniform


-- @@ L43-43 verbatim
end


-- @@ L45-45 verbatim
end OAI
