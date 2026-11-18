import OAI.NumberTheory.DirichletL.Foundation
import OAI.NumberTheory.DirichletL.Detector.Phase


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped BigOperators Classical

-- @@ L8-8 verbatim
namespace SevenEighths.ProbeCompleted

-- @@ L9-9 verbatim
open ActualEisensteinCubic CompletedGauss

-- @@ L10-10 verbatim
open RayFourExpansion QuadraticGaussRay SecondPassArithmetic


-- @@ L12-12 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L14-14 verbatim
def completedIndex (I J : Ideal O) : O := primaryGenerator I * primaryGenerator J ^ 3


-- @@ L16-17 verbatim
def completedMask (S : Finset (Ideal O)) (D I J : Ideal O) : ℂ :=
  if D ∣ I * J ^ 3 ∧ ∀ p ∈ S, ¬p ∣ I * J ^ 3 then 1 else 0


-- @@ L19-22 verbatim
def completedCorrection (I J : Ideal O) : ℂ :=
  rayMask (completedIndex I J) *
    star (fixedGQuotientValue
      (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (completedIndex I J)))


-- @@ L24-26 verbatim
theorem completedCorrection_eq_phase (I J : Ideal O) :
    completedCorrection I J = rayMask (completedIndex I J) *
      star (ProbePhase.G (completedIndex I J)) := rfl


-- @@ L28-31 verbatim
theorem completedMask_norm_le_one (S : Finset (Ideal O)) (D I J : Ideal O) :
    ‖completedMask S D I J‖ ≤ 1 := by
  unfold completedMask
  split_ifs <;> norm_num


-- @@ L33-41 verbatim
theorem completedCorrection_norm_le_two (I J : Ideal O) :
    ‖completedCorrection I J‖ ≤ 2 := by
  have hm : ‖rayMask (completedIndex I J)‖ ≤ 1 := by
    unfold rayMask
    split_ifs <;> norm_num
  unfold completedCorrection
  rw [norm_mul, norm_star]
  exact (mul_le_mul hm (fixedGQuotientValue_norm_le_two _) (norm_nonneg _) (by norm_num)).trans_eq
    (by norm_num)


-- @@ L43-45 verbatim
def markedSummand (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (W : ℝ → ℂ) (X : ℝ) (I J : Ideal O) : ℂ :=
  completedMask S D I J * summand Ψ W X I J


-- @@ L47-49 verbatim
def correctedSummand (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (W : ℝ → ℂ) (X : ℝ) (I J : Ideal O) : ℂ :=
  completedCorrection I J * markedSummand S D Ψ W X I J


-- @@ L51-53 verbatim
def markedCompletedT (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' p : Ideal O × Ideal O, markedSummand S D Ψ W X p.1 p.2


-- @@ L55-57 verbatim
def correctedCompletedT (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' p : Ideal O × Ideal O, correctedSummand S D Ψ W X p.1 p.2


-- @@ L59-60 verbatim
def correctionCoeff (χ : RayCharacter) : ℂ :=
  phaseCoeff (fun r => star (fixedGQuotientValue r)) χ


-- @@ L62-66 verbatim
theorem correctionCoeff_sum_norm_le :
    (∑ χ : RayCharacter, ‖correctionCoeff χ‖) ≤ 32 := by
  have h := phaseCoeff_sum_norm_le (fun r => star (fixedGQuotientValue r)) 2
    (fun u => by simpa only [norm_star] using fixedGQuotientValue_norm_le_two (u : RayRing))
  simpa only [correctionCoeff] using h.trans_eq (by norm_num : (16 : ℝ) * 2 = 32)


-- @@ L68-70 verbatim
theorem completedIndex_eq_primaryGenerator (I J : Ideal O) :
    completedIndex I J = primaryGenerator (I * J ^ 3) := by
  simp only [completedIndex, primaryGenerator_mul, CubicEisenstein.primaryGenerator_pow]


-- @@ L72-77 verbatim
theorem completedMask_zero_of_excluded (S : Finset (Ideal O)) (D I J p : Ideal O)
    (hp : p ∈ S) (hpdiv : p ∣ I * J ^ 3) : completedMask S D I J = 0 := by
  unfold completedMask
  rw [ite_eq_right]
  intro h
  exact h.2 p hp hpdiv


-- @@ L79-81 verbatim
theorem completedMask_zero_of_not_marked (S : Finset (Ideal O)) (D I J : Ideal O)
    (hD : ¬D ∣ I * J ^ 3) : completedMask S D I J = 0 := by
  simp [completedMask, hD]


-- @@ L83-86 verbatim
theorem completedCorrection_expansion (I J : Ideal O) :
    completedCorrection I J =
      ∑ χ : RayCharacter, correctionCoeff χ * rayCharacter χ (completedIndex I J) := by
  exact phase_expansion (fun r => star (fixedGQuotientValue r)) (completedIndex I J)


-- @@ L88-100 verbatim
theorem correctedSummand_ray_expansion (S : Finset (Ideal O)) (D I J : Ideal O)
    (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) :
    correctedSummand S D Ψ W X I J =
      ∑ χ : RayCharacter, correctionCoeff χ *
        markedSummand S D (rayMonoid χ * Ψ) W X I J := by
  unfold correctedSummand
  rw [completedCorrection_expansion, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro χ _
  unfold markedSummand
  rw [CanonicalRowCompletion.summand_mul_fixed_twist]
  simp only [rayMonoid_apply, completedIndex]
  ring


-- @@ L102-108 verbatim
theorem markedSummand_summable (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    Summable (fun p : Ideal O × Ideal O => markedSummand S D Ψ W X p.1 p.2) := by
  apply summable_of_hasFiniteSupport
  apply (completedT_finite_support Ψ W hW X hX).subset
  intro p hp
  exact fun hz => hp (by simp only [markedSummand, hz, mul_zero])


-- @@ L110-116 verbatim
theorem correctedSummand_summable (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    Summable (fun p : Ideal O × Ideal O => correctedSummand S D Ψ W X p.1 p.2) := by
  apply summable_of_hasFiniteSupport
  apply (completedT_finite_support Ψ W hW X hX).subset
  intro p hp
  exact fun hz => hp (by simp only [correctedSummand, markedSummand, hz, mul_zero])


-- @@ L118-127 verbatim
theorem correctedCompletedT_ray_expansion (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    correctedCompletedT S D Ψ W X =
      ∑ χ : RayCharacter, correctionCoeff χ *
        markedCompletedT S D (rayMonoid χ * Ψ) W X := by
  unfold correctedCompletedT
  simp_rw [correctedSummand_ray_expansion]
  rw [Summable.tsum_finsetSum (fun χ _ =>
    (markedSummand_summable S D (rayMonoid χ * Ψ) W hW X hX).mul_left (correctionCoeff χ))]
  simp only [tsum_mul_left, markedCompletedT]


-- @@ L129-144 verbatim
theorem correctedCompletedT_norm_le (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ χ : RayCharacter, ‖markedCompletedT S D (rayMonoid χ * Ψ) W X‖ ≤ B) :
    ‖correctedCompletedT S D Ψ W X‖ ≤ 32 * B := by
  rw [correctedCompletedT_ray_expansion S D Ψ W hW X hX]
  calc
    _ ≤ ∑ χ : RayCharacter, ‖correctionCoeff χ *
        markedCompletedT S D (rayMonoid χ * Ψ) W X‖ := norm_sum_le _ _
    _ ≤ ∑ χ : RayCharacter, ‖correctionCoeff χ‖ * B := by
      apply Finset.sum_le_sum
      intro χ _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hbound χ) (norm_nonneg _)
    _ = (∑ χ : RayCharacter, ‖correctionCoeff χ‖) * B := (Finset.sum_mul ..).symm
    _ ≤ 32 * B := mul_le_mul_of_nonneg_right correctionCoeff_sum_norm_le hB


-- @@ L146-146 verbatim
end SevenEighths.ProbeCompleted

-- @@ L147-147 verbatim
end


-- @@ L149-149 verbatim
end OAI
