/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteProfileFields
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileBudget
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderHighPartBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderWeightedLinear
import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteAssemblyBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketProfileCoarseBounds


-- @@ L16-16 verbatim
/-! The finite approximate velocity and its genuine time derivative share the profile bounds. -/


-- @@ L18-18 verbatim
@[expose] public section



-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
namespace EulerPacketCylinderField


-- @@ L25-26 verbatim
open Set EulerSmoothLimit EulerPacketProfileRecursion EulerPacketTimeProfile
    EulerPacketShiftArithmetic


-- @@ L28-30 verbatim
theorem rawTimeDerivative_zero (T : ℝ) : rawTimeDerivative T 0=0 := by
  funext z
  simp [rawTimeDerivative]


-- @@ L32-32 verbatim
namespace ProfileRegularity


-- @@ L34-38 verbatim
variable {P T : ℝ} [Fact (0 < P)] {N : ℕ} {a : ℕ → Profile} {support : Set Space}
  (hT : 0 < T) (G : ∀ i, i ≤ N → ProfileRegularity P T hT.le support (a i))
  {S : Scales (Icc (0 : ℝ) T)} {R : ℝ}
  (hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S R i)
  (hR : 1 ≤ R) (ha : a 0 = 0)


-- @@ L40-40 verbatim
include hG hR ha


-- @@ L42-67 verbatim
theorem velocityGrade_bound (n : ℕ) :
    (velocityGradeField hT G n).WordBound 6 R (3*S.H0^(2*n)) (highShift n) := by
  apply Field.wordBound_assembleFamily N _ _ _ _ R S.H0 hR S.H0_one_le
  · intro i hi
    by_cases hi0 : i=0
    · subst i
      have hz : ∀ (t : Icc (0 : ℝ) T) x θ,
          ((a 0).high+(a 0).mean) (t,(x,θ))=0 := by
        intro t x θ
        rw [ha]
        change (0 : Space)+0=0
        exact zero_add 0
      exact (Field.wordBound_of_zero ((G 0 hi).high.add (G 0 hi).mean) hz 6 R (highShift
          0)).mono_amplitude
        (zero_le_one.trans hR) (by norm_num)
    · have h := hG i hi (by omega)
      have hm := h.mean_unnormalized.mono_shift hR (pow_nonneg S.H0_pos.le _)
        (show meanShift i ≤ highShift i by unfold meanShift highShift; omega)
      simpa only [two_mul] using (h.high_unnormalized (by omega)).add hm
  · intro i hi
    by_cases hi0 : i=0
    · subst i
      exact (Field.wordBound_of_zero (G 0 hi).corrector
        (fun _ _ _ => by rw [ha]; rfl) 6 R (highShift 0)).mono_amplitude
          (zero_le_one.trans hR) (by norm_num)
    · exact (hG i hi (by omega)).corrector_unnormalized (by omega)


-- @@ L69-104 verbatim
theorem velocityGradeDerivative_bound (n : ℕ) :
    (velocityGradeDerivativeField hT G n).WordBound 6 R (3*S.H0^(2*n)) (highShift n) := by
  apply Field.wordBound_assembleFamily N _ _ _ _ R S.H0 hR S.H0_one_le
  · intro i hi
    by_cases hi0 : i=0
    · subst i
      have hf : (a 0).high+(a 0).mean=0 := by
        rw [ha]
        change (0 : VectorField)+0=0
        exact zero_add 0
      have hz : ∀ (t : Icc (0 : ℝ) T) x θ,
          rawTimeDerivative T ((a 0).high+(a 0).mean) (t,(x,θ))=0 := by
        intro t x θ
        rw [hf,rawTimeDerivative_zero]
        rfl
      exact (Field.wordBound_of_zero _ hz 6 R (highShift 0)).mono_amplitude
        (zero_le_one.trans hR) (by norm_num)
    · have h := hG i hi (by omega)
      have hm := h.meanDerivative_unnormalized.mono_shift hR (pow_nonneg S.H0_pos.le _)
        (show meanShift i ≤ highShift i by unfold meanShift highShift; omega)
      have hs := (h.highDerivative_unnormalized (by omega)).add hm
      have hs' : ((G i hi).highDerivative.add (G i hi).meanDerivative).WordBound
          6 R (2*S.H0^(2*i)) (highShift i) := by simpa only [two_mul] using hs
      exact hs'.of_path_eq _ rfl
  · intro i hi
    by_cases hi0 : i=0
    · subst i
      have hf : (a 0).corrector=0 := by rw [ha]; rfl
      have hz : ∀ (t : Icc (0 : ℝ) T) x θ,
          rawTimeDerivative T (a 0).corrector (t,(x,θ))=0 := by
        intro t x θ
        rw [hf,rawTimeDerivative_zero]
        rfl
      exact (Field.wordBound_of_zero _ hz 6 R (highShift 0)).mono_amplitude
        (zero_le_one.trans hR) (by norm_num)
    · exact ((hG i hi (by omega)).correctorDerivative_unnormalized (by omega)).of_path_eq _ rfl


-- @@ L106-106 verbatim
end ProfileRegularity

-- @@ L107-107 verbatim
end EulerPacketCylinderField
