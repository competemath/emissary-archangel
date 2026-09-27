/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketCoarseMajorant
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderProfileChange
import LeanPool.NavierStokesAndEuler.Euler.PacketMeanGradeBounds


-- @@ L14-14 verbatim
/-! Removing the bounded time profile and performing the one final coarse factorial split. -/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
namespace EulerPacketCylinderField.Field


-- @@ L23-23 verbatim
open Set EulerPacketProfileRecursion EulerGevrey EulerPacketCoarseMajorant


-- @@ L25-26 verbatim
variable {P T : ℝ} [Fact (0 < P)] {raw : VectorField} {G : Field P T raw}
  {q d : ℕ} {R A : ℝ}


-- @@ L28-35 verbatim
theorem WordBound.remove_profile (hT : 0 ≤ T)
    (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t)
    (hG : (G.normalized hT g hg).WordBound q R A d)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ t, g t ≤ C) : G.WordBound q R (C*A) d := by
  have h := hG.changeProfile hT (ContinuousMap.const (Icc (0 : ℝ) T) 1) (fun _ => zero_lt_one)
    C hC (by simpa only [ContinuousMap.const_apply,mul_one] using hbound)
  have hh := h.of_normalized_const hT 1 zero_lt_one
  simpa only [one_mul] using hh


-- @@ L37-43 verbatim
theorem WordBound.coarse_grade (hG : G.WordBound q R A d) (hR : 1 ≤ R) (hA : 0 ≤ A)
    (N p : ℕ) (hN : 1 ≤ N) (hp : p ≤ 2 * N + 2) (hd : d ≤ 110 * (p + 1)) :
    G.WordBound q (4*R) (A*(gradeBase R N)^(p+1)) 0 := by
  intro n
  exact (hG n).trans ((mul_le_mul_of_nonneg_left (majorant_grade_bound R hR N p d n hN hp hd)
      hA).trans_eq
    (by ring))


-- @@ L45-45 verbatim
end EulerPacketCylinderField.Field


-- @@ L47-47 verbatim
namespace EulerPacketTimeProfile.Scales


-- @@ L49-49 verbatim
variable {K : Type*} [TopologicalSpace K] (S : Scales K)


-- @@ L51-52 verbatim
theorem mean_le_coarse (p : ℕ) (t : K) : S.mean p t ≤ S.H0^(2*p) :=
  pow_le_pow_right₀ S.H0_one_le (by omega : 2*p-2 ≤ 2*p)


-- @@ L54-60 verbatim
theorem high_le_coarse (p : ℕ) (hp : 1 ≤ p) (t : K) : S.high p t ≤ S.H0^(2*p) := by
  change S.growth t*S.H0^(2*p-2) ≤ _
  calc
    _ ≤ S.H0*S.H0^(2*p-2) :=
      mul_le_mul_of_nonneg_right (S.growth_le t) (pow_nonneg S.H0_pos.le _)
    _ = S.H0^(2*p-2+1) := by rw [pow_succ,mul_comm]
    _ ≤ _ := pow_le_pow_right₀ S.H0_one_le (by omega)


-- @@ L62-62 verbatim
end EulerPacketTimeProfile.Scales


-- @@ L64-64 verbatim
namespace EulerPacketCylinderField.ProfileBudget


-- @@ L66-67 verbatim
open Set EulerSmoothLimit EulerPacketProfileRecursion EulerPacketTimeProfile
    EulerPacketShiftArithmetic


-- @@ L69-71 verbatim
variable {P T : ℝ} [Fact (0 < P)] {hT : 0 ≤ T} {support : Set Space} {a : Profile}
  {G : ProfileRegularity P T hT support a} {S : Scales (Icc (0 : ℝ) T)} {R : ℝ} {p : ℕ}
  (B : ProfileBudget G S R p)


-- @@ L73-73 verbatim
include B


-- @@ L75-77 verbatim
theorem high_unnormalized (hp : 1 ≤ p) : G.high.WordBound 6 R (S.H0^(2*p)) (highShift p) := by
  simpa only [mul_one] using B.high.remove_profile hT (S.high p) (S.high_pos p)
    (S.H0^(2*p)) (pow_nonneg S.H0_pos.le _) (S.high_le_coarse p hp)


-- @@ L79-82 verbatim
theorem highDerivative_unnormalized (hp : 1 ≤ p) :
    G.highDerivative.WordBound 6 R (S.H0^(2*p)) (highShift p) := by
  simpa only [mul_one] using B.highDerivative.remove_profile hT (S.high p) (S.high_pos p)
    (S.H0^(2*p)) (pow_nonneg S.H0_pos.le _) (S.high_le_coarse p hp)


-- @@ L84-86 verbatim
theorem mean_unnormalized : G.mean.WordBound 6 R (S.H0^(2*p)) (meanShift p) := by
  simpa only [mul_one] using B.mean.remove_profile hT (S.mean p) (S.mean_pos p)
    (S.H0^(2*p)) (pow_nonneg S.H0_pos.le _) (S.mean_le_coarse p)


-- @@ L88-91 verbatim
theorem meanDerivative_unnormalized : G.meanDerivative.WordBound 6 R (S.H0^(2*p)) (meanShift p) :=
    by
  simpa only [mul_one] using B.meanDerivative.remove_profile hT (S.mean p) (S.mean_pos p)
    (S.H0^(2*p)) (pow_nonneg S.H0_pos.le _) (S.mean_le_coarse p)


-- @@ L93-96 verbatim
theorem corrector_unnormalized (hp : 1 ≤ p) : G.corrector.WordBound 6 R (S.H0^(2*p)) (highShift p)
    := by
  simpa only [mul_one] using B.corrector.remove_profile hT (S.high p) (S.high_pos p)
    (S.H0^(2*p)) (pow_nonneg S.H0_pos.le _) (S.high_le_coarse p hp)


-- @@ L98-101 verbatim
theorem correctorDerivative_unnormalized (hp : 1 ≤ p) :
    G.correctorDerivative.WordBound 6 R (S.H0^(2*p)) (highShift p) := by
  simpa only [mul_one] using B.correctorDerivative.remove_profile hT (S.high p) (S.high_pos p)
    (S.H0^(2*p)) (pow_nonneg S.H0_pos.le _) (S.high_le_coarse p hp)


-- @@ L103-106 verbatim
theorem pressure_unnormalized (hp : 1 ≤ p) : G.pressure.WordBound 6 R (S.H0^(2*p)) (highShift p) :=
    by
  simpa only [mul_one] using B.pressure.remove_profile hT (S.high p) (S.high_pos p)
    (S.H0^(2*p)) (pow_nonneg S.H0_pos.le _) (S.high_le_coarse p hp)


-- @@ L108-108 verbatim
end EulerPacketCylinderField.ProfileBudget
