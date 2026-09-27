/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketGeometryJoinedBudget
public import LeanPool.NavierStokesAndEuler.Euler.ParentForwardGeometryInput
public import LeanPool.NavierStokesAndEuler.Euler.PacketGevreyProfileChoice
import LeanPool.NavierStokesAndEuler.Euler.PacketActivationSourceData
import LeanPool.NavierStokesAndEuler.Euler.PacketProfileEnvelope


-- @@ L15-16 verbatim
/-! The chosen geometric growth profile carries a polynomial amplitude
bound. This controls the actual grade scale, including its history part. -/


-- @@ L18-18 verbatim
@[expose] public section



-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
namespace EulerPacketSourceGeometry.ParentFrame


-- @@ L25-26 verbatim
open Set InnerProductSpace EulerSmoothLimit EulerPacketMovingFrame
  EulerPacketNormalizedPrimary EulerPacketCrossProduct EulerTransversePacketProvider


-- @@ L28-29 verbatim
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  {D : Data U} {τ : ℝ} (P : ParentFrame D τ) (hτ : 0 < τ) (hτT : τ < D.T)


-- @@ L31-38 verbatim
theorem rayScale_inv_le_frameBound : (P.rayScale hτ hτT)⁻¹ ≤ D.frameBound := by
  have hn := (frame_orthonormal (unit (P.m τ)) (unit (P.v τ))
    (unit_inner_self (P.ray_nonzero τ ⟨le_rfl,hτT.le⟩))
    (unit_inner_self (P.velocity_nonzero τ ⟨le_rfl,hτT.le⟩))
    (unit_inner_zero (P.tangent τ ⟨le_rfl,hτT.le⟩))).norm_eq_one 2
  change ‖cross (unit (P.m τ)) (unit (P.v τ))‖=1 at hn
  exact (D.activationRayScale_bounds ⟨τ,hτ.le,hτT.le⟩
    (cross (unit (P.m τ)) (unit (P.v τ))) hn).2.2


-- @@ L40-40 verbatim
end EulerPacketSourceGeometry.ParentFrame


-- @@ L42-42 verbatim
namespace EulerPacketSourceGeometry.Guards


-- @@ L44-45 verbatim
open Set EulerSmoothLimit EulerTransversePacketProvider EulerGevrey
  EulerPacketTimeProfile EulerPacketCylinderField


-- @@ L47-50 verbatim
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T} {P : ParentFrame D τ}
  {H : HistoryData (D.initial τ hτ hτT.le)} (J : Guards hτ hτT P H)
  (hball : (1 / 2 : ℝ) ≤ J.radius)


-- @@ L52-58 verbatim
theorem sourceGrowthProfile_amplitude_frame (t : Icc (0 : ℝ) (D.T - τ)) :
    J.primaryAmplitude hball*J.sourceGrowthProfile hball t ≤
      8*Real.exp 6*J.δ*J.hchild*D.frameBound := by
  apply (J.sourceGrowthProfile_amplitude hball t).trans
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (P.rayScale_inv_le_frameBound hτ hτT)
    (by positivity [J.delta_nonneg,J.child_nonneg])


-- @@ L60-61 verbatim
variable (L : EulerTransversePacketJoin.Budget D τ hτ hτT H (Fin 4) 6)
  (hg : L.g = J.sourceGrowthProfile hball)


-- @@ L63-80 verbatim
include hg in
theorem budget_fullProfile_amplitude (t : Icc (0 : ℝ) D.T) :
    J.primaryAmplitude hball*L.fullProfile t ≤
      8*Real.exp 6*J.δ*J.hchild*(1+L.C₀) := by
  have hF : ∀ t x, ‖D.F.field t x‖ ≤ L.C₀ := by
    intro t x
    simpa only [norm_iteratedFDeriv_zero,majorant,Nat.zero_add,Nat.factorial_zero,
      Nat.cast_one,pow_zero,mul_one,one_pow] using L.frame_bound 0 t x
  have hframe := D.frameBound_le_of_frame L.C₀ L.C₀_nonneg hF
  have hf (s : Icc (0 : ℝ) (D.T-τ)) :
      J.primaryAmplitude hball*L.g s ≤ 8*Real.exp 6*J.δ*J.hchild*(1+L.C₀) := by
    rw [hg]
    exact (J.sourceGrowthProfile_amplitude_frame hball s).trans
      (mul_le_mul_of_nonneg_left hframe (by positivity [J.delta_nonneg,J.child_nonneg]))
  have ha := hf ⟨0,le_rfl,(sub_pos.mpr hτT).le⟩
  rw [L.initial_one,mul_one] at ha
  exact EulerElapsedTimePathGluing.smul_profile_le D.T τ hτ.le hτT.le L.g L.initial_one
    (J.primaryAmplitude hball) _ ha hf t


-- @@ L82-88 verbatim
include hg in
theorem budget_H0_bound {T' : ℝ} (hTime : D.T = T')
    (hδ : 0 < J.δ) (hh : 0 < J.hchild) :
    (Scales.ofTimeProfile L.fullProfile L.fullProfile_pos hTime (J.primaryAmplitude hball)
      (J.primaryAmplitude_pos hball hδ hh)).H0 ≤ max 1 (8*Real.exp 6*J.δ*J.hchild*(1+L.C₀)) :=
  Scales.ofTimeProfile_H0_le L.fullProfile L.fullProfile_pos hTime _ _ _ (le_max_left _ _)
    (fun t => (J.budget_fullProfile_amplitude hball L hg t).trans (le_max_right _ _))


-- @@ L90-90 verbatim
end EulerPacketSourceGeometry.Guards


-- @@ L92-92 verbatim
namespace EulerPacketSourceGeometry.ForwardGuards


-- @@ L94-94 verbatim
open Set EulerSmoothLimit EulerTransversePacketProvider EulerPacketTimeProfile


-- @@ L96-100 verbatim
variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {P : ParentFrame D 0} (J : ForwardGuards P)
  (hball : (1 / 2 : ℝ) ≤ J.radius)
  (L : EulerTransversePacketForward.Budget D (Fin 4) 6)
  (hg : L.g = J.sourceGrowthProfile hball)


-- @@ L102-106 verbatim
include hg in
theorem budget_profile_amplitude (t : Icc (0 : ℝ) D.T) :
    J.primaryAmplitude hball*L.g t ≤ 8*Real.exp 6*J.δ*J.hchild := by
  rw [hg]
  exact J.sourceGrowthProfile_amplitude hball t


-- @@ L108-114 verbatim
include hg in
theorem budget_H0_bound {T' : ℝ} (hTime : D.T = T')
    (hδ : 0 < J.δ) (hh : 0 < J.hchild) :
    (Scales.ofTimeProfile L.g L.positive hTime (J.primaryAmplitude hball)
      (J.primaryAmplitude_pos hball hδ hh)).H0 ≤ max 1 (8*Real.exp 6*J.δ*J.hchild) :=
  Scales.ofTimeProfile_H0_le L.g L.positive hTime _ _ _ (le_max_left _ _)
    (fun t => (J.budget_profile_amplitude hball L hg t).trans (le_max_right _ _))


-- @@ L116-116 verbatim
end EulerPacketSourceGeometry.ForwardGuards
