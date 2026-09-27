/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketScaledRay
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketForcing
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPiolaData
import LeanPool.NavierStokesAndEuler.Euler.PacketInitialGeometry


-- @@ L14-16 verbatim
/-! The literal normalized covector choice for the next source normal.
It has unit length and its inverse-transpose transport is exactly the
prescribed old-frame cross direction, with a positive scale. -/


-- @@ L18-18 verbatim
@[expose] public section



-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
namespace EulerPacketMovingFrame


-- @@ L25-26 verbatim
open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerPacketNormalizedPrimary
  EulerPacketCrossProduct EulerTransversePacketProvider


-- @@ L28-30 verbatim
/-- Activation direction, given by `unit (F.toContinuousLinearMap.adjoint n)`. -/
def activationDirection (F : Space ≃L[ℝ] Space) (n : Space) : Space :=
  unit (F.toContinuousLinearMap.adjoint n)


-- @@ L32-34 verbatim
/-- Activation ray scale, given by `‖F.toContinuousLinearMap.adjoint n‖⁻¹`. -/
def activationRayScale (F : Space ≃L[ℝ] Space) (n : Space) : ℝ :=
  ‖F.toContinuousLinearMap.adjoint n‖⁻¹


-- @@ L36-45 verbatim
theorem inverse_adjoint_forward_adjoint (F : Space ≃L[ℝ] Space) (n : Space) :
    F.symm.toContinuousLinearMap.adjoint (F.toContinuousLinearMap.adjoint n)=n := by
  have hi : F.toContinuousLinearMap.comp F.symm.toContinuousLinearMap=ContinuousLinearMap.id ℝ
      Space := by
    apply ContinuousLinearMap.ext
    intro v
    exact F.apply_symm_apply v
  change (F.symm.toContinuousLinearMap.adjoint.comp F.toContinuousLinearMap.adjoint) n=n
  rw [← adjoint_comp,hi,adjoint_id]
  rfl


-- @@ L47-52 verbatim
theorem forward_adjoint_ne_zero (F : Space ≃L[ℝ] Space) {n : Space} (hn : n ≠ 0) :
    F.toContinuousLinearMap.adjoint n ≠ 0 := by
  intro hz
  have h := inverse_adjoint_forward_adjoint F n
  rw [hz,map_zero] at h
  exact hn h.symm


-- @@ L54-55 verbatim
theorem activationDirection_unit (F : Space ≃L[ℝ] Space) {n : Space} (hn : n ≠ 0) :
    ‖activationDirection F n‖=1 := unit_norm (forward_adjoint_ne_zero F hn)


-- @@ L57-58 verbatim
theorem activationRayScale_pos (F : Space ≃L[ℝ] Space) {n : Space} (hn : n ≠ 0) :
    0 < activationRayScale F n := inv_pos.mpr (norm_pos_iff.mpr (forward_adjoint_ne_zero F hn))


-- @@ L60-62 verbatim
theorem activationDirection_transport (F : Space ≃L[ℝ] Space) (n : Space) :
    F.symm.toContinuousLinearMap.adjoint (activationDirection F n)=activationRayScale F n • n := by
  simp only [activationDirection,activationRayScale,unit,map_smul,inverse_adjoint_forward_adjoint]


-- @@ L64-65 verbatim
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : Data U)


-- @@ L67-72 verbatim
theorem actual_normal_of_activation_choice (t : Icc (0 : ℝ) D.T) (x n : Space)
    (hchoice : D.m₀ = activationDirection (D.deformationEquiv t x) n) :
    D.normal.field t x=activationRayScale (D.deformationEquiv t x) n • n := by
  change (D.FInv.field t x).adjoint D.m₀=_
  rw [hchoice]
  exact activationDirection_transport (D.deformationEquiv t x) n


-- @@ L74-91 verbatim
theorem actual_activation_scaled_ray (m v : ℝ → Space) (t₀ : Icc (0 : ℝ) D.T) (a ε : ℝ)
    (hm : m t₀ ≠ 0) (hv : v t₀ ≠ 0) (hmv : ⟪m t₀, v t₀⟫_ℝ = 0)
    (hchoice : D.m₀ = activationDirection (D.deformationEquiv t₀ 0)
      (cross (unit (m t₀)) (unit (v t₀)))) :
    let s₀ := activationRayScale (D.deformationEquiv t₀ 0) (cross (unit (m t₀)) (unit (v t₀)))
    0 < s₀ ∧ scaledRay m v (fun s => D.normal.field (D.clamp s) 0) s₀ t₀ a ε 0 = ![0,0,1] := by
  dsimp only
  have hc : cross (unit (m t₀)) (unit (v t₀)) ≠ 0 := by
    have hn := (frame_orthonormal (unit (m t₀)) (unit (v t₀))
      (unit_inner_self hm) (unit_inner_self hv) (unit_inner_zero hmv)).norm_eq_one 2
    have hn' : ‖cross (unit (m t₀)) (unit (v t₀))‖=1 := hn
    intro hz
    rw [hz,norm_zero] at hn'
    norm_num at hn'
  have hpos := activationRayScale_pos (D.deformationEquiv t₀ 0) hc
  refine ⟨hpos,scaledRay_initial hpos.ne' hm hv hmv ?_⟩
  rw [Data.clamp_coe]
  exact actual_normal_of_activation_choice D t₀ 0 _ hchoice


-- @@ L93-93 verbatim
end EulerPacketMovingFrame
