/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.ParentParticleInverse
import LeanPool.NavierStokesAndEuler.Euler.ContinuousInverseDerivative
import LeanPool.NavierStokesAndEuler.Euler.GevreyInverseMap


-- @@ L12-14 verbatim
/-! The physical Euler evolution carried by a particle parent. Its
acceleration law and the smoothness of its closed spatial slices are
consequences of the actual flow identities, rather than extra premises. -/


-- @@ L16-16 verbatim
section


-- @@ L18-19 verbatim
/-! Spatial smoothness of the actual physical particle inverse follows
from its inverse identities and the genuine determinant-one Jacobian. -/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
namespace EulerParentPacketFrames.ParticleInverse


-- @@ L27-27 verbatim
open Set EulerSmoothLimit EulerContinuousInverseDerivative EulerGevreyComposition

-- @@ L28-28 verbatim
open scoped ContDiff


-- @@ L30-30 verbatim
variable {A : Parent} (I : ParticleInverse A)


-- @@ L32-42 verbatim
theorem hasFDerivAt (t : Icc (0 : ℝ) A.T) (x : Space) :
    HasFDerivAt (I.field t)
      (A.inverse.field t (A.ell⁻¹ • I.field t x)) x := by
  apply hasFDerivAt_inverse (A.position t) (I.field t) x
    (A.frame.field t (A.ell⁻¹ • I.field t x))
    (A.inverse.field t (A.ell⁻¹ • I.field t x))
    (I.continuous.uncurry_left t).continuousAt
  · simpa only [smul_smul,mul_inv_cancel₀ A.ell_pos.ne',one_smul] using
      A.position_frame t (A.ell⁻¹ • I.field t x)
  · exact Filter.Eventually.of_forall (I.right_inverse t)
  · exact A.inverse_left t (A.ell⁻¹ • I.field t x)


-- @@ L44-49 verbatim
theorem smooth (t : Icc (0 : ℝ) A.T) : ContDiff ℝ ∞ (I.field t) := by
  apply contDiff_of_fderiv_eq_comp (I.field t)
    (fun y => A.inverse.field t (A.ell⁻¹ • y))
    (fun x => (I.hasFDerivAt t x).differentiableAt)
  · exact (A.inverse.smooth t).comp (contDiff_id.const_smul A.ell⁻¹)
  · exact fun x => (I.hasFDerivAt t x).fderiv


-- @@ L51-51 verbatim
end EulerParentPacketFrames.ParticleInverse


-- @@ L53-53 verbatim
end

-- @@ L54-54 verbatim
end


-- @@ L56-56 verbatim
end


-- @@ L58-58 verbatim
@[expose] public section


-- @@ L60-60 verbatim
noncomputable section


-- @@ L62-62 verbatim
namespace EulerParentPacketFrames


-- @@ L64-64 verbatim
open Set EulerSmoothLimit EulerLagrangian EulerTimeIntervalRestriction

-- @@ L65-65 verbatim
open scoped ContDiff


-- @@ L67-86 verbatim
/-- Evolution data, collecting `inverse`, `velocity`, `pressure`, `force`, `force_continuous`,
`velocity_match` and their compatibility conditions. -/
structure Evolution (A : Parent) where
  /-- Inverse of `Evolution`, of type `ParticleInverse A`. -/
  inverse : ParticleInverse A
  /-- Velocity field of `Evolution`, of type `ℝ × Space → Space`. -/
  velocity : ℝ × Space → Space
  /-- Pressure field of `Evolution`, of type `ℝ × Space → ℝ`. -/
  pressure : ℝ × Space → ℝ
  /-- Force of `Evolution`, of type `Icc (0 : ℝ) A.T → Space → Space`. -/
  force : Icc (0 : ℝ) A.T → Space → Space
  force_continuous : Continuous (Function.uncurry force)
  velocity_match : ∀ t x, A.velocity.field t x=velocity (t,A.position t x)
  velocity_differentiable : ∀ t ∈ Ioo 0 A.T, ∀ x, DifferentiableAt ℝ velocity (t,x)
  pressure_differentiable : ∀ (t : Icc (0 : ℝ) A.T) x,
    DifferentiableAt ℝ (fun y => pressure (t,y)) x
  pressure_gradient : ∀ (t : Icc (0 : ℝ) A.T) x,
    gradient (fun y => pressure (t,y)) x=force t x
  momentum_zero : ∀ t ∈ Ioo 0 A.T, ∀ x, momentumResidual velocity pressure (t,x)=0
  divergence_zero : ∀ t ∈ Ioo 0 A.T, ∀ x, divergence (fun y => velocity (t,y)) x=0


-- @@ L88-88 verbatim
namespace Evolution


-- @@ L90-90 verbatim
variable {A : Parent} (E : Evolution A)


-- @@ L92-95 verbatim
theorem acceleration_match (t : Icc (0 : ℝ) A.T) (x : Space) :
    A.acceleration.field t x= -E.force t (A.position t x) :=
  A.acceleration_physical_of_euler E.velocity E.pressure E.force E.force_continuous
    E.pressure_gradient E.velocity_match E.velocity_differentiable E.momentum_zero t x


-- @@ L97-99 verbatim
theorem velocity_pullback (t : Icc (0 : ℝ) A.T) (x : Space) :
    E.velocity (t,x)=A.velocity.field t (E.inverse.field t x) := by
  rw [E.velocity_match,E.inverse.right_inverse]


-- @@ L101-103 verbatim
theorem force_pullback (t : Icc (0 : ℝ) A.T) (x : Space) :
    E.force t x= -A.acceleration.field t (E.inverse.field t x) := by
  rw [E.acceleration_match,E.inverse.right_inverse,neg_neg]


-- @@ L105-110 verbatim
theorem velocity_smooth (t : Icc (0 : ℝ) A.T) :
    ContDiff ℝ ∞ (fun x => E.velocity (t,x)) := by
  have he : (fun x => E.velocity (t,x))=A.velocity.field t ∘ E.inverse.field t :=
    funext (E.velocity_pullback t)
  rw [he]
  exact (A.velocity.smooth t).comp (E.inverse.smooth t)


-- @@ L112-116 verbatim
theorem force_smooth (t : Icc (0 : ℝ) A.T) : ContDiff ℝ ∞ (E.force t) := by
  have he : E.force t=(fun x => -A.acceleration.field t (E.inverse.field t x)) :=
    funext (E.force_pullback t)
  rw [he]
  exact ((A.acceleration.smooth t).comp (E.inverse.smooth t)).neg


-- @@ L118-123 verbatim
theorem strain_eq (t : Icc (0 : ℝ) A.T) (x : Space) :
    A.strain.field t x =
      fderiv ℝ (fun y => E.velocity (t,y)) (A.position t (A.ell • x)) :=
  A.strain_physical (fun s y => E.velocity (s,y))
    (fun s y => ((E.velocity_smooth s).differentiable (by simp)).differentiableAt)
    E.velocity_match t x


-- @@ L125-129 verbatim
theorem curvature_eq (t : Icc (0 : ℝ) A.T) (x : Space) :
    A.curvature.field t x=fderiv ℝ (E.force t) (A.position t (A.ell • x)) :=
  A.curvature_physical E.force
    (fun s y => ((E.force_smooth s).differentiable (by simp)).differentiableAt)
    E.acceleration_match t x


-- @@ L131-146 verbatim
/-- Restrict time, bundling `inverse`, `velocity`, `pressure`, `force` and the required
compatibility proofs. -/
def restrictTime (S : ℝ) (hS : 0 < S) (hST : S ≤ A.T) :
    Evolution (A.restrictTime S hS hST) where
  inverse := E.inverse.restrictTime S hS hST
  velocity := E.velocity
  pressure := E.pressure
  force t := E.force (initialInclusion A.T S hST t)
  force_continuous := E.force_continuous.comp
    (((initialInclusion A.T S hST).continuous.comp continuous_fst).prodMk continuous_snd)
  velocity_match t x := E.velocity_match (initialInclusion A.T S hST t) x
  velocity_differentiable t ht x := E.velocity_differentiable t ⟨ht.1,ht.2.trans_le hST⟩ x
  pressure_differentiable t x := E.pressure_differentiable (initialInclusion A.T S hST t) x
  pressure_gradient t x := E.pressure_gradient (initialInclusion A.T S hST t) x
  momentum_zero t ht x := E.momentum_zero t ⟨ht.1,ht.2.trans_le hST⟩ x
  divergence_zero t ht x := E.divergence_zero t ⟨ht.1,ht.2.trans_le hST⟩ x


-- @@ L148-148 verbatim
end Evolution

-- @@ L149-149 verbatim
end EulerParentPacketFrames
