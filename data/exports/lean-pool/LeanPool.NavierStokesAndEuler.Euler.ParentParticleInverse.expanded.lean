/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentNormalizedGeometry
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketRestriction
import LeanPool.NavierStokesAndEuler.Euler.FlowL2Transport
import LeanPool.NavierStokesAndEuler.Euler.Foundations.DeformationVolume


-- @@ L14-16 verbatim
/-! The inverse carried by the physical particle map. Preservation of
volume follows from the actual determinant, and both time restriction
and the packet child propagate the two inverse laws. -/


-- @@ L18-18 verbatim
@[expose] public section



-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
namespace EulerParentPacketFrames


-- @@ L25-26 verbatim
open Set MeasureTheory EulerSmoothLimit EulerTimeIntervalRestriction
  EulerGraphInvariantFlow

-- @@ L27-27 verbatim
open scoped ContDiff


-- @@ L29-35 verbatim
/-- Particle inverse data, collecting `field`, `left_inverse`, `right_inverse`, `continuous`. -/
structure ParticleInverse (A : Parent) where
  /-- Underlying field of `ParticleInverse`, of type `Icc (0 : ℝ) A.T → Space → Space`. -/
  field : Icc (0 : ℝ) A.T → Space → Space
  left_inverse : ∀ t x, field t (A.position t x)=x
  right_inverse : ∀ t x, A.position t (field t x)=x
  continuous : Continuous (Function.uncurry field)


-- @@ L37-37 verbatim
namespace Parent


-- @@ L39-39 verbatim
variable (A : Parent)


-- @@ L41-42 verbatim
theorem position_contDiff (t : Icc (0 : ℝ) A.T) : ContDiff ℝ ∞ (A.position t) :=
  contDiff_id.add (A.displacement.smooth t)


-- @@ L44-50 verbatim
theorem packetPosition_contDiff (t : Icc (0 : ℝ) A.T) :
    ContDiff ℝ ∞ (fun x => A.packetPosition (t,x)) := by
  have he : (fun x => A.packetPosition (t,x)) =
      (fun x => A.ell⁻¹ • A.position t (A.ell • x)) :=
    funext (A.packetPosition_apply t)
  rw [he]
  exact ((A.position_contDiff t).comp (contDiff_id.const_smul A.ell)).const_smul A.ell⁻¹


-- @@ L52-52 verbatim
end Parent


-- @@ L54-54 verbatim
namespace ParticleInverse


-- @@ L56-56 verbatim
variable {A : Parent} (I : ParticleInverse A)


-- @@ L58-61 verbatim
include I in
theorem position_bijective (t : Icc (0 : ℝ) A.T) : Function.Bijective (A.position t) :=
  ⟨Function.LeftInverse.injective (I.left_inverse t),
    Function.RightInverse.surjective (I.right_inverse t)⟩


-- @@ L63-65 verbatim
theorem field_initial (x : Space) : I.field A.zeroTime x=x := by
  have h := I.left_inverse A.zeroTime x
  simpa only [Parent.position, Parent.zeroTime, A.initial, add_zero] using h


-- @@ L67-72 verbatim
include I in
theorem position_measurePreserving (t : Icc (0 : ℝ) A.T) :
    MeasurePreserving (A.position t) volume volume :=
  EulerDeformationVolume.measurePreserving_of_det_one volume (A.position t)
    (fun x => ContinuousLinearMap.id ℝ Space+fderiv ℝ (A.displacement.field t : Space → Space) x)
    (A.position_hasFDerivAt t) (I.position_bijective t) (A.displacement_det_one t)


-- @@ L74-79 verbatim
theorem field_measurePreserving (t : Icc (0 : ℝ) A.T) :
    MeasurePreserving (I.field t) volume volume :=
  EulerFlowL2Transport.inverse_measurePreserving (A.position t) (I.field t)
    (fun x => ContinuousLinearMap.id ℝ Space+fderiv ℝ (A.displacement.field t : Space → Space) x)
    (A.position_hasFDerivAt t) (I.left_inverse t) (I.right_inverse t)
    (Continuous.uncurry_left t I.continuous) (A.displacement_det_one t)


-- @@ L81-83 verbatim
/-- Normalized, given by `A.packetInverse I.field (t,x)`. -/
def normalized (t : Icc (0 : ℝ) A.T) (x : Space) : Space :=
  A.packetInverse I.field (t,x)


-- @@ L85-87 verbatim
theorem normalized_left (t : Icc (0 : ℝ) A.T) (x : Space) :
    I.normalized t (A.packetPosition (t,x))=x :=
  A.packetInverse_left I.field I.left_inverse (t,x)


-- @@ L89-91 verbatim
theorem normalized_right (t : Icc (0 : ℝ) A.T) (x : Space) :
    A.packetPosition (t,I.normalized t x)=x :=
  A.packetInverse_right I.field I.right_inverse (t,x)


-- @@ L93-95 verbatim
theorem normalized_continuous : Continuous (Function.uncurry I.normalized) :=
  (A.packetInverse_joint_continuous I.field I.continuous).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)


-- @@ L97-104 verbatim
/-- Restrict time, bundling `field`, `left_inverse`, `right_inverse`, `continuous`. -/
def restrictTime (S : ℝ) (hS : 0 < S) (hST : S ≤ A.T) :
    ParticleInverse (A.restrictTime S hS hST) where
  field t := I.field (initialInclusion A.T S hST t)
  left_inverse t x := I.left_inverse (initialInclusion A.T S hST t) x
  right_inverse t x := I.right_inverse (initialInclusion A.T S hST t) x
  continuous := I.continuous.comp
    (((initialInclusion A.T S hST).continuous.comp continuous_fst).prodMk continuous_snd)


-- @@ L106-114 verbatim
/-- Child, bundling `field`, `left_inverse`, `right_inverse`, `continuous`. -/
def child {P : ℝ} [Fact (0 < P)] (G : EulerPhysicalGraphFlowBounds.Data P A.T)
    (k : ℝ) (m : Space) (hgraph : ∀ t z, graphConstraint k m (G.A.field t z) = 0)
    (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1) :
    ParticleInverse (A.child G k m hgraph nextEll hnext hnext1) where
  field := A.childInverse G k m I.field
  left_inverse := A.childInverse_left G k m hgraph nextEll hnext hnext1 I.field I.left_inverse
  right_inverse := A.childInverse_right G k m hgraph nextEll hnext hnext1 I.field I.right_inverse
  continuous := A.childInverse_joint_continuous G k m I.field I.continuous


-- @@ L116-116 verbatim
end ParticleInverse

-- @@ L117-117 verbatim
end EulerParentPacketFrames
