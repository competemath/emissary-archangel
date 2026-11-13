import Mathlib
import Submission.SO2FrameGauge


-- @@ L4-12 verbatim
/-!
# A concrete ambient plane-rotation isotopy

The explicit `SO(2)` block used for frame gauges also gives a global ambient
isotopy.  In ambient dimension `m+2`, this file constructs the path from the
identity to rotation through a prescribed angle in the first coordinate
plane.  Together with affine isotopies, this supplies the elementary rigid
positioning moves needed after an orbit circle has been rounded.
-/


-- @@ L14-14 verbatim
noncomputable section


-- @@ L16-16 verbatim
open Set Function

-- @@ L17-17 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L19-19 verbatim
namespace Submission

-- @@ L20-20 verbatim
namespace SmoothAmbientIsotopy


-- @@ L22-22 verbatim
variable {m : ℕ}


-- @@ L24-24 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 2))


-- @@ L26-27 verbatim
/-- Collar-flat angle used by the ambient rotation. -/
def planeRotationAngle (θ s : ℝ) : ℝ := normRamp s * θ


-- @@ L29-68 verbatim
/-- Ambient rotation in the first coordinate plane. -/
def planeRotation (θ : ℝ) : SmoothAmbientIsotopy (m + 1) where
  forward s x := SO2FrameGauge.rotate (planeRotationAngle θ s) x
  inverse s x := SO2FrameGauge.rotate (-(planeRotationAngle θ s)) x
  forward_smooth := by
    have hangle : ContDiff ℝ ∞ (fun p : ℝ × E => normRamp p.1 * θ) :=
      (contDiff_normRamp.comp contDiff_fst).mul contDiff_const
    have hpair : ContDiff ℝ ∞
        (fun p : ℝ × E => (normRamp p.1 * θ, p.2)) :=
      hangle.prodMk contDiff_snd
    simpa [Function.comp_def, planeRotationAngle] using
      SO2FrameGauge.contDiff_rotate.comp hpair
  inverse_smooth := by
    have hangle : ContDiff ℝ ∞ (fun p : ℝ × E => -(normRamp p.1 * θ)) :=
      ((contDiff_normRamp.comp contDiff_fst).mul contDiff_const).neg
    have hpair : ContDiff ℝ ∞
        (fun p : ℝ × E => (-(normRamp p.1 * θ), p.2)) :=
      hangle.prodMk contDiff_snd
    simpa [Function.comp_def, planeRotationAngle] using
      SO2FrameGauge.contDiff_rotate.comp hpair
  forward_zero := by
    funext x
    rw [planeRotationAngle,
      normRamp_of_le_quarter (show (0 : ℝ) ≤ 1 / 4 by norm_num), zero_mul,
      SO2FrameGauge.rotate_zero]
    rfl
  left_inv := by
    intro s hs x
    exact SO2FrameGauge.rotate_neg_apply (planeRotationAngle θ s) x
  right_inv := by
    intro s hs x
    exact SO2FrameGauge.rotate_apply_neg (planeRotationAngle θ s) x
  inverse_fderiv_surjective := by
    intro s hs x
    have hfd : fderiv ℝ
        (fun y : E => SO2FrameGauge.rotate (-(planeRotationAngle θ s)) y) x =
        SO2FrameGauge.rotateCLM (-(planeRotationAngle θ s)) :=
      (SO2FrameGauge.rotateCLM (-(planeRotationAngle θ s))).hasFDerivAt.fderiv
    rw [hfd]
    exact (SO2FrameGauge.rotateCLM_bijective _).2


-- @@ L70-73 verbatim
@[simp] theorem planeRotation_forward (θ s : ℝ) (x : E) :
    (planeRotation θ).forward s x =
      SO2FrameGauge.rotate (planeRotationAngle θ s) x :=
  rfl


-- @@ L75-78 verbatim
@[simp] theorem planeRotation_inverse (θ s : ℝ) (x : E) :
    (planeRotation θ).inverse s x =
      SO2FrameGauge.rotate (-(planeRotationAngle θ s)) x :=
  rfl


-- @@ L80-83 verbatim
@[simp] theorem planeRotationAngle_zero (θ : ℝ) :
    planeRotationAngle θ 0 = 0 := by
  rw [planeRotationAngle,
    normRamp_of_le_quarter (show (0 : ℝ) ≤ 1 / 4 by norm_num), zero_mul]


-- @@ L85-88 verbatim
@[simp] theorem planeRotationAngle_one (θ : ℝ) :
    planeRotationAngle θ 1 = θ := by
  rw [planeRotationAngle,
    normRamp_of_three_quarter_le (show (3 / 4 : ℝ) ≤ 1 by norm_num), one_mul]


-- @@ L90-92 verbatim
@[simp] theorem planeRotation_forward_endpoint (θ : ℝ) (x : E) :
    (planeRotation θ).forward 1 x = SO2FrameGauge.rotate θ x := by
  rw [planeRotation_forward, planeRotationAngle_one]


-- @@ L94-96 verbatim
@[simp] theorem planeRotation_inverse_endpoint (θ : ℝ) (x : E) :
    (planeRotation θ).inverse 1 x = SO2FrameGauge.rotate (-θ) x := by
  rw [planeRotation_inverse, planeRotationAngle_one]


-- @@ L98-98 verbatim
end SmoothAmbientIsotopy

-- @@ L99-99 verbatim
end Submission
