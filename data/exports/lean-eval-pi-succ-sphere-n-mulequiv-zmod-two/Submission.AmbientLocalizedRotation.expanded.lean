import Mathlib
import Submission.AmbientPlaneRotation


-- @@ L4-17 verbatim
/-!
# A compactly supported ambient rotation

A radial angle cutoff turns the global first-plane rotation into a relative
ambient move.  The cutoff is one on the unit ball and zero outside the ball of
squared radius two.  Because plane rotation preserves the full squared radius,
the inverse uses the same cutoff evaluated at the target point; hence it is
explicit and smooth.

This is a genuine locally supported `SmoothAmbientIsotopy`, not an existence
contract.  It supplies the standard way to alter one already-rounded orbit
inside a ball while fixing every previously normalized orbit outside that
ball.
-/


-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
open Set Function

-- @@ L22-22 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L24-24 verbatim
namespace Submission

-- @@ L25-25 verbatim
namespace SmoothAmbientIsotopy


-- @@ L27-27 verbatim
variable {m : ℕ}


-- @@ L29-29 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 2))


-- @@ L31-31 verbatim
/-! ## A radial smooth cutoff invariant under the rotation -/


-- @@ L33-36 verbatim
/-- Full squared radius, split into the first plane and the remaining
coordinates. -/
def localRadialSq (x : E) : ℝ :=
  x 0 ^ 2 + x 1 ^ 2 + ∑ i : Fin m, x i.succ.succ ^ 2


-- @@ L38-41 verbatim
theorem contDiff_localRadialSq :
    ContDiff ℝ ∞ (localRadialSq : E → ℝ) := by
  unfold localRadialSq
  fun_prop


-- @@ L43-45 verbatim
theorem localRadialSq_nonneg (x : E) : 0 ≤ localRadialSq x := by
  unfold localRadialSq
  positivity


-- @@ L47-70 verbatim
/-- The explicit first-plane rotation preserves the full squared radius. -/
@[simp] theorem localRadialSq_rotate (α : ℝ) (x : E) :
    localRadialSq (SO2FrameGauge.rotate α x) = localRadialSq x := by
  have htail : ∀ i : Fin m,
      SO2FrameGauge.rotate α x i.succ.succ = x i.succ.succ := by
    intro i
    apply SO2FrameGauge.rotate_apply_other
    · intro h
      have := congrArg Fin.val h
      simp at this
    · intro h
      have := congrArg Fin.val h
      simp at this
  unfold localRadialSq
  rw [SO2FrameGauge.rotate_apply_zero, SO2FrameGauge.rotate_apply_one]
  simp_rw [htail]
  calc
    (Real.cos α * x 0 - Real.sin α * x 1) ^ 2 +
          (Real.sin α * x 0 + Real.cos α * x 1) ^ 2 +
          ∑ i : Fin m, x i.succ.succ ^ 2 =
        (Real.sin α ^ 2 + Real.cos α ^ 2) * (x 0 ^ 2 + x 1 ^ 2) +
          ∑ i : Fin m, x i.succ.succ ^ 2 := by ring
    _ = x 0 ^ 2 + x 1 ^ 2 + ∑ i : Fin m, x i.succ.succ ^ 2 := by
      rw [Real.sin_sq_add_cos_sq, one_mul]


-- @@ L72-75 verbatim
/-- Radial cutoff: one on `localRadialSq ≤ 1`, zero on
`2 ≤ localRadialSq`. -/
def localRotationCutoff (x : E) : ℝ :=
  1 - Real.smoothTransition (localRadialSq x - 1)


-- @@ L77-80 verbatim
theorem contDiff_localRotationCutoff :
    ContDiff ℝ ∞ (localRotationCutoff : E → ℝ) := by
  exact contDiff_const.sub (Real.smoothTransition.contDiff.comp
    (contDiff_localRadialSq.sub contDiff_const))


-- @@ L82-85 verbatim
theorem localRotationCutoff_eq_one {x : E} (hx : localRadialSq x ≤ 1) :
    localRotationCutoff x = 1 := by
  rw [localRotationCutoff,
    Real.smoothTransition.zero_of_nonpos (by linarith), sub_zero]


-- @@ L87-90 verbatim
theorem localRotationCutoff_eq_zero {x : E} (hx : 2 ≤ localRadialSq x) :
    localRotationCutoff x = 0 := by
  rw [localRotationCutoff,
    Real.smoothTransition.one_of_one_le (by linarith), sub_self]


-- @@ L92-95 verbatim
@[simp] theorem localRotationCutoff_rotate (α : ℝ) (x : E) :
    localRotationCutoff (SO2FrameGauge.rotate α x) = localRotationCutoff x := by
  rw [localRotationCutoff, localRadialSq_rotate]
  rfl


-- @@ L97-97 verbatim
/-! ## The local ambient isotopy -/


-- @@ L99-101 verbatim
/-- Space-dependent rotation angle. -/
def localizedAngle (θ s : ℝ) (x : E) : ℝ :=
  normRamp s * θ * localRotationCutoff x


-- @@ L103-106 verbatim
theorem contDiff_localizedAngle (θ : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × E => localizedAngle θ p.1 p.2) := by
  exact ((contDiff_normRamp.comp contDiff_fst).mul contDiff_const).mul
    (contDiff_localRotationCutoff.comp contDiff_snd)


-- @@ L108-113 verbatim
/-- The local rotation is unchanged when its cutoff is evaluated after the
rotation itself. -/
@[simp] theorem localizedAngle_rotate (θ s α : ℝ) (x : E) :
    localizedAngle θ s (SO2FrameGauge.rotate α x) = localizedAngle θ s x := by
  rw [localizedAngle, localRotationCutoff_rotate]
  rfl


-- @@ L115-117 verbatim
/-- Forward map of the localized rotation. -/
def localizedForward (θ s : ℝ) (x : E) : E :=
  SO2FrameGauge.rotate (localizedAngle θ s x) x


-- @@ L119-121 verbatim
/-- Inverse map of the localized rotation. -/
def localizedInverse (θ s : ℝ) (x : E) : E :=
  SO2FrameGauge.rotate (-(localizedAngle θ s x)) x


-- @@ L123-129 verbatim
theorem contDiff_localizedForward (θ : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × E => localizedForward θ p.1 p.2) := by
  have hpair : ContDiff ℝ ∞
      (fun p : ℝ × E => (localizedAngle θ p.1 p.2, p.2)) :=
    (contDiff_localizedAngle θ).prodMk contDiff_snd
  simpa [localizedForward, Function.comp_def] using
    SO2FrameGauge.contDiff_rotate.comp hpair


-- @@ L131-137 verbatim
theorem contDiff_localizedInverse (θ : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × E => localizedInverse θ p.1 p.2) := by
  have hpair : ContDiff ℝ ∞
      (fun p : ℝ × E => (-(localizedAngle θ p.1 p.2), p.2)) :=
    (contDiff_localizedAngle θ).neg.prodMk contDiff_snd
  simpa [localizedInverse, Function.comp_def] using
    SO2FrameGauge.contDiff_rotate.comp hpair


-- @@ L139-145 verbatim
theorem localized_leftInverse (θ s : ℝ) :
    LeftInverse (localizedInverse (m := m) θ s)
      (localizedForward (m := m) θ s) := by
  intro x
  rw [localizedInverse, localizedForward,
    localizedAngle_rotate (m := m)]
  exact SO2FrameGauge.rotate_neg_apply (localizedAngle θ s x) x


-- @@ L147-153 verbatim
theorem localized_rightInverse (θ s : ℝ) :
    RightInverse (localizedInverse (m := m) θ s)
      (localizedForward (m := m) θ s) := by
  intro x
  rw [localizedInverse, localizedForward,
    localizedAngle_rotate (m := m)]
  exact SO2FrameGauge.rotate_apply_neg (localizedAngle θ s x) x


-- @@ L155-200 verbatim
/-- Rotation through `θ` on the inner ball, tapering smoothly to the identity
before squared radius two. -/
def localizedPlaneRotation (θ : ℝ) : SmoothAmbientIsotopy (m + 1) where
  forward := localizedForward (m := m) θ
  inverse := localizedInverse (m := m) θ
  forward_smooth := contDiff_localizedForward (m := m) θ
  inverse_smooth := contDiff_localizedInverse (m := m) θ
  forward_zero := by
    funext x
    rw [localizedForward, localizedAngle,
      normRamp_of_le_quarter (show (0 : ℝ) ≤ 1 / 4 by norm_num), zero_mul,
      zero_mul, SO2FrameGauge.rotate_zero]
    rfl
  left_inv := fun s _ => localized_leftInverse (m := m) θ s
  right_inv := fun s _ => localized_rightInverse (m := m) θ s
  inverse_fderiv_surjective := by
    intro s hs x
    let f : E → E := localizedForward (m := m) θ s
    let g : E → E := localizedInverse (m := m) θ s
    have hf : ContDiff ℝ ∞ f := by
      exact (contDiff_localizedForward (m := m) θ).comp
        (contDiff_const.prodMk contDiff_id)
    have hg : ContDiff ℝ ∞ g := by
      exact (contDiff_localizedInverse (m := m) θ).comp
        (contDiff_const.prodMk contDiff_id)
    let y : E := g x
    have hfy : f y = x := by
      exact localized_rightInverse (m := m) θ s x
    have hgf : (fun z => g (f z)) = id := by
      funext z
      exact localized_leftInverse (m := m) θ s z
    have hcomp : HasFDerivAt (fun z => g (f z))
        ((fderiv ℝ g (f y)).comp (fderiv ℝ f y)) y :=
      ((hg.differentiable (by simp) (f y)).hasFDerivAt.comp y
        (hf.differentiable (by simp) y).hasFDerivAt)
    rw [hgf] at hcomp
    have hderiv0 : (fderiv ℝ g (f y)).comp (fderiv ℝ f y) =
        ContinuousLinearMap.id ℝ E :=
      hcomp.fderiv.symm.trans (hasFDerivAt_id y).fderiv
    have hderiv : (fderiv ℝ g x).comp (fderiv ℝ f y) =
        ContinuousLinearMap.id ℝ E := by
      rwa [hfy] at hderiv0
    intro z
    refine ⟨fderiv ℝ f y z, ?_⟩
    have hz := congrArg (fun L : E →L[ℝ] E => L z) hderiv
    simpa [ContinuousLinearMap.comp_apply] using hz


-- @@ L202-205 verbatim
@[simp] theorem localizedPlaneRotation_forward (θ s : ℝ) (x : E) :
    (localizedPlaneRotation (m := m) θ).forward s x =
      SO2FrameGauge.rotate (localizedAngle θ s x) x :=
  rfl


-- @@ L207-212 verbatim
/-- Outside squared radius two the whole isotopy is literally stationary. -/
theorem localizedPlaneRotation_fixed_of_two_le
    (θ s : ℝ) {x : E} (hx : 2 ≤ localRadialSq x) :
    (localizedPlaneRotation (m := m) θ).forward s x = x := by
  rw [localizedPlaneRotation_forward, localizedAngle,
    localRotationCutoff_eq_zero hx, mul_zero, SO2FrameGauge.rotate_zero]


-- @@ L214-219 verbatim
/-- Relative form of the support statement, ready for finite composition. -/
theorem localizedPlaneRotation_fixedOn (θ : ℝ) :
    (localizedPlaneRotation (m := m) θ).FixedOn
      {x : E | 2 ≤ localRadialSq x} := by
  intro s hs x hx
  exact localizedPlaneRotation_fixed_of_two_le θ s hx


-- @@ L221-228 verbatim
/-- On the unit ball, the endpoint is the full prescribed rotation. -/
theorem localizedPlaneRotation_endpoint_of_le_one
    (θ : ℝ) {x : E} (hx : localRadialSq x ≤ 1) :
    (localizedPlaneRotation (m := m) θ).forward 1 x =
      SO2FrameGauge.rotate θ x := by
  rw [localizedPlaneRotation_forward, localizedAngle,
    normRamp_of_three_quarter_le (show (3 / 4 : ℝ) ≤ 1 by norm_num), one_mul,
    localRotationCutoff_eq_one hx, mul_one]


-- @@ L230-230 verbatim
end SmoothAmbientIsotopy

-- @@ L231-231 verbatim
end Submission
