import Mathlib
import Submission.CompactBirthConfiguration
import Submission.ExplicitOrbitParam
import Submission.FlatConfigurationAssembly
import Submission.TubeFrameClass
import Submission.TubeBridgeValues


-- @@ L8-31 verbatim
/-!
# A compact defining map for the untwisted standard tube circle

The tempting interpolation

`tubeCutoff x • wCoord k x + (1 - tubeCutoff x) • b`

cannot have only the standard circle as its zero set.  On the normal ray
`w = -a b`, its last scalar coordinate changes sign between the region where
the cutoff is one and the region where it is zero.  Increasing the coefficient
of `b` does not remove this intermediate zero.

For the untwisted circle there is a simple correction.  We use the polynomial
radial equation `x₀² + x₁² - 1`, put the nonzero background in that same output
coordinate, and switch to the background only when the *ambient* squared norm
is at least two.  At a putative zero all transverse coordinates vanish.  Thus
the ambient squared norm is the radial squared norm, and throughout the
transition annulus both the radial equation and the background term are
nonnegative (one is strictly positive).  No transition zero can occur.

The resulting map is exactly flat outside the radius-two ball, has zero fiber
`standardCircle`, and its differential along the circle induces the twist-zero
normal frame.
-/


-- @@ L33-33 verbatim
noncomputable section


-- @@ L35-35 verbatim
namespace Submission

-- @@ L36-36 verbatim
namespace CompactTubeConfiguration


-- @@ L38-38 verbatim
open Set Function Metric InnerProductSpace

-- @@ L39-39 verbatim
open scoped RealInnerProductSpace ContDiff Topology Matrix unitInterval


-- @@ L41-41 verbatim
variable (m : ℕ)


-- @@ L43-43 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 3))

-- @@ L44-44 verbatim
local notation "F" => EuclideanSpace ℝ (Fin (m + 2))


-- @@ L46-49 verbatim
/-- The common nonzero value outside the compact region.  It is placed in the
same output coordinate as the radial equation. -/
def background : F :=
  WithLp.toLp 2 fun i => if i = 0 then 1 else 0


-- @@ L51-52 verbatim
@[simp] theorem background_apply_zero : background m 0 = 1 := by
  simp [background]


-- @@ L54-56 verbatim
@[simp] theorem background_apply_ne_zero {i : Fin (m + 2)} (hi : i ≠ 0) :
    background m i = 0 := by
  simp [background, hi]


-- @@ L58-61 verbatim
theorem background_ne_zero : background m ≠ 0 := by
  intro h
  have h0 := congrArg (fun q : F => q 0) h
  simp at h0


-- @@ L63-67 verbatim
/-- Polynomial defining map of the unit circle in the first coordinate plane.
The output row zero is radial and row `i ≠ 0` is ambient coordinate `i+1`. -/
def coreMap (x : E) : F :=
  WithLp.toLp 2 fun i =>
    if i = 0 then (radSq x - 1) / 2 else x i.succ


-- @@ L69-71 verbatim
@[simp] theorem coreMap_apply_zero (x : E) :
    coreMap m x 0 = (radSq x - 1) / 2 := by
  simp [coreMap]


-- @@ L73-75 verbatim
@[simp] theorem coreMap_apply_ne_zero (x : E) {i : Fin (m + 2)} (hi : i ≠ 0) :
    coreMap m x i = x i.succ := by
  simp [coreMap, hi]


-- @@ L77-86 verbatim
theorem contDiff_coreMap : ContDiff ℝ ∞ (coreMap m) := by
  rw [contDiff_piLp]
  intro i
  by_cases hi : i = 0
  · subst i
    simpa only [coreMap_apply_zero] using
      ((contDiff_radSq (m := m)).sub contDiff_const).div_const 2
  · simp only [coreMap_apply_ne_zero m _ hi]
    change ContDiff ℝ ∞ (EuclideanSpace.proj i.succ : E → ℝ)
    exact (EuclideanSpace.proj i.succ : E →L[ℝ] ℝ).contDiff


-- @@ L88-91 verbatim
/-- Ambient-norm compactification of the untwisted circle equation. -/
def levelMap (x : E) : F :=
  (1 - CompactBirth.cutoff x) • coreMap m x +
    CompactBirth.cutoff x • background m


-- @@ L93-96 verbatim
theorem contDiff_levelMap : ContDiff ℝ ∞ (levelMap m) := by
  exact ((contDiff_const.sub CompactBirth.contDiff_cutoff).smul
    (contDiff_coreMap m)).add
    (CompactBirth.contDiff_cutoff.smul contDiff_const)


-- @@ L98-102 verbatim
@[simp] theorem levelMap_apply_zero (x : E) :
    levelMap m x 0 =
      (1 - CompactBirth.cutoff x) * ((radSq x - 1) / 2) +
        CompactBirth.cutoff x := by
  simp [levelMap]


-- @@ L104-106 verbatim
@[simp] theorem levelMap_apply_ne_zero (x : E) {i : Fin (m + 2)} (hi : i ≠ 0) :
    levelMap m x i = (1 - CompactBirth.cutoff x) * x i.succ := by
  simp [levelMap, hi]


-- @@ L108-113 verbatim
theorem cutoff_ne_one_of_levelMap_eq_zero {x : E}
    (hx : levelMap m x = 0) : CompactBirth.cutoff x ≠ 1 := by
  intro hc
  have h0 := congrArg (fun q : F => q 0) hx
  rw [levelMap_apply_zero, hc] at h0
  norm_num at h0


-- @@ L115-118 verbatim
theorem cutoff_lt_one_of_levelMap_eq_zero {x : E}
    (hx : levelMap m x = 0) : CompactBirth.cutoff x < 1 :=
  lt_of_le_of_ne (CompactBirth.cutoff_le_one x)
    (cutoff_ne_one_of_levelMap_eq_zero m hx)


-- @@ L120-127 verbatim
theorem transverse_eq_zero_of_levelMap_eq_zero {x : E}
    (hx : levelMap m x = 0) {i : Fin (m + 2)} (hi : i ≠ 0) :
    x i.succ = 0 := by
  have hout := congrArg (fun q : F => q i) hx
  rw [levelMap_apply_ne_zero m x hi] at hout
  simp only [PiLp.zero_apply] at hout
  exact (mul_eq_zero.mp hout).resolve_left
    (sub_ne_zero.mpr (cutoff_lt_one_of_levelMap_eq_zero m hx).ne')


-- @@ L129-143 verbatim
/-- At a zero, all coordinates outside the circle plane vanish, so the ambient
squared norm is exactly `radSq`. -/
theorem normSq_eq_radSq_of_levelMap_eq_zero {x : E}
    (hx : levelMap m x = 0) : CompactBirth.normSq x = radSq x := by
  unfold CompactBirth.normSq radSq
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  simp only [Fin.succ_zero_eq_one]
  have htail : ∀ i : Fin (m + 1), x i.succ.succ ^ 2 = 0 := by
    intro i
    let j : Fin (m + 2) := i.succ
    have hj : j ≠ 0 := Fin.succ_ne_zero i
    have hz : x j.succ = 0 := transverse_eq_zero_of_levelMap_eq_zero m hx hj
    simpa [j, hz]
  simp only [htail, Finset.sum_const_zero, add_zero]


-- @@ L145-211 verbatim
/-- The compactification adds no zero: its fiber is exactly the geometric
standard circle. -/
theorem levelMap_eq_zero_iff_standardCircle (x : E) :
    levelMap m x = 0 ↔ x ∈ standardCircle := by
  constructor
  · intro hx
    have hc_lt := cutoff_lt_one_of_levelMap_eq_zero m hx
    have hnorm := normSq_eq_radSq_of_levelMap_eq_zero m hx
    have h0 := congrArg (fun q : F => q 0) hx
    rw [levelMap_apply_zero] at h0
    simp only [PiLp.zero_apply] at h0
    have hrs_lt : radSq x < 2 := by
      by_contra hnot
      have hrs_ge : 2 ≤ radSq x := not_lt.mp hnot
      have hc0 := CompactBirth.cutoff_nonneg x
      have hfac : 0 < 1 - CompactBirth.cutoff x := sub_pos.mpr hc_lt
      nlinarith
    have hc0 : CompactBirth.cutoff x = 0 := by
      apply CompactBirth.cutoff_eq_zero
      rw [hnorm]
      exact hrs_lt.le
    rw [hc0] at h0
    norm_num at h0
    have hrs : radSq x = 1 := by linarith
    have hgood : x ∈ tubeGood := by
      change 0 < radSq x
      rw [hrs]
      norm_num
    apply (wCoord_eq_zero_iff_standardCircle (m := m) 0 hgood).mp
    apply PiLp.ext
    intro i
    by_cases hi : i = 0
    · subst i
      rw [wCoord_apply_zero, cosK, sinK, rotP_zero]
      simp only [Prod.fst, Prod.snd, one_mul, zero_mul, zero_add]
      have hr : rad x = 1 := by
        rw [rad, hrs, Real.sqrt_one]
      simp [hr]
    · by_cases hil : i = Fin.last (m + 1)
      · rw [hil, wCoord_apply_last, cosK, sinK, rotP_zero]
        simp only [Prod.fst, Prod.snd, one_mul, zero_mul, sub_zero]
        exact transverse_eq_zero_of_levelMap_eq_zero m hx
          (by exact lastW_ne_zero)
      · rw [wCoord_apply_mid 0 x hi hil]
        exact transverse_eq_zero_of_levelMap_eq_zero m hx hi
  · rintro ⟨theta, rfl⟩
    have hnorm : CompactBirth.normSq (circleAt (m := m) theta) = 1 := by
      rw [CompactBirth.normSq_eq_norm_sq, norm_circleAt, one_pow]
    have hc : CompactBirth.cutoff (circleAt (m := m) theta) = 0 :=
      CompactBirth.cutoff_eq_zero (by linarith)
    rw [levelMap, hc]
    simp only [sub_zero, one_smul, zero_smul, add_zero]
    apply PiLp.ext
    intro i
    by_cases hi : i = 0
    · subst i
      simp [coreMap, radSq_circleAt]
    · rw [coreMap_apply_ne_zero m _ hi]
      apply circleAt_apply_other theta
      · exact Fin.succ_ne_zero i
      · intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_succ, Fin.val_one] at hv
        apply hi
        apply Fin.ext
        simp only [Fin.val_zero]
        omega


-- @@ L213-220 verbatim
theorem levelMap_eventuallyEq_coreMap {x : E}
    (hx : CompactBirth.normSq x < 2) :
    levelMap m =ᶠ[nhds x] coreMap m := by
  have hopen : IsOpen {y : E | CompactBirth.normSq y < 2} :=
    isOpen_lt CompactBirth.contDiff_normSq.continuous continuous_const
  exact Filter.eventuallyEq_of_mem (hopen.mem_nhds hx) fun y hy => by
    rw [levelMap, CompactBirth.cutoff_eq_zero hy.le]
    simp


-- @@ L222-222 verbatim
/-! ## Differential of the polynomial core -/


-- @@ L224-226 verbatim
/-- The exact normal-slice expression of `coreMap`. -/
def normalModel (w : F) : F :=
  w + (w 0 ^ 2 / 2) • EuclideanSpace.single 0 1


-- @@ L228-251 verbatim
theorem coreMap_normalSlice (theta : ℝ) (w : F) :
    coreMap m (normalSlice 0 theta w) = normalModel m w := by
  apply PiLp.ext
  intro i
  by_cases hi : i = 0
  · subst i
    rw [coreMap_apply_zero]
    unfold radSq normalSlice
    rw [tubeMap_apply_zero, tubeMap_apply_one]
    simp only [tubeA, Nat.cast_zero, zero_mul, Real.cos_zero, Real.sin_zero,
      mul_one, mul_zero, sub_zero]
    simp [normalModel, PiLp.single_apply]
    nlinarith [Real.sin_sq_add_cos_sq theta]
  · rw [coreMap_apply_ne_zero m _ hi]
    by_cases hil : i = Fin.last (m + 1)
    · subst i
      have hs : ((Fin.last (m + 1)).succ : Fin (m + 3)) =
          Fin.last (m + 2) := by
        apply Fin.ext
        simp
      rw [normalSlice, hs, tubeMap_apply_last]
      simp [tubeB, normalModel, PiLp.single_apply, lastW_ne_zero]
    · rw [normalSlice, tubeMap_apply_mid 0 theta w hi hil]
      simp [normalModel, PiLp.single_apply, hi]


-- @@ L253-277 verbatim
theorem hasFDerivAt_normalModel_zero :
    HasFDerivAt (normalModel m) (ContinuousLinearMap.id ℝ F) 0 := by
  let p : F →L[ℝ] ℝ := EuclideanSpace.proj 0
  have hp : HasFDerivAt (fun w : F => w 0) p 0 := by
    change HasFDerivAt (p : F → ℝ) p 0
    exact p.hasFDerivAt
  have hsq : HasFDerivAt (fun w : F => w 0 ^ 2 / 2)
      (0 : F →L[ℝ] ℝ) (0 : F) := by
    have hsq' : HasFDerivAt (fun w : F => (1 / 2 : ℝ) * w 0 ^ 2)
        (0 : F →L[ℝ] ℝ) (0 : F) := by
      simpa using (hp.pow 2).const_mul (1 / 2 : ℝ)
    convert hsq' using 1
    funext w
    ring
  unfold normalModel
  have hadd := (hasFDerivAt_id (𝕜 := ℝ) (0 : F)).add
    (hsq.smul_const (EuclideanSpace.single (0 : Fin (m + 2)) 1))
  have hder : ContinuousLinearMap.id ℝ F +
      (0 : F →L[ℝ] ℝ).smulRight
        (EuclideanSpace.single (0 : Fin (m + 2)) 1) =
      ContinuousLinearMap.id ℝ F := by simp
  rw [hder] at hadd
  apply hadd.congr_of_eventuallyEq
  filter_upwards with w
  rfl


-- @@ L279-296 verbatim
/-- The derivative of `coreMap` has the declared twist-zero normal frame as a
right inverse along the circle. -/
theorem fderiv_coreMap_comp_normalSumCLM (theta : ℝ) :
    (fderiv ℝ (coreMap m) (circleAt theta)).comp (normalSumCLM 0 theta) =
      ContinuousLinearMap.id ℝ F := by
  have hcore : HasFDerivAt (coreMap m)
      (fderiv ℝ (coreMap m) (circleAt theta)) (normalSlice 0 theta 0) := by
    simpa only [normalSlice_zero] using
      ((contDiff_coreMap m).differentiable (by simp) (circleAt theta)).hasFDerivAt
  have hcomp := hcore.comp (0 : F) (hasFDerivAt_normalSlice 0 theta 0)
  have heq : (coreMap m ∘ normalSlice 0 theta) = normalModel m := by
    funext w
    exact coreMap_normalSlice m theta w
  have hsame : HasFDerivAt (coreMap m ∘ normalSlice 0 theta)
      (ContinuousLinearMap.id ℝ F) 0 := by
    rw [heq]
    exact hasFDerivAt_normalModel_zero m
  exact hcomp.unique hsame


-- @@ L298-304 verbatim
theorem fderiv_coreMap_nuVec (theta : ℝ) (i : Fin (m + 2)) :
    fderiv ℝ (coreMap m) (circleAt theta) (nuVec 0 theta i) =
      EuclideanSpace.single i 1 := by
  have h := congrArg (fun L : F →L[ℝ] F =>
      L (EuclideanSpace.single i 1))
    (fderiv_coreMap_comp_normalSumCLM m theta)
  simpa [normalSumCLM_single] using h


-- @@ L306-312 verbatim
theorem surjective_fderiv_coreMap_circleAt (theta : ℝ) :
    Function.Surjective (fderiv ℝ (coreMap m) (circleAt theta)) := by
  intro y
  refine ⟨normalSumCLM 0 theta y, ?_⟩
  have h := congrArg (fun L : F →L[ℝ] F => L y)
    (fderiv_coreMap_comp_normalSumCLM m theta)
  exact h


-- @@ L314-335 verbatim
/-- The compact untwisted standard circle as a genuine framed level set. -/
def X : FramedLevelSet (m + 2) where
  g := levelMap m
  smooth := contDiff_levelMap m
  fiber_bounded := by
    have heq : {x : E | levelMap m x = 0} = standardCircle := by
      ext x
      exact levelMap_eq_zero_iff_standardCircle m x
    rw [heq]
    apply (Metric.isBounded_closedBall (x := (0 : E)) (r := 1)).subset
    rintro x ⟨theta, rfl⟩
    rw [mem_closedBall, dist_zero_right, norm_circleAt]
  regular := by
    intro x hx
    have hcircle : x ∈ standardCircle :=
      (levelMap_eq_zero_iff_standardCircle m x).mp hx
    obtain ⟨theta, rfl⟩ := hcircle
    have hnorm : CompactBirth.normSq (circleAt (m := m) theta) < 2 := by
      rw [CompactBirth.normSq_eq_norm_sq, norm_circleAt, one_pow]
      norm_num
    rw [(levelMap_eventuallyEq_coreMap m hnorm).fderiv_eq]
    exact surjective_fderiv_coreMap_circleAt m theta


-- @@ L337-340 verbatim
/-- Exact geometric fiber statement for the packaged level set. -/
theorem X_fiber : (X m).fiber = standardCircle := by
  ext x
  exact levelMap_eq_zero_iff_standardCircle m x


-- @@ L342-351 verbatim
/-- The presentation is literally constant outside the radius-two ball. -/
theorem flatOutside :
    (X m).FlatOutside (background m) 0 2 := by
  intro x hx
  have hn : 2 ≤ ‖x‖ := by simpa [dist_zero_right] using hx
  have hs : 4 ≤ CompactBirth.normSq x := by
    rw [CompactBirth.normSq_eq_norm_sq]
    nlinarith [norm_nonneg x]
  have hc := CompactBirth.cutoff_eq_one hs
  simp [X, levelMap, hc]


-- @@ L353-357 verbatim
/-- Constant-positive labeling of the unique circle. -/
def positiveSign : FiberSign (X m) where
  toFun := fun _ => 1
  continuous := continuous_const
  nonzero := by simp


-- @@ L359-363 verbatim
/-- Constant-negative labeling of the unique circle. -/
def negativeSign : FiberSign (X m) where
  toFun := fun _ => -1
  continuous := continuous_const
  nonzero := by simp


-- @@ L365-365 verbatim
/-! ## The actual derivative frame -/


-- @@ L367-374 verbatim
theorem fderiv_levelMap_nuVec (theta : ℝ) (i : Fin (m + 2)) :
    fderiv ℝ (levelMap m) (circleAt theta) (nuVec 0 theta i) =
      EuclideanSpace.single i 1 := by
  have hnorm : CompactBirth.normSq (circleAt (m := m) theta) < 2 := by
    rw [CompactBirth.normSq_eq_norm_sq, norm_circleAt, one_pow]
    norm_num
  rw [(levelMap_eventuallyEq_coreMap m hnorm).fderiv_eq]
  exact fderiv_coreMap_nuVec m theta i


-- @@ L376-394 verbatim
theorem fderiv_levelMap_tangentAt (theta : ℝ) :
    fderiv ℝ (levelMap m) (circleAt theta) (tangentAt theta) = 0 := by
  let g := levelMap m
  have hg : DifferentiableAt ℝ g (circleAt (m := m) theta) :=
    (contDiff_levelMap m).differentiable (by simp) |>.differentiableAt
  have hc : DifferentiableAt ℝ (circleAt (m := m)) theta :=
    contDiff_circleAt.differentiable (by simp) |>.differentiableAt
  have hcomp := fderiv_comp (x := theta) hg hc
  have happ := congrArg
    (fun L : ℝ →L[ℝ] F => L 1) hcomp
  have hzero : fderiv ℝ (g ∘ circleAt (m := m)) theta 1 = 0 := by
    have heq : g ∘ circleAt (m := m) = fun _ : ℝ => (0 : F) := by
      funext t
      exact (levelMap_eq_zero_iff_standardCircle m _).mpr
        (circleAt_mem_standardCircle t)
    rw [heq]
    simp
  rw [hzero, ContinuousLinearMap.comp_apply, fderiv_circleAt_one] at happ
  exact happ.symm


-- @@ L396-411 verbatim
theorem gradVec_levelMap_circleAt (theta : ℝ) (i : Fin (m + 2)) :
    gradVec (levelMap m) i (circleAt theta) = nuVec 0 theta i := by
  apply ext_inner_right_basis (tubeFullONBasis m 0 theta).toBasis
  intro j
  change ⟪gradVec (levelMap m) i (circleAt theta),
      tubeFullONBasis m 0 theta j⟫_ℝ =
    ⟪nuVec 0 theta i, tubeFullONBasis m 0 theta j⟫_ℝ
  rw [tubeFullONBasis_apply]
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
  · rw [tubeFullFrame, Fin.cons_zero, inner_gradVec,
      map_neg, fderiv_levelMap_tangentAt, neg_zero,
      inner_neg_right, inner_nuVec_tangentAt, neg_zero]
    rfl
  · rw [tubeFullFrame, Fin.cons_succ, inner_gradVec,
      fderiv_levelMap_nuVec, inner_nuVec_nuVec]
    simp [PiLp.single_apply]


-- @@ L413-418 verbatim
theorem kerCross_levelMap_circleAt (theta : ℝ) :
    kerCross (levelMap m) (circleAt theta) = -(tangentAt theta) := by
  rw [kerCross, show (fun i => gradVec (levelMap m) i (circleAt theta)) =
      nuVec (m := m) 0 theta from
    funext fun i => gradVec_levelMap_circleAt m theta i]
  exact crossVec_nuVec m 0 theta


-- @@ L420-423 verbatim
theorem tauField_levelMap_circleAt (theta : ℝ) :
    tauField (levelMap m) (circleAt theta) = -(tangentAt theta) := by
  rw [tauField, kerCross_levelMap_circleAt, norm_neg, norm_tangentAt,
    inv_one, one_smul]


-- @@ L425-430 verbatim
theorem frameAt_X_circleAt (theta : ℝ) :
    frameAt (X m) (circleAt theta) = tubeFullFrame m 0 theta := by
  funext i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
  · simp [frameAt, X, tubeFullFrame, tauField_levelMap_circleAt]
  · simp [frameAt, X, tubeFullFrame, gradVec_levelMap_circleAt]


-- @@ L432-435 verbatim
theorem gramSchmidtNormed_frameAt_X_circleAt (theta : ℝ) :
    gramSchmidtNormed ℝ (frameAt (X m) (circleAt theta)) =
      tubeFullFrame m 0 theta := by
  rw [frameAt_X_circleAt, gramSchmidtNormed_tubeFullFrame]


-- @@ L437-437 verbatim
/-! ## Intrinsic orbit class and delta -/


-- @@ L439-443 verbatim
/-- Counterclockwise once-around parametrization of the geometric circle. -/
def circleCurve : C(I, E) where
  toFun u := circleAt (m := m) (2 * Real.pi * (u : ℝ))
  continuous_toFun := contDiff_circleAt.continuous.comp
    ((continuous_const.mul continuous_const).mul continuous_subtype_val)


-- @@ L445-446 verbatim
@[simp] theorem circleCurve_zero : circleCurve m 0 = circleAt (m := m) 0 := by
  simp [circleCurve]


-- @@ L448-457 verbatim
theorem circleCurve_closed : circleCurve m 0 = circleCurve m 1 := by
  apply PiLp.ext
  intro i
  by_cases hi0 : i = 0
  · subst i
    simp [circleCurve]
  · by_cases hi1 : i = 1
    · subst i
      simp [circleCurve]
    · simp [circleCurve, circleAt_apply_other _ hi0 hi1]


-- @@ L459-470 verbatim
theorem circleAt_eq_iff_mod {theta theta' : ℝ}
    (h : circleAt (m := m) theta = circleAt theta') :
    ∃ z : ℤ, theta' = theta + (z : ℝ) * (2 * Real.pi) := by
  have hcos : Real.cos theta = Real.cos theta' := by
    simpa using congrArg (fun x : E => x 0) h
  have hsin : Real.sin theta = Real.sin theta' := by
    simpa using congrArg (fun x : E => x 1) h
  have hone : Real.cos (theta' - theta) = 1 := by
    rw [Real.cos_sub, ← hcos, ← hsin]
    linear_combination Real.sin_sq_add_cos_sq theta
  obtain ⟨z, hz⟩ := (Real.cos_eq_one_iff _).mp hone
  exact ⟨z, by linarith⟩


-- @@ L472-511 verbatim
theorem circleCurve_eq_cases {u v : I} (huv : circleCurve m u = circleCurve m v) :
    u = v ∨ (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) := by
  obtain ⟨z, hz⟩ := circleAt_eq_iff_mod (m := m) huv
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have huvZ : (v : ℝ) = (u : ℝ) + (z : ℝ) := by
    change 2 * Real.pi * (v : ℝ) =
      2 * Real.pi * (u : ℝ) + (z : ℝ) * (2 * Real.pi) at hz
    nlinarith
  have hzLowerR : (-1 : ℝ) ≤ (z : ℝ) := by
    nlinarith [u.2.2, v.2.1]
  have hzUpperR : (z : ℝ) ≤ 1 := by
    nlinarith [u.2.1, v.2.2]
  have hzLower : (-1 : ℤ) ≤ z := by exact_mod_cast hzLowerR
  have hzUpper : z ≤ (1 : ℤ) := by exact_mod_cast hzUpperR
  rcases (show z = -1 ∨ z = 0 ∨ z = 1 by omega) with hzv | hzv | hzv
  · right; right
    constructor <;> apply Subtype.ext
    · change (u : ℝ) = 1
      rw [hzv] at huvZ
      norm_num at huvZ
      nlinarith [u.2.2, v.2.1]
    · change (v : ℝ) = 0
      rw [hzv] at huvZ
      norm_num at huvZ
      nlinarith [u.2.2, v.2.1]
  · left
    apply Subtype.ext
    rw [hzv] at huvZ
    norm_num at huvZ
    exact huvZ.symm
  · right; left
    constructor <;> apply Subtype.ext
    · change (u : ℝ) = 0
      rw [hzv] at huvZ
      norm_num at huvZ
      nlinarith [u.2.1, v.2.2]
    · change (v : ℝ) = 1
      rw [hzv] at huvZ
      norm_num at huvZ
      nlinarith [u.2.1, v.2.2]


-- @@ L513-516 verbatim
theorem circleAt_mem_X_fiber (theta : ℝ) :
    circleAt (m := m) theta ∈ (X m).fiber := by
  rw [X_fiber]
  exact circleAt_mem_standardCircle theta


-- @@ L518-521 verbatim
theorem circleAt_mem_orbit (V : TamedField (X m)) (theta : ℝ) :
    circleAt (m := m) theta ∈ V.orbit (circleAt (m := m) 0) := by
  exact V.continuousCurve_mem_orbit (circleAt (m := m))
    contDiff_circleAt.continuous (circleAt_mem_X_fiber m) theta


-- @@ L523-531 verbatim
def simpleClosedOrbitParam (V : TamedField (X m)) :
    SimpleClosedOrbitParam (X m) V where
  p := circleAt (m := m) 0
  hp := circleAt_mem_X_fiber m 0
  curve := circleCurve m
  curve_zero := circleCurve_zero m
  curve_closed := circleCurve_closed m
  curve_mem_orbit := fun u => circleAt_mem_orbit m V _
  curve_eq_cases := circleCurve_eq_cases m


-- @@ L533-544 verbatim
theorem paramFrameLoop_eq_tubeFrameLoop (V : TamedField (X m)) :
    (simpleClosedOrbitParam m V).paramFrameLoop = tubeFrameLoop m 0 := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  change frameLoop (X m) (simpleClosedOrbitParam m V).realCurve (u : ℝ) =
    rowsMatrix (tubeFullFrame m 0 (2 * Real.pi * (u : ℝ)))
  unfold frameLoop
  rw [(simpleClosedOrbitParam m V).realCurve_coe]
  change rowsMatrix (gramSchmidtNormed ℝ
    (frameAt (X m) (circleAt (2 * Real.pi * (u : ℝ))))) = _
  rw [gramSchmidtNormed_frameAt_X_circleAt]


-- @@ L546-567 verbatim
theorem orbitFrameClass_eq_one (V : TamedField (X m)) (O : V.OrbitIndex) :
    V.orbitFrameClass O = 1 := by
  let p : E := circleAt (m := m) 0
  let hp : p ∈ (X m).fiber := circleAt_mem_X_fiber m 0
  have hpoint : V.orbitPoint O ∈ V.orbit p := by
    have hmem := V.orbitPoint_mem_fiber O
    rw [X_fiber] at hmem
    obtain ⟨theta, htheta⟩ := hmem
    rw [← htheta]
    exact circleAt_mem_orbit m V theta
  calc
    V.orbitFrameClass O =
        V.fundamentalFrameClass (V.orbitPoint_mem_fiber O) := rfl
    _ = V.fundamentalFrameClass hp :=
      V.fundamentalFrameClass_eq_of_mem_orbit hp hpoint
    _ = loopClassZ2 (simpleClosedOrbitParam m V).paramFrameLoop
        (simpleClosedOrbitParam m V).paramFrameLoop_closed :=
      ((simpleClosedOrbitParam m V).paramFrameClass_eq_fundamental).symm
    _ = loopClassZ2 (tubeFrameLoop m 0) (tubeFrameLoop_closed m 0) := by
      apply loopClassZ2_congr_fun
      exact paramFrameLoop_eq_tubeFrameLoop m V
    _ = 1 := by simpa using loopClassZ2_tubeFrameLoop m 0


-- @@ L569-573 verbatim
theorem orbitContribution_eq_zero (V : TamedField (X m)) (O : V.OrbitIndex) :
    V.orbitContribution O = 0 := by
  unfold TamedField.orbitContribution
  rw [orbitFrameClass_eq_one]
  decide


-- @@ L575-584 verbatim
@[simp] theorem positiveSign_positiveDelta_eq_zero :
    (positiveSign m).positiveDelta = 0 := by
  let V : TamedField (X m) := (X m).exists_tamedField.some
  rw [(positiveSign m).positiveDelta_eq V]
  unfold FiberSign.positiveFramedDelta TamedField.deltaOn
  apply Fintype.sum_eq_zero
  intro O
  split_ifs
  · exact orbitContribution_eq_zero m V O
  · rfl


-- @@ L586-593 verbatim
@[simp] theorem negativeSign_negativeDelta_eq_zero :
    (negativeSign m).negativeDelta = 0 := by
  change (negativeSign m).neg.positiveDelta = 0
  have heq : (negativeSign m).neg = positiveSign m := by
    apply FiberSign.eq_of_toFun_eq
    funext x
    simp [negativeSign, positiveSign]
  rw [heq, positiveSign_positiveDelta_eq_zero]


-- @@ L595-595 verbatim
/-! ## Ready-to-assemble class-one pieces -/


-- @@ L597-597 verbatim
abbrev field : TamedField (X m) := (X m).exists_tamedField.some


-- @@ L599-602 verbatim
def circleOrbit : (field m).OrbitIndex :=
  ⟨(field m).orbit (circleAt (m := m) 0),
    (field m).mem_orbitFinset.mpr
      ⟨circleAt (m := m) 0, circleAt_mem_X_fiber m 0, rfl⟩⟩


-- @@ L604-616 verbatim
theorem orbitIndex_eq_circleOrbit (O : (field m).OrbitIndex) :
    O = circleOrbit m := by
  have hpoint : (field m).orbitPoint O ∈
      (field m).orbit (circleAt (m := m) 0) := by
    have hmem := (field m).orbitPoint_mem_fiber O
    rw [X_fiber] at hmem
    obtain ⟨theta, htheta⟩ := hmem
    rw [← htheta]
    exact circleAt_mem_orbit m (field m) theta
  apply Subtype.ext
  rw [(field m).orbitPoint_orbit O]
  apply (field m).orbit_eq_of_mem
  exact hpoint


-- @@ L618-620 verbatim
@[simp] theorem circleOrbit_frameClass :
    (field m).orbitFrameClass (circleOrbit m) = 1 :=
  orbitFrameClass_eq_one m (field m) (circleOrbit m)


-- @@ L622-653 verbatim
/-- The exact singleton ledger consumed by the standard-configuration
assembly: the untwisted geometric circle has intrinsic class one. -/
theorem positiveFrameLedger_eq_single_one :
    (positiveSign m).positiveFrameLedger (field m) = [(1 : ZMod 2)] := by
  classical
  let A := (positiveSign m).positiveOrbitCollection (field m)
  let O₀ := circleOrbit m
  have hO₀ : ((O₀ : (field m).OrbitIndex) : Set E) ∈ A := by
    intro x hx
    refine ⟨(field m).orbit_subset_fiber
      (circleAt_mem_X_fiber m 0) hx, ?_⟩
    simp [positiveSign]
  have hcard : Fintype.card ((field m).SelectedOrbitIndex A) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨O₀, hO₀⟩, ?_⟩
    intro Q
    apply Subtype.ext
    exact orbitIndex_eq_circleOrbit m Q.1
  let L := (field m).selectedFrameLedger A
  have hlength : L.length = 1 := by
    simp [L, TamedField.selectedFrameLedger, hcard]
  have hall : ∀ beta ∈ L, beta = (1 : ZMod 2) := by
    intro beta hbeta
    simp only [L, TamedField.selectedFrameLedger, List.mem_ofFn] at hbeta
    obtain ⟨i, rfl⟩ := hbeta
    let Q := (Fintype.equivFin ((field m).SelectedOrbitIndex A)).symm i
    simpa [Q, orbitIndex_eq_circleOrbit m Q.1, O₀] using
      circleOrbit_frameClass m
  change L = [(1 : ZMod 2)]
  rw [L.eq_cons_of_length_one hlength]
  congr
  exact hall _ (by simp)


-- @@ L655-661 verbatim
def positiveFlat : FlatSignedConfiguration (m + 2) (background m) where
  X := X m
  sign := positiveSign m
  center := 0
  radius := 2
  radius_nonneg := by norm_num
  flatOutside := flatOutside m


-- @@ L663-669 verbatim
def negativeFlat : FlatSignedConfiguration (m + 2) (background m) where
  X := X m
  sign := negativeSign m
  center := 0
  radius := 2
  radius_nonneg := by norm_num
  flatOutside := flatOutside m


-- @@ L671-676 verbatim
/-- A literal signed-ledger state for the class-one positive circle. -/
def positiveLedgerState : SignedLedgerState (m + 2) [(1 : ZMod 2)] where
  X := X m
  sign := positiveSign m
  field := field m
  ledger_eq := positiveFrameLedger_eq_single_one m


-- @@ L678-678 verbatim
end CompactTubeConfiguration

-- @@ L679-679 verbatim
end Submission
