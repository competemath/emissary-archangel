import Submission.ProductionMorseEventEmbeddedGeometry
import Submission.ProductionMorseDefiniteCenterClass
import Submission.FramedMorseDefiniteFrameLinearization
import Submission.CodomainEquivDelta


-- @@ L6-11 verbatim
/-!
# The definite frame class for production Morse events

This file joins the route-independent center calculation to the actual
positive-radius circles furnished by an embedded production event.
-/


-- @@ L13-13 verbatim
noncomputable section


-- @@ L15-15 verbatim
open Set Function Metric Filter InnerProductSpace Matrix

-- @@ L16-16 verbatim
open scoped RealInnerProductSpace ContDiff Topology unitInterval


-- @@ L18-18 verbatim
namespace Submission


-- @@ L20-20 verbatim
set_option autoImplicit false

-- @@ L21-21 verbatim
set_option maxHeartbeats 2400000


-- @@ L23-23 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)


-- @@ L25-25 verbatim
namespace StandardMorseEventAt


-- @@ L27-27 verbatim
open ExactFiniteMorseJetInstallation


-- @@ L29-29 verbatim
variable {a : ℕ}

-- @@ L30-30 verbatim
variable {C : FramedLevelCobordism (a + 2)}

-- @@ L31-31 verbatim
variable {center : EuclideanSpace ℝ (Fin (a + 4))}

-- @@ L32-32 verbatim
variable {M : StandardMorseEventAt C center}


-- @@ L34-34 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (a + 3))

-- @@ L35-35 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (a + 4))

-- @@ L36-36 verbatim
local notation "F" => EuclideanSpace ℝ (Fin (a + 2))


-- @@ L38-38 verbatim
/-! ## The common embedded/immersed interface -/


-- @@ L40-47 verbatim
/-- Forget only the point-injectivity field of an embedded event shrink. -/
def EmbeddedShrink.toCenterImmersion (T : M.EmbeddedShrink) :
    M.CenterImmersion where
  radius := T.radius
  radius_pos := T.radius_pos
  radius_le := T.radius_le
  param_differentiableAt := T.param_differentiableAt
  fderiv_param_injective := T.fderiv_param_injective


-- @@ L49-49 verbatim
/-! ## A transported unit angular tangent -/


-- @@ L51-55 verbatim
/-- The parameter differential in the unit angular direction. -/
def definiteUnitTangent (M : StandardMorseEventAt C center)
    (r theta : ℝ) : E₁ :=
  M.centerSpatialTangent (definiteCircleParam r theta)
    (definiteCircleTangentParam 1 theta)


-- @@ L57-61 verbatim
@[simp] theorem definiteUnitTangent_zero
    (M : StandardMorseEventAt C center) (theta : ℝ) :
    M.definiteUnitTangent 0 theta = M.centerUnitTangent theta := by
  simp [definiteUnitTangent, centerUnitTangent,
    definiteCircleParam, pairToMorseParam]


-- @@ L63-84 verbatim
/-- The transported unit tangent is jointly continuous at the center. -/
theorem continuousAt_definiteUnitTangent_zero
    (M : StandardMorseEventAt C center) (theta₀ : ℝ) :
    ContinuousAt (fun q : ℝ × ℝ => M.definiteUnitTangent q.1 q.2)
      (0, theta₀) := by
  have hparam : Continuous (fun q : ℝ × ℝ =>
      definiteCircleParam q.1 q.2) := by
    unfold definiteCircleParam pairToMorseParam
    fun_prop
  have htangent : Continuous (fun q : ℝ × ℝ =>
      definiteCircleTangentParam 1 q.2) := by
    unfold definiteCircleTangentParam pairToMorseParam
    fun_prop
  have hparam0 : definiteCircleParam (0 : ℝ) theta₀ = 0 := by
    ext i
    fin_cases i <;> simp [definiteCircleParam, pairToMorseParam]
  have hD : ContinuousAt (fun q : ℝ × ℝ =>
      fderiv ℝ M.param (definiteCircleParam q.1 q.2)) (0, theta₀) :=
    M.param_smooth.continuousAt_fderiv (by simp) |>.comp_of_eq
      hparam.continuousAt hparam0
  exact continuous_spacePart.continuousAt.comp
    (hD.clm_apply htangent.continuousAt)


-- @@ L86-100 verbatim
theorem smul_definiteUnitTangent
    (M : StandardMorseEventAt C center) (r theta : ℝ) :
    r • M.definiteUnitTangent r theta =
      spacePart (fderiv ℝ M.param (definiteCircleParam r theta)
        (definiteCircleTangentParam r theta)) := by
  rw [definiteCircleTangentParam_eq_smul_unit, map_smul]
  change r • spacePart
      ((fderiv ℝ M.param (definiteCircleParam r theta))
        (definiteCircleTangentParam 1 theta)) =
    spacePart (r •
      (fderiv ℝ M.param (definiteCircleParam r theta))
        (definiteCircleTangentParam 1 theta))
  unfold spacePart
  ext i
  rfl


-- @@ L102-102 verbatim
/-! ## A compactness lemma using only center-local continuity -/


-- @@ L104-119 verbatim
theorem eventually_uniform_det_pos_of_continuousAt
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    {m : ℕ} {K : Set X} (hK : IsCompact K)
    (A : P → X → Matrix (Fin m) (Fin m) ℝ)
    {p₀ : P}
    (hA : ∀ x ∈ K,
      ContinuousAt (fun q : P × X => A q.1 q.2) (p₀, x))
    (hpos : ∀ x ∈ K, 0 < (A p₀ x).det) :
    ∀ᶠ p in nhds p₀, ∀ x ∈ K, 0 < (A p x).det := by
  apply hK.eventually_forall_of_forall_eventually
  intro x hx
  have hdet : ContinuousAt
      (fun q : P × X => (A q.1 q.2).det) (p₀, x) := by
    fun_prop
  exact hdet
    ((isOpen_lt continuous_const continuous_id).mem_nhds (hpos x hx))


-- @@ L121-121 verbatim
/-! ## Output coordinates adapted to the critical range -/


-- @@ L123-127 verbatim
theorem centerCokernelVector_mem_orthogonal
    (M : StandardMorseEventAt C center) :
    M.centerCokernelVector ∈
      (LinearMap.range (spatialDeriv C.G center).toLinearMap)ᗮ := by
  exact criticalOutputCokernelVector_mem C center M.center_mem_timeCritical


-- @@ L129-131 verbatim
/-- Unit vector in the missing output direction. -/
def centerCokernelUnit (M : StandardMorseEventAt C center) : F :=
  ‖M.centerCokernelVector‖⁻¹ • M.centerCokernelVector


-- @@ L133-137 verbatim
theorem norm_centerCokernelUnit (M : StandardMorseEventAt C center) :
    ‖M.centerCokernelUnit‖ = 1 := by
  rw [centerCokernelUnit, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_norm, inv_mul_cancel₀]
  exact norm_ne_zero_iff.mpr M.centerCokernelVector_ne_zero


-- @@ L139-149 verbatim
theorem inner_centerTransverseRangeBasis_centerCokernelUnit
    (M : StandardMorseEventAt C center) (i : Fin (a + 1)) :
    ⟪(M.centerTransverseRangeBasis i : F), M.centerCokernelUnit⟫_ℝ = 0 := by
  rw [centerCokernelUnit, real_inner_smul_right]
  have horth := M.centerCokernelVector_mem_orthogonal
  rw [Submodule.mem_orthogonal'] at horth
  have hz : ⟪(M.centerTransverseRangeBasis i : F),
      M.centerCokernelVector⟫_ℝ = 0 :=
    inner_eq_zero_symm.mpr
      (horth _ (M.centerTransverseRangeBasis i).property)
  rw [hz, mul_zero]


-- @@ L151-155 verbatim
/-- Range coordinates followed by a signed unit cokernel coordinate. -/
def signedCenterOutputRows (M : StandardMorseEventAt C center)
    (s : ℝ) : Fin (a + 2) → F :=
  Fin.snoc (fun i => (M.centerTransverseRangeBasis i : F))
    (s • M.centerCokernelUnit)


-- @@ L157-192 verbatim
theorem orthonormal_signedCenterOutputRows
    (M : StandardMorseEventAt C center) (s : ℝ)
    (hs : s = 1 ∨ s = -1) :
    Orthonormal ℝ (M.signedCenterOutputRows s) := by
  rw [orthonormal_iff_ite]
  intro i j
  induction i using Fin.lastCases with
  | last =>
      induction j using Fin.lastCases with
      | last =>
          simp only [signedCenterOutputRows, Fin.snoc_last]
          rw [real_inner_smul_left, real_inner_smul_right,
            real_inner_self_eq_norm_sq, M.norm_centerCokernelUnit]
          rcases hs with rfl | rfl <;> norm_num
      | cast j =>
          simp only [signedCenterOutputRows, Fin.snoc_last,
            Fin.snoc_castSucc]
          rw [real_inner_smul_left]
          have hz : ⟪M.centerCokernelUnit,
              (M.centerTransverseRangeBasis j : F)⟫_ℝ = 0 :=
            inner_eq_zero_symm.mpr
              (M.inner_centerTransverseRangeBasis_centerCokernelUnit j)
          rw [hz, mul_zero]
          rw [if_neg (Fin.castSucc_lt_last j).ne']
  | cast i =>
      induction j using Fin.lastCases with
      | last =>
          simp only [signedCenterOutputRows, Fin.snoc_castSucc,
            Fin.snoc_last]
          rw [real_inner_smul_right,
            M.inner_centerTransverseRangeBasis_centerCokernelUnit, mul_zero]
          simp
      | cast j =>
          simp only [signedCenterOutputRows, Fin.snoc_castSucc]
          simpa using (orthonormal_iff_ite.mp
            M.centerTransverseRangeBasis.orthonormal i j)


-- @@ L194-208 verbatim
/-- The orthonormal output basis adapted to the center range and signed
cokernel line. -/
def signedCenterOutputONB (M : StandardMorseEventAt C center)
    (s : ℝ) (hs : s = 1 ∨ s = -1) :
    OrthonormalBasis (Fin (a + 2)) ℝ F := by
  let v := M.signedCenterOutputRows s
  have hv : Orthonormal ℝ v := M.orthonormal_signedCenterOutputRows s hs
  let b : Module.Basis (Fin (a + 2)) ℝ F :=
    basisOfOrthonormalOfCardEqFinrank hv (by simp)
  refine OrthonormalBasis.mk hv ?_
  have hb : Submodule.span ℝ (Set.range (fun i => b i)) = ⊤ := b.span_eq
  have hbfun : (fun i => b i) = v :=
    coe_basisOfOrthonormalOfCardEqFinrank hv (by simp)
  rw [hbfun] at hb
  exact hb.ge


-- @@ L210-213 verbatim
/-- Coordinates in the signed range/cokernel basis. -/
def signedCenterOutputIsometry (M : StandardMorseEventAt C center)
    (s : ℝ) (hs : s = 1 ∨ s = -1) : F ≃ₗᵢ[ℝ] F :=
  (M.signedCenterOutputONB s hs).repr


-- @@ L215-219 verbatim
@[simp] theorem signedCenterOutputONB_apply
    (M : StandardMorseEventAt C center)
    (s : ℝ) (hs : s = 1 ∨ s = -1) (i : Fin (a + 2)) :
    M.signedCenterOutputONB s hs i = M.signedCenterOutputRows s i := by
  simp [signedCenterOutputONB]


-- @@ L221-227 verbatim
theorem signedCenterOutputIsometry_apply
    (M : StandardMorseEventAt C center)
    (s : ℝ) (hs : s = 1 ∨ s = -1) (x : F) (i : Fin (a + 2)) :
    M.signedCenterOutputIsometry s hs x i =
      ⟪M.signedCenterOutputRows s i, x⟫_ℝ := by
  rw [signedCenterOutputIsometry,
    (M.signedCenterOutputONB s hs).repr_apply_apply, signedCenterOutputONB_apply]


-- @@ L229-244 verbatim
theorem isometryMatrix_signedCenterOutputIsometry_det_cases
    (M : StandardMorseEventAt C center)
    (s : ℝ) (hs : s = 1 ∨ s = -1) :
    let q := M.signedCenterOutputIsometry s hs
    (isometryMatrix q).det = 1 ∨ (isometryMatrix q).det = -1 := by
  let q := M.signedCenterOutputIsometry s hs
  let d := (isometryMatrix q).det
  have horth := isometryMatrix_mul_transpose q
  have hdet := congrArg Matrix.det horth
  have hd : d * d = 1 := by
    simpa [d, Matrix.det_mul] using hdet
  rcases lt_or_ge d 0 with hdneg | hdnonneg
  · right
    nlinarith
  · left
    nlinarith


-- @@ L246-246 verbatim
/-! ## Positively oriented limiting rows -/


-- @@ L248-252 verbatim
def centerMinimumUnitNormalLast
    (M : StandardMorseEventAt C center) (theta : ℝ) : E₁ :=
  ‖M.centerCokernelVector‖⁻¹ •
    (nonzeroOrientationSign M.centerMinimumPairingScalar •
      M.centerNormalRow 0 theta)


-- @@ L254-258 verbatim
def centerMaximumUnitNormalLast
    (M : StandardMorseEventAt C center) (theta : ℝ) : E₁ :=
  ‖M.centerCokernelVector‖⁻¹ •
    (nonzeroOrientationSign M.centerMaximumPairingScalar •
      M.centerNormalRow 0 theta)


-- @@ L260-264 verbatim
def centerMinimumUnsignedUnitRows
    (M : StandardMorseEventAt C center) (theta : ℝ) :
    Fin (a + 3) → E₁ :=
  centerRowsWith M.centerTransverseNormal (M.centerUnitTangent theta)
    (M.centerMinimumUnitNormalLast theta)


-- @@ L266-270 verbatim
def centerMaximumUnsignedUnitRows
    (M : StandardMorseEventAt C center) (theta : ℝ) :
    Fin (a + 3) → E₁ :=
  centerRowsWith M.centerTransverseNormal (M.centerUnitTangent theta)
    (M.centerMaximumUnitNormalLast theta)


-- @@ L272-286 verbatim
theorem linearIndependent_centerMinimumUnsignedUnitRows
    (T : M.CenterImmersion) (hindex : M.index = .minimum) (theta : ℝ) :
    LinearIndependent ℝ (M.centerMinimumUnsignedUnitRows theta) := by
  apply linearIndependent_centerRowsWith_test
  · exact M.linearIndependent_centerTransverseNormal
  · exact centerUnitTangent_ne_zero T theta
  · exact fun i => inner_centerTransverseNormal_unitTangent_zero T i theta
  · exact fun i => inner_centerTransverseNormal_minimumRadialTest T i theta
  · exact inner_centerUnitTangent_minimumRadialTest T theta
  · rw [centerMinimumUnitNormalLast, real_inner_smul_left]
    exact mul_ne_zero
      (inv_ne_zero (norm_ne_zero_iff.mpr M.centerCokernelVector_ne_zero))
      (ne_of_gt (by simpa [centerMinimumNormalRadialLast] using
        (inner_centerMinimumNormalRadialLast_radialTest_pos
          T hindex 0 theta)))


-- @@ L288-304 verbatim
theorem linearIndependent_centerMaximumUnsignedUnitRows
    (T : M.CenterImmersion) (hindex : M.index = .maximum) (theta : ℝ) :
    LinearIndependent ℝ (M.centerMaximumUnsignedUnitRows theta) := by
  apply linearIndependent_centerRowsWith_test
  · exact M.linearIndependent_centerTransverseNormal
  · exact centerUnitTangent_ne_zero T theta
  · exact fun i => inner_centerTransverseNormal_unitTangent_zero T i theta
  · exact fun i => inner_centerTransverseNormal_maximumRadialTest T i theta
  · have h := inner_centerUnitTangentRev_maximumRadialTest T theta
    rw [centerUnitTangentRev, inner_neg_left, neg_eq_zero] at h
    exact h
  · rw [centerMaximumUnitNormalLast, real_inner_smul_left]
    exact mul_ne_zero
      (inv_ne_zero (norm_ne_zero_iff.mpr M.centerCokernelVector_ne_zero))
      (ne_of_gt (by simpa [centerMaximumNormalRadialLast] using
        (inner_centerMaximumNormalRadialLast_radialTest_pos
          T hindex 0 theta)))


-- @@ L306-309 verbatim
def centerMinimumUnsignedUnitMatrix
    (M : StandardMorseEventAt C center) (theta : ℝ) :
    Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ :=
  rowsMatrix (M.centerMinimumUnsignedUnitRows theta)


-- @@ L311-314 verbatim
def centerMaximumUnsignedUnitMatrix
    (M : StandardMorseEventAt C center) (theta : ℝ) :
    Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ :=
  rowsMatrix (M.centerMaximumUnsignedUnitRows theta)


-- @@ L316-326 verbatim
theorem det_centerMinimumUnsignedUnitMatrix_ne_zero
    (T : M.CenterImmersion) (hindex : M.index = .minimum) (theta : ℝ) :
    (M.centerMinimumUnsignedUnitMatrix theta).det ≠ 0 := by
  have hrows : LinearIndependent ℝ
      (M.centerMinimumUnsignedUnitMatrix theta).row :=
    (linearIndependent_rowsMatrix_iff
      (M.centerMinimumUnsignedUnitRows theta)).mpr
      (linearIndependent_centerMinimumUnsignedUnitRows T hindex theta)
  rw [Matrix.linearIndependent_rows_iff_isUnit,
    Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hrows
  exact hrows


-- @@ L328-338 verbatim
theorem det_centerMaximumUnsignedUnitMatrix_ne_zero
    (T : M.CenterImmersion) (hindex : M.index = .maximum) (theta : ℝ) :
    (M.centerMaximumUnsignedUnitMatrix theta).det ≠ 0 := by
  have hrows : LinearIndependent ℝ
      (M.centerMaximumUnsignedUnitMatrix theta).row :=
    (linearIndependent_rowsMatrix_iff
      (M.centerMaximumUnsignedUnitRows theta)).mpr
      (linearIndependent_centerMaximumUnsignedUnitRows T hindex theta)
  rw [Matrix.linearIndependent_rows_iff_isUnit,
    Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hrows
  exact hrows


-- @@ L340-344 verbatim
/-- The unique sign which makes the minimum limiting frame positive at angle
zero. -/
def centerMinimumActualOrientationSign
    (M : StandardMorseEventAt C center) : ℝ :=
  nonzeroOrientationSign (M.centerMinimumUnsignedUnitMatrix 0).det


-- @@ L346-349 verbatim
/-- The analogous maximum sign. -/
def centerMaximumActualOrientationSign
    (M : StandardMorseEventAt C center) : ℝ :=
  nonzeroOrientationSign (M.centerMaximumUnsignedUnitMatrix 0).det


-- @@ L351-354 verbatim
theorem centerMinimumActualOrientationSign_ne_zero
    (M : StandardMorseEventAt C center) :
    M.centerMinimumActualOrientationSign ≠ 0 :=
  nonzeroOrientationSign_ne_zero _


-- @@ L356-359 verbatim
theorem centerMaximumActualOrientationSign_ne_zero
    (M : StandardMorseEventAt C center) :
    M.centerMaximumActualOrientationSign ≠ 0 :=
  nonzeroOrientationSign_ne_zero _


-- @@ L361-366 verbatim
def centerMinimumActualLimitRows
    (M : StandardMorseEventAt C center) (theta : ℝ) :
    Fin (a + 3) → E₁ :=
  centerRowsWith M.centerTransverseNormal
    (M.centerMinimumActualOrientationSign • M.centerUnitTangent theta)
    (M.centerMinimumUnitNormalLast theta)


-- @@ L368-373 verbatim
def centerMaximumActualLimitRows
    (M : StandardMorseEventAt C center) (theta : ℝ) :
    Fin (a + 3) → E₁ :=
  centerRowsWith M.centerTransverseNormal
    (M.centerMaximumActualOrientationSign • M.centerUnitTangent theta)
    (M.centerMaximumUnitNormalLast theta)


-- @@ L375-378 verbatim
def centerMinimumActualLimitMatrix
    (M : StandardMorseEventAt C center) (theta : ℝ) :
    Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ :=
  rowsMatrix (M.centerMinimumActualLimitRows theta)


-- @@ L380-383 verbatim
def centerMaximumActualLimitMatrix
    (M : StandardMorseEventAt C center) (theta : ℝ) :
    Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ :=
  rowsMatrix (M.centerMaximumActualLimitRows theta)


-- @@ L385-398 verbatim
theorem centerMinimumActualLimitMatrix_eq_updateRow
    (M : StandardMorseEventAt C center) (theta : ℝ) :
    M.centerMinimumActualLimitMatrix theta =
      (M.centerMinimumUnsignedUnitMatrix theta).updateRow 0
        (M.centerMinimumActualOrientationSign •
          (M.centerMinimumUnsignedUnitMatrix theta) 0) := by
  ext i j
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
  · simp [centerMinimumActualLimitMatrix, centerMinimumActualLimitRows,
      centerMinimumUnsignedUnitMatrix, centerMinimumUnsignedUnitRows,
      rowsMatrix, centerRowsWith]
  · simp [centerMinimumActualLimitMatrix, centerMinimumActualLimitRows,
      centerMinimumUnsignedUnitMatrix, centerMinimumUnsignedUnitRows,
      rowsMatrix, centerRowsWith]


-- @@ L400-413 verbatim
theorem centerMaximumActualLimitMatrix_eq_updateRow
    (M : StandardMorseEventAt C center) (theta : ℝ) :
    M.centerMaximumActualLimitMatrix theta =
      (M.centerMaximumUnsignedUnitMatrix theta).updateRow 0
        (M.centerMaximumActualOrientationSign •
          (M.centerMaximumUnsignedUnitMatrix theta) 0) := by
  ext i j
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
  · simp [centerMaximumActualLimitMatrix, centerMaximumActualLimitRows,
      centerMaximumUnsignedUnitMatrix, centerMaximumUnsignedUnitRows,
      rowsMatrix, centerRowsWith]
  · simp [centerMaximumActualLimitMatrix, centerMaximumActualLimitRows,
      centerMaximumUnsignedUnitMatrix, centerMaximumUnsignedUnitRows,
      rowsMatrix, centerRowsWith]


-- @@ L415-421 verbatim
theorem det_centerMinimumActualLimitMatrix_zero_pos
    (T : M.CenterImmersion) (hindex : M.index = .minimum) :
    0 < (M.centerMinimumActualLimitMatrix 0).det := by
  rw [M.centerMinimumActualLimitMatrix_eq_updateRow,
    Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
  exact nonzeroOrientationSign_mul_pos
    (det_centerMinimumUnsignedUnitMatrix_ne_zero T hindex 0)


-- @@ L423-429 verbatim
theorem det_centerMaximumActualLimitMatrix_zero_pos
    (T : M.CenterImmersion) (hindex : M.index = .maximum) :
    0 < (M.centerMaximumActualLimitMatrix 0).det := by
  rw [M.centerMaximumActualLimitMatrix_eq_updateRow,
    Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
  exact nonzeroOrientationSign_mul_pos
    (det_centerMaximumUnsignedUnitMatrix_ne_zero T hindex 0)


-- @@ L431-437 verbatim
theorem det_centerMinimumActualLimitMatrix_ne_zero
    (T : M.CenterImmersion) (hindex : M.index = .minimum) (theta : ℝ) :
    (M.centerMinimumActualLimitMatrix theta).det ≠ 0 := by
  rw [M.centerMinimumActualLimitMatrix_eq_updateRow,
    Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
  exact mul_ne_zero M.centerMinimumActualOrientationSign_ne_zero
    (det_centerMinimumUnsignedUnitMatrix_ne_zero T hindex theta)


-- @@ L439-445 verbatim
theorem det_centerMaximumActualLimitMatrix_ne_zero
    (T : M.CenterImmersion) (hindex : M.index = .maximum) (theta : ℝ) :
    (M.centerMaximumActualLimitMatrix theta).det ≠ 0 := by
  rw [M.centerMaximumActualLimitMatrix_eq_updateRow,
    Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
  exact mul_ne_zero M.centerMaximumActualOrientationSign_ne_zero
    (det_centerMaximumUnsignedUnitMatrix_ne_zero T hindex theta)


-- @@ L447-474 verbatim
theorem continuous_centerMinimumActualLimitMatrix
    (M : StandardMorseEventAt C center) :
    Continuous M.centerMinimumActualLimitMatrix := by
  apply continuous_matrix
  intro i j
  have hrow : Continuous fun theta => M.centerMinimumActualLimitRows theta i := by
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · have ht : Continuous fun theta : ℝ =>
          M.centerMinimumActualOrientationSign • M.centerUnitTangent theta := by
        exact (continuous_const : Continuous fun _ : ℝ =>
          M.centerMinimumActualOrientationSign).smul
            M.continuous_centerUnitTangent
      simpa [centerMinimumActualLimitRows, centerRowsWith] using ht
    · induction i using Fin.lastCases with
      | last =>
          have hn : Continuous M.centerMinimumUnitNormalLast := by
            unfold centerMinimumUnitNormalLast
            exact (continuous_const : Continuous fun _ : ℝ =>
              ‖M.centerCokernelVector‖⁻¹).smul
                ((continuous_const : Continuous fun _ : ℝ =>
                  nonzeroOrientationSign M.centerMinimumPairingScalar).smul
                    M.continuous_centerNormalRow_zero)
          simpa [centerMinimumActualLimitRows, centerRowsWith] using hn
      | cast i =>
          simpa [centerMinimumActualLimitRows, centerRowsWith] using
            (continuous_const : Continuous fun _ : ℝ =>
              M.centerTransverseNormal i)
  exact (EuclideanSpace.proj j).continuous.comp hrow


-- @@ L476-503 verbatim
theorem continuous_centerMaximumActualLimitMatrix
    (M : StandardMorseEventAt C center) :
    Continuous M.centerMaximumActualLimitMatrix := by
  apply continuous_matrix
  intro i j
  have hrow : Continuous fun theta => M.centerMaximumActualLimitRows theta i := by
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · have ht : Continuous fun theta : ℝ =>
          M.centerMaximumActualOrientationSign • M.centerUnitTangent theta := by
        exact (continuous_const : Continuous fun _ : ℝ =>
          M.centerMaximumActualOrientationSign).smul
            M.continuous_centerUnitTangent
      simpa [centerMaximumActualLimitRows, centerRowsWith] using ht
    · induction i using Fin.lastCases with
      | last =>
          have hn : Continuous M.centerMaximumUnitNormalLast := by
            unfold centerMaximumUnitNormalLast
            exact (continuous_const : Continuous fun _ : ℝ =>
              ‖M.centerCokernelVector‖⁻¹).smul
                ((continuous_const : Continuous fun _ : ℝ =>
                  nonzeroOrientationSign M.centerMaximumPairingScalar).smul
                    M.continuous_centerNormalRow_zero)
          simpa [centerMaximumActualLimitRows, centerRowsWith] using hn
      | cast i =>
          simpa [centerMaximumActualLimitRows, centerRowsWith] using
            (continuous_const : Continuous fun _ : ℝ =>
              M.centerTransverseNormal i)
  exact (EuclideanSpace.proj j).continuous.comp hrow


-- @@ L505-524 verbatim
theorem det_centerMinimumActualLimitMatrix_pos
    (T : M.CenterImmersion) (hindex : M.index = .minimum) (theta : ℝ) :
    0 < (M.centerMinimumActualLimitMatrix theta).det := by
  let d : I → ℝ := fun u =>
    (M.centerMinimumActualLimitMatrix ((u : ℝ) * theta)).det
  have hd : Continuous d := by
    exact (M.continuous_centerMinimumActualLimitMatrix.comp
      (continuous_subtype_val.mul continuous_const)).matrix_det
  have hd0 : 0 < d 0 := by
    simpa [d] using det_centerMinimumActualLimitMatrix_zero_pos T hindex
  have hd1ne : d 1 ≠ 0 := by
    simpa [d] using det_centerMinimumActualLimitMatrix_ne_zero T hindex theta
  by_contra hpos
  have hpos' : ¬ 0 < d 1 := by simpa [d] using hpos
  have hd1neg : d 1 < 0 := lt_of_le_of_ne (le_of_not_gt hpos') hd1ne
  have hmem : (0 : ℝ) ∈ Set.Icc (d 1) (d 0) :=
    ⟨hd1neg.le, hd0.le⟩
  obtain ⟨u, hu⟩ := intermediate_value_univ (1 : I) 0 hd hmem
  exact det_centerMinimumActualLimitMatrix_ne_zero T hindex
    ((u : ℝ) * theta) hu


-- @@ L526-545 verbatim
theorem det_centerMaximumActualLimitMatrix_pos
    (T : M.CenterImmersion) (hindex : M.index = .maximum) (theta : ℝ) :
    0 < (M.centerMaximumActualLimitMatrix theta).det := by
  let d : I → ℝ := fun u =>
    (M.centerMaximumActualLimitMatrix ((u : ℝ) * theta)).det
  have hd : Continuous d := by
    exact (M.continuous_centerMaximumActualLimitMatrix.comp
      (continuous_subtype_val.mul continuous_const)).matrix_det
  have hd0 : 0 < d 0 := by
    simpa [d] using det_centerMaximumActualLimitMatrix_zero_pos T hindex
  have hd1ne : d 1 ≠ 0 := by
    simpa [d] using det_centerMaximumActualLimitMatrix_ne_zero T hindex theta
  by_contra hpos
  have hpos' : ¬ 0 < d 1 := by simpa [d] using hpos
  have hd1neg : d 1 < 0 := lt_of_le_of_ne (le_of_not_gt hpos') hd1ne
  have hmem : (0 : ℝ) ∈ Set.Icc (d 1) (d 0) :=
    ⟨hd1neg.le, hd0.le⟩
  obtain ⟨u, hu⟩ := intermediate_value_univ (1 : I) 0 hd hmem
  exact det_centerMaximumActualLimitMatrix_ne_zero T hindex
    ((u : ℝ) * theta) hu


-- @@ L547-547 verbatim
/-! ## A positive center homotopy to the radial endpoint -/


-- @@ L549-552 verbatim
def centerMinimumActualNormalRadialLast
    (M : StandardMorseEventAt C center) (s : I) (theta : ℝ) : E₁ :=
  (1 - (s : ℝ)) • M.centerMinimumUnitNormalLast theta +
    (s : ℝ) • M.centerRadialTangent theta


-- @@ L554-557 verbatim
def centerMaximumActualNormalRadialLast
    (M : StandardMorseEventAt C center) (s : I) (theta : ℝ) : E₁ :=
  (1 - (s : ℝ)) • M.centerMaximumUnitNormalLast theta +
    (s : ℝ) • M.centerRadialTangent theta


-- @@ L559-564 verbatim
def centerMinimumActualNormalRadialRows
    (M : StandardMorseEventAt C center) (s : I) (theta : ℝ) :
    Fin (a + 3) → E₁ :=
  centerRowsWith M.centerTransverseNormal
    (M.centerMinimumActualOrientationSign • M.centerUnitTangent theta)
    (M.centerMinimumActualNormalRadialLast s theta)


-- @@ L566-571 verbatim
def centerMaximumActualNormalRadialRows
    (M : StandardMorseEventAt C center) (s : I) (theta : ℝ) :
    Fin (a + 3) → E₁ :=
  centerRowsWith M.centerTransverseNormal
    (M.centerMaximumActualOrientationSign • M.centerUnitTangent theta)
    (M.centerMaximumActualNormalRadialLast s theta)


-- @@ L573-576 verbatim
def centerMinimumActualNormalRadialMatrix
    (M : StandardMorseEventAt C center) (s : I) (theta : ℝ) :
    Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ :=
  rowsMatrix (M.centerMinimumActualNormalRadialRows s theta)


-- @@ L578-581 verbatim
def centerMaximumActualNormalRadialMatrix
    (M : StandardMorseEventAt C center) (s : I) (theta : ℝ) :
    Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ :=
  rowsMatrix (M.centerMaximumActualNormalRadialRows s theta)


-- @@ L583-590 verbatim
@[simp] theorem centerMinimumActualNormalRadialMatrix_zero
    (M : StandardMorseEventAt C center) (theta : ℝ) :
    M.centerMinimumActualNormalRadialMatrix 0 theta =
      M.centerMinimumActualLimitMatrix theta := by
  simp [centerMinimumActualNormalRadialMatrix,
    centerMinimumActualNormalRadialRows,
    centerMinimumActualNormalRadialLast,
    centerMinimumActualLimitMatrix, centerMinimumActualLimitRows]


-- @@ L592-599 verbatim
@[simp] theorem centerMaximumActualNormalRadialMatrix_zero
    (M : StandardMorseEventAt C center) (theta : ℝ) :
    M.centerMaximumActualNormalRadialMatrix 0 theta =
      M.centerMaximumActualLimitMatrix theta := by
  simp [centerMaximumActualNormalRadialMatrix,
    centerMaximumActualNormalRadialRows,
    centerMaximumActualNormalRadialLast,
    centerMaximumActualLimitMatrix, centerMaximumActualLimitRows]


-- @@ L601-628 verbatim
theorem inner_centerMinimumActualNormalRadialLast_test_pos
    (T : M.CenterImmersion) (hindex : M.index = .minimum)
    (s : I) (theta : ℝ) :
    0 < ⟪M.centerMinimumActualNormalRadialLast s theta,
      M.centerMinimumRadialTest theta⟫_ℝ := by
  have hcpos : 0 < ‖M.centerCokernelVector‖⁻¹ :=
    inv_pos.mpr (norm_pos_iff.mpr M.centerCokernelVector_ne_zero)
  have hunit : 0 < ⟪M.centerMinimumUnitNormalLast theta,
      M.centerMinimumRadialTest theta⟫_ℝ := by
    rw [centerMinimumUnitNormalLast, real_inner_smul_left]
    apply mul_pos hcpos
    simpa [centerMinimumNormalRadialLast] using
      (inner_centerMinimumNormalRadialLast_radialTest_pos
        T hindex 0 theta)
  have hradial : 0 < ⟪M.centerRadialTangent theta,
      M.centerMinimumRadialTest theta⟫_ℝ := by
    simpa [centerMinimumNormalRadialLast] using
      (inner_centerMinimumNormalRadialLast_radialTest_pos
        T hindex 1 theta)
  rw [centerMinimumActualNormalRadialLast, inner_add_left,
    real_inner_smul_left, real_inner_smul_left]
  have hs0 : 0 ≤ (s : ℝ) := s.property.1
  have hs1 : (s : ℝ) ≤ 1 := s.property.2
  by_cases hsone : (s : ℝ) = 1
  · simpa [hsone] using hradial
  exact add_pos_of_pos_of_nonneg
    (mul_pos (sub_pos.mpr (lt_of_le_of_ne hs1 hsone)) hunit)
    (mul_nonneg hs0 hradial.le)


-- @@ L630-657 verbatim
theorem inner_centerMaximumActualNormalRadialLast_test_pos
    (T : M.CenterImmersion) (hindex : M.index = .maximum)
    (s : I) (theta : ℝ) :
    0 < ⟪M.centerMaximumActualNormalRadialLast s theta,
      M.centerMaximumRadialTest theta⟫_ℝ := by
  have hcpos : 0 < ‖M.centerCokernelVector‖⁻¹ :=
    inv_pos.mpr (norm_pos_iff.mpr M.centerCokernelVector_ne_zero)
  have hunit : 0 < ⟪M.centerMaximumUnitNormalLast theta,
      M.centerMaximumRadialTest theta⟫_ℝ := by
    rw [centerMaximumUnitNormalLast, real_inner_smul_left]
    apply mul_pos hcpos
    simpa [centerMaximumNormalRadialLast] using
      (inner_centerMaximumNormalRadialLast_radialTest_pos
        T hindex 0 theta)
  have hradial : 0 < ⟪M.centerRadialTangent theta,
      M.centerMaximumRadialTest theta⟫_ℝ := by
    simpa [centerMaximumNormalRadialLast] using
      (inner_centerMaximumNormalRadialLast_radialTest_pos
        T hindex 1 theta)
  rw [centerMaximumActualNormalRadialLast, inner_add_left,
    real_inner_smul_left, real_inner_smul_left]
  have hs0 : 0 ≤ (s : ℝ) := s.property.1
  have hs1 : (s : ℝ) ≤ 1 := s.property.2
  by_cases hsone : (s : ℝ) = 1
  · simpa [hsone] using hradial
  exact add_pos_of_pos_of_nonneg
    (mul_pos (sub_pos.mpr (lt_of_le_of_ne hs1 hsone)) hunit)
    (mul_nonneg hs0 hradial.le)


-- @@ L659-674 verbatim
theorem linearIndependent_centerMinimumActualNormalRadialRows
    (T : M.CenterImmersion) (hindex : M.index = .minimum)
    (s : I) (theta : ℝ) :
    LinearIndependent ℝ (M.centerMinimumActualNormalRadialRows s theta) := by
  apply linearIndependent_centerRowsWith_test
  · exact M.linearIndependent_centerTransverseNormal
  · exact smul_ne_zero M.centerMinimumActualOrientationSign_ne_zero
      (centerUnitTangent_ne_zero T theta)
  · intro i
    rw [real_inner_smul_right,
      inner_centerTransverseNormal_unitTangent_zero T i theta, mul_zero]
  · exact fun i => inner_centerTransverseNormal_minimumRadialTest T i theta
  · rw [real_inner_smul_left,
      inner_centerUnitTangent_minimumRadialTest T theta, mul_zero]
  · exact ne_of_gt
      (inner_centerMinimumActualNormalRadialLast_test_pos T hindex s theta)


-- @@ L676-692 verbatim
theorem linearIndependent_centerMaximumActualNormalRadialRows
    (T : M.CenterImmersion) (hindex : M.index = .maximum)
    (s : I) (theta : ℝ) :
    LinearIndependent ℝ (M.centerMaximumActualNormalRadialRows s theta) := by
  apply linearIndependent_centerRowsWith_test
  · exact M.linearIndependent_centerTransverseNormal
  · exact smul_ne_zero M.centerMaximumActualOrientationSign_ne_zero
      (centerUnitTangent_ne_zero T theta)
  · intro i
    rw [real_inner_smul_right,
      inner_centerTransverseNormal_unitTangent_zero T i theta, mul_zero]
  · exact fun i => inner_centerTransverseNormal_maximumRadialTest T i theta
  · have h := inner_centerUnitTangentRev_maximumRadialTest T theta
    rw [centerUnitTangentRev, inner_neg_left, neg_eq_zero] at h
    rw [real_inner_smul_left, h, mul_zero]
  · exact ne_of_gt
      (inner_centerMaximumActualNormalRadialLast_test_pos T hindex s theta)


-- @@ L694-706 verbatim
theorem det_centerMinimumActualNormalRadialMatrix_ne_zero
    (T : M.CenterImmersion) (hindex : M.index = .minimum)
    (s : I) (theta : ℝ) :
    (M.centerMinimumActualNormalRadialMatrix s theta).det ≠ 0 := by
  have hrows : LinearIndependent ℝ
      (M.centerMinimumActualNormalRadialMatrix s theta).row :=
    (linearIndependent_rowsMatrix_iff
      (M.centerMinimumActualNormalRadialRows s theta)).mpr
      (linearIndependent_centerMinimumActualNormalRadialRows
        T hindex s theta)
  rw [Matrix.linearIndependent_rows_iff_isUnit,
    Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hrows
  exact hrows


-- @@ L708-720 verbatim
theorem det_centerMaximumActualNormalRadialMatrix_ne_zero
    (T : M.CenterImmersion) (hindex : M.index = .maximum)
    (s : I) (theta : ℝ) :
    (M.centerMaximumActualNormalRadialMatrix s theta).det ≠ 0 := by
  have hrows : LinearIndependent ℝ
      (M.centerMaximumActualNormalRadialMatrix s theta).row :=
    (linearIndependent_rowsMatrix_iff
      (M.centerMaximumActualNormalRadialRows s theta)).mpr
      (linearIndependent_centerMaximumActualNormalRadialRows
        T hindex s theta)
  rw [Matrix.linearIndependent_rows_iff_isUnit,
    Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hrows
  exact hrows


-- @@ L722-757 verbatim
theorem continuous_centerMinimumActualNormalRadialMatrix
    (M : StandardMorseEventAt C center) :
    Continuous fun q : I × ℝ =>
      M.centerMinimumActualNormalRadialMatrix q.1 q.2 := by
  have ht : Continuous fun q : I × ℝ =>
      M.centerMinimumActualOrientationSign • M.centerUnitTangent q.2 :=
    (continuous_const : Continuous fun _ : I × ℝ =>
      M.centerMinimumActualOrientationSign).smul
      (M.continuous_centerUnitTangent.comp continuous_snd)
  have hl : Continuous fun q : I × ℝ =>
      M.centerMinimumActualNormalRadialLast q.1 q.2 := by
    have hs : Continuous fun q : I × ℝ => (q.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    unfold centerMinimumActualNormalRadialLast centerMinimumUnitNormalLast
    exact ((continuous_const.sub hs).smul
      ((continuous_const : Continuous fun _ : I × ℝ =>
        ‖M.centerCokernelVector‖⁻¹).smul
        ((continuous_const : Continuous fun _ : I × ℝ =>
          nonzeroOrientationSign M.centerMinimumPairingScalar).smul
          (M.continuous_centerNormalRow_zero.comp continuous_snd)))).add
      ((continuous_subtype_val.comp continuous_fst).smul
        (M.continuous_centerRadialTangent.comp continuous_snd))
  apply continuous_matrix
  intro i j
  have hrow : Continuous fun q : I × ℝ =>
      M.centerMinimumActualNormalRadialRows q.1 q.2 i := by
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · simpa [centerMinimumActualNormalRadialRows, centerRowsWith] using ht
    · induction i using Fin.lastCases with
      | last =>
          simpa [centerMinimumActualNormalRadialRows, centerRowsWith] using hl
      | cast i =>
          simpa [centerMinimumActualNormalRadialRows, centerRowsWith] using
            (continuous_const : Continuous fun _ : I × ℝ =>
              M.centerTransverseNormal i)
  exact (EuclideanSpace.proj j).continuous.comp hrow


-- @@ L759-794 verbatim
theorem continuous_centerMaximumActualNormalRadialMatrix
    (M : StandardMorseEventAt C center) :
    Continuous fun q : I × ℝ =>
      M.centerMaximumActualNormalRadialMatrix q.1 q.2 := by
  have ht : Continuous fun q : I × ℝ =>
      M.centerMaximumActualOrientationSign • M.centerUnitTangent q.2 :=
    (continuous_const : Continuous fun _ : I × ℝ =>
      M.centerMaximumActualOrientationSign).smul
      (M.continuous_centerUnitTangent.comp continuous_snd)
  have hl : Continuous fun q : I × ℝ =>
      M.centerMaximumActualNormalRadialLast q.1 q.2 := by
    have hs : Continuous fun q : I × ℝ => (q.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    unfold centerMaximumActualNormalRadialLast centerMaximumUnitNormalLast
    exact ((continuous_const.sub hs).smul
      ((continuous_const : Continuous fun _ : I × ℝ =>
        ‖M.centerCokernelVector‖⁻¹).smul
        ((continuous_const : Continuous fun _ : I × ℝ =>
          nonzeroOrientationSign M.centerMaximumPairingScalar).smul
          (M.continuous_centerNormalRow_zero.comp continuous_snd)))).add
      ((continuous_subtype_val.comp continuous_fst).smul
        (M.continuous_centerRadialTangent.comp continuous_snd))
  apply continuous_matrix
  intro i j
  have hrow : Continuous fun q : I × ℝ =>
      M.centerMaximumActualNormalRadialRows q.1 q.2 i := by
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · simpa [centerMaximumActualNormalRadialRows, centerRowsWith] using ht
    · induction i using Fin.lastCases with
      | last =>
          simpa [centerMaximumActualNormalRadialRows, centerRowsWith] using hl
      | cast i =>
          simpa [centerMaximumActualNormalRadialRows, centerRowsWith] using
            (continuous_const : Continuous fun _ : I × ℝ =>
              M.centerTransverseNormal i)
  exact (EuclideanSpace.proj j).continuous.comp hrow


-- @@ L796-813 verbatim
theorem det_centerMinimumActualNormalRadialMatrix_pos
    (T : M.CenterImmersion) (hindex : M.index = .minimum)
    (s : I) (theta : ℝ) :
    0 < (M.centerMinimumActualNormalRadialMatrix s theta).det := by
  let d : I → ℝ := fun u =>
    (M.centerMinimumActualNormalRadialMatrix u theta).det
  have hd : Continuous d :=
    (M.continuous_centerMinimumActualNormalRadialMatrix.comp
      (continuous_id.prodMk continuous_const)).matrix_det
  have hd0 : 0 < d 0 := by
    simpa [d] using det_centerMinimumActualLimitMatrix_pos T hindex theta
  have hdne : ∀ u, d u ≠ 0 := fun u =>
    det_centerMinimumActualNormalRadialMatrix_ne_zero T hindex u theta
  by_contra hpos
  have hsneg : d s < 0 := lt_of_le_of_ne (le_of_not_gt hpos) (hdne s)
  have hmem : (0 : ℝ) ∈ Set.Icc (d s) (d 0) := ⟨hsneg.le, hd0.le⟩
  obtain ⟨u, hu⟩ := intermediate_value_univ s 0 hd hmem
  exact hdne u hu


-- @@ L815-832 verbatim
theorem det_centerMaximumActualNormalRadialMatrix_pos
    (T : M.CenterImmersion) (hindex : M.index = .maximum)
    (s : I) (theta : ℝ) :
    0 < (M.centerMaximumActualNormalRadialMatrix s theta).det := by
  let d : I → ℝ := fun u =>
    (M.centerMaximumActualNormalRadialMatrix u theta).det
  have hd : Continuous d :=
    (M.continuous_centerMaximumActualNormalRadialMatrix.comp
      (continuous_id.prodMk continuous_const)).matrix_det
  have hd0 : 0 < d 0 := by
    simpa [d] using det_centerMaximumActualLimitMatrix_pos T hindex theta
  have hdne : ∀ u, d u ≠ 0 := fun u =>
    det_centerMaximumActualNormalRadialMatrix_ne_zero T hindex u theta
  by_contra hpos
  have hsneg : d s < 0 := lt_of_le_of_ne (le_of_not_gt hpos) (hdne s)
  have hmem : (0 : ℝ) ∈ Set.Icc (d s) (d 0) := ⟨hsneg.le, hd0.le⟩
  obtain ⟨u, hu⟩ := intermediate_value_univ s 0 hd hmem
  exact hdne u hu


-- @@ L834-834 verbatim
/-! ## Exact rotation of the radial endpoint -/


-- @@ L836-840 verbatim
theorem centerMinimumActualOrientationSign_eq_one_or_neg_one
    (M : StandardMorseEventAt C center) :
    M.centerMinimumActualOrientationSign = 1 ∨
      M.centerMinimumActualOrientationSign = -1 :=
  nonzeroOrientationSign_eq_one_or_neg_one _


-- @@ L842-846 verbatim
theorem centerMaximumActualOrientationSign_eq_one_or_neg_one
    (M : StandardMorseEventAt C center) :
    M.centerMaximumActualOrientationSign = 1 ∨
      M.centerMaximumActualOrientationSign = -1 :=
  nonzeroOrientationSign_eq_one_or_neg_one _


-- @@ L848-859 verbatim
theorem centerSignedTangent_rotation
    (M : StandardMorseEventAt C center) (sigma theta : ℝ)
    (hsigma : sigma = 1 ∨ sigma = -1) :
    sigma • M.centerUnitTangent theta =
      Real.cos (sigma * theta) • (sigma • M.centerUnitTangent 0) -
        Real.sin (sigma * theta) • M.centerRadialTangent 0 := by
  rcases hsigma with rfl | rfl
  · simp only [one_mul, one_smul]
    exact M.centerUnitTangent_rotation theta
  · simp only [neg_mul, neg_smul, Real.cos_neg, Real.sin_neg, one_mul]
    rw [M.centerUnitTangent_rotation theta]
    module


-- @@ L861-872 verbatim
theorem centerSignedRadial_rotation
    (M : StandardMorseEventAt C center) (sigma theta : ℝ)
    (hsigma : sigma = 1 ∨ sigma = -1) :
    M.centerRadialTangent theta =
      Real.sin (sigma * theta) • (sigma • M.centerUnitTangent 0) +
        Real.cos (sigma * theta) • M.centerRadialTangent 0 := by
  rcases hsigma with rfl | rfl
  · simp only [one_mul, one_smul]
    exact M.centerRadialTangent_rotation theta
  · simp only [neg_mul, neg_smul, Real.cos_neg, Real.sin_neg, one_mul]
    rw [M.centerRadialTangent_rotation theta]
    module


-- @@ L874-877 verbatim
def centerSignedRadialRows (M : StandardMorseEventAt C center)
    (sigma theta : ℝ) : Fin (a + 3) → E₁ :=
  centerRowsWith M.centerTransverseNormal
    (sigma • M.centerUnitTangent theta) (M.centerRadialTangent theta)


-- @@ L879-881 verbatim
def centerSignedRadialMatrix (M : StandardMorseEventAt C center)
    (sigma theta : ℝ) : Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ :=
  rowsMatrix (M.centerSignedRadialRows sigma theta)


-- @@ L883-887 verbatim
@[simp] theorem centerSignedRadialRows_zero
    (M : StandardMorseEventAt C center) (sigma theta : ℝ) :
    M.centerSignedRadialRows sigma theta 0 =
      sigma • M.centerUnitTangent theta := by
  simp [centerSignedRadialRows, centerRowsWith]


-- @@ L889-893 verbatim
@[simp] theorem centerSignedRadialRows_last
    (M : StandardMorseEventAt C center) (sigma theta : ℝ) :
    M.centerSignedRadialRows sigma theta (Fin.last (a + 2)) =
      M.centerRadialTangent theta := by
  simp [centerSignedRadialRows, centerRowsWith]


-- @@ L895-900 verbatim
@[simp] theorem centerSignedRadialRows_middle
    (M : StandardMorseEventAt C center) (sigma theta : ℝ)
    (i : Fin (a + 1)) :
    M.centerSignedRadialRows sigma theta i.castSucc.succ =
      M.centerTransverseNormal i := by
  simp [centerSignedRadialRows, centerRowsWith]


-- @@ L902-937 verbatim
theorem centerSignedRadialMatrix_rotation
    (M : StandardMorseEventAt C center) (sigma theta : ℝ)
    (hsigma : sigma = 1 ∨ sigma = -1) :
    M.centerSignedRadialMatrix sigma theta =
      twistMat a (sigma * theta) * M.centerSignedRadialMatrix sigma 0 := by
  ext i j
  rw [StandardBirth.twistMat_mul_apply_birth]
  by_cases hi0 : i = 0
  · subst i
    rw [if_pos rfl]
    simp only [centerSignedRadialMatrix, rowsMatrix, Matrix.of_apply,
      M.centerSignedRadialRows_zero, M.centerSignedRadialRows_last]
    have h := congrArg (fun v : E₁ => v j)
      (M.centerSignedTangent_rotation sigma theta hsigma)
    simpa [sub_eq_add_neg] using h
  · rw [if_neg hi0]
    by_cases hil : i = Fin.last (a + 2)
    · subst i
      rw [if_pos rfl]
      simp only [centerSignedRadialMatrix, rowsMatrix, Matrix.of_apply,
        M.centerSignedRadialRows_zero, M.centerSignedRadialRows_last]
      have h := congrArg (fun v : E₁ => v j)
        (M.centerSignedRadial_rotation sigma theta hsigma)
      simpa using h
    · rw [if_neg hil]
      simp only [centerSignedRadialMatrix, rowsMatrix, Matrix.of_apply]
      obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero hi0
      induction k using Fin.lastCases with
      | last =>
          exfalso
          apply hil
          apply Fin.ext
          simp
      | cast k =>
          rw [M.centerSignedRadialRows_middle,
            M.centerSignedRadialRows_middle]


-- @@ L939-947 verbatim
theorem centerMinimumActualNormalRadialMatrix_one
    (M : StandardMorseEventAt C center) (theta : ℝ) :
    M.centerMinimumActualNormalRadialMatrix 1 theta =
      M.centerSignedRadialMatrix
        M.centerMinimumActualOrientationSign theta := by
  simp [centerMinimumActualNormalRadialMatrix,
    centerMinimumActualNormalRadialRows,
    centerMinimumActualNormalRadialLast,
    centerSignedRadialMatrix, centerSignedRadialRows]


-- @@ L949-957 verbatim
theorem centerMaximumActualNormalRadialMatrix_one
    (M : StandardMorseEventAt C center) (theta : ℝ) :
    M.centerMaximumActualNormalRadialMatrix 1 theta =
      M.centerSignedRadialMatrix
        M.centerMaximumActualOrientationSign theta := by
  simp [centerMaximumActualNormalRadialMatrix,
    centerMaximumActualNormalRadialRows,
    centerMaximumActualNormalRadialLast,
    centerSignedRadialMatrix, centerSignedRadialRows]


-- @@ L959-959 verbatim
/-! ## The plane loop for an arbitrary orientation sign -/


-- @@ L961-963 verbatim
def signedCenterFrameAngle (sigma : ℝ) : C(I, ℝ) where
  toFun u := sigma * (2 * Real.pi * (u : ℝ))
  continuous_toFun := by fun_prop


-- @@ L965-966 verbatim
def signedCenterFrameWinding (sigma : ℝ) : ℤ :=
  if sigma = 1 then 1 else -1


-- @@ L968-977 verbatim
theorem signedCenterFrameAngle_closed (sigma : ℝ)
    (hsigma : sigma = 1 ∨ sigma = -1) :
    signedCenterFrameAngle sigma 1 = signedCenterFrameAngle sigma 0 +
      2 * Real.pi * signedCenterFrameWinding sigma := by
  rcases hsigma with h | h
  · rw [signedCenterFrameWinding, if_pos h]
    simp [signedCenterFrameAngle, h]
  · have hne : sigma ≠ 1 := by rw [h]; norm_num
    rw [signedCenterFrameWinding, if_neg hne]
    simp [signedCenterFrameAngle, h]


-- @@ L979-983 verbatim
def signedCenterSO2AngleLoop (sigma : ℝ)
    (hsigma : sigma = 1 ∨ sigma = -1) : SO2AngleLoop where
  angle := signedCenterFrameAngle sigma
  winding := signedCenterFrameWinding sigma
  angle_closed := signedCenterFrameAngle_closed sigma hsigma


-- @@ L985-990 verbatim
theorem signedCenterFrameWinding_mod_two (sigma : ℝ)
    (hsigma : sigma = 1 ∨ sigma = -1) :
    (signedCenterFrameWinding sigma : ZMod 2) = 1 := by
  rcases hsigma with h | h
  · simp [signedCenterFrameWinding, h]
  · simp [signedCenterFrameWinding, h]


-- @@ L992-996 verbatim
def signedCenterPlaneLoop (sigma : ℝ)
    (hsigma : sigma = 1 ∨ sigma = -1) : C(I, SOGroup (a + 3)) :=
  (ContinuousMap.const I (swapRotSO a) *
      (signedCenterSO2AngleLoop sigma hsigma).frame (a + 3)) *
    ContinuousMap.const I (swapRotSO a)⁻¹


-- @@ L998-1004 verbatim
theorem signedCenterPlaneLoop_closed (sigma : ℝ)
    (hsigma : sigma = 1 ∨ sigma = -1) :
    signedCenterPlaneLoop (a := a) sigma hsigma 0 =
      signedCenterPlaneLoop (a := a) sigma hsigma 1 := by
  simp only [signedCenterPlaneLoop, ContinuousMap.mul_apply,
    ContinuousMap.const_apply]
  rw [(signedCenterSO2AngleLoop sigma hsigma).frame_closed]


-- @@ L1006-1014 verbatim
theorem signedCenterPlaneLoop_coe (sigma : ℝ)
    (hsigma : sigma = 1 ∨ sigma = -1) (u : I) :
    (signedCenterPlaneLoop (a := a) sigma hsigma u :
      Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) =
      twistMat a (signedCenterFrameAngle sigma u) := by
  change swapRotMat a * rotBlock (a + 3)
      (signedCenterFrameAngle sigma u) * (swapRotMat a)ᵀ = _
  rw [rotBlock_eq_rotAmbient]
  rfl


-- @@ L1016-1036 verbatim
theorem loopClassZ2_signedCenterPlaneLoop (sigma : ℝ)
    (hsigma : sigma = 1 ∨ sigma = -1) :
    loopClassZ2 (signedCenterPlaneLoop (a := a) sigma hsigma)
      (signedCenterPlaneLoop_closed sigma hsigma) = 1 := by
  have hr : 3 ≤ a + 3 := by omega
  have hbase :
      loopClassZ2 ((signedCenterSO2AngleLoop sigma hsigma).frame (a + 3))
          ((signedCenterSO2AngleLoop sigma hsigma).frame_closed (a + 3)) = 1 := by
    rw [(signedCenterSO2AngleLoop sigma hsigma).loopClassZ2_frame hr]
    change (signedCenterFrameWinding sigma : ZMod 2) = 1
    exact signedCenterFrameWinding_mod_two sigma hsigma
  have hconj := loopClassZ2_const_conj (swapRotSO a)
    ((signedCenterSO2AngleLoop sigma hsigma).frame (a + 3))
    ((signedCenterSO2AngleLoop sigma hsigma).frame_closed (a + 3))
  have hplane :
      loopClassZ2 (signedCenterPlaneLoop (a := a) sigma hsigma)
          (signedCenterPlaneLoop_closed sigma hsigma) =
        loopClassZ2 ((signedCenterSO2AngleLoop sigma hsigma).frame (a + 3))
          ((signedCenterSO2AngleLoop sigma hsigma).frame_closed (a + 3)) := by
    simpa only [signedCenterPlaneLoop] using hconj
  exact hplane.trans hbase


-- @@ L1038-1044 verbatim
def signedCenterPlaneMatrixLoop (sigma : ℝ)
    (hsigma : sigma = 1 ∨ sigma = -1) :
    C(I, Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) where
  toFun u := (signedCenterPlaneLoop (a := a) sigma hsigma u :
    Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ)
  continuous_toFun := continuous_SOGroup_val.comp
    (signedCenterPlaneLoop (a := a) sigma hsigma).continuous


-- @@ L1046-1049 verbatim
theorem signedCenterPlaneMatrixLoop_det_pos (sigma : ℝ)
    (hsigma : sigma = 1 ∨ sigma = -1) (u : I) :
    0 < (signedCenterPlaneMatrixLoop (a := a) sigma hsigma u).det :=
  SOGroup_det_pos (signedCenterPlaneLoop (a := a) sigma hsigma u)


-- @@ L1051-1055 verbatim
theorem signedCenterPlaneMatrixLoop_closed (sigma : ℝ)
    (hsigma : sigma = 1 ∨ sigma = -1) :
    signedCenterPlaneMatrixLoop (a := a) sigma hsigma 0 =
      signedCenterPlaneMatrixLoop (a := a) sigma hsigma 1 :=
  congrArg Subtype.val (signedCenterPlaneLoop_closed sigma hsigma)


-- @@ L1057-1064 verbatim
theorem positiveMatrixSOMap_signedCenterPlaneMatrixLoop (sigma : ℝ)
    (hsigma : sigma = 1 ∨ sigma = -1) :
    positiveMatrixSOMap
        (signedCenterPlaneMatrixLoop (a := a) sigma hsigma)
        (signedCenterPlaneMatrixLoop_det_pos sigma hsigma) =
      signedCenterPlaneLoop (a := a) sigma hsigma := by
  exact positiveMatrixSOMap_SOGroupMatrixMap
    (signedCenterPlaneLoop (a := a) sigma hsigma)


-- @@ L1066-1083 verbatim
theorem loopClassZ2_positiveMatrixSOMap_signedCenterPlaneMatrixLoop
    (sigma : ℝ) (hsigma : sigma = 1 ∨ sigma = -1) :
    loopClassZ2
        (positiveMatrixSOMap
          (signedCenterPlaneMatrixLoop (a := a) sigma hsigma)
          (signedCenterPlaneMatrixLoop_det_pos sigma hsigma))
        (positiveMatrixSOMap_closed
          (signedCenterPlaneMatrixLoop (a := a) sigma hsigma)
          (signedCenterPlaneMatrixLoop_det_pos sigma hsigma)
          (signedCenterPlaneMatrixLoop_closed sigma hsigma)) = 1 := by
  exact (loopClassZ2_congr_fun
    (positiveMatrixSOMap_closed
      (signedCenterPlaneMatrixLoop (a := a) sigma hsigma)
      (signedCenterPlaneMatrixLoop_det_pos sigma hsigma)
      (signedCenterPlaneMatrixLoop_closed sigma hsigma))
    (signedCenterPlaneLoop_closed sigma hsigma)
    (positiveMatrixSOMap_signedCenterPlaneMatrixLoop sigma hsigma)).trans
      (loopClassZ2_signedCenterPlaneLoop sigma hsigma)


-- @@ L1085-1085 verbatim
/-! ## Normalized positive center loops -/


-- @@ L1087-1094 verbatim
def centerMinimumActualRadialBaseUnit
    (T : M.CenterImmersion) (hindex : M.index = .minimum) :
    (Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ)ˣ :=
  ((Matrix.isUnit_iff_isUnit_det
      (M.centerMinimumActualNormalRadialMatrix 1 0)).mpr
    (isUnit_iff_ne_zero.mpr
      (det_centerMinimumActualNormalRadialMatrix_ne_zero
        T hindex 1 0))).unit


-- @@ L1096-1103 verbatim
def centerMaximumActualRadialBaseUnit
    (T : M.CenterImmersion) (hindex : M.index = .maximum) :
    (Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ)ˣ :=
  ((Matrix.isUnit_iff_isUnit_det
      (M.centerMaximumActualNormalRadialMatrix 1 0)).mpr
    (isUnit_iff_ne_zero.mpr
      (det_centerMaximumActualNormalRadialMatrix_ne_zero
        T hindex 1 0))).unit


-- @@ L1105-1114 verbatim
@[simp] theorem coe_centerMinimumActualRadialBaseUnit
    (T : M.CenterImmersion) (hindex : M.index = .minimum) :
    (centerMinimumActualRadialBaseUnit T hindex :
      Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) =
      M.centerMinimumActualNormalRadialMatrix 1 0 := by
  exact ((Matrix.isUnit_iff_isUnit_det
      (M.centerMinimumActualNormalRadialMatrix 1 0)).mpr
    (isUnit_iff_ne_zero.mpr
      (det_centerMinimumActualNormalRadialMatrix_ne_zero
        T hindex 1 0))).unit_spec


-- @@ L1116-1125 verbatim
@[simp] theorem coe_centerMaximumActualRadialBaseUnit
    (T : M.CenterImmersion) (hindex : M.index = .maximum) :
    (centerMaximumActualRadialBaseUnit T hindex :
      Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) =
      M.centerMaximumActualNormalRadialMatrix 1 0 := by
  exact ((Matrix.isUnit_iff_isUnit_det
      (M.centerMaximumActualNormalRadialMatrix 1 0)).mpr
    (isUnit_iff_ne_zero.mpr
      (det_centerMaximumActualNormalRadialMatrix_ne_zero
        T hindex 1 0))).unit_spec


-- @@ L1127-1132 verbatim
def centerMinimumActualNormalizedMatrix
    (T : M.CenterImmersion) (hindex : M.index = .minimum)
    (s : I) (theta : ℝ) : Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ :=
  M.centerMinimumActualNormalRadialMatrix s theta *
    (↑(centerMinimumActualRadialBaseUnit T hindex)⁻¹ :
      Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ)


-- @@ L1134-1139 verbatim
def centerMaximumActualNormalizedMatrix
    (T : M.CenterImmersion) (hindex : M.index = .maximum)
    (s : I) (theta : ℝ) : Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ :=
  M.centerMaximumActualNormalRadialMatrix s theta *
    (↑(centerMaximumActualRadialBaseUnit T hindex)⁻¹ :
      Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ)


-- @@ L1141-1151 verbatim
theorem centerMinimumActualNormalizedMatrix_one
    (T : M.CenterImmersion) (hindex : M.index = .minimum) (theta : ℝ) :
    centerMinimumActualNormalizedMatrix T hindex 1 theta =
      twistMat a (M.centerMinimumActualOrientationSign * theta) := by
  rw [centerMinimumActualNormalizedMatrix,
    M.centerMinimumActualNormalRadialMatrix_one,
    M.centerSignedRadialMatrix_rotation _ _
      M.centerMinimumActualOrientationSign_eq_one_or_neg_one,
    ← M.centerMinimumActualNormalRadialMatrix_one 0,
    ← coe_centerMinimumActualRadialBaseUnit T hindex]
  rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]


-- @@ L1153-1163 verbatim
theorem centerMaximumActualNormalizedMatrix_one
    (T : M.CenterImmersion) (hindex : M.index = .maximum) (theta : ℝ) :
    centerMaximumActualNormalizedMatrix T hindex 1 theta =
      twistMat a (M.centerMaximumActualOrientationSign * theta) := by
  rw [centerMaximumActualNormalizedMatrix,
    M.centerMaximumActualNormalRadialMatrix_one,
    M.centerSignedRadialMatrix_rotation _ _
      M.centerMaximumActualOrientationSign_eq_one_or_neg_one,
    ← M.centerMaximumActualNormalRadialMatrix_one 0,
    ← coe_centerMaximumActualRadialBaseUnit T hindex]
  rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]


-- @@ L1165-1169 verbatim
theorem continuous_centerMinimumActualNormalizedMatrix
    (T : M.CenterImmersion) (hindex : M.index = .minimum) :
    Continuous fun q : I × ℝ =>
      centerMinimumActualNormalizedMatrix T hindex q.1 q.2 :=
  M.continuous_centerMinimumActualNormalRadialMatrix.matrix_mul continuous_const


-- @@ L1171-1175 verbatim
theorem continuous_centerMaximumActualNormalizedMatrix
    (T : M.CenterImmersion) (hindex : M.index = .maximum) :
    Continuous fun q : I × ℝ =>
      centerMaximumActualNormalizedMatrix T hindex q.1 q.2 :=
  M.continuous_centerMaximumActualNormalRadialMatrix.matrix_mul continuous_const


-- @@ L1177-1187 verbatim
theorem det_centerMinimumActualNormalizedMatrix_ne_zero
    (T : M.CenterImmersion) (hindex : M.index = .minimum)
    (s : I) (theta : ℝ) :
    (centerMinimumActualNormalizedMatrix T hindex s theta).det ≠ 0 := by
  rw [centerMinimumActualNormalizedMatrix, Matrix.det_mul]
  apply mul_ne_zero
  · exact det_centerMinimumActualNormalRadialMatrix_ne_zero T hindex s theta
  · have hu : IsUnit
        (↑(centerMinimumActualRadialBaseUnit T hindex)⁻¹ :
          Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) := Units.isUnit _
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)


-- @@ L1189-1199 verbatim
theorem det_centerMaximumActualNormalizedMatrix_ne_zero
    (T : M.CenterImmersion) (hindex : M.index = .maximum)
    (s : I) (theta : ℝ) :
    (centerMaximumActualNormalizedMatrix T hindex s theta).det ≠ 0 := by
  rw [centerMaximumActualNormalizedMatrix, Matrix.det_mul]
  apply mul_ne_zero
  · exact det_centerMaximumActualNormalRadialMatrix_ne_zero T hindex s theta
  · have hu : IsUnit
        (↑(centerMaximumActualRadialBaseUnit T hindex)⁻¹ :
          Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) := Units.isUnit _
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)


-- @@ L1201-1222 verbatim
theorem det_centerMinimumActualNormalizedMatrix_pos
    (T : M.CenterImmersion) (hindex : M.index = .minimum)
    (s : I) (theta : ℝ) :
    0 < (centerMinimumActualNormalizedMatrix T hindex s theta).det := by
  let d : I → ℝ := fun u =>
    (centerMinimumActualNormalizedMatrix T hindex u theta).det
  have hd : Continuous d :=
    ((continuous_centerMinimumActualNormalizedMatrix T hindex).comp
      (continuous_id.prodMk continuous_const)).matrix_det
  have hdne : ∀ u, d u ≠ 0 := fun u =>
    det_centerMinimumActualNormalizedMatrix_ne_zero T hindex u theta
  have hd1 : d 1 = 1 := by
    dsimp [d]
    rw [centerMinimumActualNormalizedMatrix_one,
      StandardBirth.det_twistMat]
  by_contra hpos
  have hsneg : d s < 0 := lt_of_le_of_ne (le_of_not_gt hpos) (hdne s)
  have hmem : (0 : ℝ) ∈ Set.Icc (d s) (d 1) := by
    rw [hd1]
    exact ⟨hsneg.le, by norm_num⟩
  obtain ⟨u, hu⟩ := intermediate_value_univ s 1 hd hmem
  exact hdne u hu


-- @@ L1224-1245 verbatim
theorem det_centerMaximumActualNormalizedMatrix_pos
    (T : M.CenterImmersion) (hindex : M.index = .maximum)
    (s : I) (theta : ℝ) :
    0 < (centerMaximumActualNormalizedMatrix T hindex s theta).det := by
  let d : I → ℝ := fun u =>
    (centerMaximumActualNormalizedMatrix T hindex u theta).det
  have hd : Continuous d :=
    ((continuous_centerMaximumActualNormalizedMatrix T hindex).comp
      (continuous_id.prodMk continuous_const)).matrix_det
  have hdne : ∀ u, d u ≠ 0 := fun u =>
    det_centerMaximumActualNormalizedMatrix_ne_zero T hindex u theta
  have hd1 : d 1 = 1 := by
    dsimp [d]
    rw [centerMaximumActualNormalizedMatrix_one,
      StandardBirth.det_twistMat]
  by_contra hpos
  have hsneg : d s < 0 := lt_of_le_of_ne (le_of_not_gt hpos) (hdne s)
  have hmem : (0 : ℝ) ∈ Set.Icc (d s) (d 1) := by
    rw [hd1]
    exact ⟨hsneg.le, by norm_num⟩
  obtain ⟨u, hu⟩ := intermediate_value_univ s 1 hd hmem
  exact hdne u hu


-- @@ L1247-1256 verbatim
theorem centerMinimumActualNormalizedMatrix_two_pi
    (T : M.CenterImmersion) (hindex : M.index = .minimum) (s : I) :
    centerMinimumActualNormalizedMatrix T hindex s (2 * Real.pi) =
      centerMinimumActualNormalizedMatrix T hindex s 0 := by
  unfold centerMinimumActualNormalizedMatrix
    centerMinimumActualNormalRadialMatrix
    centerMinimumActualNormalRadialRows
    centerMinimumActualNormalRadialLast centerMinimumUnitNormalLast
  rw [M.centerUnitTangent_two_pi, M.centerNormalRow_zero_two_pi,
    M.centerRadialTangent_two_pi]


-- @@ L1258-1267 verbatim
theorem centerMaximumActualNormalizedMatrix_two_pi
    (T : M.CenterImmersion) (hindex : M.index = .maximum) (s : I) :
    centerMaximumActualNormalizedMatrix T hindex s (2 * Real.pi) =
      centerMaximumActualNormalizedMatrix T hindex s 0 := by
  unfold centerMaximumActualNormalizedMatrix
    centerMaximumActualNormalRadialMatrix
    centerMaximumActualNormalRadialRows
    centerMaximumActualNormalRadialLast centerMaximumUnitNormalLast
  rw [M.centerUnitTangent_two_pi, M.centerNormalRow_zero_two_pi,
    M.centerRadialTangent_two_pi]


-- @@ L1269-1273 verbatim
def centerMinimumActualNormalizedMatrixMap
    (T : M.CenterImmersion) (hindex : M.index = .minimum) :
    C(I × ℝ, Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) where
  toFun q := centerMinimumActualNormalizedMatrix T hindex q.1 q.2
  continuous_toFun := continuous_centerMinimumActualNormalizedMatrix T hindex


-- @@ L1275-1279 verbatim
def centerMaximumActualNormalizedMatrixMap
    (T : M.CenterImmersion) (hindex : M.index = .maximum) :
    C(I × ℝ, Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) where
  toFun q := centerMaximumActualNormalizedMatrix T hindex q.1 q.2
  continuous_toFun := continuous_centerMaximumActualNormalizedMatrix T hindex


-- @@ L1281-1284 verbatim
def centerMinimumActualNormalizedLoop
    (T : M.CenterImmersion) (hindex : M.index = .minimum) :
    C(I, Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) :=
  (centerMinimumActualNormalizedMatrixMap T hindex).comp definiteCenterLoopParam


-- @@ L1286-1289 verbatim
def centerMaximumActualNormalizedLoop
    (T : M.CenterImmersion) (hindex : M.index = .maximum) :
    C(I, Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) :=
  (centerMaximumActualNormalizedMatrixMap T hindex).comp definiteCenterLoopParam


-- @@ L1291-1297 verbatim
theorem centerMinimumActualNormalizedLoop_closed
    (T : M.CenterImmersion) (hindex : M.index = .minimum) :
    centerMinimumActualNormalizedLoop T hindex 0 =
      centerMinimumActualNormalizedLoop T hindex 1 := by
  simpa [centerMinimumActualNormalizedLoop,
    centerMinimumActualNormalizedMatrixMap, definiteCenterLoopParam] using
      (centerMinimumActualNormalizedMatrix_two_pi T hindex 0).symm


-- @@ L1299-1305 verbatim
theorem centerMaximumActualNormalizedLoop_closed
    (T : M.CenterImmersion) (hindex : M.index = .maximum) :
    centerMaximumActualNormalizedLoop T hindex 0 =
      centerMaximumActualNormalizedLoop T hindex 1 := by
  simpa [centerMaximumActualNormalizedLoop,
    centerMaximumActualNormalizedMatrixMap, definiteCenterLoopParam] using
      (centerMaximumActualNormalizedMatrix_two_pi T hindex 0).symm


-- @@ L1307-1311 verbatim
theorem centerMinimumActualNormalizedLoop_det_pos
    (T : M.CenterImmersion) (hindex : M.index = .minimum) (u : I) :
    0 < (centerMinimumActualNormalizedLoop T hindex u).det :=
  det_centerMinimumActualNormalizedMatrix_pos T hindex 0
    (2 * Real.pi * (u : ℝ))


-- @@ L1313-1317 verbatim
theorem centerMaximumActualNormalizedLoop_det_pos
    (T : M.CenterImmersion) (hindex : M.index = .maximum) (u : I) :
    0 < (centerMaximumActualNormalizedLoop T hindex u).det :=
  det_centerMaximumActualNormalizedMatrix_pos T hindex 0
    (2 * Real.pi * (u : ℝ))


-- @@ L1319-1335 verbatim
theorem centerMinimumActualNormalizedMatrix_one_eq_signedPlane
    (T : M.CenterImmersion) (hindex : M.index = .minimum) (u : I) :
    centerMinimumActualNormalizedMatrix T hindex 1
        (2 * Real.pi * (u : ℝ)) =
      signedCenterPlaneMatrixLoop (a := a)
        M.centerMinimumActualOrientationSign
        M.centerMinimumActualOrientationSign_eq_one_or_neg_one u := by
  rw [centerMinimumActualNormalizedMatrix_one]
  rw [show signedCenterPlaneMatrixLoop (a := a)
      M.centerMinimumActualOrientationSign
      M.centerMinimumActualOrientationSign_eq_one_or_neg_one u =
      (signedCenterPlaneLoop (a := a)
        M.centerMinimumActualOrientationSign
        M.centerMinimumActualOrientationSign_eq_one_or_neg_one u :
          Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) by rfl]
  rw [signedCenterPlaneLoop_coe]
  rfl


-- @@ L1337-1353 verbatim
theorem centerMaximumActualNormalizedMatrix_one_eq_signedPlane
    (T : M.CenterImmersion) (hindex : M.index = .maximum) (u : I) :
    centerMaximumActualNormalizedMatrix T hindex 1
        (2 * Real.pi * (u : ℝ)) =
      signedCenterPlaneMatrixLoop (a := a)
        M.centerMaximumActualOrientationSign
        M.centerMaximumActualOrientationSign_eq_one_or_neg_one u := by
  rw [centerMaximumActualNormalizedMatrix_one]
  rw [show signedCenterPlaneMatrixLoop (a := a)
      M.centerMaximumActualOrientationSign
      M.centerMaximumActualOrientationSign_eq_one_or_neg_one u =
      (signedCenterPlaneLoop (a := a)
        M.centerMaximumActualOrientationSign
        M.centerMaximumActualOrientationSign_eq_one_or_neg_one u :
          Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) by rfl]
  rw [signedCenterPlaneLoop_coe]
  rfl


-- @@ L1355-1367 verbatim
def centerMinimumActualBirthMatrixHomotopy
    (T : M.CenterImmersion) (hindex : M.index = .minimum) :
    ContinuousMap.Homotopy
      (centerMinimumActualNormalizedLoop T hindex)
      (signedCenterPlaneMatrixLoop (a := a)
        M.centerMinimumActualOrientationSign
        M.centerMinimumActualOrientationSign_eq_one_or_neg_one) where
  toContinuousMap :=
    (centerMinimumActualNormalizedMatrixMap T hindex).comp
      definiteCenterHomotopyParam
  map_zero_left _u := rfl
  map_one_left u :=
    centerMinimumActualNormalizedMatrix_one_eq_signedPlane T hindex u


-- @@ L1369-1381 verbatim
def centerMaximumActualBirthMatrixHomotopy
    (T : M.CenterImmersion) (hindex : M.index = .maximum) :
    ContinuousMap.Homotopy
      (centerMaximumActualNormalizedLoop T hindex)
      (signedCenterPlaneMatrixLoop (a := a)
        M.centerMaximumActualOrientationSign
        M.centerMaximumActualOrientationSign_eq_one_or_neg_one) where
  toContinuousMap :=
    (centerMaximumActualNormalizedMatrixMap T hindex).comp
      definiteCenterHomotopyParam
  map_zero_left _u := rfl
  map_one_left u :=
    centerMaximumActualNormalizedMatrix_one_eq_signedPlane T hindex u


-- @@ L1383-1388 verbatim
@[simp] theorem centerMinimumActualBirthMatrixHomotopy_apply
    (T : M.CenterImmersion) (hindex : M.index = .minimum) (q : I × I) :
    centerMinimumActualBirthMatrixHomotopy T hindex q =
      centerMinimumActualNormalizedMatrix T hindex q.1
        (2 * Real.pi * (q.2 : ℝ)) :=
  rfl


-- @@ L1390-1395 verbatim
@[simp] theorem centerMaximumActualBirthMatrixHomotopy_apply
    (T : M.CenterImmersion) (hindex : M.index = .maximum) (q : I × I) :
    centerMaximumActualBirthMatrixHomotopy T hindex q =
      centerMaximumActualNormalizedMatrix T hindex q.1
        (2 * Real.pi * (q.2 : ℝ)) :=
  rfl


-- @@ L1397-1401 verbatim
theorem centerMinimumActualBirthMatrixHomotopy_det_pos
    (T : M.CenterImmersion) (hindex : M.index = .minimum) (q : I × I) :
    0 < (centerMinimumActualBirthMatrixHomotopy T hindex q).det :=
  det_centerMinimumActualNormalizedMatrix_pos T hindex q.1
    (2 * Real.pi * (q.2 : ℝ))


-- @@ L1403-1407 verbatim
theorem centerMaximumActualBirthMatrixHomotopy_det_pos
    (T : M.CenterImmersion) (hindex : M.index = .maximum) (q : I × I) :
    0 < (centerMaximumActualBirthMatrixHomotopy T hindex q).det :=
  det_centerMaximumActualNormalizedMatrix_pos T hindex q.1
    (2 * Real.pi * (q.2 : ℝ))


-- @@ L1409-1413 verbatim
theorem centerMinimumActualBirthMatrixHomotopy_closed
    (T : M.CenterImmersion) (hindex : M.index = .minimum) (s : I) :
    centerMinimumActualBirthMatrixHomotopy T hindex (s, 0) =
      centerMinimumActualBirthMatrixHomotopy T hindex (s, 1) := by
  simpa using (centerMinimumActualNormalizedMatrix_two_pi T hindex s).symm


-- @@ L1415-1419 verbatim
theorem centerMaximumActualBirthMatrixHomotopy_closed
    (T : M.CenterImmersion) (hindex : M.index = .maximum) (s : I) :
    centerMaximumActualBirthMatrixHomotopy T hindex (s, 0) =
      centerMaximumActualBirthMatrixHomotopy T hindex (s, 1) := by
  simpa using (centerMaximumActualNormalizedMatrix_two_pi T hindex s).symm


-- @@ L1421-1446 verbatim
theorem loopClassZ2_centerMinimumActualNormalized_eq_one
    (T : M.CenterImmersion) (hindex : M.index = .minimum) :
    loopClassZ2
        (positiveMatrixSOMap
          (centerMinimumActualNormalizedLoop T hindex)
          (centerMinimumActualNormalizedLoop_det_pos T hindex))
        (positiveMatrixSOMap_closed
          (centerMinimumActualNormalizedLoop T hindex)
          (centerMinimumActualNormalizedLoop_det_pos T hindex)
          (centerMinimumActualNormalizedLoop_closed T hindex)) = 1 := by
  have hclass := loopClassZ2_positiveMatrixHomotopy_congr
    (centerMinimumActualBirthMatrixHomotopy T hindex)
    (centerMinimumActualNormalizedLoop_det_pos T hindex)
    (signedCenterPlaneMatrixLoop_det_pos
      M.centerMinimumActualOrientationSign
      M.centerMinimumActualOrientationSign_eq_one_or_neg_one)
    (centerMinimumActualBirthMatrixHomotopy_det_pos T hindex)
    (centerMinimumActualNormalizedLoop_closed T hindex)
    (signedCenterPlaneMatrixLoop_closed
      M.centerMinimumActualOrientationSign
      M.centerMinimumActualOrientationSign_eq_one_or_neg_one)
    (centerMinimumActualBirthMatrixHomotopy_closed T hindex)
  exact hclass.trans
    (loopClassZ2_positiveMatrixSOMap_signedCenterPlaneMatrixLoop
      M.centerMinimumActualOrientationSign
      M.centerMinimumActualOrientationSign_eq_one_or_neg_one)


-- @@ L1448-1473 verbatim
theorem loopClassZ2_centerMaximumActualNormalized_eq_one
    (T : M.CenterImmersion) (hindex : M.index = .maximum) :
    loopClassZ2
        (positiveMatrixSOMap
          (centerMaximumActualNormalizedLoop T hindex)
          (centerMaximumActualNormalizedLoop_det_pos T hindex))
        (positiveMatrixSOMap_closed
          (centerMaximumActualNormalizedLoop T hindex)
          (centerMaximumActualNormalizedLoop_det_pos T hindex)
          (centerMaximumActualNormalizedLoop_closed T hindex)) = 1 := by
  have hclass := loopClassZ2_positiveMatrixHomotopy_congr
    (centerMaximumActualBirthMatrixHomotopy T hindex)
    (centerMaximumActualNormalizedLoop_det_pos T hindex)
    (signedCenterPlaneMatrixLoop_det_pos
      M.centerMaximumActualOrientationSign
      M.centerMaximumActualOrientationSign_eq_one_or_neg_one)
    (centerMaximumActualBirthMatrixHomotopy_det_pos T hindex)
    (centerMaximumActualNormalizedLoop_closed T hindex)
    (signedCenterPlaneMatrixLoop_closed
      M.centerMaximumActualOrientationSign
      M.centerMaximumActualOrientationSign_eq_one_or_neg_one)
    (centerMaximumActualBirthMatrixHomotopy_closed T hindex)
  exact hclass.trans
    (loopClassZ2_positiveMatrixSOMap_signedCenterPlaneMatrixLoop
      M.centerMaximumActualOrientationSign
      M.centerMaximumActualOrientationSign_eq_one_or_neg_one)


-- @@ L1475-1475 verbatim
/-! ## The rescaled positive-radius family -/


-- @@ L1477-1481 verbatim
def centerTransverseNormalAt (M : StandardMorseEventAt C center)
    (r theta : ℝ) (i : Fin (a + 1)) : E₁ :=
  ContinuousLinearMap.adjoint
    (spatialDeriv C.G (M.definiteCircle r theta))
    (M.centerTransverseRangeBasis i : F)


-- @@ L1483-1488 verbatim
@[simp] theorem centerTransverseNormalAt_zero
    (M : StandardMorseEventAt C center) (theta : ℝ) (i : Fin (a + 1)) :
    M.centerTransverseNormalAt 0 theta i = M.centerTransverseNormal i := by
  simp [centerTransverseNormalAt, centerTransverseNormal,
    centerAdjointOnRange, definiteCircle, localPoint,
    definiteCircleParam, pairToMorseParam, M.param_zero]


-- @@ L1490-1517 verbatim
theorem continuousAt_centerTransverseNormalAt_zero
    (M : StandardMorseEventAt C center) (theta₀ : ℝ) (i : Fin (a + 1)) :
    ContinuousAt (fun q : ℝ × ℝ =>
      M.centerTransverseNormalAt q.1 q.2 i) (0, theta₀) := by
  have hspatial : ContDiff ℝ ∞ (spatialDeriv C.G) := by
    change ContDiff ℝ ∞ (fun z => (fderiv ℝ C.G z).comp spaceInclL)
    exact ContDiff.clm_comp (contDiff_fderivCLM C.smooth) contDiff_const
  have hadjoint : ContDiff ℝ ∞
      (fun z => ContinuousLinearMap.adjoint (spatialDeriv C.G z)) := by
    simpa [Function.comp_def] using
      (ExactFiniteMorseJetInstallation.spatialAdjointCLM
        (n := a + 2)).contDiff.comp hspatial
  have happly : ContDiff ℝ ∞
      (fun z => ContinuousLinearMap.adjoint (spatialDeriv C.G z)
        (M.centerTransverseRangeBasis i : F)) :=
    hadjoint.clm_apply contDiff_const
  have hlocal : ContinuousAt (fun u : E₂ =>
      ContinuousLinearMap.adjoint (spatialDeriv C.G (M.param u))
        (M.centerTransverseRangeBasis i : F)) 0 :=
    (happly.contDiffAt.comp 0 M.param_smooth).continuousAt
  have hparam : Continuous (fun q : ℝ × ℝ =>
      definiteCircleParam q.1 q.2) := by
    unfold definiteCircleParam pairToMorseParam
    fun_prop
  have hzero : definiteCircleParam (0 : ℝ) theta₀ = 0 := by
    ext j
    fin_cases j <;> simp [definiteCircleParam, pairToMorseParam]
  exact hlocal.comp_of_eq hparam.continuousAt hzero


-- @@ L1519-1526 verbatim
theorem centerNormalRow_eq_inv_smul
    (M : StandardMorseEventAt C center) {r theta : ℝ} (hr : r ≠ 0) :
    M.centerNormalRow r theta =
      r⁻¹ • M.centerNormalMap (definiteCircleParam r theta) := by
  rw [centerNormalRow, polarFirstQuotient, if_neg hr]
  change r⁻¹ • M.centerNormalMap
      (r • definiteCircleParam 1 theta) = _
  rw [← definiteCircleParam_eq_smul_unit r theta]


-- @@ L1528-1545 verbatim
theorem definiteUnitTangent_two_pi
    (M : StandardMorseEventAt C center) (r : ℝ) :
    M.definiteUnitTangent r (2 * Real.pi) =
      M.definiteUnitTangent r 0 := by
  have hp : definiteCircleParam r (2 * Real.pi) =
      definiteCircleParam r 0 := by
    ext i
    fin_cases i <;>
      simp [definiteCircleParam, pairToMorseParam,
        Real.cos_two_pi, Real.sin_two_pi]
  have ht : definiteCircleTangentParam 1 (2 * Real.pi) =
      definiteCircleTangentParam 1 0 := by
    ext i
    fin_cases i <;>
      simp [definiteCircleTangentParam, pairToMorseParam,
        Real.cos_two_pi, Real.sin_two_pi]
  simp only [definiteUnitTangent]
  rw [hp, ht]


-- @@ L1547-1558 verbatim
theorem centerTransverseNormalAt_two_pi
    (M : StandardMorseEventAt C center) (r : ℝ) (i : Fin (a + 1)) :
    M.centerTransverseNormalAt r (2 * Real.pi) i =
      M.centerTransverseNormalAt r 0 i := by
  have hp : definiteCircleParam r (2 * Real.pi) =
      definiteCircleParam r 0 := by
    ext j
    fin_cases j <;>
      simp [definiteCircleParam, pairToMorseParam,
        Real.cos_two_pi, Real.sin_two_pi]
  simp only [centerTransverseNormalAt, definiteCircle, localPoint]
  rw [hp]


-- @@ L1560-1572 verbatim
theorem centerNormalRow_two_pi
    (M : StandardMorseEventAt C center) (r : ℝ) :
    M.centerNormalRow r (2 * Real.pi) = M.centerNormalRow r 0 := by
  by_cases hr : r = 0
  · subst r
    exact M.centerNormalRow_zero_two_pi
  rw [M.centerNormalRow_eq_inv_smul hr,
    M.centerNormalRow_eq_inv_smul hr]
  congr 2
  ext j
  fin_cases j <;>
    simp [definiteCircleParam, pairToMorseParam,
      Real.cos_two_pi, Real.sin_two_pi]


-- @@ L1574-1581 verbatim
def minimumRescaledRadiusRows
    (M : StandardMorseEventAt C center) (r theta : ℝ) :
    Fin (a + 3) → E₁ :=
  centerRowsWith (M.centerTransverseNormalAt r theta)
    (M.centerMinimumActualOrientationSign • M.definiteUnitTangent r theta)
    (‖M.centerCokernelVector‖⁻¹ •
      (nonzeroOrientationSign M.centerMinimumPairingScalar •
        M.centerNormalRow r theta))


-- @@ L1583-1590 verbatim
def maximumRescaledRadiusRows
    (M : StandardMorseEventAt C center) (r theta : ℝ) :
    Fin (a + 3) → E₁ :=
  centerRowsWith (M.centerTransverseNormalAt r theta)
    (M.centerMaximumActualOrientationSign • M.definiteUnitTangent r theta)
    (‖M.centerCokernelVector‖⁻¹ •
      (nonzeroOrientationSign M.centerMaximumPairingScalar •
        M.centerNormalRow r theta))


-- @@ L1592-1595 verbatim
def minimumRescaledRadiusMatrix
    (M : StandardMorseEventAt C center) (r theta : ℝ) :
    Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ :=
  rowsMatrix (M.minimumRescaledRadiusRows r theta)


-- @@ L1597-1600 verbatim
def maximumRescaledRadiusMatrix
    (M : StandardMorseEventAt C center) (r theta : ℝ) :
    Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ :=
  rowsMatrix (M.maximumRescaledRadiusRows r theta)


-- @@ L1602-1612 verbatim
@[simp] theorem minimumRescaledRadiusMatrix_zero
    (M : StandardMorseEventAt C center) (theta : ℝ) :
    M.minimumRescaledRadiusMatrix 0 theta =
      M.centerMinimumActualLimitMatrix theta := by
  have htrans : M.centerTransverseNormalAt 0 theta =
      M.centerTransverseNormal := by
    funext i
    exact M.centerTransverseNormalAt_zero theta i
  rw [minimumRescaledRadiusMatrix, minimumRescaledRadiusRows, htrans]
  simp [centerMinimumActualLimitMatrix, centerMinimumActualLimitRows,
    centerMinimumUnitNormalLast]


-- @@ L1614-1624 verbatim
@[simp] theorem maximumRescaledRadiusMatrix_zero
    (M : StandardMorseEventAt C center) (theta : ℝ) :
    M.maximumRescaledRadiusMatrix 0 theta =
      M.centerMaximumActualLimitMatrix theta := by
  have htrans : M.centerTransverseNormalAt 0 theta =
      M.centerTransverseNormal := by
    funext i
    exact M.centerTransverseNormalAt_zero theta i
  rw [maximumRescaledRadiusMatrix, maximumRescaledRadiusRows, htrans]
  simp [centerMaximumActualLimitMatrix, centerMaximumActualLimitRows,
    centerMaximumUnitNormalLast]


-- @@ L1626-1631 verbatim
def minimumRescaledNormalizedMatrix
    (T : M.CenterImmersion) (hindex : M.index = .minimum)
    (r theta : ℝ) : Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ :=
  M.minimumRescaledRadiusMatrix r theta *
    (↑(centerMinimumActualRadialBaseUnit T hindex)⁻¹ :
      Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ)


-- @@ L1633-1638 verbatim
def maximumRescaledNormalizedMatrix
    (T : M.CenterImmersion) (hindex : M.index = .maximum)
    (r theta : ℝ) : Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ :=
  M.maximumRescaledRadiusMatrix r theta *
    (↑(centerMaximumActualRadialBaseUnit T hindex)⁻¹ :
      Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ)


-- @@ L1640-1645 verbatim
@[simp] theorem minimumRescaledNormalizedMatrix_zero
    (T : M.CenterImmersion) (hindex : M.index = .minimum) (theta : ℝ) :
    minimumRescaledNormalizedMatrix T hindex 0 theta =
      centerMinimumActualNormalizedMatrix T hindex 0 theta := by
  simp [minimumRescaledNormalizedMatrix,
    centerMinimumActualNormalizedMatrix]


-- @@ L1647-1652 verbatim
@[simp] theorem maximumRescaledNormalizedMatrix_zero
    (T : M.CenterImmersion) (hindex : M.index = .maximum) (theta : ℝ) :
    maximumRescaledNormalizedMatrix T hindex 0 theta =
      centerMaximumActualNormalizedMatrix T hindex 0 theta := by
  simp [maximumRescaledNormalizedMatrix,
    centerMaximumActualNormalizedMatrix]


-- @@ L1654-1695 verbatim
theorem continuousAt_minimumRescaledNormalizedMatrix_zero
    (T : M.CenterImmersion) (hindex : M.index = .minimum) (theta₀ : ℝ) :
    ContinuousAt (fun q : ℝ × ℝ =>
      minimumRescaledNormalizedMatrix T hindex q.1 q.2) (0, theta₀) := by
  apply ContinuousAt.mul
  · let f : (ℝ × ℝ) → Fin (a + 3) → Fin (a + 3) → ℝ :=
      fun q i j => WithLp.ofLp
        (M.minimumRescaledRadiusRows q.1 q.2 i) j
    have hf : ContinuousAt f (0, theta₀) := by
      apply continuousAt_pi.mpr
      intro i
      apply continuousAt_pi.mpr
      intro j
      have hrow : ContinuousAt (fun q : ℝ × ℝ =>
          M.minimumRescaledRadiusRows q.1 q.2 i) (0, theta₀) := by
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
        · exact ((continuous_const : Continuous fun _ : ℝ × ℝ =>
            M.centerMinimumActualOrientationSign).continuousAt.smul
              (M.continuousAt_definiteUnitTangent_zero theta₀))
        · induction i using Fin.lastCases with
          | last =>
              have hn : ContinuousAt (fun q : ℝ × ℝ =>
                  (‖M.centerCokernelVector‖⁻¹ *
                    nonzeroOrientationSign M.centerMinimumPairingScalar) •
                      M.centerNormalRow q.1 q.2) (0, theta₀) := by
                exact (M.continuousAt_centerNormalRow_zero theta₀).const_smul
                  (‖M.centerCokernelVector‖⁻¹ *
                    nonzeroOrientationSign M.centerMinimumPairingScalar)
              simpa [minimumRescaledRadiusRows, centerRowsWith,
                smul_smul] using hn
          | cast i =>
              simpa [minimumRescaledRadiusRows, centerRowsWith] using
                M.continuousAt_centerTransverseNormalAt_zero theta₀ i
      exact (EuclideanSpace.proj j).continuous.continuousAt.comp hrow
    have hOf : Continuous
        (Matrix.of : (Fin (a + 3) → Fin (a + 3) → ℝ) →
          Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) := by
      rw [continuous_matrixOf]
      exact continuous_id
    simpa [minimumRescaledRadiusMatrix, rowsMatrix, f,
      Function.comp_def] using hOf.continuousAt.comp hf
  · exact continuousAt_const


-- @@ L1697-1738 verbatim
theorem continuousAt_maximumRescaledNormalizedMatrix_zero
    (T : M.CenterImmersion) (hindex : M.index = .maximum) (theta₀ : ℝ) :
    ContinuousAt (fun q : ℝ × ℝ =>
      maximumRescaledNormalizedMatrix T hindex q.1 q.2) (0, theta₀) := by
  apply ContinuousAt.mul
  · let f : (ℝ × ℝ) → Fin (a + 3) → Fin (a + 3) → ℝ :=
      fun q i j => WithLp.ofLp
        (M.maximumRescaledRadiusRows q.1 q.2 i) j
    have hf : ContinuousAt f (0, theta₀) := by
      apply continuousAt_pi.mpr
      intro i
      apply continuousAt_pi.mpr
      intro j
      have hrow : ContinuousAt (fun q : ℝ × ℝ =>
          M.maximumRescaledRadiusRows q.1 q.2 i) (0, theta₀) := by
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
        · exact ((continuous_const : Continuous fun _ : ℝ × ℝ =>
            M.centerMaximumActualOrientationSign).continuousAt.smul
              (M.continuousAt_definiteUnitTangent_zero theta₀))
        · induction i using Fin.lastCases with
          | last =>
              have hn : ContinuousAt (fun q : ℝ × ℝ =>
                  (‖M.centerCokernelVector‖⁻¹ *
                    nonzeroOrientationSign M.centerMaximumPairingScalar) •
                      M.centerNormalRow q.1 q.2) (0, theta₀) := by
                exact (M.continuousAt_centerNormalRow_zero theta₀).const_smul
                  (‖M.centerCokernelVector‖⁻¹ *
                    nonzeroOrientationSign M.centerMaximumPairingScalar)
              simpa [maximumRescaledRadiusRows, centerRowsWith,
                smul_smul] using hn
          | cast i =>
              simpa [maximumRescaledRadiusRows, centerRowsWith] using
                M.continuousAt_centerTransverseNormalAt_zero theta₀ i
      exact (EuclideanSpace.proj j).continuous.continuousAt.comp hrow
    have hOf : Continuous
        (Matrix.of : (Fin (a + 3) → Fin (a + 3) → ℝ) →
          Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) := by
      rw [continuous_matrixOf]
      exact continuous_id
    simpa [maximumRescaledRadiusMatrix, rowsMatrix, f,
      Function.comp_def] using hOf.continuousAt.comp hf
  · exact continuousAt_const


-- @@ L1740-1750 verbatim
theorem minimumRescaledNormalizedMatrix_two_pi
    (T : M.CenterImmersion) (hindex : M.index = .minimum) (r : ℝ) :
    minimumRescaledNormalizedMatrix T hindex r (2 * Real.pi) =
      minimumRescaledNormalizedMatrix T hindex r 0 := by
  have htrans : M.centerTransverseNormalAt r (2 * Real.pi) =
      M.centerTransverseNormalAt r 0 := by
    funext i
    exact M.centerTransverseNormalAt_two_pi r i
  unfold minimumRescaledNormalizedMatrix minimumRescaledRadiusMatrix
    minimumRescaledRadiusRows
  rw [htrans, M.definiteUnitTangent_two_pi, M.centerNormalRow_two_pi]


-- @@ L1752-1762 verbatim
theorem maximumRescaledNormalizedMatrix_two_pi
    (T : M.CenterImmersion) (hindex : M.index = .maximum) (r : ℝ) :
    maximumRescaledNormalizedMatrix T hindex r (2 * Real.pi) =
      maximumRescaledNormalizedMatrix T hindex r 0 := by
  have htrans : M.centerTransverseNormalAt r (2 * Real.pi) =
      M.centerTransverseNormalAt r 0 := by
    funext i
    exact M.centerTransverseNormalAt_two_pi r i
  unfold maximumRescaledNormalizedMatrix maximumRescaledRadiusMatrix
    maximumRescaledRadiusRows
  rw [htrans, M.definiteUnitTangent_two_pi, M.centerNormalRow_two_pi]


-- @@ L1764-1764 verbatim
/-! ## Continuous positive-radius loops in a local `C¹` ball -/


-- @@ L1766-1775 verbatim
theorem exists_param_contDiffOn_ball_one
    (M : StandardMorseEventAt C center) :
    ∃ rho : ℝ, 0 < rho ∧
      ContDiffOn ℝ 1 M.param (ball (0 : E₂) rho) := by
  obtain ⟨U, hUopen, h0U, hC1⟩ :=
    M.param_smooth.contDiffOn' (m := (1 : ℕ∞ω)) (by simp) (by simp)
  have hC1U : ContDiffOn ℝ 1 M.param U := by
    simpa using hC1
  obtain ⟨rho, hrho, hball⟩ := Metric.isOpen_iff.mp hUopen 0 h0U
  exact ⟨rho, hrho, hC1U.mono hball⟩


-- @@ L1777-1799 verbatim
theorem continuous_definiteUnitTangent_radius_of_contDiffOn
    (M : StandardMorseEventAt C center) {rho r : ℝ}
    (hC1 : ContDiffOn ℝ 1 M.param (ball (0 : E₂) rho))
    (hr : 0 ≤ r) (hrrho : r < rho) :
    Continuous fun theta : ℝ => M.definiteUnitTangent r theta := by
  have hp : Continuous fun theta : ℝ => definiteCircleParam r theta := by
    unfold definiteCircleParam pairToMorseParam
    fun_prop
  have hpmem : ∀ theta : ℝ,
      definiteCircleParam r theta ∈ ball (0 : E₂) rho := by
    intro theta
    rw [mem_ball, dist_zero_right, norm_definiteCircleParam hr]
    exact hrrho
  have hD : Continuous fun theta : ℝ =>
      fderiv ℝ M.param (definiteCircleParam r theta) := by
    exact ContinuousOn.comp_continuous
      (hC1.continuousOn_fderiv_of_isOpen isOpen_ball (by simp))
      hp hpmem
  have ht : Continuous fun theta : ℝ =>
      definiteCircleTangentParam 1 theta := by
    unfold definiteCircleTangentParam pairToMorseParam
    fun_prop
  exact continuous_spacePart.comp (hD.clm_apply ht)


-- @@ L1801-1812 verbatim
theorem continuous_centerParamCircle
    (T : M.CenterImmersion) {r : ℝ}
    (hr : 0 ≤ r) (hrradius : r < T.radius) :
    Continuous fun theta : ℝ => M.param (definiteCircleParam r theta) := by
  have hp : Continuous fun theta : ℝ => definiteCircleParam r theta := by
    unfold definiteCircleParam pairToMorseParam
    fun_prop
  rw [continuous_iff_continuousAt]
  intro theta
  exact (T.param_differentiableAt _ (by
    rw [norm_definiteCircleParam hr]
    exact hrradius)).continuousAt.comp hp.continuousAt


-- @@ L1814-1830 verbatim
theorem continuous_centerTransverseNormalAt_radius
    (T : M.CenterImmersion) {r : ℝ}
    (hr : 0 ≤ r) (hrradius : r < T.radius) (i : Fin (a + 1)) :
    Continuous fun theta : ℝ => M.centerTransverseNormalAt r theta i := by
  have hspatial : ContDiff ℝ ∞ (spatialDeriv C.G) := by
    change ContDiff ℝ ∞ (fun z => (fderiv ℝ C.G z).comp spaceInclL)
    exact ContDiff.clm_comp (contDiff_fderivCLM C.smooth) contDiff_const
  have hadjoint : ContDiff ℝ ∞
      (fun z => ContinuousLinearMap.adjoint (spatialDeriv C.G z)) := by
    simpa [Function.comp_def] using
      (ExactFiniteMorseJetInstallation.spatialAdjointCLM
        (n := a + 2)).contDiff.comp hspatial
  have happly : Continuous
      (fun z => ContinuousLinearMap.adjoint (spatialDeriv C.G z)
        (M.centerTransverseRangeBasis i : F)) :=
    (hadjoint.clm_apply contDiff_const).continuous
  exact happly.comp (continuous_centerParamCircle T hr hrradius)


-- @@ L1832-1853 verbatim
theorem continuous_centerNormalRow_radius
    (T : M.CenterImmersion) {r : ℝ}
    (hr : 0 < r) (hrradius : r < T.radius) :
    Continuous fun theta : ℝ => M.centerNormalRow r theta := by
  have hspatial : ContDiff ℝ ∞ (spatialDeriv C.G) := by
    change ContDiff ℝ ∞ (fun z => (fderiv ℝ C.G z).comp spaceInclL)
    exact ContDiff.clm_comp (contDiff_fderivCLM C.smooth) contDiff_const
  have hadjoint : ContDiff ℝ ∞
      (fun z => ContinuousLinearMap.adjoint (spatialDeriv C.G z)) := by
    simpa [Function.comp_def] using
      (ExactFiniteMorseJetInstallation.spatialAdjointCLM
        (n := a + 2)).contDiff.comp hspatial
  have hnormal : Continuous fun theta : ℝ =>
      M.centerNormalMap (definiteCircleParam r theta) := by
    exact ((hadjoint.clm_apply contDiff_const).continuous).comp
      (continuous_centerParamCircle T hr.le hrradius)
  have heq : (fun theta : ℝ => M.centerNormalRow r theta) =
      fun theta => r⁻¹ • M.centerNormalMap (definiteCircleParam r theta) := by
    funext theta
    exact M.centerNormalRow_eq_inv_smul hr.ne'
  rw [heq]
  exact hnormal.const_smul r⁻¹


-- @@ L1855-1891 verbatim
theorem continuous_minimumRescaledNormalizedMatrix_radius
    (T : M.CenterImmersion) (hindex : M.index = .minimum)
    {rho r : ℝ}
    (hC1 : ContDiffOn ℝ 1 M.param (ball (0 : E₂) rho))
    (hr : 0 < r) (hrrho : r < rho) (hrradius : r < T.radius) :
    Continuous fun theta : ℝ =>
      minimumRescaledNormalizedMatrix T hindex r theta := by
  apply Continuous.mul
  · apply continuous_matrix
    intro i j
    have hrow : Continuous fun theta : ℝ =>
        M.minimumRescaledRadiusRows r theta i := by
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
      · have ht : Continuous fun theta : ℝ =>
            M.centerMinimumActualOrientationSign •
              M.definiteUnitTangent r theta :=
          (continuous_const_smul M.centerMinimumActualOrientationSign).comp
            (M.continuous_definiteUnitTangent_radius_of_contDiffOn
              hC1 hr.le hrrho)
        simpa [minimumRescaledRadiusRows, centerRowsWith] using ht
      · induction i using Fin.lastCases with
        | last =>
            have hn : Continuous fun theta : ℝ =>
                (‖M.centerCokernelVector‖⁻¹ *
                  nonzeroOrientationSign M.centerMinimumPairingScalar) •
                    M.centerNormalRow r theta :=
              (continuous_const_smul
                (‖M.centerCokernelVector‖⁻¹ *
                  nonzeroOrientationSign M.centerMinimumPairingScalar)).comp
                (continuous_centerNormalRow_radius T hr hrradius)
            simpa [minimumRescaledRadiusRows, centerRowsWith,
              smul_smul] using hn
        | cast i =>
            simpa [minimumRescaledRadiusRows, centerRowsWith] using
              continuous_centerTransverseNormalAt_radius T hr.le hrradius i
    exact (EuclideanSpace.proj j).continuous.comp hrow
  · exact continuous_const


-- @@ L1893-1929 verbatim
theorem continuous_maximumRescaledNormalizedMatrix_radius
    (T : M.CenterImmersion) (hindex : M.index = .maximum)
    {rho r : ℝ}
    (hC1 : ContDiffOn ℝ 1 M.param (ball (0 : E₂) rho))
    (hr : 0 < r) (hrrho : r < rho) (hrradius : r < T.radius) :
    Continuous fun theta : ℝ =>
      maximumRescaledNormalizedMatrix T hindex r theta := by
  apply Continuous.mul
  · apply continuous_matrix
    intro i j
    have hrow : Continuous fun theta : ℝ =>
        M.maximumRescaledRadiusRows r theta i := by
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
      · have ht : Continuous fun theta : ℝ =>
            M.centerMaximumActualOrientationSign •
              M.definiteUnitTangent r theta :=
          (continuous_const_smul M.centerMaximumActualOrientationSign).comp
            (M.continuous_definiteUnitTangent_radius_of_contDiffOn
              hC1 hr.le hrrho)
        simpa [maximumRescaledRadiusRows, centerRowsWith] using ht
      · induction i using Fin.lastCases with
        | last =>
            have hn : Continuous fun theta : ℝ =>
                (‖M.centerCokernelVector‖⁻¹ *
                  nonzeroOrientationSign M.centerMaximumPairingScalar) •
                    M.centerNormalRow r theta :=
              (continuous_const_smul
                (‖M.centerCokernelVector‖⁻¹ *
                  nonzeroOrientationSign M.centerMaximumPairingScalar)).comp
                (continuous_centerNormalRow_radius T hr hrradius)
            simpa [maximumRescaledRadiusRows, centerRowsWith,
              smul_smul] using hn
        | cast i =>
            simpa [maximumRescaledRadiusRows, centerRowsWith] using
              continuous_centerTransverseNormalAt_radius T hr.le hrradius i
    exact (EuclideanSpace.proj j).continuous.comp hrow
  · exact continuous_const


-- @@ L1931-1942 verbatim
def minimumRescaledNormalizedLoopAt
    (T : M.CenterImmersion) (hindex : M.index = .minimum)
    {rho r : ℝ}
    (hC1 : ContDiffOn ℝ 1 M.param (ball (0 : E₂) rho))
    (hr : 0 < r) (hrrho : r < rho) (hrradius : r < T.radius) :
    C(I, Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) where
  toFun u := minimumRescaledNormalizedMatrix T hindex r
    (2 * Real.pi * (u : ℝ))
  continuous_toFun :=
    (continuous_minimumRescaledNormalizedMatrix_radius
      T hindex hC1 hr hrrho hrradius).comp
        (continuous_const.mul continuous_subtype_val)


-- @@ L1944-1955 verbatim
def maximumRescaledNormalizedLoopAt
    (T : M.CenterImmersion) (hindex : M.index = .maximum)
    {rho r : ℝ}
    (hC1 : ContDiffOn ℝ 1 M.param (ball (0 : E₂) rho))
    (hr : 0 < r) (hrrho : r < rho) (hrradius : r < T.radius) :
    C(I, Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) where
  toFun u := maximumRescaledNormalizedMatrix T hindex r
    (2 * Real.pi * (u : ℝ))
  continuous_toFun :=
    (continuous_maximumRescaledNormalizedMatrix_radius
      T hindex hC1 hr hrrho hrradius).comp
        (continuous_const.mul continuous_subtype_val)


-- @@ L1957-1965 verbatim
theorem minimumRescaledNormalizedLoopAt_closed
    (T : M.CenterImmersion) (hindex : M.index = .minimum)
    {rho r : ℝ}
    (hC1 : ContDiffOn ℝ 1 M.param (ball (0 : E₂) rho))
    (hr : 0 < r) (hrrho : r < rho) (hrradius : r < T.radius) :
    minimumRescaledNormalizedLoopAt T hindex hC1 hr hrrho hrradius 0 =
      minimumRescaledNormalizedLoopAt T hindex hC1 hr hrrho hrradius 1 := by
  simpa [minimumRescaledNormalizedLoopAt] using
    (minimumRescaledNormalizedMatrix_two_pi T hindex r).symm


-- @@ L1967-1975 verbatim
theorem maximumRescaledNormalizedLoopAt_closed
    (T : M.CenterImmersion) (hindex : M.index = .maximum)
    {rho r : ℝ}
    (hC1 : ContDiffOn ℝ 1 M.param (ball (0 : E₂) rho))
    (hr : 0 < r) (hrrho : r < rho) (hrradius : r < T.radius) :
    maximumRescaledNormalizedLoopAt T hindex hC1 hr hrrho hrradius 0 =
      maximumRescaledNormalizedLoopAt T hindex hC1 hr hrrho hrradius 1 := by
  simpa [maximumRescaledNormalizedLoopAt] using
    (maximumRescaledNormalizedMatrix_two_pi T hindex r).symm


-- @@ L1977-1977 verbatim
/-! ## A uniformly positive small-radius segment -/


-- @@ L1979-2047 verbatim
theorem eventually_minimumRescaledNormalized_segment_det_pos
    (T : M.CenterImmersion) (hindex : M.index = .minimum) :
    ∀ᶠ r in nhds (0 : ℝ), ∀ q : I × I,
      0 < (matrixSegment
        (minimumRescaledNormalizedMatrix T hindex r
          (2 * Real.pi * (q.2 : ℝ)))
        (centerMinimumActualNormalizedLoop T hindex q.2) q.1).det := by
  let L : ℝ → I × I → Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ :=
    fun r q => matrixSegment
      (minimumRescaledNormalizedMatrix T hindex r
        (2 * Real.pi * (q.2 : ℝ)))
      (centerMinimumActualNormalizedLoop T hindex q.2) q.1
  have hL : ∀ q ∈ (Set.univ : Set (I × I)),
      ContinuousAt (fun z : ℝ × (I × I) => L z.1 z.2) (0, q) := by
    intro q _
    have hparam : Continuous fun z : ℝ × (I × I) =>
        (z.1, 2 * Real.pi * (z.2.2 : ℝ)) := by
      fun_prop
    have hA0 :=
      continuousAt_minimumRescaledNormalizedMatrix_zero T hindex
        (2 * Real.pi * (q.2 : ℝ))
    have hA : ContinuousAt (fun z : ℝ × (I × I) =>
        minimumRescaledNormalizedMatrix T hindex z.1
          (2 * Real.pi * (z.2.2 : ℝ))) (0, q) := by
      have hmap_eq :
          (fun z : ℝ × (I × I) =>
            (z.1, 2 * Real.pi * (z.2.2 : ℝ))) (0, q) =
            (0, 2 * Real.pi * (q.2 : ℝ)) := rfl
      have hcomp := ContinuousAt.comp_of_eq
        (f := fun z : ℝ × (I × I) =>
          (z.1, 2 * Real.pi * (z.2.2 : ℝ)))
        (g := fun p : ℝ × ℝ =>
          minimumRescaledNormalizedMatrix T hindex p.1 p.2)
        hA0 hparam.continuousAt hmap_eq
      simpa only [Function.comp_def] using hcomp
    have hS : ContinuousAt (fun z : ℝ × (I × I) =>
        centerMinimumActualNormalizedLoop T hindex z.2.2) (0, q) :=
      (centerMinimumActualNormalizedLoop T hindex).continuous.continuousAt.comp
        (continuous_snd.comp continuous_snd).continuousAt
    have hs : ContinuousAt (fun z : ℝ × (I × I) =>
        (z.2.1 : ℝ)) (0, q) :=
      (continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).continuousAt
    have hone : ContinuousAt (fun _ : ℝ × (I × I) => (1 : ℝ)) (0, q) :=
      continuousAt_const
    dsimp only [L]
    unfold matrixSegment
    exact ((hone.sub hs).smul hA).add (hs.smul hS)
  have hpos : ∀ q ∈ (Set.univ : Set (I × I)),
      0 < (L 0 q).det := by
    intro q _
    have heq : minimumRescaledNormalizedMatrix T hindex 0
        (2 * Real.pi * (q.2 : ℝ)) =
        centerMinimumActualNormalizedLoop T hindex q.2 := by
      rw [minimumRescaledNormalizedMatrix_zero]
      rfl
    dsimp only [L]
    rw [heq]
    have hseg : matrixSegment
        (centerMinimumActualNormalizedLoop T hindex q.2)
        (centerMinimumActualNormalizedLoop T hindex q.2) q.1 =
        centerMinimumActualNormalizedLoop T hindex q.2 := by
      unfold matrixSegment
      module
    rw [hseg]
    exact centerMinimumActualNormalizedLoop_det_pos T hindex q.2
  change ∀ᶠ r in nhds (0 : ℝ), ∀ q : I × I, 0 < (L r q).det
  simpa only [Set.mem_univ, forall_const] using
    (eventually_uniform_det_pos_of_continuousAt
      isCompact_univ L hL hpos)


-- @@ L2049-2117 verbatim
theorem eventually_maximumRescaledNormalized_segment_det_pos
    (T : M.CenterImmersion) (hindex : M.index = .maximum) :
    ∀ᶠ r in nhds (0 : ℝ), ∀ q : I × I,
      0 < (matrixSegment
        (maximumRescaledNormalizedMatrix T hindex r
          (2 * Real.pi * (q.2 : ℝ)))
        (centerMaximumActualNormalizedLoop T hindex q.2) q.1).det := by
  let L : ℝ → I × I → Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ :=
    fun r q => matrixSegment
      (maximumRescaledNormalizedMatrix T hindex r
        (2 * Real.pi * (q.2 : ℝ)))
      (centerMaximumActualNormalizedLoop T hindex q.2) q.1
  have hL : ∀ q ∈ (Set.univ : Set (I × I)),
      ContinuousAt (fun z : ℝ × (I × I) => L z.1 z.2) (0, q) := by
    intro q _
    have hparam : Continuous fun z : ℝ × (I × I) =>
        (z.1, 2 * Real.pi * (z.2.2 : ℝ)) := by
      fun_prop
    have hA0 :=
      continuousAt_maximumRescaledNormalizedMatrix_zero T hindex
        (2 * Real.pi * (q.2 : ℝ))
    have hA : ContinuousAt (fun z : ℝ × (I × I) =>
        maximumRescaledNormalizedMatrix T hindex z.1
          (2 * Real.pi * (z.2.2 : ℝ))) (0, q) := by
      have hmap_eq :
          (fun z : ℝ × (I × I) =>
            (z.1, 2 * Real.pi * (z.2.2 : ℝ))) (0, q) =
            (0, 2 * Real.pi * (q.2 : ℝ)) := rfl
      have hcomp := ContinuousAt.comp_of_eq
        (f := fun z : ℝ × (I × I) =>
          (z.1, 2 * Real.pi * (z.2.2 : ℝ)))
        (g := fun p : ℝ × ℝ =>
          maximumRescaledNormalizedMatrix T hindex p.1 p.2)
        hA0 hparam.continuousAt hmap_eq
      simpa only [Function.comp_def] using hcomp
    have hS : ContinuousAt (fun z : ℝ × (I × I) =>
        centerMaximumActualNormalizedLoop T hindex z.2.2) (0, q) :=
      (centerMaximumActualNormalizedLoop T hindex).continuous.continuousAt.comp
        (continuous_snd.comp continuous_snd).continuousAt
    have hs : ContinuousAt (fun z : ℝ × (I × I) =>
        (z.2.1 : ℝ)) (0, q) :=
      (continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).continuousAt
    have hone : ContinuousAt (fun _ : ℝ × (I × I) => (1 : ℝ)) (0, q) :=
      continuousAt_const
    dsimp only [L]
    unfold matrixSegment
    exact ((hone.sub hs).smul hA).add (hs.smul hS)
  have hpos : ∀ q ∈ (Set.univ : Set (I × I)),
      0 < (L 0 q).det := by
    intro q _
    have heq : maximumRescaledNormalizedMatrix T hindex 0
        (2 * Real.pi * (q.2 : ℝ)) =
        centerMaximumActualNormalizedLoop T hindex q.2 := by
      rw [maximumRescaledNormalizedMatrix_zero]
      rfl
    dsimp only [L]
    rw [heq]
    have hseg : matrixSegment
        (centerMaximumActualNormalizedLoop T hindex q.2)
        (centerMaximumActualNormalizedLoop T hindex q.2) q.1 =
        centerMaximumActualNormalizedLoop T hindex q.2 := by
      unfold matrixSegment
      module
    rw [hseg]
    exact centerMaximumActualNormalizedLoop_det_pos T hindex q.2
  change ∀ᶠ r in nhds (0 : ℝ), ∀ q : I × I, 0 < (L r q).det
  simpa only [Set.mem_univ, forall_const] using
    (eventually_uniform_det_pos_of_continuousAt
      isCompact_univ L hL hpos)


-- @@ L2119-2139 verbatim
theorem exists_pos_radius_minimumRescaledNormalized_segment_det_pos
    (T : M.CenterImmersion) (hindex : M.index = .minimum)
    {rho : ℝ} (hrho : 0 < rho) :
    ∃ r, 0 < r ∧ r < rho ∧ ∀ q : I × I,
      0 < (matrixSegment
        (minimumRescaledNormalizedMatrix T hindex r
          (2 * Real.pi * (q.2 : ℝ)))
        (centerMinimumActualNormalizedLoop T hindex q.2) q.1).det := by
  have hevent :=
    eventually_minimumRescaledNormalized_segment_det_pos T hindex
  obtain ⟨eps, heps, heps_sub⟩ := Metric.mem_nhds_iff.mp hevent
  let r := min (rho / 2) (eps / 2)
  have hr : 0 < r := lt_min (half_pos hrho) (half_pos heps)
  have hrrho : r < rho :=
    (min_le_left (rho / 2) (eps / 2)).trans_lt (half_lt_self hrho)
  have hreps : r < eps :=
    (min_le_right (rho / 2) (eps / 2)).trans_lt (half_lt_self heps)
  refine ⟨r, hr, hrrho, ?_⟩
  apply heps_sub
  simpa [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hr]
    using hreps


-- @@ L2141-2161 verbatim
theorem exists_pos_radius_maximumRescaledNormalized_segment_det_pos
    (T : M.CenterImmersion) (hindex : M.index = .maximum)
    {rho : ℝ} (hrho : 0 < rho) :
    ∃ r, 0 < r ∧ r < rho ∧ ∀ q : I × I,
      0 < (matrixSegment
        (maximumRescaledNormalizedMatrix T hindex r
          (2 * Real.pi * (q.2 : ℝ)))
        (centerMaximumActualNormalizedLoop T hindex q.2) q.1).det := by
  have hevent :=
    eventually_maximumRescaledNormalized_segment_det_pos T hindex
  obtain ⟨eps, heps, heps_sub⟩ := Metric.mem_nhds_iff.mp hevent
  let r := min (rho / 2) (eps / 2)
  have hr : 0 < r := lt_min (half_pos hrho) (half_pos heps)
  have hrrho : r < rho :=
    (min_le_left (rho / 2) (eps / 2)).trans_lt (half_lt_self hrho)
  have hreps : r < eps :=
    (min_le_right (rho / 2) (eps / 2)).trans_lt (half_lt_self heps)
  refine ⟨r, hr, hrrho, ?_⟩
  apply heps_sub
  simpa [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hr]
    using hreps


-- @@ L2163-2207 verbatim
theorem exists_minimumRescaledNormalizedLoop_class_one
    (T : M.EmbeddedShrink) (hindex : M.index = .minimum) :
    ∃ rho : ℝ, ∃ hrho : 0 < rho,
      ∃ hC1 : ContDiffOn ℝ 1 M.param (ball (0 : E₂) rho),
      ∃ r : ℝ, ∃ hr : 0 < r, ∃ hrrho : r < rho,
      ∃ hrradius : r < T.radius,
      ∃ hpos : ∀ u,
        0 < (minimumRescaledNormalizedLoopAt T.toCenterImmersion hindex
          hC1 hr hrrho hrradius u).det,
      loopClassZ2
          (positiveMatrixSOMap
            (minimumRescaledNormalizedLoopAt T.toCenterImmersion hindex
              hC1 hr hrrho hrradius) hpos)
          (positiveMatrixSOMap_closed
            (minimumRescaledNormalizedLoopAt T.toCenterImmersion hindex
              hC1 hr hrrho hrradius) hpos
            (minimumRescaledNormalizedLoopAt_closed T.toCenterImmersion hindex
              hC1 hr hrrho hrradius)) = 1 := by
  obtain ⟨rho, hrho, hC1⟩ := exists_param_contDiffOn_ball_one M
  let T₀ := T.toCenterImmersion
  have hbound : 0 < min T.radius rho := lt_min T.radius_pos hrho
  obtain ⟨r, hr, hrbound, hsegment⟩ :=
    exists_pos_radius_minimumRescaledNormalized_segment_det_pos
      T₀ hindex hbound
  have hrradius : r < T.radius := hrbound.trans_le (min_le_left _ _)
  have hrrho : r < rho := hrbound.trans_le (min_le_right _ _)
  let A := minimumRescaledNormalizedLoopAt T₀ hindex
    hC1 hr hrrho hrradius
  have hpos : ∀ u, 0 < (A u).det := by
    intro u
    have h := hsegment (0, u)
    simpa [A, minimumRescaledNormalizedLoopAt] using h
  have hclosed : A 0 = A 1 :=
    minimumRescaledNormalizedLoopAt_closed T₀ hindex
      hC1 hr hrrho hrradius
  have hsegA : ∀ q : I × I,
      0 < (matrixSegment (A q.2)
        (centerMinimumActualNormalizedLoop T₀ hindex q.2) q.1).det := by
    simpa [A, minimumRescaledNormalizedLoopAt] using hsegment
  refine ⟨rho, hrho, hC1, r, hr, hrrho, hrradius, hpos, ?_⟩
  exact loopClassZ2_positiveMatrixSOMap_eq_one_of_segment_pos
    A (centerMinimumActualNormalizedLoop T₀ hindex)
    hpos (centerMinimumActualNormalizedLoop_det_pos T₀ hindex)
    hclosed (centerMinimumActualNormalizedLoop_closed T₀ hindex)
    (loopClassZ2_centerMinimumActualNormalized_eq_one T₀ hindex) hsegA


-- @@ L2209-2253 verbatim
theorem exists_maximumRescaledNormalizedLoop_class_one
    (T : M.EmbeddedShrink) (hindex : M.index = .maximum) :
    ∃ rho : ℝ, ∃ hrho : 0 < rho,
      ∃ hC1 : ContDiffOn ℝ 1 M.param (ball (0 : E₂) rho),
      ∃ r : ℝ, ∃ hr : 0 < r, ∃ hrrho : r < rho,
      ∃ hrradius : r < T.radius,
      ∃ hpos : ∀ u,
        0 < (maximumRescaledNormalizedLoopAt T.toCenterImmersion hindex
          hC1 hr hrrho hrradius u).det,
      loopClassZ2
          (positiveMatrixSOMap
            (maximumRescaledNormalizedLoopAt T.toCenterImmersion hindex
              hC1 hr hrrho hrradius) hpos)
          (positiveMatrixSOMap_closed
            (maximumRescaledNormalizedLoopAt T.toCenterImmersion hindex
              hC1 hr hrrho hrradius) hpos
            (maximumRescaledNormalizedLoopAt_closed T.toCenterImmersion hindex
              hC1 hr hrrho hrradius)) = 1 := by
  obtain ⟨rho, hrho, hC1⟩ := exists_param_contDiffOn_ball_one M
  let T₀ := T.toCenterImmersion
  have hbound : 0 < min T.radius rho := lt_min T.radius_pos hrho
  obtain ⟨r, hr, hrbound, hsegment⟩ :=
    exists_pos_radius_maximumRescaledNormalized_segment_det_pos
      T₀ hindex hbound
  have hrradius : r < T.radius := hrbound.trans_le (min_le_left _ _)
  have hrrho : r < rho := hrbound.trans_le (min_le_right _ _)
  let A := maximumRescaledNormalizedLoopAt T₀ hindex
    hC1 hr hrrho hrradius
  have hpos : ∀ u, 0 < (A u).det := by
    intro u
    have h := hsegment (0, u)
    simpa [A, maximumRescaledNormalizedLoopAt] using h
  have hclosed : A 0 = A 1 :=
    maximumRescaledNormalizedLoopAt_closed T₀ hindex
      hC1 hr hrrho hrradius
  have hsegA : ∀ q : I × I,
      0 < (matrixSegment (A q.2)
        (centerMaximumActualNormalizedLoop T₀ hindex q.2) q.1).det := by
    simpa [A, maximumRescaledNormalizedLoopAt] using hsegment
  refine ⟨rho, hrho, hC1, r, hr, hrrho, hrradius, hpos, ?_⟩
  exact loopClassZ2_positiveMatrixSOMap_eq_one_of_segment_pos
    A (centerMaximumActualNormalizedLoop T₀ hindex)
    hpos (centerMaximumActualNormalizedLoop_det_pos T₀ hindex)
    hclosed (centerMaximumActualNormalizedLoop_closed T₀ hindex)
    (loopClassZ2_centerMaximumActualNormalized_eq_one T₀ hindex) hsegA


-- @@ L2255-2255 verbatim
/-! ## Comparison with the canonical regular-zero frame -/


-- @@ L2257-2267 verbatim
/-- The matrix of the adapted output isometry has as its rows the adapted
output orthonormal basis. -/
theorem isometryMatrix_signedCenterOutputIsometry_apply
    (M : StandardMorseEventAt C center) (s : ℝ)
    (hs : s = 1 ∨ s = -1) (i j : Fin (a + 2)) :
    isometryMatrix (M.signedCenterOutputIsometry s hs) i j =
      M.signedCenterOutputRows s i j := by
  have h := M.signedCenterOutputIsometry_apply s hs
    (EuclideanSpace.single j 1) i
  rw [isometryMatrix_apply] at h
  simpa [PiLp.inner_apply, RCLike.inner_apply, dotProduct] using h


-- @@ L2269-2276 verbatim
/-- The orientation-preserving block which simultaneously changes output
coordinates and compensates for their determinant on the tangent row. -/
def signedCenterOrientationBlock
    (M : StandardMorseEventAt C center) (s : ℝ)
    (hs : s = 1 ∨ s = -1) : SOGroup (a + 3) :=
  let q := M.signedCenterOutputIsometry s hs
  orientationBlockSO q (isometryMatrix q).det
    (M.isometryMatrix_signedCenterOutputIsometry_det_cases s hs) rfl


-- @@ L2278-2286 verbatim
@[simp] theorem signedCenterOrientationBlock_coe
    (M : StandardMorseEventAt C center) (s : ℝ)
    (hs : s = 1 ∨ s = -1) :
    ((M.signedCenterOrientationBlock s hs : SOGroup (a + 3)) :
      Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) =
      tangentNormalBlock
        (isometryMatrix (M.signedCenterOutputIsometry s hs)).det
        (isometryMatrix (M.signedCenterOutputIsometry s hs)) := by
  rfl


-- @@ L2288-2299 verbatim
/-- Apply the adapted orientation-preserving output block to the ordinary
slice frame at a definite-circle point. -/
def signedCenterActedSliceRows
    (M : StandardMorseEventAt C center) (s : ℝ)
    (hs : s = 1 ∨ s = -1) (r theta : ℝ) :
    Fin (a + 3) → E₁ :=
  frameRowAction
    (M.signedCenterOrientationBlock s hs :
      Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ)
    (SlabTamedField.sliceFrameAt C.G
      (tcoord (M.definiteCircle r theta))
      (spacePart (M.definiteCircle r theta)))


-- @@ L2301-2325 verbatim
/-- Every normal row of the acted frame is the pullback of the corresponding
adapted output-basis vector. -/
theorem signedCenterActedSliceRows_succ
    (M : StandardMorseEventAt C center) (s : ℝ)
    (hs : s = 1 ∨ s = -1) (r theta : ℝ) (i : Fin (a + 2)) :
    M.signedCenterActedSliceRows s hs r theta i.succ =
      ContinuousLinearMap.adjoint
        (spatialDeriv C.G (M.definiteCircle r theta))
        (M.signedCenterOutputRows s i) := by
  unfold signedCenterActedSliceRows frameRowAction
  rw [Fin.sum_univ_succ]
  simp only [signedCenterOrientationBlock_coe,
    tangentNormalBlock_succ_zero, zero_smul, zero_add,
    tangentNormalBlock_succ_succ, SlabTamedField.sliceFrameAt,
    Fin.cons_succ]
  apply InnerProductSpace.ext_inner_right_basis
    (EuclideanSpace.basisFun (Fin (a + 3)) ℝ).toBasis
  intro w
  rw [sum_inner, ContinuousLinearMap.adjoint_inner_left]
  simp_rw [real_inner_smul_left, inner_gradVec,
    M.isometryMatrix_signedCenterOutputIsometry_apply]
  rw [fderiv_sliceMap C.smooth, spaceTime_spacePart,
    PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]


-- @@ L2327-2338 verbatim
theorem signedCenterActedSliceRows_zero
    (M : StandardMorseEventAt C center) (s : ℝ)
    (hs : s = 1 ∨ s = -1) (r theta : ℝ) :
    M.signedCenterActedSliceRows s hs r theta 0 =
      (isometryMatrix (M.signedCenterOutputIsometry s hs)).det •
        tauField
          (sliceMap C.G (tcoord (M.definiteCircle r theta)))
          (spacePart (M.definiteCircle r theta)) := by
  unfold signedCenterActedSliceRows frameRowAction
  rw [Fin.sum_univ_succ]
  simp [signedCenterOrientationBlock_coe,
    SlabTamedField.sliceFrameAt]


-- @@ L2340-2350 verbatim
/-- The acted raw frame with its last normal row divided by the positive
radius.  The division is the exact desingularization used by the center
family. -/
def signedCenterRescaledActedRows
    (M : StandardMorseEventAt C center) (s : ℝ)
    (hs : s = 1 ∨ s = -1) (r theta : ℝ) :
    Fin (a + 3) → E₁ :=
  Function.update (M.signedCenterActedSliceRows s hs r theta)
    (Fin.last (a + 2))
    (r⁻¹ • M.signedCenterActedSliceRows s hs r theta
      (Fin.last (a + 2)))


-- @@ L2352-2356 verbatim
def signedCenterRescaledActedMatrix
    (M : StandardMorseEventAt C center) (s : ℝ)
    (hs : s = 1 ∨ s = -1) (r theta : ℝ) :
    Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ :=
  rowsMatrix (M.signedCenterRescaledActedRows s hs r theta)


-- @@ L2358-2372 verbatim
theorem signedCenterRescaledActedRows_zero
    (M : StandardMorseEventAt C center) (s : ℝ)
    (hs : s = 1 ∨ s = -1) (r theta : ℝ) :
    M.signedCenterRescaledActedRows s hs r theta 0 =
      (isometryMatrix (M.signedCenterOutputIsometry s hs)).det •
        tauField
          (sliceMap C.G (tcoord (M.definiteCircle r theta)))
          (spacePart (M.definiteCircle r theta)) := by
  have hzero : (0 : Fin (a + 3)) ≠ Fin.last (a + 2) := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  rw [signedCenterRescaledActedRows,
    Function.update_of_ne hzero]
  exact M.signedCenterActedSliceRows_zero s hs r theta


-- @@ L2374-2388 verbatim
theorem signedCenterRescaledActedRows_transverse
    (M : StandardMorseEventAt C center) (s : ℝ)
    (hs : s = 1 ∨ s = -1) (r theta : ℝ)
    (i : Fin (a + 1)) :
    M.signedCenterRescaledActedRows s hs r theta i.castSucc.succ =
      M.centerTransverseNormalAt r theta i := by
  have hil : (i.castSucc.succ : Fin (a + 3)) ≠ Fin.last (a + 2) := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
    omega
  rw [signedCenterRescaledActedRows,
    Function.update_of_ne hil]
  rw [M.signedCenterActedSliceRows_succ s hs r theta i.castSucc]
  simp [signedCenterOutputRows, centerTransverseNormalAt]


-- @@ L2390-2406 verbatim
theorem signedCenterRescaledActedRows_last
    (M : StandardMorseEventAt C center) (s : ℝ)
    (hs : s = 1 ∨ s = -1) {r : ℝ} (hr : r ≠ 0) (theta : ℝ) :
    M.signedCenterRescaledActedRows s hs r theta (Fin.last (a + 2)) =
      ‖M.centerCokernelVector‖⁻¹ •
        (s • M.centerNormalRow r theta) := by
  rw [signedCenterRescaledActedRows, Function.update_self]
  have hlast := M.signedCenterActedSliceRows_succ s hs r theta
    (Fin.last (a + 1))
  rw [Fin.succ_last] at hlast
  rw [hlast]
  simp only [signedCenterOutputRows, Fin.snoc_last,
    centerCokernelUnit, map_smul,
    definiteCircle, localPoint]
  rw [M.centerNormalRow_eq_inv_smul hr]
  unfold centerNormalMap
  module


-- @@ L2408-2423 verbatim
theorem signedCenterRescaledActedMatrix_eq_updateRow
    (M : StandardMorseEventAt C center) (s : ℝ)
    (hs : s = 1 ∨ s = -1) (r theta : ℝ) :
    M.signedCenterRescaledActedMatrix s hs r theta =
      (rowsMatrix (M.signedCenterActedSliceRows s hs r theta)).updateRow
        (Fin.last (a + 2))
        (r⁻¹ • (rowsMatrix
          (M.signedCenterActedSliceRows s hs r theta)) (Fin.last (a + 2))) := by
  ext i j
  by_cases hi : i = Fin.last (a + 2)
  · subst i
    simp [signedCenterRescaledActedMatrix,
      signedCenterRescaledActedRows, rowsMatrix]
  · simp [signedCenterRescaledActedMatrix,
      signedCenterRescaledActedRows, rowsMatrix,
      Matrix.updateRow, hi, Function.update_of_ne hi]


-- @@ L2425-2453 verbatim
theorem signedCenterRescaledActedMatrix_det_pos
    (T : M.CenterImmersion) (s : ℝ)
    (hs : s = 1 ∨ s = -1) {r : ℝ} (hr : 0 < r)
    (hrradius : r < T.radius) (theta : ℝ) :
    0 < (M.signedCenterRescaledActedMatrix s hs r theta).det := by
  have hsurj : Surjective
      (spatialDeriv C.G (M.definiteCircle r theta)) :=
    M.definiteCircle_spatialDeriv_surjective hr
      (hrradius.trans_le T.radius_le)
  have hxreg : spacePart (M.definiteCircle r theta) ∈
      regularSet
        (sliceMap C.G (tcoord (M.definiteCircle r theta))) :=
    spacePart_mem_regularSet_of_spatialDeriv_surjective C.smooth hsurj
  have hraw : 0 < (rowsMatrix
      (SlabTamedField.sliceFrameAt C.G
        (tcoord (M.definiteCircle r theta))
        (spacePart (M.definiteCircle r theta)))).det :=
    PositiveSheetSlabTamedField.det_rowsMatrix_sliceFrameAt_pos
      C.G _ _ hxreg
  have hacted : 0 < (rowsMatrix
      (M.signedCenterActedSliceRows s hs r theta)).det := by
    exact det_rowsMatrix_frameRowAction_pos
      (M.signedCenterOrientationBlock s hs)
      (SlabTamedField.sliceFrameAt C.G
        (tcoord (M.definiteCircle r theta))
        (spacePart (M.definiteCircle r theta))) hraw
  rw [M.signedCenterRescaledActedMatrix_eq_updateRow s hs r theta,
    Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
  exact mul_pos (inv_pos.mpr hr) hacted


-- @@ L2455-2484 verbatim
/-- If two positive matrices have the same rows after their tangent row, the
straight segment between them remains positive. -/
theorem matrixSegment_det_pos_of_succ_rows_eq
    {m : ℕ} (A B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hA : 0 < A.det) (hB : 0 < B.det)
    (hrows : ∀ i : Fin m, A i.succ = B i.succ) (s : I) :
    0 < (matrixSegment A B s).det := by
  have hBA : A.updateRow 0 (B 0) = B := by
    ext i j
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · simp
    · simp [hrows i]
  have hseg : matrixSegment A B s =
      A.updateRow 0
        ((1 - (s : ℝ)) • A 0 + (s : ℝ) • B 0) := by
    ext i j
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · simp [matrixSegment]
    · simp [matrixSegment, hrows i]
      ring
  rw [hseg, Matrix.det_updateRow_add,
    Matrix.det_updateRow_smul, Matrix.updateRow_eq_self,
    Matrix.det_updateRow_smul, hBA]
  have hs0 : 0 ≤ (s : ℝ) := s.property.1
  have hs1 : (s : ℝ) ≤ 1 := s.property.2
  by_cases hsone : (s : ℝ) = 1
  · simp [hsone, hB]
  · exact add_pos_of_pos_of_nonneg
      (mul_pos (sub_pos.mpr (lt_of_le_of_ne hs1 hsone)) hA)
      (mul_nonneg hs0 hB.le)


-- @@ L2486-2487 verbatim
/-! A positive matrix admits a canonical straight positive path to its
Gram--Schmidt special-orthogonal factor. -/


-- @@ L2489-2489 verbatim
section PositiveQRSegment


-- @@ L2491-2491 verbatim
variable {m : ℕ} [NeZero m]

-- @@ L2492-2492 verbatim
local notation "Em" => EuclideanSpace ℝ (Fin m)


-- @@ L2494-2495 verbatim
def gsBasis (v : Fin m → Em) : OrthonormalBasis (Fin m) ℝ Em :=
  gramSchmidtOrthonormalBasis (by simp) v


-- @@ L2497-2503 verbatim
theorem gsBasis_apply (v : Fin m → Em) (hv : LinearIndependent ℝ v)
    (i : Fin m) :
    gsBasis v i = gramSchmidtNormed ℝ v i := by
  apply gramSchmidtOrthonormalBasis_apply
  exact smul_ne_zero
    (inv_ne_zero (norm_ne_zero_iff.mpr (gramSchmidt_ne_zero i hv)))
    (gramSchmidt_ne_zero i hv)


-- @@ L2505-2527 verbatim
theorem inner_gsBasis_self_pos (v : Fin m → Em)
    (hv : LinearIndependent ℝ v) (i : Fin m) :
    0 < ⟪gsBasis v i, v i⟫_ℝ := by
  rw [gsBasis_apply v hv i, gramSchmidtNormed]
  rw [gramSchmidt_def'' ℝ v i]
  simp only [inner_add_right, inner_sum, real_inner_smul_right,
    real_inner_smul_left]
  let S : ℝ := ∑ x ∈ Finset.Iio i,
      ((⟪gramSchmidt ℝ v x, v i⟫_ℝ / ‖gramSchmidt ℝ v x‖ ^ 2) *
        ((‖gramSchmidt ℝ v i‖ : ℝ)⁻¹ *
          ⟪gramSchmidt ℝ v i, gramSchmidt ℝ v x⟫_ℝ))
  change 0 < (‖gramSchmidt ℝ v i‖ : ℝ)⁻¹ *
    ⟪gramSchmidt ℝ v i, gramSchmidt ℝ v i⟫_ℝ + S
  have hsum : S = 0 := by
    dsimp [S]
    apply Finset.sum_eq_zero
    intro j hj
    rw [gramSchmidt_orthogonal ℝ v (ne_of_gt (Finset.mem_Iio.mp hj)),
      mul_zero, mul_zero]
  rw [hsum, add_zero, real_inner_self_eq_norm_sq]
  have hnorm : 0 < ‖gramSchmidt ℝ v i‖ :=
    norm_pos_iff.mpr (gramSchmidt_ne_zero i hv)
  exact mul_pos (inv_pos.mpr hnorm) (sq_pos_of_pos hnorm)


-- @@ L2529-2530 verbatim
def gsCoeff (v : Fin m → Em) : Matrix (Fin m) (Fin m) ℝ :=
  (gsBasis v).toBasis.toMatrix v


-- @@ L2532-2539 verbatim
theorem rowsMatrix_eq_gsCoeff (v : Fin m → Em) :
    rowsMatrix v = (gsCoeff v)ᵀ * rowsMatrix (gsBasis v) := by
  ext i j
  simp only [rowsMatrix, Matrix.of_apply, Matrix.mul_apply,
    Matrix.transpose_apply, gsCoeff, Module.Basis.toMatrix_apply]
  have h := (gsBasis v).toBasis.sum_repr (v i)
  have h' := congrArg (fun z : Em => WithLp.ofLp z j) h
  simpa using h'.symm


-- @@ L2541-2543 verbatim
theorem gsCoeff_blockTriangular (v : Fin m → Em) :
    (gsCoeff v).BlockTriangular id := by
  exact gramSchmidtOrthonormalBasis_inv_blockTriangular (by simp) v


-- @@ L2545-2547 verbatim
def gsSegmentCoeff (v : Fin m → Em) (s : I) :
    Matrix (Fin m) (Fin m) ℝ :=
  (1 - (s : ℝ)) • (gsCoeff v)ᵀ + (s : ℝ) • 1


-- @@ L2549-2557 verbatim
theorem gsSegmentCoeff_lower (v : Fin m → Em) (s : I) :
    (gsSegmentCoeff v s).BlockTriangular OrderDual.toDual := by
  intro i j hij
  have hji : i < j := hij
  change (1 - (s : ℝ)) * gsCoeff v j i +
    (s : ℝ) * (if i = j then 1 else 0) = 0
  have hzero : gsCoeff v j i = 0 := gsCoeff_blockTriangular v hji
  rw [hzero]
  simp [ne_of_lt hji]


-- @@ L2559-2581 verbatim
theorem det_gsSegmentCoeff_pos (v : Fin m → Em)
    (hv : LinearIndependent ℝ v) (s : I) :
    0 < (gsSegmentCoeff v s).det := by
  rw [Matrix.det_of_lowerTriangular _ (gsSegmentCoeff_lower v s)]
  apply Finset.prod_pos
  intro i _
  unfold gsSegmentCoeff
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.transpose_apply,
    Matrix.one_apply, if_pos]
  rw [gsCoeff, Module.Basis.toMatrix_apply]
  have hre : ((gsBasis v).toBasis.repr (v i)) i =
      ⟪gsBasis v i, v i⟫_ℝ :=
    (gsBasis v).repr_apply_apply (v i) i
  rw [hre]
  simp only [smul_eq_mul]
  have hd := inner_gsBasis_self_pos v hv i
  have hs0 : 0 ≤ (s : ℝ) := s.property.1
  have hs1 : (s : ℝ) ≤ 1 := s.property.2
  by_cases hsone : (s : ℝ) = 1
  · simp [hsone]
  exact add_pos_of_pos_of_nonneg
    (mul_pos (sub_pos.mpr (lt_of_le_of_ne hs1 hsone)) hd)
    (by simpa using hs0)


-- @@ L2583-2588 verbatim
theorem matrixSegment_rowsMatrix_gs_factor (v : Fin m → Em) (s : I) :
    matrixSegment (rowsMatrix v) (rowsMatrix (gsBasis v)) s =
      gsSegmentCoeff v s * rowsMatrix (gsBasis v) := by
  rw [matrixSegment, rowsMatrix_eq_gsCoeff]
  unfold gsSegmentCoeff
  rw [add_mul, smul_mul, smul_mul, one_mul]


-- @@ L2590-2609 verbatim
theorem det_matrixSegment_rowsMatrix_gs_pos (v : Fin m → Em)
    (hv : LinearIndependent ℝ v) (hpos : 0 < (rowsMatrix v).det)
    (s : I) :
    0 < (matrixSegment (rowsMatrix v)
      (rowsMatrix (gramSchmidtNormed ℝ v)) s).det := by
  have hgs : rowsMatrix (gramSchmidtNormed ℝ v) =
      rowsMatrix (gsBasis v) := by
    congr 1
    funext i
    exact (gsBasis_apply v hv i).symm
  rw [hgs, matrixSegment_rowsMatrix_gs_factor, Matrix.det_mul]
  exact mul_pos (det_gsSegmentCoeff_pos v hv s)
    (by
      rw [← hgs, det_rowsMatrix_gramSchmidtNormed]
      apply mul_pos
      · apply Finset.prod_pos
        intro i _
        exact inv_pos.mpr
          (norm_pos_iff.mpr (gramSchmidt_ne_zero i hv))
      · exact hpos)


-- @@ L2611-2611 verbatim
end PositiveQRSegment


-- @@ L2613-2614 verbatim
/-! Constant positive changes of raw coordinates do not affect the projected
frame-loop class. -/


-- @@ L2616-2620 verbatim
def matrixMulRightSO {m : ℕ}
    (A : C(I, Matrix (Fin m) (Fin m) ℝ)) (Q : SOGroup m) :
    C(I, Matrix (Fin m) (Fin m) ℝ) where
  toFun u := A u * (Q : Matrix (Fin m) (Fin m) ℝ)
  continuous_toFun := A.continuous.mul continuous_const


-- @@ L2622-2627 verbatim
def matrixMulRightConst {m : ℕ}
    (A : C(I, Matrix (Fin m) (Fin m) ℝ))
    (B : Matrix (Fin m) (Fin m) ℝ) :
    C(I, Matrix (Fin m) (Fin m) ℝ) where
  toFun u := A u * B
  continuous_toFun := A.continuous.mul continuous_const


-- @@ L2629-2633 verbatim
def matrixMulLeftSO {m : ℕ} (Q : SOGroup m)
    (A : C(I, Matrix (Fin m) (Fin m) ℝ)) :
    C(I, Matrix (Fin m) (Fin m) ℝ) where
  toFun u := (Q : Matrix (Fin m) (Fin m) ℝ) * A u
  continuous_toFun := continuous_const.mul A.continuous


-- @@ L2635-2642 verbatim
theorem matrixMulRightSO_det_pos {m : ℕ}
    (A : C(I, Matrix (Fin m) (Fin m) ℝ)) (Q : SOGroup m)
    (hA : ∀ u, 0 < (A u).det) (u : I) :
    0 < (matrixMulRightSO A Q u).det := by
  change 0 < (A u * (Q : Matrix (Fin m) (Fin m) ℝ)).det
  rw [Matrix.det_mul,
    (Matrix.mem_specialOrthogonalGroup_iff.mp Q.property).2, mul_one]
  exact hA u


-- @@ L2644-2651 verbatim
theorem matrixMulRightConst_det_pos {m : ℕ}
    (A : C(I, Matrix (Fin m) (Fin m) ℝ))
    {B : Matrix (Fin m) (Fin m) ℝ} (hB : 0 < B.det)
    (hA : ∀ u, 0 < (A u).det) (u : I) :
    0 < (matrixMulRightConst A B u).det := by
  change 0 < (A u * B).det
  rw [Matrix.det_mul]
  exact mul_pos (hA u) hB


-- @@ L2653-2660 verbatim
theorem matrixMulLeftSO_det_pos {m : ℕ} (Q : SOGroup m)
    (A : C(I, Matrix (Fin m) (Fin m) ℝ))
    (hA : ∀ u, 0 < (A u).det) (u : I) :
    0 < (matrixMulLeftSO Q A u).det := by
  change 0 < ((Q : Matrix (Fin m) (Fin m) ℝ) * A u).det
  rw [Matrix.det_mul,
    (Matrix.mem_specialOrthogonalGroup_iff.mp Q.property).2, one_mul]
  exact hA u


-- @@ L2662-2667 verbatim
theorem matrixMulRightSO_closed {m : ℕ}
    (A : C(I, Matrix (Fin m) (Fin m) ℝ)) (Q : SOGroup m)
    (hA : A 0 = A 1) :
    matrixMulRightSO A Q 0 = matrixMulRightSO A Q 1 := by
  change A 0 * (Q : Matrix (Fin m) (Fin m) ℝ) = A 1 * Q
  rw [hA]


-- @@ L2669-2674 verbatim
theorem matrixMulRightConst_closed {m : ℕ}
    (A : C(I, Matrix (Fin m) (Fin m) ℝ))
    (B : Matrix (Fin m) (Fin m) ℝ) (hA : A 0 = A 1) :
    matrixMulRightConst A B 0 = matrixMulRightConst A B 1 := by
  change A 0 * B = A 1 * B
  rw [hA]


-- @@ L2676-2680 verbatim
theorem matrixMulLeftSO_closed {m : ℕ} (Q : SOGroup m)
    (A : C(I, Matrix (Fin m) (Fin m) ℝ)) (hA : A 0 = A 1) :
    matrixMulLeftSO Q A 0 = matrixMulLeftSO Q A 1 := by
  change (Q : Matrix (Fin m) (Fin m) ℝ) * A 0 = Q * A 1
  rw [hA]


-- @@ L2682-2694 verbatim
def matrixMulRightSOHomotopy {m : ℕ}
    (A : C(I, Matrix (Fin m) (Fin m) ℝ)) (Q : SOGroup m) :
    ContinuousMap.Homotopy (matrixMulRightSO A Q) A where
  toFun p := A p.2 *
    (((PathConnectedSpace.somePath Q 1) p.1 : SOGroup m) :
      Matrix (Fin m) (Fin m) ℝ)
  continuous_toFun := by fun_prop
  map_zero_left u := by
    rw [(PathConnectedSpace.somePath Q 1).source]
    rfl
  map_one_left u := by
    rw [(PathConnectedSpace.somePath Q 1).target]
    simp


-- @@ L2696-2708 verbatim
def matrixMulLeftSOHomotopy {m : ℕ} (Q : SOGroup m)
    (A : C(I, Matrix (Fin m) (Fin m) ℝ)) :
    ContinuousMap.Homotopy (matrixMulLeftSO Q A) A where
  toFun p :=
    (((PathConnectedSpace.somePath Q 1) p.1 : SOGroup m) :
      Matrix (Fin m) (Fin m) ℝ) * A p.2
  continuous_toFun := by fun_prop
  map_zero_left u := by
    rw [(PathConnectedSpace.somePath Q 1).source]
    rfl
  map_one_left u := by
    rw [(PathConnectedSpace.somePath Q 1).target]
    simp


-- @@ L2710-2721 verbatim
def matrixMulRightConstQRHomotopy {m : ℕ} [NeZero m]
    (A : C(I, Matrix (Fin m) (Fin m) ℝ))
    (B : Matrix (Fin m) (Fin m) ℝ) (hB : 0 < B.det) :
    ContinuousMap.Homotopy (matrixMulRightConst A B)
      (matrixMulRightSO A (matrixGramSchmidtSO B hB)) where
  toFun p := A p.2 * matrixSegment B
    (matrixGramSchmidtSO B hB : Matrix (Fin m) (Fin m) ℝ) p.1
  continuous_toFun := by
    unfold matrixSegment
    fun_prop
  map_zero_left u := by simp [matrixMulRightConst]
  map_one_left u := by simp [matrixMulRightSO]


-- @@ L2723-2733 verbatim
theorem matrixMulRightSOHomotopy_det_pos {m : ℕ}
    (A : C(I, Matrix (Fin m) (Fin m) ℝ)) (Q : SOGroup m)
    (hA : ∀ u, 0 < (A u).det) (p : I × I) :
    0 < (matrixMulRightSOHomotopy A Q p).det := by
  change 0 < (A p.2 *
    (((PathConnectedSpace.somePath Q 1) p.1 : SOGroup m) :
      Matrix (Fin m) (Fin m) ℝ)).det
  rw [Matrix.det_mul,
    (Matrix.mem_specialOrthogonalGroup_iff.mp
      ((PathConnectedSpace.somePath Q 1) p.1).property).2, mul_one]
  exact hA p.2


-- @@ L2735-2745 verbatim
theorem matrixMulLeftSOHomotopy_det_pos {m : ℕ}
    (Q : SOGroup m) (A : C(I, Matrix (Fin m) (Fin m) ℝ))
    (hA : ∀ u, 0 < (A u).det) (p : I × I) :
    0 < (matrixMulLeftSOHomotopy Q A p).det := by
  change 0 <
    ((((PathConnectedSpace.somePath Q 1) p.1 : SOGroup m) :
      Matrix (Fin m) (Fin m) ℝ) * A p.2).det
  rw [Matrix.det_mul,
    (Matrix.mem_specialOrthogonalGroup_iff.mp
      ((PathConnectedSpace.somePath Q 1) p.1).property).2, one_mul]
  exact hA p.2


-- @@ L2747-2759 verbatim
theorem matrixMulRightConstQRHomotopy_det_pos {m : ℕ} [NeZero m]
    (A : C(I, Matrix (Fin m) (Fin m) ℝ))
    (B : Matrix (Fin m) (Fin m) ℝ) (hB : 0 < B.det)
    (hA : ∀ u, 0 < (A u).det) (p : I × I) :
    0 < (matrixMulRightConstQRHomotopy A B hB p).det := by
  change 0 < (A p.2 * matrixSegment B
    (matrixGramSchmidtSO B hB : Matrix (Fin m) (Fin m) ℝ) p.1).det
  rw [Matrix.det_mul]
  apply mul_pos (hA p.2)
  have hv : LinearIndependent ℝ (matrixRows B) :=
    linearIndependent_matrixRows_of_det_ne_zero (ne_of_gt hB)
  simpa using det_matrixSegment_rowsMatrix_gs_pos
    (matrixRows B) hv (by simpa using hB) p.1


-- @@ L2761-2782 verbatim
theorem loopClassZ2_positiveMatrixSOMap_mulRightSO_congr {m : ℕ}
    (A : C(I, Matrix (Fin m) (Fin m) ℝ)) (Q : SOGroup m)
    (hApos : ∀ u, 0 < (A u).det) (hAclosed : A 0 = A 1) :
    loopClassZ2
        (positiveMatrixSOMap (matrixMulRightSO A Q)
          (matrixMulRightSO_det_pos A Q hApos))
        (positiveMatrixSOMap_closed (matrixMulRightSO A Q)
          (matrixMulRightSO_det_pos A Q hApos)
          (matrixMulRightSO_closed A Q hAclosed)) =
      loopClassZ2 (positiveMatrixSOMap A hApos)
        (positiveMatrixSOMap_closed A hApos hAclosed) := by
  exact loopClassZ2_positiveMatrixHomotopy_congr
    (matrixMulRightSOHomotopy A Q)
    (matrixMulRightSO_det_pos A Q hApos) hApos
    (matrixMulRightSOHomotopy_det_pos A Q hApos)
    (matrixMulRightSO_closed A Q hAclosed) hAclosed
    (fun t => by
      change A 0 *
          (((PathConnectedSpace.somePath Q 1) t : SOGroup m) :
            Matrix (Fin m) (Fin m) ℝ) =
        A 1 * ((PathConnectedSpace.somePath Q 1) t : SOGroup m)
      rw [hAclosed])


-- @@ L2784-2805 verbatim
theorem loopClassZ2_positiveMatrixSOMap_mulLeftSO_congr {m : ℕ}
    (Q : SOGroup m) (A : C(I, Matrix (Fin m) (Fin m) ℝ))
    (hApos : ∀ u, 0 < (A u).det) (hAclosed : A 0 = A 1) :
    loopClassZ2
        (positiveMatrixSOMap (matrixMulLeftSO Q A)
          (matrixMulLeftSO_det_pos Q A hApos))
        (positiveMatrixSOMap_closed (matrixMulLeftSO Q A)
          (matrixMulLeftSO_det_pos Q A hApos)
          (matrixMulLeftSO_closed Q A hAclosed)) =
      loopClassZ2 (positiveMatrixSOMap A hApos)
        (positiveMatrixSOMap_closed A hApos hAclosed) := by
  exact loopClassZ2_positiveMatrixHomotopy_congr
    (matrixMulLeftSOHomotopy Q A)
    (matrixMulLeftSO_det_pos Q A hApos) hApos
    (matrixMulLeftSOHomotopy_det_pos Q A hApos)
    (matrixMulLeftSO_closed Q A hAclosed) hAclosed
    (fun t => by
      change
          (((PathConnectedSpace.somePath Q 1) t : SOGroup m) :
            Matrix (Fin m) (Fin m) ℝ) * A 0 =
        ((PathConnectedSpace.somePath Q 1) t : SOGroup m) * A 1
      rw [hAclosed])


-- @@ L2807-2836 verbatim
theorem loopClassZ2_positiveMatrixSOMap_mulRightConst_congr
    {m : ℕ} [NeZero m]
    (A : C(I, Matrix (Fin m) (Fin m) ℝ))
    (B : Matrix (Fin m) (Fin m) ℝ) (hB : 0 < B.det)
    (hApos : ∀ u, 0 < (A u).det) (hAclosed : A 0 = A 1) :
    loopClassZ2
        (positiveMatrixSOMap (matrixMulRightConst A B)
          (matrixMulRightConst_det_pos A hB hApos))
        (positiveMatrixSOMap_closed (matrixMulRightConst A B)
          (matrixMulRightConst_det_pos A hB hApos)
          (matrixMulRightConst_closed A B hAclosed)) =
      loopClassZ2 (positiveMatrixSOMap A hApos)
        (positiveMatrixSOMap_closed A hApos hAclosed) := by
  let Q := matrixGramSchmidtSO B hB
  have hQpos := matrixMulRightSO_det_pos A Q hApos
  have hQclosed := matrixMulRightSO_closed A Q hAclosed
  have hfirst := loopClassZ2_positiveMatrixHomotopy_congr
    (matrixMulRightConstQRHomotopy A B hB)
    (matrixMulRightConst_det_pos A hB hApos) hQpos
    (matrixMulRightConstQRHomotopy_det_pos A B hB hApos)
    (matrixMulRightConst_closed A B hAclosed) hQclosed
    (fun t => by
      change A 0 * matrixSegment B
          (matrixGramSchmidtSO B hB : Matrix (Fin m) (Fin m) ℝ) t =
        A 1 * matrixSegment B
          (matrixGramSchmidtSO B hB : Matrix (Fin m) (Fin m) ℝ) t
      rw [hAclosed])
  exact hfirst.trans
    (loopClassZ2_positiveMatrixSOMap_mulRightSO_congr
      A Q hApos hAclosed)


-- @@ L2838-2843 verbatim
def matrixScaleLastRow {m : ℕ} (c : ℝ)
    (A : C(I, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) :
    C(I, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) where
  toFun u := (A u).updateRow (Fin.last m)
    (c • (A u) (Fin.last m))
  continuous_toFun := by fun_prop


-- @@ L2845-2852 verbatim
theorem matrixScaleLastRow_det_pos {m : ℕ} {c : ℝ} (hc : 0 < c)
    (A : C(I, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ))
    (hA : ∀ u, 0 < (A u).det) (u : I) :
    0 < (matrixScaleLastRow c A u).det := by
  change 0 < ((A u).updateRow (Fin.last m)
    (c • (A u) (Fin.last m))).det
  rw [Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
  exact mul_pos hc (hA u)


-- @@ L2854-2860 verbatim
theorem matrixScaleLastRow_closed {m : ℕ} (c : ℝ)
    (A : C(I, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ))
    (hA : A 0 = A 1) :
    matrixScaleLastRow c A 0 = matrixScaleLastRow c A 1 := by
  change (A 0).updateRow (Fin.last m) (c • (A 0) (Fin.last m)) =
    (A 1).updateRow (Fin.last m) (c • (A 1) (Fin.last m))
  rw [hA]


-- @@ L2862-2872 verbatim
def matrixScaleLastRowHomotopy {m : ℕ} (c : ℝ)
    (A : C(I, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) :
    ContinuousMap.Homotopy (matrixScaleLastRow c A) A where
  toFun p := (A p.2).updateRow (Fin.last m)
    (((1 - (p.1 : ℝ)) * c + (p.1 : ℝ)) •
      (A p.2) (Fin.last m))
  continuous_toFun := by fun_prop
  map_zero_left u := by
    simp [matrixScaleLastRow]
  map_one_left u := by
    simp


-- @@ L2874-2886 verbatim
theorem matrixScaleLastRowHomotopy_det_pos {m : ℕ} {c : ℝ}
    (hc : 0 < c)
    (A : C(I, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ))
    (hA : ∀ u, 0 < (A u).det) (p : I × I) :
    0 < (matrixScaleLastRowHomotopy c A p).det := by
  change 0 < ((A p.2).updateRow (Fin.last m)
    (((1 - (p.1 : ℝ)) * c + (p.1 : ℝ)) •
      (A p.2) (Fin.last m))).det
  rw [Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
  have hcoef : 0 < (1 - (p.1 : ℝ)) * c + (p.1 : ℝ) := by
    simpa [definiteRadiusInterpolation] using
      (definiteRadiusInterpolation_pos hc zero_lt_one p.1)
  exact mul_pos hcoef (hA p.2)


-- @@ L2888-2910 verbatim
theorem loopClassZ2_positiveMatrixSOMap_scaleLastRow_congr {m : ℕ}
    {c : ℝ} (hc : 0 < c)
    (A : C(I, Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ))
    (hApos : ∀ u, 0 < (A u).det) (hAclosed : A 0 = A 1) :
    loopClassZ2
        (positiveMatrixSOMap (matrixScaleLastRow c A)
          (matrixScaleLastRow_det_pos hc A hApos))
        (positiveMatrixSOMap_closed (matrixScaleLastRow c A)
          (matrixScaleLastRow_det_pos hc A hApos)
          (matrixScaleLastRow_closed c A hAclosed)) =
      loopClassZ2 (positiveMatrixSOMap A hApos)
        (positiveMatrixSOMap_closed A hApos hAclosed) := by
  exact loopClassZ2_positiveMatrixHomotopy_congr
    (matrixScaleLastRowHomotopy c A)
    (matrixScaleLastRow_det_pos hc A hApos) hApos
    (matrixScaleLastRowHomotopy_det_pos hc A hApos)
    (matrixScaleLastRow_closed c A hAclosed) hAclosed
    (fun t => by
      change (A 0).updateRow (Fin.last m)
          (((1 - (t : ℝ)) * c + (t : ℝ)) • (A 0) (Fin.last m)) =
        (A 1).updateRow (Fin.last m)
          (((1 - (t : ℝ)) * c + (t : ℝ)) • (A 1) (Fin.last m))
      rw [hAclosed])


-- @@ L2912-2912 verbatim
/-! The canonical raw frame loop on a production definite circle. -/


-- @@ L2914-2919 verbatim
def definiteCircleRawLoop (T : M.EmbeddedShrink)
    (r : ℝ) (hr : 0 < r) (hrradius : r < T.radius) :
    C(I, Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) :=
  regularZeroRawFrame C.smooth (T.definiteCircleCurve r hr hrradius)
    (fun _ => M.definiteCircle_spatialDeriv_surjective hr
      (hrradius.trans_le T.radius_le))


-- @@ L2921-2927 verbatim
theorem definiteCircleRawLoop_det_pos (T : M.EmbeddedShrink)
    (r : ℝ) (hr : 0 < r) (hrradius : r < T.radius) (u : I) :
    0 < (definiteCircleRawLoop T r hr hrradius u).det := by
  exact regularZeroRawFrame_det_pos C.smooth
    (T.definiteCircleCurve r hr hrradius)
    (fun _ => M.definiteCircle_spatialDeriv_surjective hr
      (hrradius.trans_le T.radius_le)) u


-- @@ L2929-2935 verbatim
@[simp] theorem definiteCircleRawLoop_apply (T : M.EmbeddedShrink)
    (r : ℝ) (hr : 0 < r) (hrradius : r < T.radius) (u : I) :
    definiteCircleRawLoop T r hr hrradius u =
      rowsMatrix (SlabTamedField.sliceFrameAt C.G
        (tcoord (M.definiteCircle r (2 * Real.pi * (u : ℝ))))
        (spacePart (M.definiteCircle r (2 * Real.pi * (u : ℝ))))) := by
  rfl


-- @@ L2937-2945 verbatim
theorem definiteCircleRawLoop_closed (T : M.EmbeddedShrink)
    (r : ℝ) (hr : 0 < r) (hrradius : r < T.radius) :
    definiteCircleRawLoop T r hr hrradius 0 =
      definiteCircleRawLoop T r hr hrradius 1 := by
  exact regularZeroRawFrame_closed C.smooth
    (T.definiteCircleCurve r hr hrradius)
    (fun _ => M.definiteCircle_spatialDeriv_surjective hr
      (hrradius.trans_le T.radius_le))
    (T.definiteCircleCurve_closed r hr hrradius)


-- @@ L2947-2953 verbatim
def signedCenterRescaledActedLoop (T : M.EmbeddedShrink)
    (s : ℝ) (hs : s = 1 ∨ s = -1)
    (r : ℝ) (hr : 0 < r) (hrradius : r < T.radius) :
    C(I, Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) :=
  matrixScaleLastRow r⁻¹
    (matrixMulLeftSO (M.signedCenterOrientationBlock s hs)
      (definiteCircleRawLoop T r hr hrradius))


-- @@ L2955-2988 verbatim
theorem signedCenterRescaledActedLoop_apply
    (T : M.EmbeddedShrink) (s : ℝ) (hs : s = 1 ∨ s = -1)
    (r : ℝ) (hr : 0 < r) (hrradius : r < T.radius) (u : I) :
    signedCenterRescaledActedLoop T s hs r hr hrradius u =
      M.signedCenterRescaledActedMatrix s hs r
        (2 * Real.pi * (u : ℝ)) := by
  rw [M.signedCenterRescaledActedMatrix_eq_updateRow s hs]
  have hacted :
      ((M.signedCenterOrientationBlock s hs : SOGroup (a + 3)) :
          Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) *
        definiteCircleRawLoop T r hr hrradius u =
      rowsMatrix (M.signedCenterActedSliceRows s hs r
        (2 * Real.pi * (u : ℝ))) := by
    rw [definiteCircleRawLoop_apply]
    exact (rowsMatrix_frameRowAction
    ((M.signedCenterOrientationBlock s hs : SOGroup (a + 3)) :
      Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ)
    (SlabTamedField.sliceFrameAt C.G
      (tcoord (M.definiteCircle r (2 * Real.pi * (u : ℝ))))
      (spacePart (M.definiteCircle r (2 * Real.pi * (u : ℝ)))))).symm
  change
    (((M.signedCenterOrientationBlock s hs : SOGroup (a + 3)) :
        Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) *
      definiteCircleRawLoop T r hr hrradius u).updateRow
        (Fin.last (a + 2))
        (r⁻¹ •
          (((M.signedCenterOrientationBlock s hs : SOGroup (a + 3)) :
              Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) *
            definiteCircleRawLoop T r hr hrradius u) (Fin.last (a + 2))) =
      (rowsMatrix (M.signedCenterActedSliceRows s hs r
        (2 * Real.pi * (u : ℝ)))).updateRow (Fin.last (a + 2))
        (r⁻¹ • (rowsMatrix (M.signedCenterActedSliceRows s hs r
          (2 * Real.pi * (u : ℝ)))) (Fin.last (a + 2)))
  rw [hacted]


-- @@ L2990-2996 verbatim
theorem signedCenterRescaledActedLoop_det_pos
    (T : M.EmbeddedShrink) (s : ℝ) (hs : s = 1 ∨ s = -1)
    (r : ℝ) (hr : 0 < r) (hrradius : r < T.radius) (u : I) :
    0 < (signedCenterRescaledActedLoop T s hs r hr hrradius u).det := by
  rw [signedCenterRescaledActedLoop_apply]
  exact signedCenterRescaledActedMatrix_det_pos T.toCenterImmersion
    s hs hr hrradius (2 * Real.pi * (u : ℝ))


-- @@ L2998-3005 verbatim
theorem signedCenterRescaledActedLoop_closed
    (T : M.EmbeddedShrink) (s : ℝ) (hs : s = 1 ∨ s = -1)
    (r : ℝ) (hr : 0 < r) (hrradius : r < T.radius) :
    signedCenterRescaledActedLoop T s hs r hr hrradius 0 =
      signedCenterRescaledActedLoop T s hs r hr hrradius 1 := by
  exact matrixScaleLastRow_closed r⁻¹ _
    (matrixMulLeftSO_closed (M.signedCenterOrientationBlock s hs) _
      (definiteCircleRawLoop_closed T r hr hrradius))


-- @@ L3007-3030 verbatim
theorem minimumRescaledRadiusRows_succ_eq_signedActed
    (M : StandardMorseEventAt C center) {r : ℝ} (hr : 0 < r)
    (theta : ℝ) (i : Fin (a + 2)) :
    M.minimumRescaledRadiusRows r theta i.succ =
      M.signedCenterRescaledActedRows
        (nonzeroOrientationSign M.centerMinimumPairingScalar)
        (nonzeroOrientationSign_eq_one_or_neg_one _)
        r theta i.succ := by
  induction i using Fin.lastCases with
  | last =>
      have hlast : (Fin.last (a + 1)).succ =
          (Fin.last (a + 2) : Fin (a + 3)) := by
        apply Fin.ext
        simp
      rw [hlast]
      rw [M.signedCenterRescaledActedRows_last
        (nonzeroOrientationSign M.centerMinimumPairingScalar)
        (nonzeroOrientationSign_eq_one_or_neg_one _) hr.ne' theta]
      simp [minimumRescaledRadiusRows, centerRowsWith]
  | cast i =>
      rw [M.signedCenterRescaledActedRows_transverse
        (nonzeroOrientationSign M.centerMinimumPairingScalar)
        (nonzeroOrientationSign_eq_one_or_neg_one _) r theta i]
      simp [minimumRescaledRadiusRows, centerRowsWith]


-- @@ L3032-3055 verbatim
theorem maximumRescaledRadiusRows_succ_eq_signedActed
    (M : StandardMorseEventAt C center) {r : ℝ} (hr : 0 < r)
    (theta : ℝ) (i : Fin (a + 2)) :
    M.maximumRescaledRadiusRows r theta i.succ =
      M.signedCenterRescaledActedRows
        (nonzeroOrientationSign M.centerMaximumPairingScalar)
        (nonzeroOrientationSign_eq_one_or_neg_one _)
        r theta i.succ := by
  induction i using Fin.lastCases with
  | last =>
      have hlast : (Fin.last (a + 1)).succ =
          (Fin.last (a + 2) : Fin (a + 3)) := by
        apply Fin.ext
        simp
      rw [hlast]
      rw [M.signedCenterRescaledActedRows_last
        (nonzeroOrientationSign M.centerMaximumPairingScalar)
        (nonzeroOrientationSign_eq_one_or_neg_one _) hr.ne' theta]
      simp [maximumRescaledRadiusRows, centerRowsWith]
  | cast i =>
      rw [M.signedCenterRescaledActedRows_transverse
        (nonzeroOrientationSign M.centerMaximumPairingScalar)
        (nonzeroOrientationSign_eq_one_or_neg_one _) r theta i]
      simp [maximumRescaledRadiusRows, centerRowsWith]


-- @@ L3057-3065 verbatim
def minimumRescaledRadiusLoopAt
    (T : M.CenterImmersion) (hindex : M.index = .minimum)
    {rho r : ℝ} (hC1 : ContDiffOn ℝ 1 M.param (ball (0 : E₂) rho))
    (hr : 0 < r) (hrrho : r < rho) (hrradius : r < T.radius) :
    C(I, Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) :=
  matrixMulRightConst
    (minimumRescaledNormalizedLoopAt T hindex hC1 hr hrrho hrradius)
    (centerMinimumActualRadialBaseUnit T hindex :
      Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ)


-- @@ L3067-3075 verbatim
def maximumRescaledRadiusLoopAt
    (T : M.CenterImmersion) (hindex : M.index = .maximum)
    {rho r : ℝ} (hC1 : ContDiffOn ℝ 1 M.param (ball (0 : E₂) rho))
    (hr : 0 < r) (hrrho : r < rho) (hrradius : r < T.radius) :
    C(I, Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) :=
  matrixMulRightConst
    (maximumRescaledNormalizedLoopAt T hindex hC1 hr hrrho hrradius)
    (centerMaximumActualRadialBaseUnit T hindex :
      Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ)


-- @@ L3077-3090 verbatim
@[simp] theorem minimumRescaledRadiusLoopAt_apply
    (T : M.CenterImmersion) (hindex : M.index = .minimum)
    {rho r : ℝ} (hC1 : ContDiffOn ℝ 1 M.param (ball (0 : E₂) rho))
    (hr : 0 < r) (hrrho : r < rho) (hrradius : r < T.radius) (u : I) :
    minimumRescaledRadiusLoopAt T hindex hC1 hr hrrho hrradius u =
      M.minimumRescaledRadiusMatrix r (2 * Real.pi * (u : ℝ)) := by
  let U := centerMinimumActualRadialBaseUnit T hindex
  change
    (M.minimumRescaledRadiusMatrix r (2 * Real.pi * (u : ℝ)) *
        (↑U⁻¹ : Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ)) *
      (↑U : Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) =
    M.minimumRescaledRadiusMatrix r (2 * Real.pi * (u : ℝ))
  rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, mul_one]


-- @@ L3092-3105 verbatim
@[simp] theorem maximumRescaledRadiusLoopAt_apply
    (T : M.CenterImmersion) (hindex : M.index = .maximum)
    {rho r : ℝ} (hC1 : ContDiffOn ℝ 1 M.param (ball (0 : E₂) rho))
    (hr : 0 < r) (hrrho : r < rho) (hrradius : r < T.radius) (u : I) :
    maximumRescaledRadiusLoopAt T hindex hC1 hr hrrho hrradius u =
      M.maximumRescaledRadiusMatrix r (2 * Real.pi * (u : ℝ)) := by
  let U := centerMaximumActualRadialBaseUnit T hindex
  change
    (M.maximumRescaledRadiusMatrix r (2 * Real.pi * (u : ℝ)) *
        (↑U⁻¹ : Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ)) *
      (↑U : Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) =
    M.maximumRescaledRadiusMatrix r (2 * Real.pi * (u : ℝ))
  rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, mul_one]


-- @@ L3107-3112 verbatim
theorem centerMinimumActualRadialBaseUnit_det_pos
    (T : M.CenterImmersion) (hindex : M.index = .minimum) :
    0 < ((centerMinimumActualRadialBaseUnit T hindex :
      Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ)).det := by
  rw [coe_centerMinimumActualRadialBaseUnit]
  exact det_centerMinimumActualNormalRadialMatrix_pos T hindex 1 0


-- @@ L3114-3119 verbatim
theorem centerMaximumActualRadialBaseUnit_det_pos
    (T : M.CenterImmersion) (hindex : M.index = .maximum) :
    0 < ((centerMaximumActualRadialBaseUnit T hindex :
      Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ)).det := by
  rw [coe_centerMaximumActualRadialBaseUnit]
  exact det_centerMaximumActualNormalRadialMatrix_pos T hindex 1 0


-- @@ L3121-3204 verbatim
theorem exists_minimumDefiniteCircleRawLoop_class_one
    (T : M.EmbeddedShrink) (hindex : M.index = .minimum) :
    ∃ r : ℝ, ∃ hr : 0 < r, ∃ hrradius : r < T.radius,
      loopClassZ2
          (positiveMatrixSOMap (definiteCircleRawLoop T r hr hrradius)
            (definiteCircleRawLoop_det_pos T r hr hrradius))
          (positiveMatrixSOMap_closed (definiteCircleRawLoop T r hr hrradius)
            (definiteCircleRawLoop_det_pos T r hr hrradius)
            (definiteCircleRawLoop_closed T r hr hrradius)) = 1 := by
  obtain ⟨rho, hrho, hC1, r, hr, hrrho, hrradius, hNpos, hNclass⟩ :=
    exists_minimumRescaledNormalizedLoop_class_one T hindex
  let T₀ := T.toCenterImmersion
  let N := minimumRescaledNormalizedLoopAt T₀ hindex
    hC1 hr hrrho hrradius
  let U := centerMinimumActualRadialBaseUnit T₀ hindex
  let R := minimumRescaledRadiusLoopAt T₀ hindex
    hC1 hr hrrho hrradius
  let sigma := nonzeroOrientationSign M.centerMinimumPairingScalar
  let hsigma : sigma = 1 ∨ sigma = -1 :=
    nonzeroOrientationSign_eq_one_or_neg_one _
  let A := signedCenterRescaledActedLoop T sigma hsigma
    r hr hrradius
  let Z := definiteCircleRawLoop T r hr hrradius
  have hNclosed : N 0 = N 1 :=
    minimumRescaledNormalizedLoopAt_closed T₀ hindex
      hC1 hr hrrho hrradius
  have hUpos : 0 < ((U :
      Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ)).det := by
    exact centerMinimumActualRadialBaseUnit_det_pos T₀ hindex
  have hRpos : ∀ u, 0 < (R u).det := by
    exact matrixMulRightConst_det_pos N hUpos hNpos
  have hRclosed : R 0 = R 1 := by
    exact matrixMulRightConst_closed N (U :
      Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) hNclosed
  have hRclass : loopClassZ2 (positiveMatrixSOMap R hRpos)
      (positiveMatrixSOMap_closed R hRpos hRclosed) = 1 := by
    have hcongr := loopClassZ2_positiveMatrixSOMap_mulRightConst_congr
      N (U : Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ)
      hUpos hNpos hNclosed
    exact hcongr.trans hNclass
  have hApos : ∀ u, 0 < (A u).det := by
    exact signedCenterRescaledActedLoop_det_pos T sigma hsigma
      r hr hrradius
  have hAclosed : A 0 = A 1 :=
    signedCenterRescaledActedLoop_closed T sigma hsigma
      r hr hrradius
  have hsegment : ∀ p : I × I,
      0 < (matrixSegment (A p.2) (R p.2) p.1).det := by
    intro p
    apply matrixSegment_det_pos_of_succ_rows_eq
      (A p.2) (R p.2) (hApos p.2) (hRpos p.2) _ p.1
    intro i
    rw [signedCenterRescaledActedLoop_apply,
      minimumRescaledRadiusLoopAt_apply]
    ext j
    exact congrArg (fun v : E₁ => WithLp.ofLp v j)
      (M.minimumRescaledRadiusRows_succ_eq_signedActed
        hr (2 * Real.pi * (p.2 : ℝ)) i).symm
  have hAclass : loopClassZ2 (positiveMatrixSOMap A hApos)
      (positiveMatrixSOMap_closed A hApos hAclosed) = 1 :=
    loopClassZ2_positiveMatrixSOMap_eq_one_of_segment_pos
      A R hApos hRpos hAclosed hRclosed hRclass hsegment
  have hZpos : ∀ u, 0 < (Z u).det :=
    definiteCircleRawLoop_det_pos T r hr hrradius
  have hZclosed : Z 0 = Z 1 :=
    definiteCircleRawLoop_closed T r hr hrradius
  let O := M.signedCenterOrientationBlock sigma hsigma
  have hleftpos : ∀ u, 0 < (matrixMulLeftSO O Z u).det :=
    matrixMulLeftSO_det_pos O Z hZpos
  have hleftclosed : matrixMulLeftSO O Z 0 =
      matrixMulLeftSO O Z 1 :=
    matrixMulLeftSO_closed O Z hZclosed
  have hscale := loopClassZ2_positiveMatrixSOMap_scaleLastRow_congr
    (inv_pos.mpr hr) (matrixMulLeftSO O Z) hleftpos hleftclosed
  have hleft := loopClassZ2_positiveMatrixSOMap_mulLeftSO_congr
    O Z hZpos hZclosed
  have hAZ : loopClassZ2 (positiveMatrixSOMap A hApos)
        (positiveMatrixSOMap_closed A hApos hAclosed) =
      loopClassZ2 (positiveMatrixSOMap Z hZpos)
        (positiveMatrixSOMap_closed Z hZpos hZclosed) := by
    simpa [A, Z, O, signedCenterRescaledActedLoop] using
      hscale.trans hleft
  refine ⟨r, hr, hrradius, ?_⟩
  exact hAZ.symm.trans hAclass


-- @@ L3206-3289 verbatim
theorem exists_maximumDefiniteCircleRawLoop_class_one
    (T : M.EmbeddedShrink) (hindex : M.index = .maximum) :
    ∃ r : ℝ, ∃ hr : 0 < r, ∃ hrradius : r < T.radius,
      loopClassZ2
          (positiveMatrixSOMap (definiteCircleRawLoop T r hr hrradius)
            (definiteCircleRawLoop_det_pos T r hr hrradius))
          (positiveMatrixSOMap_closed (definiteCircleRawLoop T r hr hrradius)
            (definiteCircleRawLoop_det_pos T r hr hrradius)
            (definiteCircleRawLoop_closed T r hr hrradius)) = 1 := by
  obtain ⟨rho, hrho, hC1, r, hr, hrrho, hrradius, hNpos, hNclass⟩ :=
    exists_maximumRescaledNormalizedLoop_class_one T hindex
  let T₀ := T.toCenterImmersion
  let N := maximumRescaledNormalizedLoopAt T₀ hindex
    hC1 hr hrrho hrradius
  let U := centerMaximumActualRadialBaseUnit T₀ hindex
  let R := maximumRescaledRadiusLoopAt T₀ hindex
    hC1 hr hrrho hrradius
  let sigma := nonzeroOrientationSign M.centerMaximumPairingScalar
  let hsigma : sigma = 1 ∨ sigma = -1 :=
    nonzeroOrientationSign_eq_one_or_neg_one _
  let A := signedCenterRescaledActedLoop T sigma hsigma
    r hr hrradius
  let Z := definiteCircleRawLoop T r hr hrradius
  have hNclosed : N 0 = N 1 :=
    maximumRescaledNormalizedLoopAt_closed T₀ hindex
      hC1 hr hrrho hrradius
  have hUpos : 0 < ((U :
      Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ)).det := by
    exact centerMaximumActualRadialBaseUnit_det_pos T₀ hindex
  have hRpos : ∀ u, 0 < (R u).det := by
    exact matrixMulRightConst_det_pos N hUpos hNpos
  have hRclosed : R 0 = R 1 := by
    exact matrixMulRightConst_closed N (U :
      Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) hNclosed
  have hRclass : loopClassZ2 (positiveMatrixSOMap R hRpos)
      (positiveMatrixSOMap_closed R hRpos hRclosed) = 1 := by
    have hcongr := loopClassZ2_positiveMatrixSOMap_mulRightConst_congr
      N (U : Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ)
      hUpos hNpos hNclosed
    exact hcongr.trans hNclass
  have hApos : ∀ u, 0 < (A u).det := by
    exact signedCenterRescaledActedLoop_det_pos T sigma hsigma
      r hr hrradius
  have hAclosed : A 0 = A 1 :=
    signedCenterRescaledActedLoop_closed T sigma hsigma
      r hr hrradius
  have hsegment : ∀ p : I × I,
      0 < (matrixSegment (A p.2) (R p.2) p.1).det := by
    intro p
    apply matrixSegment_det_pos_of_succ_rows_eq
      (A p.2) (R p.2) (hApos p.2) (hRpos p.2) _ p.1
    intro i
    rw [signedCenterRescaledActedLoop_apply,
      maximumRescaledRadiusLoopAt_apply]
    ext j
    exact congrArg (fun v : E₁ => WithLp.ofLp v j)
      (M.maximumRescaledRadiusRows_succ_eq_signedActed
        hr (2 * Real.pi * (p.2 : ℝ)) i).symm
  have hAclass : loopClassZ2 (positiveMatrixSOMap A hApos)
      (positiveMatrixSOMap_closed A hApos hAclosed) = 1 :=
    loopClassZ2_positiveMatrixSOMap_eq_one_of_segment_pos
      A R hApos hRpos hAclosed hRclosed hRclass hsegment
  have hZpos : ∀ u, 0 < (Z u).det :=
    definiteCircleRawLoop_det_pos T r hr hrradius
  have hZclosed : Z 0 = Z 1 :=
    definiteCircleRawLoop_closed T r hr hrradius
  let O := M.signedCenterOrientationBlock sigma hsigma
  have hleftpos : ∀ u, 0 < (matrixMulLeftSO O Z u).det :=
    matrixMulLeftSO_det_pos O Z hZpos
  have hleftclosed : matrixMulLeftSO O Z 0 =
      matrixMulLeftSO O Z 1 :=
    matrixMulLeftSO_closed O Z hZclosed
  have hscale := loopClassZ2_positiveMatrixSOMap_scaleLastRow_congr
    (inv_pos.mpr hr) (matrixMulLeftSO O Z) hleftpos hleftclosed
  have hleft := loopClassZ2_positiveMatrixSOMap_mulLeftSO_congr
    O Z hZpos hZclosed
  have hAZ : loopClassZ2 (positiveMatrixSOMap A hApos)
        (positiveMatrixSOMap_closed A hApos hAclosed) =
      loopClassZ2 (positiveMatrixSOMap Z hZpos)
        (positiveMatrixSOMap_closed Z hZpos hZclosed) := by
    simpa [A, Z, O, signedCenterRescaledActedLoop] using
      hscale.trans hleft
  refine ⟨r, hr, hrradius, ?_⟩
  exact hAZ.symm.trans hAclass


-- @@ L3291-3291 verbatim
/-! The raw-loop calculation is exactly the canonical regular-zero frame. -/


-- @@ L3293-3322 verbatim
theorem exists_minimumDefiniteCircleRegularZeroFrame_class_one
    (T : M.EmbeddedShrink) (hindex : M.index = .minimum) :
    ∃ r : ℝ, ∃ hr : 0 < r, ∃ hrradius : r < T.radius,
      let z := T.definiteCircleCurve r hr hrradius
      let hreg : ∀ u, Surjective (spatialDeriv C.G (z u)) := fun _ =>
        M.definiteCircle_spatialDeriv_surjective hr
          (hrradius.trans_le T.radius_le)
      loopClassZ2 (regularZeroFrame C.smooth z hreg)
        (regularZeroFrame_closed C.smooth z hreg
          (T.definiteCircleCurve_closed r hr hrradius)) = 1 := by
  obtain ⟨r, hr, hrradius, hclass⟩ :=
    exists_minimumDefiniteCircleRawLoop_class_one T hindex
  refine ⟨r, hr, hrradius, ?_⟩
  dsimp only
  let z := T.definiteCircleCurve r hr hrradius
  let hreg : ∀ u, Surjective (spatialDeriv C.G (z u)) := fun _ =>
    M.definiteCircle_spatialDeriv_surjective hr
      (hrradius.trans_le T.radius_le)
  have hzclosed : z 0 = z 1 :=
    T.definiteCircleCurve_closed r hr hrradius
  have hframe := regularZeroFrame_eq_positiveMatrixSOMap_raw
    C.smooth z hreg
  have hrawclosed := regularZeroRawFrame_closed C.smooth z hreg hzclosed
  have hcongr := loopClassZ2_congr_fun
    (regularZeroFrame_closed C.smooth z hreg hzclosed)
    (positiveMatrixSOMap_closed (regularZeroRawFrame C.smooth z hreg)
      (regularZeroRawFrame_det_pos C.smooth z hreg) hrawclosed)
    hframe
  exact hcongr.trans (by
    simpa [z, hreg, definiteCircleRawLoop] using hclass)


-- @@ L3324-3353 verbatim
theorem exists_maximumDefiniteCircleRegularZeroFrame_class_one
    (T : M.EmbeddedShrink) (hindex : M.index = .maximum) :
    ∃ r : ℝ, ∃ hr : 0 < r, ∃ hrradius : r < T.radius,
      let z := T.definiteCircleCurve r hr hrradius
      let hreg : ∀ u, Surjective (spatialDeriv C.G (z u)) := fun _ =>
        M.definiteCircle_spatialDeriv_surjective hr
          (hrradius.trans_le T.radius_le)
      loopClassZ2 (regularZeroFrame C.smooth z hreg)
        (regularZeroFrame_closed C.smooth z hreg
          (T.definiteCircleCurve_closed r hr hrradius)) = 1 := by
  obtain ⟨r, hr, hrradius, hclass⟩ :=
    exists_maximumDefiniteCircleRawLoop_class_one T hindex
  refine ⟨r, hr, hrradius, ?_⟩
  dsimp only
  let z := T.definiteCircleCurve r hr hrradius
  let hreg : ∀ u, Surjective (spatialDeriv C.G (z u)) := fun _ =>
    M.definiteCircle_spatialDeriv_surjective hr
      (hrradius.trans_le T.radius_le)
  have hzclosed : z 0 = z 1 :=
    T.definiteCircleCurve_closed r hr hrradius
  have hframe := regularZeroFrame_eq_positiveMatrixSOMap_raw
    C.smooth z hreg
  have hrawclosed := regularZeroRawFrame_closed C.smooth z hreg hzclosed
  have hcongr := loopClassZ2_congr_fun
    (regularZeroFrame_closed C.smooth z hreg hzclosed)
    (positiveMatrixSOMap_closed (regularZeroRawFrame C.smooth z hreg)
      (regularZeroRawFrame_det_pos C.smooth z hreg) hrawclosed)
    hframe
  exact hcongr.trans (by
    simpa [z, hreg, definiteCircleRawLoop] using hclass)


-- @@ L3355-3355 verbatim
/-! ## Radius invariance inside the production embedded shrink -/


-- @@ L3357-3397 verbatim
/-- The literal annulus joining two positive definite circles. -/
def EmbeddedShrink.definiteCircleRadiusHomotopy
    (T : M.EmbeddedShrink)
    (r₀ r₁ : ℝ) (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (hrad₀ : r₀ < T.radius) (hrad₁ : r₁ < T.radius) :
    ContinuousMap.Homotopy
      (T.definiteCircleCurve r₀ hr₀ hrad₀)
      (T.definiteCircleCurve r₁ hr₁ hrad₁) where
  toFun q := M.definiteCircle
    (definiteRadiusInterpolation r₀ r₁ q.1)
    (2 * Real.pi * (q.2 : ℝ))
  continuous_toFun := by
    let u : I × I → E₂ := fun q => definiteCircleParam
      (definiteRadiusInterpolation r₀ r₁ q.1)
      (2 * Real.pi * (q.2 : ℝ))
    have hu : Continuous u := by
      unfold u definiteCircleParam pairToMorseParam
        definiteRadiusInterpolation
      fun_prop
    rw [continuous_iff_continuousAt]
    intro q
    apply (T.param_differentiableAt (u q) ?_).continuousAt.comp'
      hu.continuousAt
    change ‖definiteCircleParam
      (definiteRadiusInterpolation r₀ r₁ q.1)
      (2 * Real.pi * (q.2 : ℝ))‖ < T.radius
    rw [norm_definiteCircleParam
      (definiteRadiusInterpolation_pos hr₀ hr₁ q.1).le]
    exact definiteRadiusInterpolation_lt hrad₀ hrad₁ q.1
  map_zero_left u := by
    change M.definiteCircle
      (definiteRadiusInterpolation r₀ r₁ 0)
      (2 * Real.pi * (u : ℝ)) =
        M.param (definiteCircleParamCurve r₀ u)
    simp [definiteCircleParamCurve, definiteCircle, localPoint]
  map_one_left u := by
    change M.definiteCircle
      (definiteRadiusInterpolation r₀ r₁ 1)
      (2 * Real.pi * (u : ℝ)) =
        M.param (definiteCircleParamCurve r₁ u)
    simp [definiteCircleParamCurve, definiteCircle, localPoint]


-- @@ L3399-3410 verbatim
theorem EmbeddedShrink.definiteCircleRadiusHomotopy_regular
    (T : M.EmbeddedShrink)
    (r₀ r₁ : ℝ) (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (hrad₀ : r₀ < T.radius) (hrad₁ : r₁ < T.radius)
    (q : I × I) :
    Surjective (spatialDeriv C.G
      (T.definiteCircleRadiusHomotopy r₀ r₁ hr₀ hr₁
        hrad₀ hrad₁ q)) := by
  exact M.definiteCircle_spatialDeriv_surjective
    (definiteRadiusInterpolation_pos hr₀ hr₁ q.1)
    ((definiteRadiusInterpolation_lt hrad₀ hrad₁ q.1).trans_le
      T.radius_le)


-- @@ L3412-3435 verbatim
theorem EmbeddedShrink.definiteCircleRadiusHomotopy_closed
    (T : M.EmbeddedShrink)
    (r₀ r₁ : ℝ) (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (hrad₀ : r₀ < T.radius) (hrad₁ : r₁ < T.radius)
    (s : I) :
    T.definiteCircleRadiusHomotopy r₀ r₁ hr₀ hr₁
        hrad₀ hrad₁ (s, 0) =
      T.definiteCircleRadiusHomotopy r₀ r₁ hr₀ hr₁
        hrad₀ hrad₁ (s, 1) := by
  change (T.definiteCircleRadiusHomotopy r₀ r₁ hr₀ hr₁
      hrad₀ hrad₁).toFun (s, 0) =
    (T.definiteCircleRadiusHomotopy r₀ r₁ hr₀ hr₁
      hrad₀ hrad₁).toFun (s, 1)
  simp only [EmbeddedShrink.definiteCircleRadiusHomotopy]
  norm_num
  change M.definiteCircle (definiteRadiusInterpolation r₀ r₁ s) 0 =
    M.definiteCircle (definiteRadiusInterpolation r₀ r₁ s)
      (2 * Real.pi)
  unfold definiteCircle
  congr 1
  ext i
  fin_cases i <;>
    simp [definiteCircleParam, pairToMorseParam,
      Real.cos_two_pi, Real.sin_two_pi]


-- @@ L3437-3465 verbatim
/-- The regular-zero frame class is independent of the positive radius. -/
theorem EmbeddedShrink.loopClassZ2_definiteCircle_radius_congr
    (T : M.EmbeddedShrink)
    (r₀ r₁ : ℝ) (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (hrad₀ : r₀ < T.radius) (hrad₁ : r₁ < T.radius) :
    let z₀ := T.definiteCircleCurve r₀ hr₀ hrad₀
    let z₁ := T.definiteCircleCurve r₁ hr₁ hrad₁
    let hreg₀ : ∀ u, Surjective (spatialDeriv C.G (z₀ u)) := fun _ =>
      M.definiteCircle_spatialDeriv_surjective hr₀
        (hrad₀.trans_le T.radius_le)
    let hreg₁ : ∀ u, Surjective (spatialDeriv C.G (z₁ u)) := fun _ =>
      M.definiteCircle_spatialDeriv_surjective hr₁
        (hrad₁.trans_le T.radius_le)
    loopClassZ2 (regularZeroFrame C.smooth z₀ hreg₀)
        (regularZeroFrame_closed C.smooth z₀ hreg₀
          (T.definiteCircleCurve_closed r₀ hr₀ hrad₀)) =
      loopClassZ2 (regularZeroFrame C.smooth z₁ hreg₁)
        (regularZeroFrame_closed C.smooth z₁ hreg₁
          (T.definiteCircleCurve_closed r₁ hr₁ hrad₁)) := by
  dsimp only
  exact loopClassZ2_regularZeroFrame_congr C.smooth
    (T.definiteCircleRadiusHomotopy r₀ r₁ hr₀ hr₁
      hrad₀ hrad₁)
    (T.definiteCircleRadiusHomotopy_regular r₀ r₁ hr₀ hr₁
      hrad₀ hrad₁)
    (T.definiteCircleCurve_closed r₀ hr₀ hrad₀)
    (T.definiteCircleCurve_closed r₁ hr₁ hrad₁)
    (T.definiteCircleRadiusHomotopy_closed r₀ r₁ hr₀ hr₁
      hrad₀ hrad₁)


-- @@ L3467-3482 verbatim
theorem EmbeddedShrink.minimumDefiniteCircleRegularZeroFrame_class_one
    (T : M.EmbeddedShrink) (hindex : M.index = .minimum)
    (r : ℝ) (hr : 0 < r) (hrradius : r < T.radius) :
    let z := T.definiteCircleCurve r hr hrradius
    let hreg : ∀ u, Surjective (spatialDeriv C.G (z u)) := fun _ =>
      M.definiteCircle_spatialDeriv_surjective hr
        (hrradius.trans_le T.radius_le)
    loopClassZ2 (regularZeroFrame C.smooth z hreg)
      (regularZeroFrame_closed C.smooth z hreg
        (T.definiteCircleCurve_closed r hr hrradius)) = 1 := by
  obtain ⟨r₀, hr₀, hrad₀, hsmall⟩ :=
    exists_minimumDefiniteCircleRegularZeroFrame_class_one T hindex
  have hcongr := T.loopClassZ2_definiteCircle_radius_congr
    r₀ r hr₀ hr hrad₀ hrradius
  dsimp only at hcongr ⊢
  exact hcongr.symm.trans hsmall


-- @@ L3484-3499 verbatim
theorem EmbeddedShrink.maximumDefiniteCircleRegularZeroFrame_class_one
    (T : M.EmbeddedShrink) (hindex : M.index = .maximum)
    (r : ℝ) (hr : 0 < r) (hrradius : r < T.radius) :
    let z := T.definiteCircleCurve r hr hrradius
    let hreg : ∀ u, Surjective (spatialDeriv C.G (z u)) := fun _ =>
      M.definiteCircle_spatialDeriv_surjective hr
        (hrradius.trans_le T.radius_le)
    loopClassZ2 (regularZeroFrame C.smooth z hreg)
      (regularZeroFrame_closed C.smooth z hreg
        (T.definiteCircleCurve_closed r hr hrradius)) = 1 := by
  obtain ⟨r₀, hr₀, hrad₀, hsmall⟩ :=
    exists_maximumDefiniteCircleRegularZeroFrame_class_one T hindex
  have hcongr := T.loopClassZ2_definiteCircle_radius_congr
    r₀ r hr₀ hr hrad₀ hrradius
  dsimp only at hcongr ⊢
  exact hcongr.symm.trans hsmall


-- @@ L3501-3501 verbatim
/-! ## Identification with the actual simple-orbit parameter frames -/


-- @@ L3503-3536 verbatim
theorem EmbeddedShrink.minimumDefiniteCircleRegularZeroFrame_eq_paramFrameLoop
    (T : M.EmbeddedShrink) (hindex : M.index = .minimum)
    (r : ℝ) (hr : 0 < r) (hrradius : r < T.radius)
    (hreg : sliceRegular C.G (tcoord center + r ^ 2))
    (V : TamedField (T.minimumPositiveSlice r hreg)) :
    regularZeroFrame C.smooth (T.definiteCircleCurve r hr hrradius)
        (fun _ => M.definiteCircle_spatialDeriv_surjective hr
          (hrradius.trans_le T.radius_le)) =
      (T.minimumSimpleClosedOrbitParam hindex r hr hrradius hreg V).paramFrameLoop := by
  let P := T.minimumSimpleClosedOrbitParam hindex r hr hrradius hreg V
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  change regularZeroFrameMatrix C.G
      (T.definiteCircleCurve r hr hrradius) u =
    frameLoop (T.minimumPositiveSlice r hreg) P.realCurve (u : ℝ)
  unfold regularZeroFrameMatrix frameLoop
  rw [P.realCurve_coe]
  have htime := M.minimumCircle_time hindex (theta :=
    2 * Real.pi * (u : ℝ)) hr.le
      (hrradius.trans_le T.radius_le)
  change tcoord (M.definiteCircle r (2 * Real.pi * (u : ℝ))) =
    tcoord center + r ^ 2 at htime
  change rowsMatrix (gramSchmidtNormed ℝ
      (SlabTamedField.sliceFrameAt C.G
        (tcoord (M.definiteCircle r (2 * Real.pi * (u : ℝ))))
        (spacePart (M.definiteCircle r (2 * Real.pi * (u : ℝ)))))) =
    rowsMatrix (gramSchmidtNormed ℝ
      (frameAt (T.minimumPositiveSlice r hreg) (P.curve u)))
  rw [htime]
  simp [P, minimumSimpleClosedOrbitParam, definiteSpatialCircle,
    minimumPositiveSlice, SlabTamedField.sliceFLSAt, sliceFLS, frameAt,
    SlabTamedField.sliceFrameAt]
  rfl


-- @@ L3538-3571 verbatim
theorem EmbeddedShrink.maximumDefiniteCircleRegularZeroFrame_eq_paramFrameLoop
    (T : M.EmbeddedShrink) (hindex : M.index = .maximum)
    (r : ℝ) (hr : 0 < r) (hrradius : r < T.radius)
    (hreg : sliceRegular C.G (tcoord center - r ^ 2))
    (V : TamedField (T.maximumNegativeSlice r hreg)) :
    regularZeroFrame C.smooth (T.definiteCircleCurve r hr hrradius)
        (fun _ => M.definiteCircle_spatialDeriv_surjective hr
          (hrradius.trans_le T.radius_le)) =
      (T.maximumSimpleClosedOrbitParam hindex r hr hrradius hreg V).paramFrameLoop := by
  let P := T.maximumSimpleClosedOrbitParam hindex r hr hrradius hreg V
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  change regularZeroFrameMatrix C.G
      (T.definiteCircleCurve r hr hrradius) u =
    frameLoop (T.maximumNegativeSlice r hreg) P.realCurve (u : ℝ)
  unfold regularZeroFrameMatrix frameLoop
  rw [P.realCurve_coe]
  have htime := M.maximumCircle_time hindex (theta :=
    2 * Real.pi * (u : ℝ)) hr.le
      (hrradius.trans_le T.radius_le)
  change tcoord (M.definiteCircle r (2 * Real.pi * (u : ℝ))) =
    tcoord center - r ^ 2 at htime
  change rowsMatrix (gramSchmidtNormed ℝ
      (SlabTamedField.sliceFrameAt C.G
        (tcoord (M.definiteCircle r (2 * Real.pi * (u : ℝ))))
        (spacePart (M.definiteCircle r (2 * Real.pi * (u : ℝ)))))) =
    rowsMatrix (gramSchmidtNormed ℝ
      (frameAt (T.maximumNegativeSlice r hreg) (P.curve u)))
  rw [htime]
  simp [P, maximumSimpleClosedOrbitParam, definiteSpatialCircle,
    maximumNegativeSlice, SlabTamedField.sliceFLSAt, sliceFLS, frameAt,
    SlabTamedField.sliceFrameAt]
  rfl


-- @@ L3573-3600 verbatim
/-- The actual born minimum circle has the nontrivial stable frame class. -/
theorem EmbeddedShrink.minimumSimpleClosedOrbitParam_frame_class_one
    (T : M.EmbeddedShrink) (hindex : M.index = .minimum)
    (r : ℝ) (hr : 0 < r) (hrradius : r < T.radius)
    (hreg : sliceRegular C.G (tcoord center + r ^ 2))
    (V : TamedField (T.minimumPositiveSlice r hreg)) :
    loopClassZ2
        (T.minimumSimpleClosedOrbitParam hindex r hr hrradius hreg V).paramFrameLoop
        (T.minimumSimpleClosedOrbitParam hindex r hr hrradius hreg V).paramFrameLoop_closed =
      1 := by
  let z := T.definiteCircleCurve r hr hrradius
  let hz : ∀ u, Surjective (spatialDeriv C.G (z u)) := fun _ =>
    M.definiteCircle_spatialDeriv_surjective hr
      (hrradius.trans_le T.radius_le)
  let P := T.minimumSimpleClosedOrbitParam hindex r hr hrradius hreg V
  have hclass : loopClassZ2 (regularZeroFrame C.smooth z hz)
      (regularZeroFrame_closed C.smooth z hz
        (T.definiteCircleCurve_closed r hr hrradius)) = 1 := by
    exact T.minimumDefiniteCircleRegularZeroFrame_class_one
      hindex r hr hrradius
  have heq : regularZeroFrame C.smooth z hz = P.paramFrameLoop := by
    exact T.minimumDefiniteCircleRegularZeroFrame_eq_paramFrameLoop
      hindex r hr hrradius hreg V
  have hcongr := loopClassZ2_congr_fun
    (regularZeroFrame_closed C.smooth z hz
      (T.definiteCircleCurve_closed r hr hrradius))
    P.paramFrameLoop_closed heq
  exact hcongr.symm.trans hclass


-- @@ L3602-3629 verbatim
/-- The actual pre-death maximum circle has the nontrivial stable frame class. -/
theorem EmbeddedShrink.maximumSimpleClosedOrbitParam_frame_class_one
    (T : M.EmbeddedShrink) (hindex : M.index = .maximum)
    (r : ℝ) (hr : 0 < r) (hrradius : r < T.radius)
    (hreg : sliceRegular C.G (tcoord center - r ^ 2))
    (V : TamedField (T.maximumNegativeSlice r hreg)) :
    loopClassZ2
        (T.maximumSimpleClosedOrbitParam hindex r hr hrradius hreg V).paramFrameLoop
        (T.maximumSimpleClosedOrbitParam hindex r hr hrradius hreg V).paramFrameLoop_closed =
      1 := by
  let z := T.definiteCircleCurve r hr hrradius
  let hz : ∀ u, Surjective (spatialDeriv C.G (z u)) := fun _ =>
    M.definiteCircle_spatialDeriv_surjective hr
      (hrradius.trans_le T.radius_le)
  let P := T.maximumSimpleClosedOrbitParam hindex r hr hrradius hreg V
  have hclass : loopClassZ2 (regularZeroFrame C.smooth z hz)
      (regularZeroFrame_closed C.smooth z hz
        (T.definiteCircleCurve_closed r hr hrradius)) = 1 := by
    exact T.maximumDefiniteCircleRegularZeroFrame_class_one
      hindex r hr hrradius
  have heq : regularZeroFrame C.smooth z hz = P.paramFrameLoop := by
    exact T.maximumDefiniteCircleRegularZeroFrame_eq_paramFrameLoop
      hindex r hr hrradius hreg V
  have hcongr := loopClassZ2_congr_fun
    (regularZeroFrame_closed C.smooth z hz
      (T.definiteCircleCurve_closed r hr hrradius))
    P.paramFrameLoop_closed heq
  exact hcongr.symm.trans hclass


-- @@ L3631-3631 verbatim
end StandardMorseEventAt


-- @@ L3633-3633 verbatim
end Submission
