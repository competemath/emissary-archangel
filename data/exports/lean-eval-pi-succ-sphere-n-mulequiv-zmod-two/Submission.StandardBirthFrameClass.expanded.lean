import Submission.StandardBirthDelta
import Submission.TubeFrameClass


-- @@ L4-12 verbatim
/-!
# The explicit frame class of the standard definite birth

This file discharges the last local calculation left by
`StandardBirthDelta`: the Gram--Schmidt frame around the literal outgoing unit
circle makes one turn.  The orientation sign of the kernel vector is kept as
the (constant) sign of an initial determinant, avoiding a parity split on the
ambient dimension.
-/


-- @@ L14-14 verbatim
noncomputable section


-- @@ L16-16 verbatim
set_option maxHeartbeats 1600000


-- @@ L18-18 verbatim
namespace Submission

-- @@ L19-19 verbatim
namespace StandardBirth


-- @@ L21-21 verbatim
open Set Function InnerProductSpace

-- @@ L22-22 verbatim
open scoped RealInnerProductSpace Topology Matrix unitInterval


-- @@ L24-24 verbatim
variable (m : ℕ)


-- @@ L26-26 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 2))

-- @@ L27-27 verbatim
local notation "F" => EuclideanSpace ℝ (Fin (m + 1))


-- @@ L29-29 verbatim
/-! ## Derivative and gradient rows -/


-- @@ L31-48 verbatim
theorem fderiv_circleMap_apply_castSucc (a : ℝ) (x h : E) (j : Fin m) :
    fderiv ℝ (circleMap m a) x h j.castSucc = h j.castSucc.castSucc := by
  let outProj : F →L[ℝ] ℝ := EuclideanSpace.proj j.castSucc
  let inProj : E →L[ℝ] ℝ := EuclideanSpace.proj j.castSucc.castSucc
  have hG : HasFDerivAt (circleMap m a) (fderiv ℝ (circleMap m a) x) x :=
    ((contDiff_circleMap m a).differentiable infty_ne_zero x).hasFDerivAt
  have hcomp : HasFDerivAt (fun w => circleMap m a w j.castSucc)
      (outProj.comp (fderiv ℝ (circleMap m a) x)) x := by
    exact (PiLp.hasFDerivAt_apply 2 (circleMap m a x) j.castSucc).comp x hG
  have hcoord : HasFDerivAt (fun w : E => w j.castSucc.castSucc) inProj x :=
    inProj.hasFDerivAt
  have hfun : (fun w => circleMap m a w j.castSucc) =
      fun w : E => w j.castSucc.castSucc := by
    funext w
    simp [circleMap]
  have hmaps : outProj.comp (fderiv ℝ (circleMap m a) x) = inProj := by
    rw [← hcomp.fderiv, hfun, hcoord.fderiv]
  exact congrArg (fun A : E →L[ℝ] ℝ => A h) hmaps


-- @@ L50-79 verbatim
theorem fderiv_circleMap_apply_last (a : ℝ) (x h : E) :
    fderiv ℝ (circleMap m a) x h (Fin.last m) =
      2 * x (radialFirst m) * h (radialFirst m) +
        2 * x (radialSecond m) * h (radialSecond m) := by
  let outProj : F →L[ℝ] ℝ := EuclideanSpace.proj (Fin.last m)
  have hG : HasFDerivAt (circleMap m a) (fderiv ℝ (circleMap m a) x) x :=
    ((contDiff_circleMap m a).differentiable infty_ne_zero x).hasFDerivAt
  have hcomp : HasFDerivAt (fun w => circleMap m a w (Fin.last m))
      (outProj.comp (fderiv ℝ (circleMap m a) x)) x := by
    exact (PiLp.hasFDerivAt_apply 2 (circleMap m a x) (Fin.last m)).comp x hG
  have hfun : (fun w => circleMap m a w (Fin.last m)) = fun w : E =>
      w (radialFirst m) ^ 2 + w (radialSecond m) ^ 2 - a := by
    funext w
    simp [circleMap, radialSq]
  have happ := congrArg (fun A : E →L[ℝ] ℝ => A h) hcomp.fderiv.symm
  rw [hfun] at happ
  let pA : E →L[ℝ] ℝ := EuclideanSpace.proj (radialFirst m)
  let pB : E →L[ℝ] ℝ := EuclideanSpace.proj (radialSecond m)
  have hA := (pA.hasFDerivAt : HasFDerivAt pA pA x).pow 2
  have hB := (pB.hasFDerivAt : HasFDerivAt pB pB x).pow 2
  have hdirect := (hA.add hB).sub (hasFDerivAt_const a x)
  have hscalarEq :
      (((fun z => pA z ^ 2) + fun z => pB z ^ 2) - fun _ : E => a) =
        (fun w : E =>
          w (radialFirst m) ^ 2 + w (radialSecond m) ^ 2 - a) := by
    funext w
    rfl
  rw [hscalarEq] at hdirect
  rw [hdirect.fderiv] at happ
  simpa [outProj, pA, pB, mul_comm, mul_left_comm, mul_assoc] using happ


-- @@ L81-92 verbatim
theorem gradVec_circleMap_castSucc (a : ℝ) (x : E) (j : Fin m) :
    gradVec (circleMap m a) j.castSucc x =
      EuclideanSpace.single j.castSucc.castSucc 1 := by
  apply ext_inner_right_basis (EuclideanSpace.basisFun (Fin (m + 2)) ℝ).toBasis
  intro k
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  change ⟪gradVec (circleMap m a) j.castSucc x,
      EuclideanSpace.single k 1⟫_ℝ =
    ⟪EuclideanSpace.single j.castSucc.castSucc 1,
      EuclideanSpace.single k 1⟫_ℝ
  rw [inner_gradVec, fderiv_circleMap_apply_castSucc]
  simp [EuclideanSpace.inner_single_left, PiLp.single_apply]


-- @@ L94-113 verbatim
theorem gradVec_circleMap_last (a : ℝ) (x : E) :
    gradVec (circleMap m a) (Fin.last m) x =
      (((2 : ℝ) * x (radialFirst m)) •
        EuclideanSpace.single (radialFirst m) 1) +
      (((2 : ℝ) * x (radialSecond m)) •
        EuclideanSpace.single (radialSecond m) 1) := by
  apply ext_inner_right_basis (EuclideanSpace.basisFun (Fin (m + 2)) ℝ).toBasis
  intro k
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  change ⟪gradVec (circleMap m a) (Fin.last m) x,
      EuclideanSpace.single k 1⟫_ℝ =
    ⟪(((2 : ℝ) * x (radialFirst m)) •
        EuclideanSpace.single (radialFirst m) 1) +
      (((2 : ℝ) * x (radialSecond m)) •
        EuclideanSpace.single (radialSecond m) 1),
      EuclideanSpace.single k 1⟫_ℝ
  rw [inner_gradVec, fderiv_circleMap_apply_last]
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
    EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_left]
  simp [EuclideanSpace.inner_single_left, PiLp.single_apply]


-- @@ L115-115 verbatim
/-! ## The elementary radial and tangent frame -/


-- @@ L117-120 verbatim
/-- Counterclockwise unit tangent to `circlePoint`. -/
def tangentPoint (theta : ℝ) : E :=
  (-Real.sin theta) • EuclideanSpace.single (radialFirst m) 1 +
    Real.cos theta • EuclideanSpace.single (radialSecond m) 1


-- @@ L122-128 verbatim
@[simp] theorem tangentPoint_apply_radialFirst (theta : ℝ) :
    tangentPoint m theta (radialFirst m) = -Real.sin theta := by
  have hAB : radialFirst m ≠ radialSecond m := by
    intro h
    have := congrArg Fin.val h
    simp [radialFirst, radialSecond] at this
  simp [tangentPoint, hAB]


-- @@ L130-136 verbatim
@[simp] theorem tangentPoint_apply_radialSecond (theta : ℝ) :
    tangentPoint m theta (radialSecond m) = Real.cos theta := by
  have hBA : radialSecond m ≠ radialFirst m := by
    intro h
    have := congrArg Fin.val h
    simp [radialFirst, radialSecond] at this
  simp [tangentPoint, hBA]


-- @@ L138-150 verbatim
@[simp] theorem tangentPoint_apply_transverse (theta : ℝ) (j : Fin m) :
    tangentPoint m theta j.castSucc.castSucc = 0 := by
  have hjA : j.castSucc.castSucc ≠ radialFirst m := by
    intro h
    have := congrArg Fin.val h
    simp [radialFirst] at this
    omega
  have hjB : j.castSucc.castSucc ≠ radialSecond m := by
    intro h
    have := congrArg Fin.val h
    simp [radialSecond] at this
    omega
  simp [tangentPoint, hjA, hjB]


-- @@ L152-167 verbatim
theorem norm_tangentPoint (theta : ℝ) : ‖tangentPoint m theta‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num)]
  rw [normSq_eq_sum_sq]
  have hsum : (∑ j, tangentPoint m theta j ^ 2) =
      (-Real.sin theta) ^ 2 + (Real.cos theta) ^ 2 := by
    rw [Fin.sum_univ_castSucc]
    change (∑ j : Fin (m + 1), tangentPoint m theta j.castSucc ^ 2) +
      tangentPoint m theta (radialSecond m) ^ 2 = _
    rw [tangentPoint_apply_radialSecond]
    rw [Fin.sum_univ_castSucc]
    change (∑ j : Fin m, tangentPoint m theta j.castSucc.castSucc ^ 2) +
      tangentPoint m theta (radialFirst m) ^ 2 + Real.cos theta ^ 2 = _
    rw [tangentPoint_apply_radialFirst]
    simp [tangentPoint_apply_transverse]
  rw [hsum]
  nlinarith [Real.sin_sq_add_cos_sq theta]


-- @@ L169-184 verbatim
theorem norm_circlePoint (theta : ℝ) : ‖circlePoint m theta‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num)]
  rw [normSq_eq_sum_sq]
  have hsum : (∑ j, circlePoint m theta j ^ 2) =
      (Real.cos theta) ^ 2 + (Real.sin theta) ^ 2 := by
    rw [Fin.sum_univ_castSucc]
    change (∑ j : Fin (m + 1), circlePoint m theta j.castSucc ^ 2) +
      circlePoint m theta (radialSecond m) ^ 2 = _
    rw [circlePoint_apply_radialSecond]
    rw [Fin.sum_univ_castSucc]
    change (∑ j : Fin m, circlePoint m theta j.castSucc.castSucc ^ 2) +
      circlePoint m theta (radialFirst m) ^ 2 + Real.sin theta ^ 2 = _
    rw [circlePoint_apply_radialFirst]
    simp [circlePoint_apply_transverse]
  rw [hsum]
  nlinarith [Real.sin_sq_add_cos_sq theta]


-- @@ L186-203 verbatim
theorem inner_tangentPoint_circlePoint (theta : ℝ) :
    ⟪tangentPoint m theta, circlePoint m theta⟫_ℝ = 0 := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  rw [Fin.sum_univ_castSucc]
  change (∑ j : Fin (m + 1),
      circlePoint m theta j.castSucc * tangentPoint m theta j.castSucc) +
    circlePoint m theta (radialSecond m) *
      tangentPoint m theta (radialSecond m) = 0
  rw [tangentPoint_apply_radialSecond, circlePoint_apply_radialSecond]
  rw [Fin.sum_univ_castSucc]
  change (∑ j : Fin m, circlePoint m theta j.castSucc.castSucc *
      tangentPoint m theta j.castSucc.castSucc) +
    circlePoint m theta (radialFirst m) * tangentPoint m theta (radialFirst m) +
      Real.sin theta * Real.cos theta = 0
  rw [tangentPoint_apply_radialFirst, circlePoint_apply_radialFirst]
  simp [tangentPoint_apply_transverse, circlePoint_apply_transverse]
  ring


-- @@ L205-209 verbatim
theorem inner_transverse_tangentPoint (theta : ℝ) (j : Fin m) :
    ⟪EuclideanSpace.single j.castSucc.castSucc 1,
      tangentPoint m theta⟫_ℝ = 0 := by
  rw [EuclideanSpace.inner_single_left]
  simp


-- @@ L211-215 verbatim
theorem inner_transverse_circlePoint (theta : ℝ) (j : Fin m) :
    ⟪EuclideanSpace.single j.castSucc.castSucc 1,
      circlePoint m theta⟫_ℝ = 0 := by
  rw [EuclideanSpace.inner_single_left]
  simp


-- @@ L217-233 verbatim
theorem inner_transverse_transverse (j k : Fin m) :
    ⟪EuclideanSpace.single j.castSucc.castSucc (1 : ℝ),
      EuclideanSpace.single k.castSucc.castSucc (1 : ℝ)⟫_ℝ =
        if j = k then 1 else 0 := by
  rw [EuclideanSpace.inner_single_left]
  by_cases h : j = k
  · subst k
    simp
  · have hcast : j.castSucc.castSucc ≠ k.castSucc.castSucc := by
      intro heq
      apply h
      apply Fin.ext
      have hv : (j.castSucc.castSucc : Fin (m + 2)).val =
          (k.castSucc.castSucc : Fin (m + 2)).val :=
        congrArg (fun z : Fin (m + 2) => z.val) heq
      exact hv
    simp [h, hcast]


-- @@ L235-239 verbatim
/-- The component gradients before their final positive scaling: the transverse
coordinate vectors followed by the outward radial unit vector. -/
def normalUnit (theta : ℝ) : Fin (m + 1) → E :=
  Fin.lastCases (circlePoint m theta)
    (fun j : Fin m => EuclideanSpace.single j.castSucc.castSucc 1)


-- @@ L241-243 verbatim
@[simp] theorem normalUnit_last (theta : ℝ) :
    normalUnit m theta (Fin.last m) = circlePoint m theta := by
  simp [normalUnit]


-- @@ L245-248 verbatim
@[simp] theorem normalUnit_castSucc (theta : ℝ) (j : Fin m) :
    normalUnit m theta j.castSucc =
      EuclideanSpace.single j.castSucc.castSucc 1 := by
  simp [normalUnit]


-- @@ L250-273 verbatim
theorem orthonormal_normalUnit (theta : ℝ) :
    Orthonormal ℝ (normalUnit m theta) := by
  rw [orthonormal_iff_ite]
  intro i j
  induction i using Fin.lastCases with
  | last =>
      induction j using Fin.lastCases with
      | last =>
          rw [normalUnit_last, real_inner_self_eq_norm_sq, norm_circlePoint]
          simp
      | cast j =>
          rw [normalUnit_last, normalUnit_castSucc, real_inner_comm,
            inner_transverse_circlePoint]
          simp [Fin.castSucc_lt_last j |>.ne']
  | cast i =>
      induction j using Fin.lastCases with
      | last =>
          rw [normalUnit_castSucc, normalUnit_last,
            inner_transverse_circlePoint]
          simp [Fin.castSucc_lt_last i |>.ne]
      | cast j =>
          rw [normalUnit_castSucc, normalUnit_castSucc,
            inner_transverse_transverse]
          simp


-- @@ L275-277 verbatim
/-- The unoriented elementary full frame, with counterclockwise tangent first. -/
def unitFrame (theta : ℝ) : Fin (m + 2) → E :=
  Fin.cons (tangentPoint m theta) (normalUnit m theta)


-- @@ L279-309 verbatim
theorem orthonormal_unitFrame (theta : ℝ) :
    Orthonormal ℝ (unitFrame m theta) := by
  rw [orthonormal_iff_ite]
  intro i j
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · rw [unitFrame, Fin.cons_zero, real_inner_self_eq_norm_sq,
        norm_tangentPoint]
      simp
    · induction j using Fin.lastCases with
      | last =>
          rw [unitFrame, Fin.cons_zero, Fin.cons_succ, normalUnit_last,
            inner_tangentPoint_circlePoint]
          simp
      | cast j =>
          rw [unitFrame, Fin.cons_zero, Fin.cons_succ, normalUnit_castSucc,
            real_inner_comm, inner_transverse_tangentPoint]
          simp only [if_neg (Fin.succ_ne_zero j.castSucc).symm]
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · induction i using Fin.lastCases with
      | last =>
          rw [unitFrame, Fin.cons_succ, normalUnit_last, Fin.cons_zero,
            real_inner_comm, inner_tangentPoint_circlePoint]
          simp
      | cast i =>
          rw [unitFrame, Fin.cons_succ, normalUnit_castSucc, Fin.cons_zero,
            inner_transverse_tangentPoint]
          simp
    · rw [unitFrame, Fin.cons_succ, Fin.cons_succ]
      simpa only [Fin.succ_inj] using
        orthonormal_iff_ite.mp (orthonormal_normalUnit m theta) i j


-- @@ L311-311 verbatim
/-! ## Rotation of the elementary frame -/


-- @@ L313-323 verbatim
theorem tangentPoint_rotation (theta : ℝ) :
    tangentPoint m theta =
      Real.cos theta • tangentPoint m 0 -
        Real.sin theta • circlePoint m 0 := by
  apply (WithLp.equiv 2 _).injective
  funext j
  change tangentPoint m theta j =
    (Real.cos theta • tangentPoint m 0 -
      Real.sin theta • circlePoint m 0) j
  simp [tangentPoint, circlePoint, Pi.single_apply, smul_smul]
  split_ifs <;> ring


-- @@ L325-335 verbatim
theorem circlePoint_rotation (theta : ℝ) :
    circlePoint m theta =
      Real.sin theta • tangentPoint m 0 +
        Real.cos theta • circlePoint m 0 := by
  apply (WithLp.equiv 2 _).injective
  funext j
  change circlePoint m theta j =
    (Real.sin theta • tangentPoint m 0 +
      Real.cos theta • circlePoint m 0) j
  simp [tangentPoint, circlePoint, Pi.single_apply, smul_smul]
  split_ifs <;> ring


-- @@ L337-339 verbatim
theorem unitFrame_zero (theta : ℝ) :
    unitFrame m theta 0 = tangentPoint m theta := by
  simp [unitFrame]


-- @@ L341-346 verbatim
theorem unitFrame_last (theta : ℝ) :
    unitFrame m theta (Fin.last (m + 1)) = circlePoint m theta := by
  have hs : (Fin.last m).succ = (Fin.last (m + 1) : Fin (m + 2)) := by
    apply Fin.ext
    simp
  rw [← hs, unitFrame, Fin.cons_succ, normalUnit_last]


-- @@ L348-359 verbatim
theorem unitFrame_middle_eq_zero (theta : ℝ) {i : Fin (m + 2)}
    (hi0 : i ≠ 0) (hil : i ≠ Fin.last (m + 1)) :
    unitFrame m theta i = unitFrame m 0 i := by
  obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero hi0
  induction k using Fin.lastCases with
  | last =>
      exfalso
      apply hil
      apply Fin.ext
      simp
  | cast k =>
      simp [unitFrame, normalUnit]


-- @@ L361-361 verbatim
variable (a : ℕ)


-- @@ L363-396 verbatim
lemma twistMat_mul_apply_birth
    (theta : ℝ) (A : Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ)
    (i j : Fin (a + 3)) :
    (twistMat a theta * A) i j =
      if i = 0 then
        Real.cos theta * A 0 j - Real.sin theta * A (Fin.last (a + 2)) j
      else if i = Fin.last (a + 2) then
        Real.sin theta * A 0 j + Real.cos theta * A (Fin.last (a + 2)) j
      else A i j := by
  rw [Matrix.mul_apply]
  by_cases hi0 : i = 0
  · subst i
    rw [if_pos rfl]
    simp only [twistMat_entries, if_pos]
    simpa [sub_eq_add_neg] using
      sum_two_ite (m := a) (Ne.symm (lastA_ne_zero (m := a)))
        (fun x => Real.cos theta * A x j)
        (fun x => -(Real.sin theta * A x j))
  · rw [if_neg hi0]
    by_cases hil : i = Fin.last (a + 2)
    · subst i
      rw [if_pos rfl]
      simp only [twistMat_entries, if_neg (lastA_ne_zero (m := a)), if_pos]
      simpa using
        sum_two_ite (m := a) (Ne.symm (lastA_ne_zero (m := a)))
          (fun x => Real.sin theta * A x j)
          (fun x => Real.cos theta * A x j)
    · rw [if_neg hil]
      simp only [twistMat_entries, if_neg hi0, if_neg hil]
      rw [Finset.sum_eq_single i]
      · simp
      · intro c _ hc
        simp [hc]
      · exact fun h => absurd (Finset.mem_univ i) h


-- @@ L398-429 verbatim
/-- The elementary frame rotates only its first and last rows. -/
theorem rowsMatrix_unitFrame_rotation (theta : ℝ) :
    rowsMatrix (unitFrame (a + 1) theta) =
      twistMat a theta * rowsMatrix (unitFrame (a + 1) 0) := by
  ext i j
  rw [twistMat_mul_apply_birth]
  by_cases hi0 : i = 0
  · subst i
    rw [if_pos rfl]
    simp only [rowsMatrix, Matrix.of_apply, unitFrame_zero]
    have hlast : unitFrame (a + 1) 0 (Fin.last (a + 2)) =
        circlePoint (a + 1) 0 := by
      exact unitFrame_last (a + 1) 0
    rw [hlast]
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin (a + 3)) => v j)
      (tangentPoint_rotation (a + 1) theta)
    simpa [sub_eq_add_neg] using h
  · rw [if_neg hi0]
    by_cases hil : i = Fin.last (a + 2)
    · subst i
      rw [if_pos rfl]
      simp only [rowsMatrix, Matrix.of_apply, unitFrame_last]
      have hzero : unitFrame (a + 1) 0 0 = tangentPoint (a + 1) 0 := by
        exact unitFrame_zero (a + 1) 0
      rw [hzero]
      have h := congrArg (fun v : EuclideanSpace ℝ (Fin (a + 3)) => v j)
        (circlePoint_rotation (a + 1) theta)
      simpa using h
    · rw [if_neg hil]
      simp only [rowsMatrix, Matrix.of_apply]
      exact congrArg (fun v : EuclideanSpace ℝ (Fin (a + 3)) => v j)
        (unitFrame_middle_eq_zero (a + 1) theta hi0 hil)


-- @@ L431-439 verbatim
theorem det_twistMat (theta : ℝ) : (twistMat a theta).det = 1 := by
  rw [twistMat, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    det_swapRotMat]
  have hrot : (rotAmbient a theta).det = 1 := by
    rw [← rotBlock_eq_rotAmbient]
    exact (Matrix.mem_specialOrthogonalGroup_iff.mp
      (rotBlock_mem (a + 3) theta)).2
  rw [hrot]
  ring


-- @@ L441-443 verbatim
/-- The determinant of the counterclockwise elementary frame at angle zero. -/
def unitFrameDet : ℝ :=
  (rowsMatrix (unitFrame (a + 1) 0)).det


-- @@ L445-448 verbatim
theorem det_rowsMatrix_unitFrame (theta : ℝ) :
    (rowsMatrix (unitFrame (a + 1) theta)).det = unitFrameDet a := by
  rw [rowsMatrix_unitFrame_rotation, Matrix.det_mul, det_twistMat]
  simp [unitFrameDet]


-- @@ L450-454 verbatim
theorem unitFrameDet_mul_self : unitFrameDet a * unitFrameDet a = 1 := by
  have hmul := rowsMatrix_mul_transpose_of_orthonormal
    (orthonormal_unitFrame (a + 1) 0)
  have hdet := congrArg Matrix.det hmul
  simpa [Matrix.det_mul, Matrix.det_transpose, unitFrameDet] using hdet


-- @@ L456-460 verbatim
theorem unitFrameDet_ne_zero : unitFrameDet a ≠ 0 := by
  intro h
  have hself := unitFrameDet_mul_self a
  rw [h, zero_mul] at hself
  norm_num at hself


-- @@ L462-464 verbatim
/-- The fixed sign which converts the counterclockwise tangent into the
orientation selected by the generalized cross product. -/
def orientationSign : ℝ := if 0 < unitFrameDet a then 1 else -1


-- @@ L466-469 verbatim
theorem orientationSign_eq_one_or_neg_one :
    orientationSign a = 1 ∨ orientationSign a = -1 := by
  unfold orientationSign
  split_ifs <;> simp


-- @@ L471-472 verbatim
theorem abs_orientationSign : |orientationSign a| = 1 := by
  rcases orientationSign_eq_one_or_neg_one a with h | h <;> rw [h] <;> norm_num


-- @@ L474-475 verbatim
theorem orientationSign_ne_zero : orientationSign a ≠ 0 := by
  rcases orientationSign_eq_one_or_neg_one a with h | h <;> rw [h] <;> norm_num


-- @@ L477-484 verbatim
theorem orientationSign_mul_unitFrameDet_pos :
    0 < orientationSign a * unitFrameDet a := by
  unfold orientationSign
  split_ifs with hpos
  · simpa using hpos
  · have hneg : unitFrameDet a < 0 :=
      lt_of_le_of_ne (not_lt.mp hpos) (unitFrameDet_ne_zero a)
    simpa using neg_pos.mpr hneg


-- @@ L486-486 verbatim
/-! ## Identification with the actual derivative frame -/


-- @@ L488-493 verbatim
/-- The actual gradient rows: the last radial row has the harmless positive
factor `2`. -/
def scaledNormal (theta : ℝ) :
    Fin (a + 2) → EuclideanSpace ℝ (Fin (a + 3)) :=
  Fin.lastCases ((2 : ℝ) • circlePoint (a + 1) theta)
    (fun j : Fin (a + 1) => EuclideanSpace.single j.castSucc.castSucc 1)


-- @@ L495-498 verbatim
@[simp] theorem scaledNormal_last (theta : ℝ) :
    scaledNormal a theta (Fin.last (a + 1)) =
      (2 : ℝ) • circlePoint (a + 1) theta := by
  simp [scaledNormal]


-- @@ L500-503 verbatim
@[simp] theorem scaledNormal_castSucc (theta : ℝ) (j : Fin (a + 1)) :
    scaledNormal a theta j.castSucc =
      EuclideanSpace.single j.castSucc.castSucc 1 := by
  simp [scaledNormal]


-- @@ L505-509 verbatim
/-- The positively oriented tangent followed by the actual gradient rows. -/
def scaledFrame (theta : ℝ) :
    Fin (a + 3) → EuclideanSpace ℝ (Fin (a + 3)) :=
  Fin.cons (orientationSign a • tangentPoint (a + 1) theta)
    (scaledNormal a theta)


-- @@ L511-513 verbatim
def frameScale (i : Fin (a + 3)) : ℝ :=
  (if i = 0 then orientationSign a else 1) *
    (if i = Fin.last (a + 2) then 2 else 1)


-- @@ L515-539 verbatim
theorem scaledFrame_eq_smul (theta : ℝ) (i : Fin (a + 3)) :
    scaledFrame a theta i =
      frameScale a i • unitFrame (a + 1) theta i := by
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
  · simp [scaledFrame, frameScale, unitFrame, lastA_ne_zero,
      orientationSign_ne_zero]
  · induction i using Fin.lastCases with
    | last =>
        have hs : (Fin.last (a + 1)).succ =
            (Fin.last (a + 2) : Fin (a + 3)) := by
          apply Fin.ext
          simp
        rw [hs]
        simp [scaledFrame, frameScale, unitFrame, scaledNormal,
          normalUnit, lastA_ne_zero]
    | cast i =>
        have hi0 : (i.castSucc.succ : Fin (a + 3)) ≠ 0 :=
          (Fin.succ_ne_zero i.castSucc)
        have hil : (i.castSucc.succ : Fin (a + 3)) ≠ Fin.last (a + 2) := by
          intro h
          have hv := congrArg (fun z : Fin (a + 3) => z.val) h
          simp at hv
          omega
        simp [scaledFrame, frameScale, unitFrame, scaledNormal,
          normalUnit, hi0, hil]


-- @@ L541-552 verbatim
theorem prod_frameScale : ∏ i, frameScale a i = 2 * orientationSign a := by
  classical
  unfold frameScale
  rw [Finset.prod_mul_distrib]
  have hzero : (∏ i : Fin (a + 3),
      if i = 0 then orientationSign a else 1) = orientationSign a := by
    simp
  have hlast : (∏ i : Fin (a + 3),
      if i = Fin.last (a + 2) then (2 : ℝ) else 1) = 2 := by
    simp
  rw [hzero, hlast]
  ring


-- @@ L554-560 verbatim
theorem rowsMatrix_scaledFrame (theta : ℝ) :
    rowsMatrix (scaledFrame a theta) =
      Matrix.of fun i j => frameScale a i *
        rowsMatrix (unitFrame (a + 1) theta) i j := by
  ext i j
  rw [rowsMatrix, Matrix.of_apply, scaledFrame_eq_smul]
  rfl


-- @@ L562-566 verbatim
theorem det_rowsMatrix_scaledFrame (theta : ℝ) :
    (rowsMatrix (scaledFrame a theta)).det =
      2 * orientationSign a * unitFrameDet a := by
  rw [rowsMatrix_scaledFrame, Matrix.det_mul_column,
    prod_frameScale, det_rowsMatrix_unitFrame]


-- @@ L568-571 verbatim
theorem det_rowsMatrix_scaledFrame_pos (theta : ℝ) :
    0 < (rowsMatrix (scaledFrame a theta)).det := by
  rw [det_rowsMatrix_scaledFrame]
  nlinarith [orientationSign_mul_unitFrameDet_pos a]


-- @@ L573-586 verbatim
theorem gradVec_target_circle (theta : ℝ) (i : Fin (a + 2)) :
    gradVec (targetFLS (a + 1)).g i (circlePoint (a + 1) theta) =
      scaledNormal a theta i := by
  change gradVec (circleMap (a + 1) 1) i (circlePoint (a + 1) theta) = _
  induction i using Fin.lastCases with
  | last =>
      rw [gradVec_circleMap_last, scaledNormal_last]
      have hAB : radialFirst (a + 1) ≠ radialSecond (a + 1) := by
        intro h
        have := congrArg Fin.val h
        simp [radialFirst, radialSecond] at this
      simp [circlePoint, hAB, hAB.symm, smul_add, smul_smul]
  | cast i =>
      rw [gradVec_circleMap_castSucc, scaledNormal_castSucc]


-- @@ L588-602 verbatim
theorem fderiv_target_circle_oriented_tangent (theta : ℝ) :
    fderiv ℝ (targetFLS (a + 1)).g (circlePoint (a + 1) theta)
        (orientationSign a • tangentPoint (a + 1) theta) = 0 := by
  apply (WithLp.equiv 2 _).injective
  funext i
  change fderiv ℝ (circleMap (a + 1) 1) (circlePoint (a + 1) theta)
      (orientationSign a • tangentPoint (a + 1) theta) i = 0
  induction i using Fin.lastCases with
  | last =>
      rw [fderiv_circleMap_apply_last]
      simp
      ring
  | cast i =>
      rw [fderiv_circleMap_apply_castSucc]
      simp


-- @@ L604-607 verbatim
theorem norm_oriented_tangent (theta : ℝ) :
    ‖orientationSign a • tangentPoint (a + 1) theta‖ = 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_orientationSign,
    norm_tangentPoint, one_mul]


-- @@ L609-650 verbatim
theorem tauField_target_circle (theta : ℝ) :
    tauField (targetFLS (a + 1)).g (circlePoint (a + 1) theta) =
      orientationSign a • tangentPoint (a + 1) theta := by
  let X := targetFLS (a + 1)
  let x := circlePoint (a + 1) theta
  let q := orientationSign a • tangentPoint (a + 1) theta
  have hxFiber : x ∈ X.fiber := circlePoint_mem_target_fiber (a + 1) theta
  have hreg : x ∈ regularSet X.g := X.fiber_subset_regularSet hxFiber
  have hgrads : (fun i => gradVec X.g i x) = scaledNormal a theta := by
    funext i
    exact gradVec_target_circle a theta i
  have hdetQ : 0 < crossDet (fun i => gradVec X.g i x) q := by
    rw [hgrads]
    have hrows : crossRows (scaledNormal a theta) q =
        rowsMatrix (scaledFrame a theta) := by
      ext i j
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩ <;>
        simp [crossRows, rowsMatrix, scaledFrame, q]
    rw [crossDet, hrows]
    exact det_rowsMatrix_scaledFrame_pos a theta
  have hkernel : fderiv ℝ X.g x q = 0 :=
    fderiv_target_circle_oriented_tangent a theta
  have hmem : q ∈ Submodule.span ℝ {tauField X.g x} :=
    (fderiv_eq_zero_iff_mem_span_tauField hreg _).mp hkernel
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hdetTau : 0 < crossDet (fun i => gradVec X.g i x) (tauField X.g x) :=
    crossDet_tauField_pos hreg
  have hdetEq := congrArg (crossDet (fun i => gradVec X.g i x)) hc
  rw [crossDet_smul] at hdetEq
  have hprod : 0 < c * crossDet (fun i => gradVec X.g i x) (tauField X.g x) := by
    rw [hdetEq]
    exact hdetQ
  have hcPos : 0 < c := by
    rcases mul_pos_iff.mp hprod with hp | hn
    · exact hp.1
    · exact False.elim ((not_lt_of_ge (le_of_lt hdetTau)) hn.2)
  have hnormEq := congrArg norm hc
  rw [norm_smul, norm_tauField hreg, mul_one, norm_oriented_tangent,
    Real.norm_eq_abs, abs_of_pos hcPos] at hnormEq
  have hcOne : c = 1 := hnormEq
  rw [hcOne, one_smul] at hc
  exact hc


-- @@ L652-660 verbatim
theorem frameAt_target_circle (theta : ℝ) :
    frameAt (targetFLS (a + 1)) (circlePoint (a + 1) theta) =
      scaledFrame a theta := by
  funext i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
  · rw [frameAt, Fin.cons_zero, scaledFrame, Fin.cons_zero,
      tauField_target_circle]
  · rw [frameAt, Fin.cons_succ, scaledFrame, Fin.cons_succ,
      gradVec_target_circle]


-- @@ L662-666 verbatim
/-- The actual orthonormal frame, after removing the positive radial factor. -/
def orientedUnitFrame (theta : ℝ) :
    Fin (a + 3) → EuclideanSpace ℝ (Fin (a + 3)) :=
  Fin.cons (orientationSign a • tangentPoint (a + 1) theta)
    (normalUnit (a + 1) theta)


-- @@ L668-700 verbatim
theorem gramSchmidtNormed_scaledFrame (theta : ℝ) :
    gramSchmidtNormed ℝ (scaledFrame a theta) = orientedUnitFrame a theta := by
  have horth : Pairwise
      (fun i j => ⟪scaledFrame a theta i, scaledFrame a theta j⟫_ℝ = 0) := by
    intro i j hij
    rw [scaledFrame_eq_smul, scaledFrame_eq_smul,
      real_inner_smul_left, real_inner_smul_right,
      (orthonormal_unitFrame (a + 1) theta).2 hij, mul_zero, mul_zero]
  funext i
  rw [gramSchmidtNormed, gramSchmidt_of_orthogonal ℝ horth,
    scaledFrame_eq_smul, norm_smul,
    (orthonormal_unitFrame (a + 1) theta).1 i]
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
  · simp [frameScale, orientedUnitFrame, unitFrame, abs_orientationSign,
      orientationSign_ne_zero, smul_smul]
  · induction i using Fin.lastCases with
    | last =>
        have hs : (Fin.last (a + 1)).succ =
            (Fin.last (a + 2) : Fin (a + 3)) := by
          apply Fin.ext
          simp
        rw [hs]
        simp [frameScale, orientedUnitFrame, unitFrame, smul_smul,
          lastA_ne_zero]
    | cast i =>
        have hi0 : (i.castSucc.succ : Fin (a + 3)) ≠ 0 :=
          Fin.succ_ne_zero i.castSucc
        have hil : (i.castSucc.succ : Fin (a + 3)) ≠ Fin.last (a + 2) := by
          intro h
          have hv := congrArg (fun z : Fin (a + 3) => z.val) h
          simp at hv
          omega
        simp [frameScale, orientedUnitFrame, unitFrame, hi0, hil]


-- @@ L702-706 verbatim
theorem gramSchmidtNormed_frameAt_target_circle (theta : ℝ) :
    gramSchmidtNormed ℝ
        (frameAt (targetFLS (a + 1)) (circlePoint (a + 1) theta)) =
      orientedUnitFrame a theta := by
  rw [frameAt_target_circle, gramSchmidtNormed_scaledFrame]


-- @@ L708-720 verbatim
theorem orientedTangent_rotation (theta : ℝ) :
    orientationSign a • tangentPoint (a + 1) theta =
      Real.cos (orientationSign a * theta) •
          (orientationSign a • tangentPoint (a + 1) 0) -
        Real.sin (orientationSign a * theta) • circlePoint (a + 1) 0 := by
  rcases orientationSign_eq_one_or_neg_one a with h | h
  · rw [h]
    simp only [one_mul, one_smul]
    exact tangentPoint_rotation (a + 1) theta
  · rw [h]
    simp only [neg_mul, neg_smul, Real.cos_neg, Real.sin_neg, one_mul]
    rw [tangentPoint_rotation]
    module


-- @@ L722-734 verbatim
theorem circlePoint_signed_rotation (theta : ℝ) :
    circlePoint (a + 1) theta =
      Real.sin (orientationSign a * theta) •
          (orientationSign a • tangentPoint (a + 1) 0) +
        Real.cos (orientationSign a * theta) • circlePoint (a + 1) 0 := by
  rcases orientationSign_eq_one_or_neg_one a with h | h
  · rw [h]
    simp only [one_mul, one_smul]
    exact circlePoint_rotation (a + 1) theta
  · rw [h]
    simp only [neg_mul, neg_smul, Real.cos_neg, Real.sin_neg, one_mul]
    rw [circlePoint_rotation]
    module


-- @@ L736-739 verbatim
theorem orientedUnitFrame_zero (theta : ℝ) :
    orientedUnitFrame a theta 0 =
      orientationSign a • tangentPoint (a + 1) theta := by
  simp [orientedUnitFrame]


-- @@ L741-748 verbatim
theorem orientedUnitFrame_last (theta : ℝ) :
    orientedUnitFrame a theta (Fin.last (a + 2)) =
      circlePoint (a + 1) theta := by
  have hs : (Fin.last (a + 1)).succ =
      (Fin.last (a + 2) : Fin (a + 3)) := by
    apply Fin.ext
    simp
  rw [← hs, orientedUnitFrame, Fin.cons_succ, normalUnit_last]


-- @@ L750-761 verbatim
theorem orientedUnitFrame_middle_eq_zero (theta : ℝ) {i : Fin (a + 3)}
    (hi0 : i ≠ 0) (hil : i ≠ Fin.last (a + 2)) :
    orientedUnitFrame a theta i = orientedUnitFrame a 0 i := by
  obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero hi0
  induction k using Fin.lastCases with
  | last =>
      exfalso
      apply hil
      apply Fin.ext
      simp
  | cast k =>
      simp [orientedUnitFrame, normalUnit]


-- @@ L763-796 verbatim
/-- The oriented frame rotates by `orientationSign * theta` in its first/last
row plane. -/
theorem rowsMatrix_orientedUnitFrame_rotation (theta : ℝ) :
    rowsMatrix (orientedUnitFrame a theta) =
      twistMat a (orientationSign a * theta) *
        rowsMatrix (orientedUnitFrame a 0) := by
  ext i j
  rw [twistMat_mul_apply_birth]
  by_cases hi0 : i = 0
  · subst i
    rw [if_pos rfl]
    simp only [rowsMatrix, Matrix.of_apply, orientedUnitFrame_zero]
    have hlast : orientedUnitFrame a 0 (Fin.last (a + 2)) =
        circlePoint (a + 1) 0 := orientedUnitFrame_last a 0
    rw [hlast]
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin (a + 3)) => v j)
      (orientedTangent_rotation a theta)
    simpa [sub_eq_add_neg] using h
  · rw [if_neg hi0]
    by_cases hil : i = Fin.last (a + 2)
    · subst i
      rw [if_pos rfl]
      simp only [rowsMatrix, Matrix.of_apply, orientedUnitFrame_last]
      have hzero : orientedUnitFrame a 0 0 =
          orientationSign a • tangentPoint (a + 1) 0 :=
        orientedUnitFrame_zero a 0
      rw [hzero]
      have h := congrArg (fun v : EuclideanSpace ℝ (Fin (a + 3)) => v j)
        (circlePoint_signed_rotation a theta)
      simpa using h
    · rw [if_neg hil]
      simp only [rowsMatrix, Matrix.of_apply]
      exact congrArg (fun v : EuclideanSpace ℝ (Fin (a + 3)) => v j)
        (orientedUnitFrame_middle_eq_zero a theta hi0 hil)


-- @@ L798-798 verbatim
/-! ## Stable class of the signed row-plane rotation -/


-- @@ L800-802 verbatim
def birthFrameAngle : C(I, ℝ) where
  toFun u := orientationSign a * (2 * Real.pi * (u : ℝ))
  continuous_toFun := by fun_prop


-- @@ L804-805 verbatim
def birthFrameWinding : ℤ :=
  if orientationSign a = 1 then 1 else -1


-- @@ L807-815 verbatim
theorem birthFrameAngle_closed :
    birthFrameAngle a 1 = birthFrameAngle a 0 +
      2 * Real.pi * birthFrameWinding a := by
  rcases orientationSign_eq_one_or_neg_one a with h | h
  · rw [birthFrameWinding, if_pos h]
    simp [birthFrameAngle, h]
  · have hne : orientationSign a ≠ 1 := by rw [h]; norm_num
    rw [birthFrameWinding, if_neg hne]
    simp [birthFrameAngle, h]


-- @@ L817-820 verbatim
def birthSO2AngleLoop : SO2AngleLoop where
  angle := birthFrameAngle a
  winding := birthFrameWinding a
  angle_closed := birthFrameAngle_closed a


-- @@ L822-826 verbatim
theorem birthFrameWinding_mod_two :
    (birthFrameWinding a : ZMod 2) = 1 := by
  rcases orientationSign_eq_one_or_neg_one a with h | h
  · simp [birthFrameWinding, h]
  · simp [birthFrameWinding, h]


-- @@ L828-832 verbatim
/-- Move the signed standard first-plane rotation to the first/last row plane. -/
def birthPlaneLoop : C(I, SOGroup (a + 3)) :=
  (ContinuousMap.const I (swapRotSO a) *
      (birthSO2AngleLoop a).frame (a + 3)) *
    ContinuousMap.const I (swapRotSO a)⁻¹


-- @@ L834-836 verbatim
theorem birthPlaneLoop_closed : birthPlaneLoop a 0 = birthPlaneLoop a 1 := by
  simp only [birthPlaneLoop, ContinuousMap.mul_apply, ContinuousMap.const_apply]
  rw [(birthSO2AngleLoop a).frame_closed]


-- @@ L838-844 verbatim
theorem birthPlaneLoop_coe (u : I) :
    (birthPlaneLoop a u : Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) =
      twistMat a (birthFrameAngle a u) := by
  change swapRotMat a * rotBlock (a + 3) (birthFrameAngle a u) *
      (swapRotMat a)ᵀ = _
  rw [rotBlock_eq_rotAmbient]
  rfl


-- @@ L846-863 verbatim
theorem loopClassZ2_birthPlaneLoop :
    loopClassZ2 (birthPlaneLoop a) (birthPlaneLoop_closed a) = 1 := by
  have hr : 3 ≤ a + 3 := by omega
  have hbase :
      loopClassZ2 ((birthSO2AngleLoop a).frame (a + 3))
          ((birthSO2AngleLoop a).frame_closed (a + 3)) = 1 := by
    rw [(birthSO2AngleLoop a).loopClassZ2_frame hr]
    change (birthFrameWinding a : ZMod 2) = 1
    exact birthFrameWinding_mod_two a
  have hconj := loopClassZ2_const_conj (swapRotSO a)
    ((birthSO2AngleLoop a).frame (a + 3))
    ((birthSO2AngleLoop a).frame_closed (a + 3))
  have hplane :
      loopClassZ2 (birthPlaneLoop a) (birthPlaneLoop_closed a) =
        loopClassZ2 ((birthSO2AngleLoop a).frame (a + 3))
          ((birthSO2AngleLoop a).frame_closed (a + 3)) := by
    simpa only [birthPlaneLoop] using hconj
  exact hplane.trans hbase


-- @@ L865-865 verbatim
/-! ## The literal parameter loop is the signed plane rotation -/


-- @@ L867-878 verbatim
theorem paramFrameLoop_apply (V : TamedField (targetFLS (a + 1))) (u : I) :
    ((simpleClosedOrbitParam (a + 1) V).paramFrameLoop u :
        Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) =
      rowsMatrix (orientedUnitFrame a (2 * Real.pi * (u : ℝ))) := by
  change frameLoop (targetFLS (a + 1))
      (simpleClosedOrbitParam (a + 1) V).realCurve (u : ℝ) = _
  unfold frameLoop
  rw [(simpleClosedOrbitParam (a + 1) V).realCurve_coe]
  change rowsMatrix (gramSchmidtNormed ℝ
      (frameAt (targetFLS (a + 1))
        (circlePoint (a + 1) (2 * Real.pi * (u : ℝ))))) = _
  rw [gramSchmidtNormed_frameAt_target_circle]


-- @@ L880-896 verbatim
theorem paramFrameLoop_eq_plane_mul_const
    (V : TamedField (targetFLS (a + 1))) :
    (simpleClosedOrbitParam (a + 1) V).paramFrameLoop =
      birthPlaneLoop a * ContinuousMap.const I
        ((simpleClosedOrbitParam (a + 1) V).paramFrameLoop 0) := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  rw [paramFrameLoop_apply]
  change rowsMatrix (orientedUnitFrame a (2 * Real.pi * (u : ℝ))) =
    (birthPlaneLoop a u : Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ) *
      ((simpleClosedOrbitParam (a + 1) V).paramFrameLoop 0 :
        Matrix (Fin (a + 3)) (Fin (a + 3)) ℝ)
  rw [birthPlaneLoop_coe, paramFrameLoop_apply]
  simp only [Set.Icc.coe_zero, mul_zero]
  rw [rowsMatrix_orientedUnitFrame_rotation]
  congr 2


-- @@ L898-916 verbatim
theorem unitCircle_paramFrameClass (V : TamedField (targetFLS (a + 1))) :
    loopClassZ2 (simpleClosedOrbitParam (a + 1) V).paramFrameLoop
        (simpleClosedOrbitParam (a + 1) V).paramFrameLoop_closed = 1 := by
  let P := simpleClosedOrbitParam (a + 1) V
  let R := birthPlaneLoop a * ContinuousMap.const I (P.paramFrameLoop 0)
  have hRclosed : R 0 = R 1 := by
    change birthPlaneLoop a 0 * P.paramFrameLoop 0 =
      birthPlaneLoop a 1 * P.paramFrameLoop 0
    rw [birthPlaneLoop_closed]
  have heq : P.paramFrameLoop = R :=
    paramFrameLoop_eq_plane_mul_const a V
  calc
    loopClassZ2 P.paramFrameLoop P.paramFrameLoop_closed =
        loopClassZ2 R hRclosed :=
      loopClassZ2_congr_fun P.paramFrameLoop_closed hRclosed heq
    _ = loopClassZ2 (birthPlaneLoop a) (birthPlaneLoop_closed a) := by
      exact loopClassZ2_mul_const_right (birthPlaneLoop a)
        (birthPlaneLoop_closed a) (P.paramFrameLoop 0)
    _ = 1 := loopClassZ2_birthPlaneLoop a


-- @@ L918-923 verbatim
/-- The literal positive definite birth has vanishing signed delta. -/
theorem targetSign_positiveDelta_eq_zero
    (V : TamedField (targetFLS (a + 1))) :
    (targetSign (a + 1)).positiveDelta = 0 :=
  targetSign_positiveDelta_eq_zero_of_paramFrameClass (a + 1) V
    (unitCircle_paramFrameClass a V)


-- @@ L925-930 verbatim
theorem source_target_positiveDelta_eq
    (V : TamedField (targetFLS (a + 1))) :
    (sourceSign (a + 1)).positiveDelta =
      (targetSign (a + 1)).positiveDelta :=
  source_target_positiveDelta_eq_of_paramFrameClass (a + 1) V
    (unitCircle_paramFrameClass a V)


-- @@ L932-938 verbatim
/-- Dimension-independent wrapper for every positive codimension. -/
theorem unitCircle_paramFrameClass_of_pos {m : ℕ} (hm : 0 < m)
    (V : TamedField (targetFLS m)) :
    loopClassZ2 (simpleClosedOrbitParam m V).paramFrameLoop
        (simpleClosedOrbitParam m V).paramFrameLoop_closed = 1 := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  exact unitCircle_paramFrameClass a V


-- @@ L940-944 verbatim
theorem targetSign_positiveDelta_eq_zero_of_pos {m : ℕ} (hm : 0 < m)
    (V : TamedField (targetFLS m)) :
    (targetSign m).positiveDelta = 0 := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  exact targetSign_positiveDelta_eq_zero a V


-- @@ L946-950 verbatim
theorem source_target_positiveDelta_eq_of_pos {m : ℕ} (hm : 0 < m)
    (V : TamedField (targetFLS m)) :
    (sourceSign m).positiveDelta = (targetSign m).positiveDelta := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  exact source_target_positiveDelta_eq a V


-- @@ L952-952 verbatim
end StandardBirth

-- @@ L953-953 verbatim
end Submission
