import Submission.ConcreteZeroPairCassiniCoefficientSO


-- @@ L3-9 verbatim
/-!
# Intrinsic-frame adapter for the Cassini coefficient

This file transports the two-row Cassini coefficient from the output
differential to the intrinsic tangent-normal frame.  The tangent row is fixed;
the first two normal rows carry the complex coefficient.
-/


-- @@ L11-11 verbatim
set_option autoImplicit false

-- @@ L12-12 verbatim
set_option maxHeartbeats 1600000


-- @@ L14-14 verbatim
noncomputable section


-- @@ L16-16 verbatim
namespace Submission

-- @@ L17-17 verbatim
namespace ConcreteZeroPairCassiniFrameAdapter


-- @@ L19-19 verbatim
open Set Function Matrix InnerProductSpace

-- @@ L20-20 verbatim
open scoped Topology Matrix RealInnerProductSpace unitInterval


-- @@ L22-22 verbatim
open ConcreteZeroPairCassiniTwist

-- @@ L23-23 verbatim
open ConcreteZeroPairCassiniWinding

-- @@ L24-24 verbatim
open ConcreteZeroPairCassiniCoefficientSO


-- @@ L26-26 verbatim
/-! ## The coefficient block on normal rows -/


-- @@ L28-32 verbatim
/-- The normal-row block `diag([[a,-b],[b,a]],1,...,1)`. -/
def normalCoefficientBlock : (k : ℕ) → ℝ → ℝ →
    Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ
  | 0, a, b => !![a, -b; b, a]
  | k + 1, a, b => incMatrix (normalCoefficientBlock k a b)


-- @@ L34-44 verbatim
theorem normalCoefficientBlock_det : ∀ k a b,
    (normalCoefficientBlock k a b).det = a ^ 2 + b ^ 2
  | 0, a, b => by
      rw [normalCoefficientBlock, Matrix.det_fin_two]
      simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.head_fin_const, Matrix.of_apply,
        Matrix.vecHead, Matrix.vecTail, Function.comp_apply]
      ring
  | k + 1, a, b => by
      rw [normalCoefficientBlock, incMatrix_det,
        normalCoefficientBlock_det k a b]


-- @@ L46-86 verbatim
theorem incMatrix_tangentNormalBlock {n : ℕ} (a : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    incMatrix (tangentNormalBlock a A) =
      tangentNormalBlock a (incMatrix A) := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
      induction j using Fin.lastCases with
      | last =>
          rw [incMatrix_apply_last_last]
          change 1 = incMatrix A (Fin.last n) (Fin.last n)
          rw [incMatrix_apply_last_last]
      | cast j =>
          rw [incMatrix_apply_last_castSucc]
          rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
          · change 0 = 0
            rfl
          · change 0 = incMatrix A (Fin.last n) (Fin.castSucc j)
            rw [incMatrix_apply_last_castSucc]
  | cast i =>
      induction j using Fin.lastCases with
      | last =>
          rw [incMatrix_apply_castSucc_last]
          rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
          · change 0 = 0
            rfl
          · change 0 = incMatrix A (Fin.castSucc i) (Fin.last n)
            rw [incMatrix_apply_castSucc_last]
      | cast j =>
          rw [incMatrix_apply_castSucc_castSucc]
          rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
          · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
            · change a = a
              rfl
            · change 0 = 0
              rfl
          · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
            · change 0 = 0
              rfl
            · change A i j = incMatrix A (Fin.castSucc i) (Fin.castSucc j)
              rw [incMatrix_apply_castSucc_castSucc]


-- @@ L88-97 verbatim
theorem fullCoefficientBlock_eq_tangentNormalBlock : ∀ k a b,
    fullCoefficientBlock k a b =
      tangentNormalBlock 1 (normalCoefficientBlock k a b)
  | 0, a, b => by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
  | k + 1, a, b => by
      rw [fullCoefficientBlock, normalCoefficientBlock,
        fullCoefficientBlock_eq_tangentNormalBlock k a b,
        incMatrix_tangentNormalBlock]


-- @@ L99-99 verbatim
/-! A dimension-independent row action, used to induct through `incMatrix`. -/


-- @@ L101-103 verbatim
def rowAction {n : ℕ} {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → V) : Fin n → V :=
  fun i => ∑ j, A i j • v j


-- @@ L105-114 verbatim
theorem rowAction_incMatrix_castSucc {n : ℕ} {V : Type*}
    [AddCommMonoid V] [Module ℝ V]
    (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin (n + 1) → V) (i : Fin n) :
    rowAction (incMatrix A) v i.castSucc =
      rowAction A (fun j => v j.castSucc) i := by
  classical
  unfold rowAction
  rw [Fin.sum_univ_castSucc]
  simp [incMatrix_apply_castSucc_castSucc,
    incMatrix_apply_castSucc_last]


-- @@ L116-123 verbatim
theorem rowAction_incMatrix_last {n : ℕ} {V : Type*}
    [AddCommMonoid V] [Module ℝ V]
    (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin (n + 1) → V) :
    rowAction (incMatrix A) v (Fin.last n) = v (Fin.last n) := by
  classical
  unfold rowAction
  rw [Fin.sum_univ_castSucc]
  simp [incMatrix_apply_last_castSucc, incMatrix_apply_last_last]


-- @@ L125-138 verbatim
theorem rowAction_normalCoefficientBlock_zero {V : Type*}
    [AddCommGroup V] [Module ℝ V] : ∀ (k : ℕ) (a b : ℝ)
      (v : Fin (k + 2) → V),
    rowAction (normalCoefficientBlock k a b) v 0 =
      a • v 0 - b • v 1
  | 0, a, b, v => by
      simp [rowAction, normalCoefficientBlock, Fin.sum_univ_two,
        sub_eq_add_neg]
  | k + 1, a, b, v => by
      rw [normalCoefficientBlock,
        show (0 : Fin (k + 3)) = (0 : Fin (k + 2)).castSucc by rfl,
        rowAction_incMatrix_castSucc]
      simpa using rowAction_normalCoefficientBlock_zero k a b
        (fun j => v j.castSucc)


-- @@ L140-152 verbatim
theorem rowAction_normalCoefficientBlock_one {V : Type*}
    [AddCommGroup V] [Module ℝ V] : ∀ (k : ℕ) (a b : ℝ)
      (v : Fin (k + 2) → V),
    rowAction (normalCoefficientBlock k a b) v 1 =
      b • v 0 + a • v 1
  | 0, a, b, v => by
      simp [rowAction, normalCoefficientBlock, Fin.sum_univ_two]
  | k + 1, a, b, v => by
      rw [normalCoefficientBlock,
        show (1 : Fin (k + 3)) = (1 : Fin (k + 2)).castSucc by rfl,
        rowAction_incMatrix_castSucc]
      simpa using rowAction_normalCoefficientBlock_one k a b
        (fun j => v j.castSucc)


-- @@ L154-178 verbatim
theorem rowAction_normalCoefficientBlock_of_ne {V : Type*}
    [AddCommGroup V] [Module ℝ V] : ∀ (k : ℕ) (a b : ℝ)
      (v : Fin (k + 2) → V) (i : Fin (k + 2)),
    i ≠ 0 → i ≠ 1 →
      rowAction (normalCoefficientBlock k a b) v i = v i
  | 0, a, b, v, i, hi0, hi1 => by
      fin_cases i <;> contradiction
  | k + 1, a, b, v, i, hi0, hi1 => by
      rw [normalCoefficientBlock]
      induction i using Fin.lastCases with
      | last => exact rowAction_incMatrix_last _ _
      | cast i =>
          rw [rowAction_incMatrix_castSucc]
          exact rowAction_normalCoefficientBlock_of_ne k a b
            (fun j => v j.castSucc) i
            (by
              intro h
              apply hi0
              apply Fin.ext
              exact congrArg (fun z : Fin (k + 2) => z.val) h)
            (by
              intro h
              apply hi1
              apply Fin.ext
              exact congrArg (fun z : Fin (k + 2) => z.val) h)


-- @@ L180-183 verbatim
theorem rowAction_eq_normalRowAction {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → EuclideanSpace ℝ (Fin (n + 1))) :
    rowAction A v = normalRowAction A v := rfl


-- @@ L185-185 verbatim
/-! ## Fixed-time derivatives -/


-- @@ L187-187 verbatim
variable (m : ℕ)


-- @@ L189-189 verbatim
local notation "A" => EuclideanSpace ℝ (Fin (m + 4))

-- @@ L190-190 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 3))

-- @@ L191-191 verbatim
local notation "F" => EuclideanSpace ℝ (Fin (m + 2))


-- @@ L193-200 verbatim
theorem hasFDerivAt_spaceTime_fixed (x : E) (t : ℝ) :
    HasFDerivAt (fun y : E => spaceTime y t) (embedCLM (m + 3)) x := by
  have heq : (fun y : E => spaceTime y t) =
      fun y => embedCLM (m + 3) y + t • eLast (m + 3) := by
    funext y
    exact spaceTime_eq_affine y t
  rw [heq]
  exact (embedCLM (m + 3)).hasFDerivAt.add_const _


-- @@ L202-213 verbatim
theorem fderiv_sourceLevelMap_eq_event (x : E) :
    fderiv ℝ (sourceLevelMap m) x =
      (fderiv ℝ (ConcreteZeroPairCassiniTwist.eventMap m)
        (spaceTime x 0)).comp (embedCLM (m + 3)) := by
  have hG : HasFDerivAt (ConcreteZeroPairCassiniTwist.eventMap m)
      (fderiv ℝ (ConcreteZeroPairCassiniTwist.eventMap m)
        (spaceTime x 0)) (spaceTime x 0) :=
    ((ConcreteZeroPairCassiniTwist.contDiff_eventMap m).differentiable
      infty_ne_zero _).hasFDerivAt
  change fderiv ℝ (fun y : E =>
    ConcreteZeroPairCassiniTwist.eventMap m (spaceTime y 0)) x = _
  exact (hG.comp x (hasFDerivAt_spaceTime_fixed m x 0)).fderiv


-- @@ L215-226 verbatim
theorem fderiv_targetLevelMap_eq_event (x : E) :
    fderiv ℝ (targetLevelMap m) x =
      (fderiv ℝ (ConcreteZeroPairCassiniTwist.eventMap m)
        (spaceTime x 1)).comp (embedCLM (m + 3)) := by
  have hG : HasFDerivAt (ConcreteZeroPairCassiniTwist.eventMap m)
      (fderiv ℝ (ConcreteZeroPairCassiniTwist.eventMap m)
        (spaceTime x 1)) (spaceTime x 1) :=
    ((ConcreteZeroPairCassiniTwist.contDiff_eventMap m).differentiable
      infty_ne_zero _).hasFDerivAt
  change fderiv ℝ (fun y : E =>
    ConcreteZeroPairCassiniTwist.eventMap m (spaceTime y 1)) x = _
  exact (hG.comp x (hasFDerivAt_spaceTime_fixed m x 1)).fderiv


-- @@ L228-242 verbatim
theorem fderiv_standard_source_eq_event (x : E) :
    fderiv ℝ (StandardSaddle.levelMap m (-1 / 2)) x =
      (fderiv ℝ (StandardSaddle.eventMap m)
        (spaceTime x 0)).comp (embedCLM (m + 3)) := by
  have hfun : (fun y : E => StandardSaddle.eventMap m (spaceTime y 0)) =
      StandardSaddle.levelMap m (-1 / 2) := by
    funext y
    exact StandardSaddle.eventMap_collar_zero m y (by norm_num)
  have hG : HasFDerivAt (StandardSaddle.eventMap m)
      (fderiv ℝ (StandardSaddle.eventMap m) (spaceTime x 0))
      (spaceTime x 0) :=
    ((StandardSaddle.contDiff_eventMap m).differentiable
      infty_ne_zero _).hasFDerivAt
  rw [← hfun]
  exact (hG.comp x (hasFDerivAt_spaceTime_fixed m x 0)).fderiv


-- @@ L244-258 verbatim
theorem fderiv_standard_target_eq_event (x : E) :
    fderiv ℝ (StandardSaddle.levelMap m (1 / 2)) x =
      (fderiv ℝ (StandardSaddle.eventMap m)
        (spaceTime x 1)).comp (embedCLM (m + 3)) := by
  have hfun : (fun y : E => StandardSaddle.eventMap m (spaceTime y 1)) =
      StandardSaddle.levelMap m (1 / 2) := by
    funext y
    exact StandardSaddle.eventMap_collar_one m y (by norm_num)
  have hG : HasFDerivAt (StandardSaddle.eventMap m)
      (fderiv ℝ (StandardSaddle.eventMap m) (spaceTime x 1))
      (spaceTime x 1) :=
    ((StandardSaddle.contDiff_eventMap m).differentiable
      infty_ne_zero _).hasFDerivAt
  rw [← hfun]
  exact (hG.comp x (hasFDerivAt_spaceTime_fixed m x 1)).fderiv


-- @@ L260-267 verbatim
theorem twistShift_eq_zero_of_standard_zero {v : A}
    (hv : StandardSaddle.eventMap m v = 0) :
    twistShift m v = 0 := by
  have h0 := congrArg (fun q : F => q (rowZero m)) hv
  have h1 := congrArg (fun q : F => q (rowOne m)) hv
  unfold twistShift transverseSq
  rw [h0, h1]
  norm_num


-- @@ L269-291 verbatim
theorem fderiv_sourceLevelMap_apply_rowZero
    {x : E} (hx : StandardSaddle.levelMap m (-1 / 2) x = 0)
    (h : E) :
    fderiv ℝ (sourceLevelMap m) x h (rowZero m) =
      twistRe m (spaceTime x 0) *
          fderiv ℝ (StandardSaddle.levelMap m (-1 / 2)) x h (rowZero m) -
        twistIm m (spaceTime x 0) *
          fderiv ℝ (StandardSaddle.levelMap m (-1 / 2)) x h (rowOne m) := by
  let v : A := spaceTime x 0
  have hv : StandardSaddle.eventMap m v = 0 := by
    exact (StandardSaddle.eventMap_collar_zero m x (by norm_num)).trans hx
  have hs := congrArg
    (fun L : E →L[ℝ] F => L h (rowZero m))
    (fderiv_sourceLevelMap_eq_event m x)
  have h0 := congrArg
    (fun L : E →L[ℝ] F => L h (rowZero m))
    (fderiv_standard_source_eq_event m x)
  have h1 := congrArg
    (fun L : E →L[ℝ] F => L h (rowOne m))
    (fderiv_standard_source_eq_event m x)
  simp only [ContinuousLinearMap.comp_apply] at hs h0 h1
  rw [hs, fderiv_eventMap_apply_rowZero_of_standard_zero m hv,
    twistShift_eq_zero_of_standard_zero m hv, add_zero, ← h0, ← h1]


-- @@ L293-315 verbatim
theorem fderiv_sourceLevelMap_apply_rowOne
    {x : E} (hx : StandardSaddle.levelMap m (-1 / 2) x = 0)
    (h : E) :
    fderiv ℝ (sourceLevelMap m) x h (rowOne m) =
      twistIm m (spaceTime x 0) *
          fderiv ℝ (StandardSaddle.levelMap m (-1 / 2)) x h (rowZero m) +
        twistRe m (spaceTime x 0) *
          fderiv ℝ (StandardSaddle.levelMap m (-1 / 2)) x h (rowOne m) := by
  let v : A := spaceTime x 0
  have hv : StandardSaddle.eventMap m v = 0 := by
    exact (StandardSaddle.eventMap_collar_zero m x (by norm_num)).trans hx
  have hs := congrArg
    (fun L : E →L[ℝ] F => L h (rowOne m))
    (fderiv_sourceLevelMap_eq_event m x)
  have h0 := congrArg
    (fun L : E →L[ℝ] F => L h (rowZero m))
    (fderiv_standard_source_eq_event m x)
  have h1 := congrArg
    (fun L : E →L[ℝ] F => L h (rowOne m))
    (fderiv_standard_source_eq_event m x)
  simp only [ContinuousLinearMap.comp_apply] at hs h0 h1
  rw [hs, fderiv_eventMap_apply_rowOne_of_standard_zero m hv,
    twistShift_eq_zero_of_standard_zero m hv, add_zero, ← h0, ← h1]


-- @@ L317-326 verbatim
theorem fderiv_sourceLevelMap_apply_of_ne {i : Fin (m + 2)}
    (hi0 : i ≠ rowZero m) (hi1 : i ≠ rowOne m) (x h : E) :
    fderiv ℝ (sourceLevelMap m) x h i =
      fderiv ℝ (StandardSaddle.levelMap m (-1 / 2)) x h i := by
  have hs := congrArg (fun L : E →L[ℝ] F => L h i)
    (fderiv_sourceLevelMap_eq_event m x)
  have hstd := congrArg (fun L : E →L[ℝ] F => L h i)
    (fderiv_standard_source_eq_event m x)
  simp only [ContinuousLinearMap.comp_apply] at hs hstd
  rw [hs, fderiv_eventMap_apply_of_ne m hi0 hi1, ← hstd]


-- @@ L328-350 verbatim
theorem fderiv_targetLevelMap_apply_rowZero
    {x : E} (hx : StandardSaddle.levelMap m (1 / 2) x = 0)
    (h : E) :
    fderiv ℝ (targetLevelMap m) x h (rowZero m) =
      twistRe m (spaceTime x 1) *
          fderiv ℝ (StandardSaddle.levelMap m (1 / 2)) x h (rowZero m) -
        twistIm m (spaceTime x 1) *
          fderiv ℝ (StandardSaddle.levelMap m (1 / 2)) x h (rowOne m) := by
  let v : A := spaceTime x 1
  have hv : StandardSaddle.eventMap m v = 0 := by
    exact (StandardSaddle.eventMap_collar_one m x (by norm_num)).trans hx
  have hs := congrArg
    (fun L : E →L[ℝ] F => L h (rowZero m))
    (fderiv_targetLevelMap_eq_event m x)
  have h0 := congrArg
    (fun L : E →L[ℝ] F => L h (rowZero m))
    (fderiv_standard_target_eq_event m x)
  have h1 := congrArg
    (fun L : E →L[ℝ] F => L h (rowOne m))
    (fderiv_standard_target_eq_event m x)
  simp only [ContinuousLinearMap.comp_apply] at hs h0 h1
  rw [hs, fderiv_eventMap_apply_rowZero_of_standard_zero m hv,
    twistShift_eq_zero_of_standard_zero m hv, add_zero, ← h0, ← h1]


-- @@ L352-374 verbatim
theorem fderiv_targetLevelMap_apply_rowOne
    {x : E} (hx : StandardSaddle.levelMap m (1 / 2) x = 0)
    (h : E) :
    fderiv ℝ (targetLevelMap m) x h (rowOne m) =
      twistIm m (spaceTime x 1) *
          fderiv ℝ (StandardSaddle.levelMap m (1 / 2)) x h (rowZero m) +
        twistRe m (spaceTime x 1) *
          fderiv ℝ (StandardSaddle.levelMap m (1 / 2)) x h (rowOne m) := by
  let v : A := spaceTime x 1
  have hv : StandardSaddle.eventMap m v = 0 := by
    exact (StandardSaddle.eventMap_collar_one m x (by norm_num)).trans hx
  have hs := congrArg
    (fun L : E →L[ℝ] F => L h (rowOne m))
    (fderiv_targetLevelMap_eq_event m x)
  have h0 := congrArg
    (fun L : E →L[ℝ] F => L h (rowZero m))
    (fderiv_standard_target_eq_event m x)
  have h1 := congrArg
    (fun L : E →L[ℝ] F => L h (rowOne m))
    (fderiv_standard_target_eq_event m x)
  simp only [ContinuousLinearMap.comp_apply] at hs h0 h1
  rw [hs, fderiv_eventMap_apply_rowOne_of_standard_zero m hv,
    twistShift_eq_zero_of_standard_zero m hv, add_zero, ← h0, ← h1]


-- @@ L376-385 verbatim
theorem fderiv_targetLevelMap_apply_of_ne {i : Fin (m + 2)}
    (hi0 : i ≠ rowZero m) (hi1 : i ≠ rowOne m) (x h : E) :
    fderiv ℝ (targetLevelMap m) x h i =
      fderiv ℝ (StandardSaddle.levelMap m (1 / 2)) x h i := by
  have hs := congrArg (fun L : E →L[ℝ] F => L h i)
    (fderiv_targetLevelMap_eq_event m x)
  have hstd := congrArg (fun L : E →L[ℝ] F => L h i)
    (fderiv_standard_target_eq_event m x)
  simp only [ContinuousLinearMap.comp_apply] at hs hstd
  rw [hs, fderiv_eventMap_apply_of_ne m hi0 hi1, ← hstd]


-- @@ L387-387 verbatim
/-! ## Gradient and intrinsic tangent transport -/


-- @@ L389-401 verbatim
theorem gradVec_source_rowZero
    {x : E} (hx : StandardSaddle.levelMap m (-1 / 2) x = 0) :
    gradVec (sourceLevelMap m) (rowZero m) x =
      twistRe m (spaceTime x 0) •
          gradVec (StandardSaddle.levelMap m (-1 / 2)) (rowZero m) x -
        twistIm m (spaceTime x 0) •
          gradVec (StandardSaddle.levelMap m (-1 / 2)) (rowOne m) x := by
  apply InnerProductSpace.ext_inner_right_basis
    (EuclideanSpace.basisFun (Fin (m + 3)) ℝ).toBasis
  intro h
  rw [inner_gradVec, fderiv_sourceLevelMap_apply_rowZero m hx,
    inner_sub_left, real_inner_smul_left, real_inner_smul_left,
    inner_gradVec, inner_gradVec]


-- @@ L403-415 verbatim
theorem gradVec_source_rowOne
    {x : E} (hx : StandardSaddle.levelMap m (-1 / 2) x = 0) :
    gradVec (sourceLevelMap m) (rowOne m) x =
      twistIm m (spaceTime x 0) •
          gradVec (StandardSaddle.levelMap m (-1 / 2)) (rowZero m) x +
        twistRe m (spaceTime x 0) •
          gradVec (StandardSaddle.levelMap m (-1 / 2)) (rowOne m) x := by
  apply InnerProductSpace.ext_inner_right_basis
    (EuclideanSpace.basisFun (Fin (m + 3)) ℝ).toBasis
  intro h
  rw [inner_gradVec, fderiv_sourceLevelMap_apply_rowOne m hx,
    inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_gradVec, inner_gradVec]


-- @@ L417-425 verbatim
theorem gradVec_source_of_ne {i : Fin (m + 2)}
    (hi0 : i ≠ rowZero m) (hi1 : i ≠ rowOne m) (x : E) :
    gradVec (sourceLevelMap m) i x =
      gradVec (StandardSaddle.levelMap m (-1 / 2)) i x := by
  apply InnerProductSpace.ext_inner_right_basis
    (EuclideanSpace.basisFun (Fin (m + 3)) ℝ).toBasis
  intro h
  rw [inner_gradVec, fderiv_sourceLevelMap_apply_of_ne m hi0 hi1,
    inner_gradVec]


-- @@ L427-439 verbatim
theorem gradVec_target_rowZero
    {x : E} (hx : StandardSaddle.levelMap m (1 / 2) x = 0) :
    gradVec (targetLevelMap m) (rowZero m) x =
      twistRe m (spaceTime x 1) •
          gradVec (StandardSaddle.levelMap m (1 / 2)) (rowZero m) x -
        twistIm m (spaceTime x 1) •
          gradVec (StandardSaddle.levelMap m (1 / 2)) (rowOne m) x := by
  apply InnerProductSpace.ext_inner_right_basis
    (EuclideanSpace.basisFun (Fin (m + 3)) ℝ).toBasis
  intro h
  rw [inner_gradVec, fderiv_targetLevelMap_apply_rowZero m hx,
    inner_sub_left, real_inner_smul_left, real_inner_smul_left,
    inner_gradVec, inner_gradVec]


-- @@ L441-453 verbatim
theorem gradVec_target_rowOne
    {x : E} (hx : StandardSaddle.levelMap m (1 / 2) x = 0) :
    gradVec (targetLevelMap m) (rowOne m) x =
      twistIm m (spaceTime x 1) •
          gradVec (StandardSaddle.levelMap m (1 / 2)) (rowZero m) x +
        twistRe m (spaceTime x 1) •
          gradVec (StandardSaddle.levelMap m (1 / 2)) (rowOne m) x := by
  apply InnerProductSpace.ext_inner_right_basis
    (EuclideanSpace.basisFun (Fin (m + 3)) ℝ).toBasis
  intro h
  rw [inner_gradVec, fderiv_targetLevelMap_apply_rowOne m hx,
    inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_gradVec, inner_gradVec]


-- @@ L455-463 verbatim
theorem gradVec_target_of_ne {i : Fin (m + 2)}
    (hi0 : i ≠ rowZero m) (hi1 : i ≠ rowOne m) (x : E) :
    gradVec (targetLevelMap m) i x =
      gradVec (StandardSaddle.levelMap m (1 / 2)) i x := by
  apply InnerProductSpace.ext_inner_right_basis
    (EuclideanSpace.basisFun (Fin (m + 3)) ℝ).toBasis
  intro h
  rw [inner_gradVec, fderiv_targetLevelMap_apply_of_ne m hi0 hi1,
    inner_gradVec]


-- @@ L465-484 verbatim
theorem source_gradients_eq_rowAction
    {x : E} (hx : StandardSaddle.levelMap m (-1 / 2) x = 0) :
    (fun i => gradVec (sourceLevelMap m) i x) =
      rowAction (normalCoefficientBlock m
          (twistRe m (spaceTime x 0)) (twistIm m (spaceTime x 0)))
        (fun i => gradVec (StandardSaddle.levelMap m (-1 / 2)) i x) := by
  funext i
  by_cases hi0 : i = rowZero m
  · subst i
    simp only [rowZero, rowOne]
    rw [rowAction_normalCoefficientBlock_zero]
    simpa only [rowZero, rowOne] using gradVec_source_rowZero m hx
  · by_cases hi1 : i = rowOne m
    · subst i
      simp only [rowZero, rowOne]
      rw [rowAction_normalCoefficientBlock_one]
      simpa only [rowZero, rowOne] using gradVec_source_rowOne m hx
    · rw [rowAction_normalCoefficientBlock_of_ne m _ _ _ i
          (by simpa [rowZero] using hi0) (by simpa [rowOne] using hi1)]
      exact gradVec_source_of_ne m hi0 hi1 x


-- @@ L486-505 verbatim
theorem target_gradients_eq_rowAction
    {x : E} (hx : StandardSaddle.levelMap m (1 / 2) x = 0) :
    (fun i => gradVec (targetLevelMap m) i x) =
      rowAction (normalCoefficientBlock m
          (twistRe m (spaceTime x 1)) (twistIm m (spaceTime x 1)))
        (fun i => gradVec (StandardSaddle.levelMap m (1 / 2)) i x) := by
  funext i
  by_cases hi0 : i = rowZero m
  · subst i
    simp only [rowZero, rowOne]
    rw [rowAction_normalCoefficientBlock_zero]
    simpa only [rowZero, rowOne] using gradVec_target_rowZero m hx
  · by_cases hi1 : i = rowOne m
    · subst i
      simp only [rowZero, rowOne]
      rw [rowAction_normalCoefficientBlock_one]
      simpa only [rowZero, rowOne] using gradVec_target_rowOne m hx
    · rw [rowAction_normalCoefficientBlock_of_ne m _ _ _ i
          (by simpa [rowZero] using hi0) (by simpa [rowOne] using hi1)]
      exact gradVec_target_of_ne m hi0 hi1 x


-- @@ L507-516 verbatim
theorem kerCross_source_eq_smul
    {x : E} (hx : StandardSaddle.levelMap m (-1 / 2) x = 0) :
    kerCross (sourceLevelMap m) x =
      (twistRe m (spaceTime x 0) ^ 2 +
        twistIm m (spaceTime x 0) ^ 2) •
          kerCross (StandardSaddle.levelMap m (-1 / 2)) x := by
  unfold kerCross
  rw [source_gradients_eq_rowAction m hx,
    rowAction_eq_normalRowAction,
    crossVec_frameRowAction_normals, normalCoefficientBlock_det]


-- @@ L518-527 verbatim
theorem kerCross_target_eq_smul
    {x : E} (hx : StandardSaddle.levelMap m (1 / 2) x = 0) :
    kerCross (targetLevelMap m) x =
      (twistRe m (spaceTime x 1) ^ 2 +
        twistIm m (spaceTime x 1) ^ 2) •
          kerCross (StandardSaddle.levelMap m (1 / 2)) x := by
  unfold kerCross
  rw [target_gradients_eq_rowAction m hx,
    rowAction_eq_normalRowAction,
    crossVec_frameRowAction_normals, normalCoefficientBlock_det]


-- @@ L529-535 verbatim
theorem tauField_eq_of_kerCross_pos_smul {g g' : E → F} {x : E}
    {c : ℝ} (hc : 0 < c)
    (hker : kerCross g x = c • kerCross g' x) :
    tauField g x = tauField g' x := by
  unfold tauField
  rw [hker, norm_smul, Real.norm_eq_abs, abs_of_pos hc, smul_smul]
  simp [_root_.mul_inv_rev, hc.ne']


-- @@ L537-543 verbatim
theorem tauField_source_eq_standard {x : E}
    (hx : StandardSaddle.levelMap m (-1 / 2) x = 0)
    (hc : 0 < twistRe m (spaceTime x 0) ^ 2 +
      twistIm m (spaceTime x 0) ^ 2) :
    tauField (sourceLevelMap m) x =
      tauField (StandardSaddle.levelMap m (-1 / 2)) x :=
  tauField_eq_of_kerCross_pos_smul m hc (kerCross_source_eq_smul m hx)


-- @@ L545-551 verbatim
theorem tauField_target_eq_standard {x : E}
    (hx : StandardSaddle.levelMap m (1 / 2) x = 0)
    (hc : 0 < twistRe m (spaceTime x 1) ^ 2 +
      twistIm m (spaceTime x 1) ^ 2) :
    tauField (targetLevelMap m) x =
      tauField (StandardSaddle.levelMap m (1 / 2)) x :=
  tauField_eq_of_kerCross_pos_smul m hc (kerCross_target_eq_smul m hx)


-- @@ L553-564 verbatim
theorem frameRowAction_tangentNormalBlock {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ)
    (t : EuclideanSpace ℝ (Fin (n + 1)))
    (v : Fin n → EuclideanSpace ℝ (Fin (n + 1))) :
    frameRowAction (tangentNormalBlock 1 M) (Fin.cons t v) =
      Fin.cons t (rowAction M v) := by
  classical
  funext i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
  · simp [frameRowAction, Fin.sum_univ_succ, tangentNormalBlock]
  · simp [frameRowAction, Fin.sum_univ_succ,
      tangentNormalBlock, rowAction]


-- @@ L566-594 verbatim
theorem frameAt_source_eq_coefficientAction (hm : 0 < m)
    {x : E} (hx : x ∈ (ConcreteZeroPairCassiniTwist.sourceFLS m hm).fiber) :
    frameAt (ConcreteZeroPairCassiniTwist.sourceFLS m hm) x =
      frameRowAction
        (fullCoefficientBlock m (twistRe m (spaceTime x 0))
          (twistIm m (spaceTime x 0)))
        (frameAt (StandardSaddle.sourceFLS m) x) := by
  have hxstd : x ∈ (StandardSaddle.sourceFLS m).fiber := by
    rw [← source_fiber_eq_standard m hm]
    exact hx
  have hxlevel : StandardSaddle.levelMap m (-1 / 2) x = 0 := hxstd
  have hv : ConcreteZeroPairCassiniTwist.eventMap m (spaceTime x 0) = 0 := hx
  have hvstd : StandardSaddle.eventMap m (spaceTime x 0) = 0 :=
    (StandardSaddle.eventMap_collar_zero m x (by norm_num)).trans hxlevel
  have hc : 0 < twistRe m (spaceTime x 0) ^ 2 +
      twistIm m (spaceTime x 0) ^ 2 := by
    have hp := twistCoefficient_normSq_pos_of_eventMap_eq_zero m hm hv
    rw [twistShift_eq_zero_of_standard_zero m hvstd, add_zero] at hp
    exact hp
  rw [fullCoefficientBlock_eq_tangentNormalBlock,
    show frameAt (ConcreteZeroPairCassiniTwist.sourceFLS m hm) x =
        Fin.cons (tauField (sourceLevelMap m) x)
          (fun i => gradVec (sourceLevelMap m) i x) by rfl,
    show frameAt (StandardSaddle.sourceFLS m) x =
        Fin.cons (tauField (StandardSaddle.levelMap m (-1 / 2)) x)
          (fun i => gradVec (StandardSaddle.levelMap m (-1 / 2)) i x) by rfl,
    frameRowAction_tangentNormalBlock,
    tauField_source_eq_standard m hxlevel hc,
    source_gradients_eq_rowAction m hxlevel]


-- @@ L596-624 verbatim
theorem frameAt_target_eq_coefficientAction (hm : 0 < m)
    {x : E} (hx : x ∈ (ConcreteZeroPairCassiniTwist.targetFLS m hm).fiber) :
    frameAt (ConcreteZeroPairCassiniTwist.targetFLS m hm) x =
      frameRowAction
        (fullCoefficientBlock m (twistRe m (spaceTime x 1))
          (twistIm m (spaceTime x 1)))
        (frameAt (StandardSaddle.targetFLS m) x) := by
  have hxstd : x ∈ (StandardSaddle.targetFLS m).fiber := by
    rw [← target_fiber_eq_standard m hm]
    exact hx
  have hxlevel : StandardSaddle.levelMap m (1 / 2) x = 0 := hxstd
  have hv : ConcreteZeroPairCassiniTwist.eventMap m (spaceTime x 1) = 0 := hx
  have hvstd : StandardSaddle.eventMap m (spaceTime x 1) = 0 :=
    (StandardSaddle.eventMap_collar_one m x (by norm_num)).trans hxlevel
  have hc : 0 < twistRe m (spaceTime x 1) ^ 2 +
      twistIm m (spaceTime x 1) ^ 2 := by
    have hp := twistCoefficient_normSq_pos_of_eventMap_eq_zero m hm hv
    rw [twistShift_eq_zero_of_standard_zero m hvstd, add_zero] at hp
    exact hp
  rw [fullCoefficientBlock_eq_tangentNormalBlock,
    show frameAt (ConcreteZeroPairCassiniTwist.targetFLS m hm) x =
        Fin.cons (tauField (targetLevelMap m) x)
          (fun i => gradVec (targetLevelMap m) i x) by rfl,
    show frameAt (StandardSaddle.targetFLS m) x =
        Fin.cons (tauField (StandardSaddle.levelMap m (1 / 2)) x)
          (fun i => gradVec (StandardSaddle.levelMap m (1 / 2)) i x) by rfl,
    frameRowAction_tangentNormalBlock,
    tauField_target_eq_standard m hxlevel hc,
    target_gradients_eq_rowAction m hxlevel]


-- @@ L626-626 verbatim
/-! ## Normalized endpoint frames -/


-- @@ L628-643 verbatim
theorem orthonormal_frameRowAction {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M * Mᵀ = 1)
    (v : Fin n → EuclideanSpace ℝ (Fin n))
    (hv : Orthonormal ℝ v) :
    Orthonormal ℝ (frameRowAction M v) := by
  rw [orthonormal_iff_ite]
  intro i j
  simp only [frameRowAction]
  rw [sum_inner]
  simp_rw [inner_sum, real_inner_smul_left, real_inner_smul_right,
    orthonormal_iff_ite.mp hv]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  have hij := congrArg (fun N : Matrix (Fin n) (Fin n) ℝ => N i j) hM
  simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using hij


-- @@ L645-658 verbatim
theorem orthonormal_normalizedCoefficient_endpointUnitFrame
    {a b level : ℝ} {x : E}
    (hc : 0 < a ^ 2 + b ^ 2)
    (hx : StandardSaddle.levelMap m level x = 0)
    (hlevel : level = (-1 / 2 : ℝ) ∨ level = (1 / 2 : ℝ)) :
    Orthonormal ℝ
      (frameRowAction
        (fullCoefficientBlock m (a / coefficientNorm a b)
          (b / coefficientNorm a b))
        (StandardSaddle.endpointUnitFrame m level x)) := by
  apply orthonormal_frameRowAction
  · exact fullCoefficientBlock_mul_transpose_of_normSq_one m _ _
      (normalized_coefficient_normSq hc)
  · exact StandardSaddle.orthonormal_endpointUnitFrame m hx hlevel


-- @@ L660-664 verbatim
def cassiniFrameScale (x : E) (a b : ℝ) (i : Fin (m + 3)) : ℝ :=
  if i = 0 then 1
  else if i = (0 : Fin (m + 2)).succ ∨
      i = (1 : Fin (m + 2)).succ then coefficientNorm a b
  else StandardSaddle.endpointFrameScale m x i


-- @@ L666-676 verbatim
theorem cassiniFrameScale_pos {a b level : ℝ} {x : E}
    (hc : 0 < a ^ 2 + b ^ 2)
    (hx : StandardSaddle.levelMap m level x = 0)
    (hlevel : level = (-1 / 2 : ℝ) ∨ level = (1 / 2 : ℝ))
    (i : Fin (m + 3)) :
    0 < cassiniFrameScale m x a b i := by
  unfold cassiniFrameScale
  split_ifs
  · norm_num
  · exact coefficientNorm_pos hc
  · exact StandardSaddle.endpointFrameScale_pos m hx hlevel i


-- @@ L678-688 verbatim
theorem endpointRawFrame_firstNormal_eq_unit (hm : 0 < m)
    {level : ℝ} {x : E}
    (hx : StandardSaddle.levelMap m level x = 0)
    (hlevel : level = (-1 / 2 : ℝ) ∨ level = (1 / 2 : ℝ)) :
    StandardSaddle.endpointRawNormal m x 0 =
      StandardSaddle.endpointNormalUnit m x 0 := by
  let j : Fin (m + 1) := ⟨0, by omega⟩
  change StandardSaddle.endpointRawNormal m x j.castSucc =
    StandardSaddle.endpointNormalUnit m x j.castSucc
  simp [StandardSaddle.endpointRawNormal,
    StandardSaddle.endpointNormalUnit]


-- @@ L690-700 verbatim
theorem endpointRawFrame_secondNormal_eq_unit (hm : 0 < m)
    {level : ℝ} {x : E}
    (hx : StandardSaddle.levelMap m level x = 0)
    (hlevel : level = (-1 / 2 : ℝ) ∨ level = (1 / 2 : ℝ)) :
    StandardSaddle.endpointRawNormal m x 1 =
      StandardSaddle.endpointNormalUnit m x 1 := by
  let j : Fin (m + 1) := ⟨1, by omega⟩
  change StandardSaddle.endpointRawNormal m x j.castSucc =
    StandardSaddle.endpointNormalUnit m x j.castSucc
  simp [StandardSaddle.endpointRawNormal,
    StandardSaddle.endpointNormalUnit]


-- @@ L702-777 verbatim
theorem coefficientAction_endpointRawFrame_eq_smul (hm : 0 < m)
    {a b level : ℝ} {x : E}
    (hc : 0 < a ^ 2 + b ^ 2)
    (hx : StandardSaddle.levelMap m level x = 0)
    (hlevel : level = (-1 / 2 : ℝ) ∨ level = (1 / 2 : ℝ))
    (i : Fin (m + 3)) :
    frameRowAction (fullCoefficientBlock m a b)
        (StandardSaddle.endpointRawFrame m level x) i =
      cassiniFrameScale m x a b i •
        frameRowAction
          (fullCoefficientBlock m (a / coefficientNorm a b)
            (b / coefficientNorm a b))
          (StandardSaddle.endpointUnitFrame m level x) i := by
  rw [fullCoefficientBlock_eq_tangentNormalBlock,
    fullCoefficientBlock_eq_tangentNormalBlock,
    show StandardSaddle.endpointRawFrame m level x =
        Fin.cons (StandardSaddle.orientedUnitPlanarTangent m level x)
          (StandardSaddle.endpointRawNormal m x) by rfl,
    show StandardSaddle.endpointUnitFrame m level x =
        Fin.cons (StandardSaddle.orientedUnitPlanarTangent m level x)
          (StandardSaddle.endpointNormalUnit m x) by rfl,
    frameRowAction_tangentNormalBlock,
    frameRowAction_tangentNormalBlock]
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
  · simp [cassiniFrameScale, StandardSaddle.endpointRawFrame,
      StandardSaddle.endpointUnitFrame]
  · simp only [Fin.cons_succ]
    by_cases hi0 : i = 0
    · subst i
      rw [rowAction_normalCoefficientBlock_zero,
        rowAction_normalCoefficientBlock_zero,
        endpointRawFrame_firstNormal_eq_unit m hm hx hlevel,
        endpointRawFrame_secondNormal_eq_unit m hm hx hlevel]
      have hr := coefficientNorm_pos hc
      have ha : coefficientNorm a b * (a / coefficientNorm a b) = a := by
        field_simp [hr.ne']
      have hb : coefficientNorm a b * (b / coefficientNorm a b) = b := by
        field_simp [hr.ne']
      simp only [cassiniFrameScale, Fin.succ_ne_zero, ↓reduceIte,
        true_or, smul_sub, smul_smul]
      simp [ha, hb]
    · by_cases hi1 : i = 1
      · subst i
        rw [rowAction_normalCoefficientBlock_one,
          rowAction_normalCoefficientBlock_one,
          endpointRawFrame_firstNormal_eq_unit m hm hx hlevel,
          endpointRawFrame_secondNormal_eq_unit m hm hx hlevel]
        have hr := coefficientNorm_pos hc
        have ha : coefficientNorm a b * (a / coefficientNorm a b) = a := by
          field_simp [hr.ne']
        have hb : coefficientNorm a b * (b / coefficientNorm a b) = b := by
          field_simp [hr.ne']
        simp only [cassiniFrameScale, Fin.succ_ne_zero, ↓reduceIte,
          smul_add, smul_smul]
        simp [ha, hb]
      · rw [rowAction_normalCoefficientBlock_of_ne m _ _ _ i hi0 hi1,
          rowAction_normalCoefficientBlock_of_ne m _ _ _ i hi0 hi1]
        have hraw := StandardSaddle.endpointRawFrame_eq_smul_endpointUnitFrame
          m hx hlevel i.succ
        simp only [StandardSaddle.endpointRawFrame,
          StandardSaddle.endpointUnitFrame, Fin.cons_succ] at hraw
        rw [hraw]
        have hs0 : (i.succ : Fin (m + 3)) ≠ 0 := Fin.succ_ne_zero i
        have hs1 : (i.succ : Fin (m + 3)) ≠
            (0 : Fin (m + 2)).succ := by
          intro h
          exact hi0 (Fin.succ_injective (m + 2) h)
        have hs2 : (i.succ : Fin (m + 3)) ≠
            (1 : Fin (m + 2)).succ := by
          intro h
          exact hi1 (Fin.succ_injective (m + 2) h)
        have hspecial : ¬ ((i.succ : Fin (m + 3)) =
            (0 : Fin (m + 2)).succ ∨
            (i.succ : Fin (m + 3)) = (1 : Fin (m + 2)).succ) :=
          fun h => h.elim hs1 hs2
        rw [cassiniFrameScale, if_neg hs0, if_neg hspecial]


-- @@ L779-813 verbatim
theorem gramSchmidtNormed_coefficientAction_endpointRawFrame
    (hm : 0 < m) {a b level : ℝ} {x : E}
    (hc : 0 < a ^ 2 + b ^ 2)
    (hx : StandardSaddle.levelMap m level x = 0)
    (hlevel : level = (-1 / 2 : ℝ) ∨ level = (1 / 2 : ℝ)) :
    gramSchmidtNormed ℝ
        (frameRowAction (fullCoefficientBlock m a b)
          (StandardSaddle.endpointRawFrame m level x)) =
      frameRowAction
        (fullCoefficientBlock m (a / coefficientNorm a b)
          (b / coefficientNorm a b))
        (StandardSaddle.endpointUnitFrame m level x) := by
  let U := frameRowAction
    (fullCoefficientBlock m (a / coefficientNorm a b)
      (b / coefficientNorm a b))
    (StandardSaddle.endpointUnitFrame m level x)
  have hon : Orthonormal ℝ U :=
    orthonormal_normalizedCoefficient_endpointUnitFrame m hc hx hlevel
  have horth : Pairwise
      (fun i j => inner ℝ
        (frameRowAction (fullCoefficientBlock m a b)
          (StandardSaddle.endpointRawFrame m level x) i)
        (frameRowAction (fullCoefficientBlock m a b)
          (StandardSaddle.endpointRawFrame m level x) j) = 0) := by
    intro i j hij
    rw [coefficientAction_endpointRawFrame_eq_smul m hm hc hx hlevel,
      coefficientAction_endpointRawFrame_eq_smul m hm hc hx hlevel,
      real_inner_smul_left, real_inner_smul_right, hon.2 hij,
      mul_zero, mul_zero]
  funext i
  rw [gramSchmidtNormed, gramSchmidt_of_orthogonal ℝ horth,
    coefficientAction_endpointRawFrame_eq_smul m hm hc hx hlevel,
    norm_smul, hon.1 i, mul_one, Real.norm_eq_abs,
    abs_of_pos (cassiniFrameScale_pos m hc hx hlevel i), smul_smul]
  simp [inv_mul_cancel₀ (cassiniFrameScale_pos m hc hx hlevel i).ne']


-- @@ L815-827 verbatim
theorem sourceCoefficient_normSq_pos (hm : 0 < m)
    {x : E} (hx : x ∈ (ConcreteZeroPairCassiniTwist.sourceFLS m hm).fiber) :
    0 < twistRe m (spaceTime x 0) ^ 2 +
      twistIm m (spaceTime x 0) ^ 2 := by
  have hxstd : x ∈ (StandardSaddle.sourceFLS m).fiber := by
    rw [← source_fiber_eq_standard m hm]
    exact hx
  have hv : ConcreteZeroPairCassiniTwist.eventMap m
      (spaceTime x 0) = 0 := hx
  have hvstd : StandardSaddle.eventMap m (spaceTime x 0) = 0 :=
    (StandardSaddle.eventMap_collar_zero m x (by norm_num)).trans hxstd
  have hp := twistCoefficient_normSq_pos_of_eventMap_eq_zero m hm hv
  rwa [twistShift_eq_zero_of_standard_zero m hvstd, add_zero] at hp


-- @@ L829-841 verbatim
theorem targetCoefficient_normSq_pos (hm : 0 < m)
    {x : E} (hx : x ∈ (ConcreteZeroPairCassiniTwist.targetFLS m hm).fiber) :
    0 < twistRe m (spaceTime x 1) ^ 2 +
      twistIm m (spaceTime x 1) ^ 2 := by
  have hxstd : x ∈ (StandardSaddle.targetFLS m).fiber := by
    rw [← target_fiber_eq_standard m hm]
    exact hx
  have hv : ConcreteZeroPairCassiniTwist.eventMap m
      (spaceTime x 1) = 0 := hx
  have hvstd : StandardSaddle.eventMap m (spaceTime x 1) = 0 :=
    (StandardSaddle.eventMap_collar_one m x (by norm_num)).trans hxstd
  have hp := twistCoefficient_normSq_pos_of_eventMap_eq_zero m hm hv
  rwa [twistShift_eq_zero_of_standard_zero m hvstd, add_zero] at hp


-- @@ L843-859 verbatim
theorem gramSchmidtNormed_frameAt_source (hm : 0 < m)
    {x : E} (hx : x ∈ (ConcreteZeroPairCassiniTwist.sourceFLS m hm).fiber) :
    gramSchmidtNormed ℝ
        (frameAt (ConcreteZeroPairCassiniTwist.sourceFLS m hm) x) =
      frameRowAction
        ((coefficientSO m (twistRe m (spaceTime x 0))
          (twistIm m (spaceTime x 0)) (sourceCoefficient_normSq_pos m hm hx) :
            SOGroup (m + 3)) : Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ)
        (StandardSaddle.endpointUnitFrame m (-1 / 2) x) := by
  have hxstd : x ∈ (StandardSaddle.sourceFLS m).fiber := by
    rw [← source_fiber_eq_standard m hm]
    exact hx
  have hc := sourceCoefficient_normSq_pos m hm hx
  rw [frameAt_source_eq_coefficientAction m hm hx,
    StandardSaddle.frameAt_source_eq_endpointRawFrame m hxstd,
    gramSchmidtNormed_coefficientAction_endpointRawFrame m hm hc hxstd
      (Or.inl rfl), coefficientSO_coe]


-- @@ L861-877 verbatim
theorem gramSchmidtNormed_frameAt_target (hm : 0 < m)
    {x : E} (hx : x ∈ (ConcreteZeroPairCassiniTwist.targetFLS m hm).fiber) :
    gramSchmidtNormed ℝ
        (frameAt (ConcreteZeroPairCassiniTwist.targetFLS m hm) x) =
      frameRowAction
        ((coefficientSO m (twistRe m (spaceTime x 1))
          (twistIm m (spaceTime x 1)) (targetCoefficient_normSq_pos m hm hx) :
            SOGroup (m + 3)) : Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ)
        (StandardSaddle.endpointUnitFrame m (1 / 2) x) := by
  have hxstd : x ∈ (StandardSaddle.targetFLS m).fiber := by
    rw [← target_fiber_eq_standard m hm]
    exact hx
  have hc := targetCoefficient_normSq_pos m hm hx
  rw [frameAt_target_eq_coefficientAction m hm hx,
    StandardSaddle.frameAt_target_eq_endpointRawFrame m hxstd,
    gramSchmidtNormed_coefficientAction_endpointRawFrame m hm hc hxstd
      (Or.inr rfl), coefficientSO_coe]


-- @@ L879-879 verbatim
end ConcreteZeroPairCassiniFrameAdapter

-- @@ L880-880 verbatim
end Submission
