import Mathlib
import Submission.CompactHopfPairFrame
import Submission.FrameAtMatrixRows


-- @@ L5-10 verbatim
/-!
# Intrinsic frames of the compact Hopf pair

This file connects the explicit simultaneous-double-rotation matrices to the
actual normalized intrinsic frames on the two coordinate-circle components.
-/


-- @@ L12-12 verbatim
set_option autoImplicit false

-- @@ L13-13 verbatim
set_option maxHeartbeats 1600000

-- @@ L14-14 verbatim
set_option maxRecDepth 4000

-- @@ L15-15 verbatim
set_option linter.unusedSimpArgs false


-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
namespace Submission

-- @@ L20-20 verbatim
namespace CompactHopfPairConfiguration


-- @@ L22-22 verbatim
open Set Function Matrix InnerProductSpace

-- @@ L23-23 verbatim
open scoped Topology Matrix RealInnerProductSpace unitInterval


-- @@ L25-25 verbatim
variable (k : ℕ)


-- @@ L27-27 verbatim
local notation "hk" => Nat.succ_pos k

-- @@ L28-28 verbatim
local notation "Ek" => EuclideanSpace ℝ (Fin (k + 4))

-- @@ L29-29 verbatim
local notation "Fk" => EuclideanSpace ℝ (Fin (k + 3))


-- @@ L31-34 verbatim
private lemma amb_zero_ne_one : (0 : Fin (k + 4)) ≠ 1 := by
  intro h
  have hv := congrArg Fin.val h
  norm_num [Nat.mod_eq_of_lt (by omega : 1 < k + 4)] at hv


-- @@ L36-39 verbatim
private lemma amb_zero_ne_two : (0 : Fin (k + 4)) ≠ 2 := by
  intro h
  have hv := congrArg Fin.val h
  norm_num [Nat.mod_eq_of_lt (by omega : 2 < k + 4)] at hv


-- @@ L41-44 verbatim
private lemma amb_zero_ne_three : (0 : Fin (k + 4)) ≠ 3 := by
  intro h
  have hv := congrArg Fin.val h
  norm_num [Nat.mod_eq_of_lt (by omega : 3 < k + 4)] at hv


-- @@ L46-50 verbatim
private lemma amb_one_ne_two : (1 : Fin (k + 4)) ≠ 2 := by
  intro h
  have hv := congrArg Fin.val h
  norm_num [Nat.mod_eq_of_lt (by omega : 1 < k + 4),
    Nat.mod_eq_of_lt (by omega : 2 < k + 4)] at hv


-- @@ L52-56 verbatim
private lemma amb_one_ne_three : (1 : Fin (k + 4)) ≠ 3 := by
  intro h
  have hv := congrArg Fin.val h
  norm_num [Nat.mod_eq_of_lt (by omega : 1 < k + 4),
    Nat.mod_eq_of_lt (by omega : 3 < k + 4)] at hv


-- @@ L58-62 verbatim
private lemma amb_two_ne_three : (2 : Fin (k + 4)) ≠ 3 := by
  intro h
  have hv := congrArg Fin.val h
  norm_num [Nat.mod_eq_of_lt (by omega : 2 < k + 4),
    Nat.mod_eq_of_lt (by omega : 3 < k + 4)] at hv


-- @@ L64-67 verbatim
private lemma out_zero_ne_one : (0 : Fin (k + 3)) ≠ 1 := by
  intro h
  have hv := congrArg Fin.val h
  norm_num [Nat.mod_eq_of_lt (by omega : 1 < k + 3)] at hv


-- @@ L69-72 verbatim
private lemma out_zero_ne_two : (0 : Fin (k + 3)) ≠ 2 := by
  intro h
  have hv := congrArg Fin.val h
  norm_num [Nat.mod_eq_of_lt (by omega : 2 < k + 3)] at hv


-- @@ L74-78 verbatim
private lemma out_one_ne_two : (1 : Fin (k + 3)) ≠ 2 := by
  intro h
  have hv := congrArg Fin.val h
  norm_num [Nat.mod_eq_of_lt (by omega : 1 < k + 3),
    Nat.mod_eq_of_lt (by omega : 2 < k + 3)] at hv


-- @@ L80-81 verbatim
private lemma amb_one_ne_zero : (1 : Fin (k + 4)) ≠ 0 :=
  (amb_zero_ne_one k).symm


-- @@ L83-84 verbatim
private lemma amb_two_ne_zero : (2 : Fin (k + 4)) ≠ 0 :=
  (amb_zero_ne_two k).symm


-- @@ L86-87 verbatim
private lemma amb_three_ne_zero : (3 : Fin (k + 4)) ≠ 0 :=
  (amb_zero_ne_three k).symm


-- @@ L89-90 verbatim
private lemma amb_two_ne_one : (2 : Fin (k + 4)) ≠ 1 :=
  (amb_one_ne_two k).symm


-- @@ L92-93 verbatim
private lemma amb_three_ne_one : (3 : Fin (k + 4)) ≠ 1 :=
  (amb_one_ne_three k).symm


-- @@ L95-96 verbatim
private lemma amb_three_ne_two : (3 : Fin (k + 4)) ≠ 2 :=
  (amb_two_ne_three k).symm


-- @@ L98-99 verbatim
private lemma out_one_ne_zero : (1 : Fin (k + 3)) ≠ 0 :=
  (out_zero_ne_one k).symm


-- @@ L101-102 verbatim
private lemma out_two_ne_zero : (2 : Fin (k + 3)) ≠ 0 :=
  (out_zero_ne_two k).symm


-- @@ L104-105 verbatim
private lemma out_two_ne_one : (2 : Fin (k + 3)) ≠ 1 :=
  (out_one_ne_two k).symm


-- @@ L107-110 verbatim
private lemma out_zero_succ :
    (0 : Fin (k + 3)).succ = (1 : Fin (k + 4)) := by
  apply Fin.ext
  simp [Nat.mod_eq_of_lt (by omega : 1 < k + 4)]


-- @@ L112-116 verbatim
private lemma out_one_succ :
    (1 : Fin (k + 3)).succ = (2 : Fin (k + 4)) := by
  apply Fin.ext
  simp [Nat.mod_eq_of_lt (by omega : 1 < k + 3),
    Nat.mod_eq_of_lt (by omega : 2 < k + 4)]


-- @@ L118-122 verbatim
private lemma out_two_succ :
    (2 : Fin (k + 3)).succ = (3 : Fin (k + 4)) := by
  apply Fin.ext
  simp [Nat.mod_eq_of_lt (by omega : 2 < k + 3),
    Nat.mod_eq_of_lt (by omega : 3 < k + 4)]


-- @@ L124-127 verbatim
private lemma succ_eq_one_iff (i : Fin (k + 3)) :
    i.succ = (1 : Fin (k + 4)) ↔ i = 0 := by
  rw [← out_zero_succ k]
  exact Fin.succ_inj


-- @@ L129-132 verbatim
private lemma succ_eq_two_iff (i : Fin (k + 3)) :
    i.succ = (2 : Fin (k + 4)) ↔ i = 1 := by
  rw [← out_one_succ k]
  exact Fin.succ_inj


-- @@ L134-137 verbatim
private lemma succ_eq_three_iff (i : Fin (k + 3)) :
    i.succ = (3 : Fin (k + 4)) ↔ i = 2 := by
  rw [← out_two_succ k]
  exact Fin.succ_inj


-- @@ L139-144 verbatim
attribute [local simp] amb_zero_ne_one amb_zero_ne_two amb_zero_ne_three
  amb_one_ne_two amb_one_ne_three amb_two_ne_three amb_one_ne_zero
  amb_two_ne_zero amb_three_ne_zero amb_two_ne_one amb_three_ne_one
  amb_three_ne_two out_zero_ne_one out_zero_ne_two out_one_ne_two
  out_one_ne_zero out_two_ne_zero out_two_ne_one succ_eq_one_iff
  succ_eq_two_iff succ_eq_three_iff


-- @@ L146-152 verbatim
lemma fderiv_levelMap_eq_coreMap_of_coreMap_eq_zero
    {x : Ek} (hx : coreMap (k + 1) hk x = 0) :
    fderiv ℝ (levelMap (k + 1) hk) x =
      fderiv ℝ (coreMap (k + 1) hk) x := by
  have hn := normSq_eq_one_of_coreMap_eq_zero (k + 1) hk hx
  have hlt : CompactBirth.normSq x < 2 := by rw [hn]; norm_num
  exact (levelMap_eventuallyEq_coreMap (k + 1) hk hlt).fderiv_eq


-- @@ L154-165 verbatim
lemma firstHopfSO_row_one (theta : ℝ) :
    matrixRows
        ((firstHopfSO k theta : SOGroup (k + 4)) :
          Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ) 1 =
      circleAt (m := k + 1) theta := by
  apply PiLp.ext
  intro j
  change ((firstHopfSO k theta : SOGroup (k + 4)) :
    Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ) 1 j = _
  rw [firstHopfSO_apply]
  simp [circleAt_apply, amb_zero_ne_one k, amb_one_ne_two k,
    amb_one_ne_three k, eq_comm]


-- @@ L167-178 verbatim
lemma secondHopfSO_row_one (theta : ℝ) :
    matrixRows
        ((secondHopfSO k theta : SOGroup (k + 4)) :
          Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ) 1 =
      secondCircleAt (k + 1) hk theta := by
  apply PiLp.ext
  intro j
  change ((secondHopfSO k theta : SOGroup (k + 4)) :
    Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ) 1 j = _
  rw [secondHopfSO_apply]
  simp [secondCircleAt, amb_zero_ne_one k, amb_one_ne_two k,
    amb_one_ne_three k, eq_comm]


-- @@ L180-212 verbatim
lemma firstHopfSO_normal_eq_firstPreimage (theta : ℝ) (i : Fin (k + 3)) :
    matrixRows
        ((firstHopfSO k theta : SOGroup (k + 4)) :
          Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ) i.succ =
      firstPreimage (k + 1) hk (circleAt (m := k + 1) theta)
        (EuclideanSpace.single i 1) := by
  apply PiLp.ext
  intro j
  have ha01 := amb_zero_ne_one k
  have ha02 := amb_zero_ne_two k
  have ha03 := amb_zero_ne_three k
  have ha12 := amb_one_ne_two k
  have ha13 := amb_one_ne_three k
  have ha23 := amb_two_ne_three k
  have ho01 := out_zero_ne_one k
  have ho02 := out_zero_ne_two k
  have ho12 := out_one_ne_two k
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨q, rfl⟩
  · change ((firstHopfSO k theta : SOGroup (k + 4)) :
      Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ) i.succ 0 = _
    rw [firstHopfSO_apply, firstPreimage_apply_zero,
      circleAt_apply_zero]
    by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;>
      by_cases hi2 : i = 2 <;>
      simp_all [PiLp.single_apply, eq_comm]
  · change ((firstHopfSO k theta : SOGroup (k + 4)) :
      Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ) i.succ q.succ = _
    rw [firstHopfSO_apply, firstPreimage_apply_succ]
    by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;>
      by_cases hi2 : i = 2 <;> by_cases hq0 : q = 0 <;>
      by_cases hq1 : q = 1 <;> by_cases hq2 : q = 2 <;>
      by_cases hqi : q = i <;>
      simp_all [PiLp.single_apply, circleAt_apply, eq_comm]


-- @@ L214-246 verbatim
lemma secondHopfSO_normal_eq_secondPreimage (theta : ℝ) (i : Fin (k + 3)) :
    matrixRows
        ((secondHopfSO k theta : SOGroup (k + 4)) :
          Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ) i.succ =
      secondPreimage (k + 1) hk (secondCircleAt (k + 1) hk theta)
        (EuclideanSpace.single i 1) := by
  apply PiLp.ext
  intro j
  have ha01 := amb_zero_ne_one k
  have ha02 := amb_zero_ne_two k
  have ha03 := amb_zero_ne_three k
  have ha12 := amb_one_ne_two k
  have ha13 := amb_one_ne_three k
  have ha23 := amb_two_ne_three k
  have ho01 := out_zero_ne_one k
  have ho02 := out_zero_ne_two k
  have ho12 := out_one_ne_two k
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨q, rfl⟩
  · change ((secondHopfSO k theta : SOGroup (k + 4)) :
      Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ) i.succ 0 = _
    rw [secondHopfSO_apply, secondPreimage_apply_zero,
      secondCircleAt_apply_two, secondCircleAt_apply_three]
    by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;>
      by_cases hi2 : i = 2 <;>
      simp_all [PiLp.single_apply, eq_comm]
  · change ((secondHopfSO k theta : SOGroup (k + 4)) :
      Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ) i.succ q.succ = _
    rw [secondHopfSO_apply, secondPreimage_apply_succ]
    by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;>
      by_cases hi2 : i = 2 <;> by_cases hq0 : q = 0 <;>
      by_cases hq1 : q = 1 <;> by_cases hq2 : q = 2 <;>
      by_cases hqi : q = i <;>
      simp_all [PiLp.single_apply, secondCircleAt, eq_comm]


-- @@ L248-278 verbatim
lemma fderiv_coreMap_firstHopfSO_row_zero (theta : ℝ) :
    fderiv ℝ (coreMap (k + 1) hk) (circleAt (m := k + 1) theta)
        (matrixRows
          ((firstHopfSO k theta : SOGroup (k + 4)) :
            Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ) 0) = 0 := by
  apply PiLp.ext
  intro i
  by_cases hi0 : i = 0
  · subst i
    rw [fderiv_coreMap_apply_zero]
    have horth := orthonormal_matrixRows_of_mem_orthogonalGroup
      (Matrix.mem_specialOrthogonalGroup_iff.mp
        (firstHopfSO k theta).property).1
    have hrow := orthonormal_iff_ite.mp horth
      (1 : Fin (k + 4)) (0 : Fin (k + 4))
    rw [firstHopfSO_row_one] at hrow
    simpa using hrow
  · by_cases hi1 : i = 1
    · subst i
      rw [fderiv_coreMap_apply_one]
      change _ * _ + _ * _ + _ * _ + _ * _ = 0
      simp [matrixRows, circleAt_apply, firstHopfSO_apply]
    · by_cases hi2 : i = 2
      · subst i
        rw [fderiv_coreMap_apply_two]
        change _ * _ + _ * _ - _ * _ - _ * _ = 0
        simp [matrixRows, circleAt_apply, firstHopfSO_apply]
      · rw [fderiv_coreMap_apply_tail (k + 1) hk _ _ hi0 hi1 hi2]
        change ((firstHopfSO k theta : SOGroup (k + 4)) :
          Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ) 0 i.succ = 0
        simp [firstHopfSO_apply, hi0, hi1, hi2]


-- @@ L280-310 verbatim
lemma fderiv_coreMap_secondHopfSO_row_zero (theta : ℝ) :
    fderiv ℝ (coreMap (k + 1) hk) (secondCircleAt (k + 1) hk theta)
        (matrixRows
          ((secondHopfSO k theta : SOGroup (k + 4)) :
            Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ) 0) = 0 := by
  apply PiLp.ext
  intro i
  by_cases hi0 : i = 0
  · subst i
    rw [fderiv_coreMap_apply_zero]
    have horth := orthonormal_matrixRows_of_mem_orthogonalGroup
      (Matrix.mem_specialOrthogonalGroup_iff.mp
        (secondHopfSO k theta).property).1
    have hrow := orthonormal_iff_ite.mp horth
      (1 : Fin (k + 4)) (0 : Fin (k + 4))
    rw [secondHopfSO_row_one] at hrow
    simpa using hrow
  · by_cases hi1 : i = 1
    · subst i
      rw [fderiv_coreMap_apply_one]
      change _ * _ + _ * _ + _ * _ + _ * _ = 0
      simp [matrixRows, secondCircleAt, secondHopfSO_apply]
    · by_cases hi2 : i = 2
      · subst i
        rw [fderiv_coreMap_apply_two]
        change _ * _ + _ * _ - _ * _ - _ * _ = 0
        simp [matrixRows, secondCircleAt, secondHopfSO_apply]
      · rw [fderiv_coreMap_apply_tail (k + 1) hk _ _ hi0 hi1 hi2]
        change ((secondHopfSO k theta : SOGroup (k + 4)) :
          Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ) 0 i.succ = 0
        simp [secondHopfSO_apply, hi0, hi1, hi2]


-- @@ L312-319 verbatim
lemma fderiv_levelMap_firstHopfSO_row_zero (theta : ℝ) :
    fderiv ℝ (levelMap (k + 1) hk) (circleAt (m := k + 1) theta)
        (matrixRows
          ((firstHopfSO k theta : SOGroup (k + 4)) :
            Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ) 0) = 0 := by
  rw [fderiv_levelMap_eq_coreMap_of_coreMap_eq_zero k
    (coreMap_circleAt_eq_zero (k + 1) hk theta)]
  exact fderiv_coreMap_firstHopfSO_row_zero k theta


-- @@ L321-328 verbatim
lemma fderiv_levelMap_secondHopfSO_row_zero (theta : ℝ) :
    fderiv ℝ (levelMap (k + 1) hk) (secondCircleAt (k + 1) hk theta)
        (matrixRows
          ((secondHopfSO k theta : SOGroup (k + 4)) :
            Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ) 0) = 0 := by
  rw [fderiv_levelMap_eq_coreMap_of_coreMap_eq_zero k
    (coreMap_secondCircleAt_eq_zero (k + 1) hk theta)]
  exact fderiv_coreMap_secondHopfSO_row_zero k theta


-- @@ L330-346 verbatim
lemma fderiv_levelMap_firstHopfSO_normal (theta : ℝ) (i : Fin (k + 3)) :
    fderiv ℝ (levelMap (k + 1) hk) (circleAt (m := k + 1) theta)
        (matrixRows
          ((firstHopfSO k theta : SOGroup (k + 4)) :
            Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ) i.succ) =
      EuclideanSpace.single i 1 := by
  have hx := coreMap_circleAt_eq_zero (k + 1) hk theta
  rw [fderiv_levelMap_eq_coreMap_of_coreMap_eq_zero k hx,
    firstHopfSO_normal_eq_firstPreimage]
  apply fderiv_coreMap_firstPreimage (k + 1) hk hx
  constructor
  · apply circleAt_apply_other theta
    · exact amb_two_ne_zero k
    · exact amb_two_ne_one k
  · apply circleAt_apply_other theta
    · exact amb_three_ne_zero k
    · exact amb_three_ne_one k


-- @@ L348-362 verbatim
lemma fderiv_levelMap_secondHopfSO_normal (theta : ℝ) (i : Fin (k + 3)) :
    fderiv ℝ (levelMap (k + 1) hk) (secondCircleAt (k + 1) hk theta)
        (matrixRows
          ((secondHopfSO k theta : SOGroup (k + 4)) :
            Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ) i.succ) =
      EuclideanSpace.single i 1 := by
  have hx := coreMap_secondCircleAt_eq_zero (k + 1) hk theta
  rw [fderiv_levelMap_eq_coreMap_of_coreMap_eq_zero k hx,
    secondHopfSO_normal_eq_secondPreimage]
  apply fderiv_coreMap_secondPreimage (k + 1) hk hx
  constructor
  · exact secondCircleAt_apply_other (k + 1) hk theta
      (amb_zero_ne_two k) (amb_zero_ne_three k)
  · exact secondCircleAt_apply_other (k + 1) hk theta
      (amb_one_ne_two k) (amb_one_ne_three k)


-- @@ L364-364 verbatim
/-! ## Exact normalized frame matrices on the two components -/


-- @@ L366-375 verbatim
theorem first_frameMatrix_eq_firstHopfSO (theta : ℝ) :
    rowsMatrix (gramSchmidtNormed ℝ
        (frameAt (X (k + 1) hk) (circleAt (m := k + 1) theta))) =
      ((firstHopfSO k theta : SOGroup (k + 4)) :
        Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ) := by
  exact frameMatrix_eq_of_SO_rightInverse
    (X (k + 1) hk) (circleAt (m := k + 1) theta)
    (firstHopfSO k theta)
    (fderiv_levelMap_firstHopfSO_row_zero k theta)
    (fderiv_levelMap_firstHopfSO_normal k theta)


-- @@ L377-387 verbatim
theorem second_frameMatrix_eq_secondHopfSO (theta : ℝ) :
    rowsMatrix (gramSchmidtNormed ℝ
        (frameAt (X (k + 1) hk)
          (secondCircleAt (k + 1) hk theta))) =
      ((secondHopfSO k theta : SOGroup (k + 4)) :
        Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ) := by
  exact frameMatrix_eq_of_SO_rightInverse
    (X (k + 1) hk) (secondCircleAt (k + 1) hk theta)
    (secondHopfSO k theta)
    (fderiv_levelMap_secondHopfSO_row_zero k theta)
    (fderiv_levelMap_secondHopfSO_normal k theta)


-- @@ L389-389 verbatim
/-! ## Explicit component loops -/


-- @@ L391-401 verbatim
theorem continuous_secondCircleAt :
    Continuous (secondCircleAt (k + 1) hk) := by
  unfold secondCircleAt
  exact (PiLp.continuous_toLp 2 _).comp <| continuous_pi fun j => by
    by_cases hj2 : j = 2
    · simp [hj2]
      fun_prop
    · by_cases hj3 : j = 3
      · simp [hj2, hj3]
        fun_prop
      · simpa [hj2, hj3] using (continuous_const : Continuous fun _ : ℝ => (0 : ℝ))


-- @@ L403-404 verbatim
def firstHopfLoop : C(I, SOGroup (k + 4)) :=
  doubleRotLoop k 1 * ContinuousMap.const I (firstInitialSO k)


-- @@ L406-407 verbatim
def secondHopfLoop : C(I, SOGroup (k + 4)) :=
  doubleRotLoop k (-1) * ContinuousMap.const I (secondInitialSO k)


-- @@ L409-412 verbatim
theorem firstHopfLoop_closed : firstHopfLoop k 0 = firstHopfLoop k 1 := by
  change doubleRotLoop k 1 0 * firstInitialSO k =
    doubleRotLoop k 1 1 * firstInitialSO k
  rw [doubleRotLoop_closed]


-- @@ L414-417 verbatim
theorem secondHopfLoop_closed : secondHopfLoop k 0 = secondHopfLoop k 1 := by
  change doubleRotLoop k (-1) 0 * secondInitialSO k =
    doubleRotLoop k (-1) 1 * secondInitialSO k
  rw [doubleRotLoop_closed]


-- @@ L419-429 verbatim
theorem firstHopfLoop_apply (u : I) :
    firstHopfLoop k u = firstHopfSO k (2 * Real.pi * (u : ℝ)) := by
  apply Subtype.ext
  change
    ((doubleRotLoop k 1 u : SOGroup (k + 4)) :
        Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ) *
        (firstInitialSO k : Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ) =
      doubleRotMat k (2 * Real.pi * (u : ℝ)) *
        (firstInitialSO k : Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ)
  rw [doubleRotLoop_apply]
  simp [linearAngle]


-- @@ L431-441 verbatim
theorem secondHopfLoop_apply (u : I) :
    secondHopfLoop k u = secondHopfSO k (2 * Real.pi * (u : ℝ)) := by
  apply Subtype.ext
  change
    ((doubleRotLoop k (-1) u : SOGroup (k + 4)) :
        Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ) *
        (secondInitialSO k : Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ) =
      doubleRotMat k (-(2 * Real.pi * (u : ℝ))) *
        (secondInitialSO k : Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ)
  rw [doubleRotLoop_apply]
  simp [linearAngle]


-- @@ L443-448 verbatim
theorem firstHopfLoop_class_zero :
    loopClassZ2 (firstHopfLoop k) (firstHopfLoop_closed k) = 0 := by
  change loopClassZ2
    (doubleRotLoop k 1 * ContinuousMap.const I (firstInitialSO k)) _ = 0
  rw [loopClassZ2_mul_const_right]
  exact doubleRotLoop_class_zero k 1


-- @@ L450-455 verbatim
theorem secondHopfLoop_class_zero :
    loopClassZ2 (secondHopfLoop k) (secondHopfLoop_closed k) = 0 := by
  change loopClassZ2
    (doubleRotLoop k (-1) * ContinuousMap.const I (secondInitialSO k)) _ = 0
  rw [loopClassZ2_mul_const_right]
  exact doubleRotLoop_class_zero k (-1)


-- @@ L457-460 verbatim
def secondCircleCurve : C(I, Ek) where
  toFun u := secondCircleAt (k + 1) hk (2 * Real.pi * (u : ℝ))
  continuous_toFun := (continuous_secondCircleAt k).comp
    ((continuous_const.mul continuous_const).mul continuous_subtype_val)


-- @@ L462-464 verbatim
@[simp] theorem secondCircleCurve_zero :
    secondCircleCurve k 0 = secondCircleAt (k + 1) hk 0 := by
  simp [secondCircleCurve]


-- @@ L466-477 verbatim
theorem secondCircleCurve_closed :
    secondCircleCurve k 0 = secondCircleCurve k 1 := by
  apply PiLp.ext
  intro j
  by_cases hj2 : j = 2
  · subst j
    simp [secondCircleCurve, secondCircleAt_apply_two]
  · by_cases hj3 : j = 3
    · subst j
      simp [secondCircleCurve, secondCircleAt_apply_three]
    · simp [secondCircleCurve,
        secondCircleAt_apply_other (k + 1) hk _ hj2 hj3]


-- @@ L479-493 verbatim
theorem secondCircleAt_eq_iff_mod {theta theta' : ℝ}
    (h : secondCircleAt (k + 1) hk theta =
      secondCircleAt (k + 1) hk theta') :
    ∃ z : ℤ, theta' = theta + (z : ℝ) * (2 * Real.pi) := by
  have hcos : Real.cos theta = Real.cos theta' := by
    simpa only [secondCircleAt_apply_two] using
      congrArg (fun x : Ek => x 2) h
  have hsin : Real.sin theta = Real.sin theta' := by
    simpa only [secondCircleAt_apply_three] using
      congrArg (fun x : Ek => x 3) h
  have hone : Real.cos (theta' - theta) = 1 := by
    rw [Real.cos_sub, ← hcos, ← hsin]
    linear_combination Real.sin_sq_add_cos_sq theta
  obtain ⟨z, hz⟩ := (Real.cos_eq_one_iff _).mp hone
  exact ⟨z, by linarith⟩


-- @@ L495-535 verbatim
theorem secondCircleCurve_eq_cases {u v : I}
    (huv : secondCircleCurve k u = secondCircleCurve k v) :
    u = v ∨ (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) := by
  obtain ⟨z, hz⟩ := secondCircleAt_eq_iff_mod k huv
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


-- @@ L537-540 verbatim
theorem firstCircleAt_mem_fiber (theta : ℝ) :
    circleAt (m := k + 1) theta ∈ (X (k + 1) hk).fiber := by
  rw [X_fiber]
  exact coreMap_circleAt_eq_zero (k + 1) hk theta


-- @@ L542-545 verbatim
theorem secondCircleAt_mem_fiber (theta : ℝ) :
    secondCircleAt (k + 1) hk theta ∈ (X (k + 1) hk).fiber := by
  rw [X_fiber]
  exact coreMap_secondCircleAt_eq_zero (k + 1) hk theta


-- @@ L547-552 verbatim
theorem firstCircleAt_mem_orbit (V : TamedField (X (k + 1) hk))
    (theta : ℝ) :
    circleAt (m := k + 1) theta ∈
      V.orbit (circleAt (m := k + 1) 0) := by
  exact V.continuousCurve_mem_orbit (circleAt (m := k + 1))
    contDiff_circleAt.continuous (firstCircleAt_mem_fiber k) theta


-- @@ L554-559 verbatim
theorem secondCircleAt_mem_orbit (V : TamedField (X (k + 1) hk))
    (theta : ℝ) :
    secondCircleAt (k + 1) hk theta ∈
      V.orbit (secondCircleAt (k + 1) hk 0) := by
  exact V.continuousCurve_mem_orbit (secondCircleAt (k + 1) hk)
    (continuous_secondCircleAt k) (secondCircleAt_mem_fiber k) theta


-- @@ L561-569 verbatim
def firstSimpleClosedOrbitParam (V : TamedField (X (k + 1) hk)) :
    SimpleClosedOrbitParam (X (k + 1) hk) V where
  p := circleAt (m := k + 1) 0
  hp := firstCircleAt_mem_fiber k 0
  curve := CompactTubeConfiguration.circleCurve (k + 1)
  curve_zero := CompactTubeConfiguration.circleCurve_zero (k + 1)
  curve_closed := CompactTubeConfiguration.circleCurve_closed (k + 1)
  curve_mem_orbit := fun _ => firstCircleAt_mem_orbit k V _
  curve_eq_cases := CompactTubeConfiguration.circleCurve_eq_cases (k + 1)


-- @@ L571-579 verbatim
def secondSimpleClosedOrbitParam (V : TamedField (X (k + 1) hk)) :
    SimpleClosedOrbitParam (X (k + 1) hk) V where
  p := secondCircleAt (k + 1) hk 0
  hp := secondCircleAt_mem_fiber k 0
  curve := secondCircleCurve k
  curve_zero := secondCircleCurve_zero k
  curve_closed := secondCircleCurve_closed k
  curve_mem_orbit := fun _ => secondCircleAt_mem_orbit k V _
  curve_eq_cases := secondCircleCurve_eq_cases k


-- @@ L581-597 verbatim
theorem first_paramFrameLoop_eq_firstHopfLoop
    (V : TamedField (X (k + 1) hk)) :
    (firstSimpleClosedOrbitParam k V).paramFrameLoop = firstHopfLoop k := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  change frameLoop (X (k + 1) hk)
      (firstSimpleClosedOrbitParam k V).realCurve (u : ℝ) =
    ((firstHopfLoop k u : SOGroup (k + 4)) :
      Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ)
  unfold frameLoop
  rw [(firstSimpleClosedOrbitParam k V).realCurve_coe]
  change rowsMatrix (gramSchmidtNormed ℝ
      (frameAt (X (k + 1) hk)
        (circleAt (m := k + 1) (2 * Real.pi * (u : ℝ))))) = _
  rw [first_frameMatrix_eq_firstHopfSO]
  exact congrArg Subtype.val (firstHopfLoop_apply k u).symm


-- @@ L599-615 verbatim
theorem second_paramFrameLoop_eq_secondHopfLoop
    (V : TamedField (X (k + 1) hk)) :
    (secondSimpleClosedOrbitParam k V).paramFrameLoop = secondHopfLoop k := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  change frameLoop (X (k + 1) hk)
      (secondSimpleClosedOrbitParam k V).realCurve (u : ℝ) =
    ((secondHopfLoop k u : SOGroup (k + 4)) :
      Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ)
  unfold frameLoop
  rw [(secondSimpleClosedOrbitParam k V).realCurve_coe]
  change rowsMatrix (gramSchmidtNormed ℝ
      (frameAt (X (k + 1) hk)
        (secondCircleAt (k + 1) hk (2 * Real.pi * (u : ℝ))))) = _
  rw [second_frameMatrix_eq_secondHopfSO]
  exact congrArg Subtype.val (secondHopfLoop_apply k u).symm


-- @@ L617-627 verbatim
theorem first_paramFrameClass_eq_zero
    (V : TamedField (X (k + 1) hk)) :
    loopClassZ2 (firstSimpleClosedOrbitParam k V).paramFrameLoop
        (firstSimpleClosedOrbitParam k V).paramFrameLoop_closed = 0 := by
  calc
    loopClassZ2 (firstSimpleClosedOrbitParam k V).paramFrameLoop
        (firstSimpleClosedOrbitParam k V).paramFrameLoop_closed =
      loopClassZ2 (firstHopfLoop k) (firstHopfLoop_closed k) := by
        apply loopClassZ2_congr_fun
        exact first_paramFrameLoop_eq_firstHopfLoop k V
    _ = 0 := firstHopfLoop_class_zero k


-- @@ L629-639 verbatim
theorem second_paramFrameClass_eq_zero
    (V : TamedField (X (k + 1) hk)) :
    loopClassZ2 (secondSimpleClosedOrbitParam k V).paramFrameLoop
        (secondSimpleClosedOrbitParam k V).paramFrameLoop_closed = 0 := by
  calc
    loopClassZ2 (secondSimpleClosedOrbitParam k V).paramFrameLoop
        (secondSimpleClosedOrbitParam k V).paramFrameLoop_closed =
      loopClassZ2 (secondHopfLoop k) (secondHopfLoop_closed k) := by
        apply loopClassZ2_congr_fun
        exact second_paramFrameLoop_eq_secondHopfLoop k V
    _ = 0 := secondHopfLoop_class_zero k


-- @@ L641-641 verbatim
end CompactHopfPairConfiguration

-- @@ L642-642 verbatim
end Submission
