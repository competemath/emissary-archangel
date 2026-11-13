import Mathlib
import Submission.CompactHopfPairRegularity
import Submission.CompactTubeConfiguration


-- @@ L5-11 verbatim
/-!
# Exact two-circle fiber of the compact Hopf pair

The two branches of the Hopf-product equation are the coordinate circles in
the `(0,1)` and `(2,3)` planes.  This file identifies the compact level fiber
with their disjoint union and supplies explicit parametrizations.
-/


-- @@ L13-13 verbatim
set_option autoImplicit false


-- @@ L15-15 verbatim
noncomputable section


-- @@ L17-17 verbatim
namespace Submission

-- @@ L18-18 verbatim
namespace CompactHopfPairConfiguration


-- @@ L20-20 verbatim
open Set Function Metric

-- @@ L21-21 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L23-23 verbatim
variable (m : ℕ) (hm : 0 < m)

-- @@ L24-24 verbatim
include hm


-- @@ L26-26 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 3))

-- @@ L27-27 verbatim
local notation "F" => EuclideanSpace ℝ (Fin (m + 2))


-- @@ L29-32 verbatim
private lemma fin_zero_ne_two : (0 : Fin (m + 3)) ≠ 2 := by
  intro h
  have hv := congrArg Fin.val h
  simp [Nat.mod_eq_of_lt (by omega : 2 < m + 3)] at hv


-- @@ L34-37 verbatim
private lemma fin_zero_ne_three : (0 : Fin (m + 3)) ≠ 3 := by
  intro h
  have hv := congrArg Fin.val h
  simp [Nat.mod_eq_of_lt (by omega : 3 < m + 3)] at hv


-- @@ L39-42 verbatim
private lemma fin_one_ne_two : (1 : Fin (m + 3)) ≠ 2 := by
  intro h
  have hv := congrArg Fin.val h
  simp [Nat.mod_eq_of_lt (by omega : 2 < m + 3)] at hv


-- @@ L44-47 verbatim
private lemma fin_one_ne_three : (1 : Fin (m + 3)) ≠ 3 := by
  intro h
  have hv := congrArg Fin.val h
  simp [Nat.mod_eq_of_lt (by omega : 3 < m + 3)] at hv


-- @@ L49-50 verbatim
private lemma fin_two_ne_zero : (2 : Fin (m + 3)) ≠ 0 :=
  (fin_zero_ne_two m hm).symm


-- @@ L52-53 verbatim
private lemma fin_two_ne_one : (2 : Fin (m + 3)) ≠ 1 :=
  (fin_one_ne_two m hm).symm


-- @@ L55-56 verbatim
private lemma fin_three_ne_zero : (3 : Fin (m + 3)) ≠ 0 :=
  (fin_zero_ne_three m hm).symm


-- @@ L58-59 verbatim
private lemma fin_three_ne_one : (3 : Fin (m + 3)) ≠ 1 :=
  (fin_one_ne_three m hm).symm


-- @@ L61-66 verbatim
/-- The second coordinate circle, in the `(2,3)` plane. -/
def secondCircleAt (_hm : 0 < m) (theta : ℝ) : E :=
  WithLp.toLp 2 fun j =>
    if j = 2 then Real.cos theta
    else if j = 3 then Real.sin theta
    else 0


-- @@ L68-75 verbatim
lemma secondCircleAt_apply_two (theta : ℝ) :
    secondCircleAt m hm theta 2 = Real.cos theta := by
  have h23 : (2 : Fin (m + 3)) ≠ 3 := by
    intro h
    have hv := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (by omega : 2 < m + 3),
      Nat.mod_eq_of_lt (by omega : 3 < m + 3)] at hv
  simp [secondCircleAt, h23]


-- @@ L77-84 verbatim
lemma secondCircleAt_apply_three (theta : ℝ) :
    secondCircleAt m hm theta 3 = Real.sin theta := by
  have h32 : (3 : Fin (m + 3)) ≠ 2 := by
    intro h
    have hv := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (by omega : 2 < m + 3),
      Nat.mod_eq_of_lt (by omega : 3 < m + 3)] at hv
  simp [secondCircleAt, h32]


-- @@ L86-88 verbatim
lemma secondCircleAt_apply_other (theta : ℝ) {j : Fin (m + 3)}
    (hj2 : j ≠ 2) (hj3 : j ≠ 3) : secondCircleAt m hm theta j = 0 := by
  simp [secondCircleAt, hj2, hj3]


-- @@ L90-90 verbatim
def secondCircle : Set E := Set.range (secondCircleAt m hm)


-- @@ L92-93 verbatim
lemma secondCircleAt_mem_secondCircle (theta : ℝ) :
    secondCircleAt m hm theta ∈ secondCircle m hm := ⟨theta, rfl⟩


-- @@ L95-123 verbatim
lemma normSq_secondCircleAt (theta : ℝ) :
    CompactBirth.normSq (secondCircleAt m hm theta) = 1 := by
  unfold CompactBirth.normSq
  have hkey : ∀ j : Fin (m + 3), secondCircleAt m hm theta j ^ 2 =
      (if j = 2 then Real.cos theta ^ 2 else 0) +
        (if j = 3 then Real.sin theta ^ 2 else 0) := by
    intro j
    by_cases hj2 : j = 2
    · subst j
      rw [secondCircleAt_apply_two]
      have h23 : (2 : Fin (m + 3)) ≠ 3 := by
        intro h
        have hv := congrArg Fin.val h
        simp [Nat.mod_eq_of_lt (by omega : 2 < m + 3),
          Nat.mod_eq_of_lt (by omega : 3 < m + 3)] at hv
      simp [h23]
    · by_cases hj3 : j = 3
      · subst j
        rw [secondCircleAt_apply_three]
        simp [hj2]
      · rw [secondCircleAt_apply_other m hm theta hj2 hj3,
          if_neg hj2, if_neg hj3]
        norm_num
  rw [Finset.sum_congr rfl fun j _ => hkey j,
    Finset.sum_add_distrib,
    Finset.sum_ite_eq' _ (2 : Fin (m + 3)) (fun _ => Real.cos theta ^ 2),
    Finset.sum_ite_eq' _ (3 : Fin (m + 3)) (fun _ => Real.sin theta ^ 2),
    if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]
  exact Real.cos_sq_add_sin_sq theta


-- @@ L125-158 verbatim
lemma coreMap_circleAt_eq_zero (theta : ℝ) :
    coreMap m hm (circleAt (m := m) theta) = 0 := by
  apply PiLp.ext
  intro i
  by_cases hi0 : i = 0
  · subst i
    rw [coreMap_apply_zero, CompactBirth.normSq_eq_norm_sq,
      norm_circleAt, one_pow]
    norm_num
  · by_cases hi1 : i = 1
    · subst i
      rw [coreMap_apply_one]
      have h2 : circleAt (m := m) theta 2 = 0 :=
        circleAt_apply_other theta (fin_two_ne_zero m hm) (fin_two_ne_one m hm)
      have h3 : circleAt (m := m) theta 3 = 0 :=
        circleAt_apply_other theta (fin_three_ne_zero m hm) (fin_three_ne_one m hm)
      rw [hopfRe, h2, h3]
      simp
    · by_cases hi2 : i = 2
      · subst i
        rw [coreMap_apply_two]
        have h2 : circleAt (m := m) theta 2 = 0 :=
          circleAt_apply_other theta (fin_two_ne_zero m hm) (fin_two_ne_one m hm)
        have h3 : circleAt (m := m) theta 3 = 0 :=
          circleAt_apply_other theta (fin_three_ne_zero m hm) (fin_three_ne_one m hm)
        rw [hopfIm, h2, h3]
        simp
      · rw [coreMap_apply_tail m hm _ hi0 hi1 hi2]
        apply circleAt_apply_other theta
        · exact Fin.succ_ne_zero i
        · intro h
          apply hi0
          apply Fin.succ_injective
          simpa using h


-- @@ L160-199 verbatim
lemma coreMap_secondCircleAt_eq_zero (theta : ℝ) :
    coreMap m hm (secondCircleAt m hm theta) = 0 := by
  apply PiLp.ext
  intro i
  by_cases hi0 : i = 0
  · subst i
    rw [coreMap_apply_zero, normSq_secondCircleAt]
    norm_num
  · by_cases hi1 : i = 1
    · subst i
      rw [coreMap_apply_one]
      have h02 := fin_zero_ne_two m hm
      have h03 := fin_zero_ne_three m hm
      have h12 := fin_one_ne_two m hm
      have h13 := fin_one_ne_three m hm
      simp [hopfRe, secondCircleAt_apply_other m hm theta h02 h03,
        secondCircleAt_apply_other m hm theta h12 h13]
    · by_cases hi2 : i = 2
      · subst i
        rw [coreMap_apply_two]
        have h02 := fin_zero_ne_two m hm
        have h03 := fin_zero_ne_three m hm
        have h12 := fin_one_ne_two m hm
        have h13 := fin_one_ne_three m hm
        simp [hopfIm, secondCircleAt_apply_other m hm theta h02 h03,
          secondCircleAt_apply_other m hm theta h12 h13]
      · rw [coreMap_apply_tail m hm _ hi0 hi1 hi2]
        apply secondCircleAt_apply_other m hm theta
        · intro h
          apply hi1
          apply Fin.succ_injective
          simpa using h
        · intro h
          apply hi2
          apply Fin.succ_injective
          have h3 : (2 : Fin (m + 2)).succ = (3 : Fin (m + 3)) := by
            apply Fin.ext
            simp [Nat.mod_eq_of_lt (by omega : 2 < m + 2),
              Nat.mod_eq_of_lt (by omega : 3 < m + 3)]
          simpa [h3] using h


-- @@ L201-216 verbatim
private lemma exists_angle_of_sq_add_sq_eq_one {a b : ℝ}
    (hab : a ^ 2 + b ^ 2 = 1) :
    ∃ theta : ℝ, Real.cos theta = a ∧ Real.sin theta = b := by
  have ha : -1 ≤ a ∧ a ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg b, sq_nonneg (a + 1), sq_nonneg (a - 1)]
  rcases le_or_gt 0 b with hb | hb
  · refine ⟨Real.arccos a, Real.cos_arccos ha.1 ha.2, ?_⟩
    rw [Real.sin_arccos]
    have h1 : 1 - a ^ 2 = b ^ 2 := by linarith
    rw [h1, Real.sqrt_sq hb]
  · refine ⟨-Real.arccos a, ?_, ?_⟩
    · rw [Real.cos_neg]
      exact Real.cos_arccos ha.1 ha.2
    · rw [Real.sin_neg, Real.sin_arccos]
      have h1 : 1 - a ^ 2 = b ^ 2 := by linarith
      rw [h1, Real.sqrt_sq_eq_abs, abs_of_nonpos hb.le, neg_neg]


-- @@ L218-273 verbatim
theorem coreMap_eq_zero_iff_two_circles (x : E) :
    coreMap m hm x = 0 ↔
      x ∈ standardCircle ∨ x ∈ secondCircle m hm := by
  constructor
  · intro hx
    rcases plane_dichotomy_of_coreMap_eq_zero m hm hx with hz | hu
    · have hn := second_branch_normSq m hm hx hz
      obtain ⟨theta, hcos, hsin⟩ :=
        exists_angle_of_sq_add_sq_eq_one m hm hn
      right
      refine ⟨theta, ?_⟩
      apply PiLp.ext
      intro j
      by_cases hj0 : j = 0
      · subst j
        have h02 := fin_zero_ne_two m hm
        have h03 := fin_zero_ne_three m hm
        simp [hz.1, secondCircleAt_apply_other m hm theta h02 h03]
      · by_cases hj1 : j = 1
        · subst j
          have h12 := fin_one_ne_two m hm
          have h13 := fin_one_ne_three m hm
          simp [hz.2, secondCircleAt_apply_other m hm theta h12 h13]
        · by_cases hj2 : j = 2
          · subst j
            rw [secondCircleAt_apply_two, hcos]
          · by_cases hj3 : j = 3
            · subst j
              rw [secondCircleAt_apply_three, hsin]
            · rw [secondCircleAt_apply_other m hm theta hj2 hj3,
                coordinate_eq_zero_of_coreMap_eq_zero m hm hx hj0 hj1 hj2 hj3]
    · have hn := first_branch_normSq m hm hx hu
      obtain ⟨theta, hcos, hsin⟩ :=
        exists_angle_of_sq_add_sq_eq_one m hm hn
      left
      refine ⟨theta, ?_⟩
      apply PiLp.ext
      intro j
      by_cases hj0 : j = 0
      · subst j
        rw [circleAt_apply_zero, hcos]
      · by_cases hj1 : j = 1
        · subst j
          rw [circleAt_apply_one, hsin]
        · rw [circleAt_apply_other theta hj0 hj1]
          by_cases hj2 : j = 2
          · subst j
            exact hu.1.symm
          · by_cases hj3 : j = 3
            · subst j
              exact hu.2.symm
            · exact (coordinate_eq_zero_of_coreMap_eq_zero m hm hx
                hj0 hj1 hj2 hj3).symm
  · rintro (⟨theta, rfl⟩ | ⟨theta, rfl⟩)
    · exact coreMap_circleAt_eq_zero m hm theta
    · exact coreMap_secondCircleAt_eq_zero m hm theta


-- @@ L275-278 verbatim
theorem X_fiber_eq_two_circles :
    (X m hm).fiber = standardCircle ∪ secondCircle m hm := by
  ext x
  rw [mem_union, X_fiber, coreMap_eq_zero_iff_two_circles]


-- @@ L280-294 verbatim
theorem standardCircle_disjoint_secondCircle :
    Disjoint (standardCircle : Set E) (secondCircle m hm) := by
  rw [Set.disjoint_left]
  rintro x ⟨theta, rfl⟩ ⟨phi, hphi⟩
  have h2 := congrArg (fun q : E => q 2) hphi
  have h3 := congrArg (fun q : E => q 3) hphi
  rw [secondCircleAt_apply_two] at h2
  rw [secondCircleAt_apply_three] at h3
  have hc2 : circleAt (m := m) theta 2 = 0 :=
    circleAt_apply_other theta (fin_two_ne_zero m hm) (fin_two_ne_one m hm)
  have hc3 : circleAt (m := m) theta 3 = 0 :=
    circleAt_apply_other theta (fin_three_ne_zero m hm) (fin_three_ne_one m hm)
  rw [hc2] at h2
  rw [hc3] at h3
  nlinarith [Real.cos_sq_add_sin_sq phi]


-- @@ L296-296 verbatim
end CompactHopfPairConfiguration

-- @@ L297-297 verbatim
end Submission
