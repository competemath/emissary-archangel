import Mathlib
import Submission.CompactBirthConfiguration


-- @@ L4-21 verbatim
/-!
# A compact all-positive pair of class-zero candidate circles

The two components needed at the source of the residual saddle admit a much
simpler compact presentation than a compactified Cassini twist.  In four
distinguished spatial coordinates write `(z,u) ∈ ℂ²`.  The equations

`|z|² + |u|² = 1`, `z * conj(u) = 0`

cut out the two coordinate circles `u = 0` and `z = 0`.  Multiplication by the
nonzero coordinate supplies one normal-plane turn on each circle.  The total
pair is null, as required by spatial flatness.

This file records the analytic compactification checkpoint.  The radial row
uses the same positive-background blend as `CompactTubeConfiguration`; once
the Hopf rows vanish, a transition zero is impossible because the radial
equation is already positive in the cutoff annulus.
-/


-- @@ L23-23 verbatim
set_option autoImplicit false


-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
namespace Submission

-- @@ L28-28 verbatim
namespace CompactHopfPairConfiguration


-- @@ L30-30 verbatim
open Set Function Metric

-- @@ L31-31 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L33-33 verbatim
variable (m : ℕ) (hm : 0 < m)

-- @@ L34-34 verbatim
include hm


-- @@ L36-36 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 3))

-- @@ L37-37 verbatim
local notation "F" => EuclideanSpace ℝ (Fin (m + 2))


-- @@ L39-39 verbatim
def hopfRe (_hm : 0 < m) (x : E) : ℝ := x 0 * x 2 + x 1 * x 3


-- @@ L41-41 verbatim
def hopfIm (_hm : 0 < m) (x : E) : ℝ := x 1 * x 2 - x 0 * x 3


-- @@ L43-47 verbatim
lemma hopf_normSq (x : E) :
    hopfRe m hm x ^ 2 + hopfIm m hm x ^ 2 =
      (x 0 ^ 2 + x 1 ^ 2) * (x 2 ^ 2 + x 3 ^ 2) := by
  simp only [hopfRe, hopfIm]
  ring


-- @@ L49-53 verbatim
lemma contDiff_hopfRe : ContDiff ℝ ∞ (hopfRe m hm) := by
  exact ((EuclideanSpace.proj 0 : E →L[ℝ] ℝ).contDiff.mul
    (EuclideanSpace.proj 2 : E →L[ℝ] ℝ).contDiff).add
    ((EuclideanSpace.proj 1 : E →L[ℝ] ℝ).contDiff.mul
      (EuclideanSpace.proj 3 : E →L[ℝ] ℝ).contDiff)


-- @@ L55-59 verbatim
lemma contDiff_hopfIm : ContDiff ℝ ∞ (hopfIm m hm) := by
  exact ((EuclideanSpace.proj 1 : E →L[ℝ] ℝ).contDiff.mul
    (EuclideanSpace.proj 2 : E →L[ℝ] ℝ).contDiff).sub
    ((EuclideanSpace.proj 0 : E →L[ℝ] ℝ).contDiff.mul
      (EuclideanSpace.proj 3 : E →L[ℝ] ℝ).contDiff)


-- @@ L61-63 verbatim
/-- Positive last-value convention, placed in radial output row zero. -/
def background (_hm : 0 < m) : F :=
  WithLp.toLp 2 fun i => if i = 0 then 1 else 0


-- @@ L65-66 verbatim
@[simp] lemma background_apply_zero : background m hm 0 = 1 := by
  simp [background]


-- @@ L68-70 verbatim
@[simp] lemma background_apply_ne_zero {i : Fin (m + 2)} (hi : i ≠ 0) :
    background m hm i = 0 := by
  simp [background, hi]


-- @@ L72-75 verbatim
lemma background_ne_zero : background m hm ≠ 0 := by
  intro h
  have h0 := congrArg (fun q : F => q 0) h
  simp at h0


-- @@ L77-84 verbatim
/-- Polynomial Hopf-pair equation.  Rows at index at least three kill every
spatial coordinate beyond the four-coordinate Hopf block. -/
def coreMap (x : E) : F :=
  WithLp.toLp 2 fun i =>
    if i = 0 then (CompactBirth.normSq x - 1) / 2
    else if i = 1 then hopfRe m hm x
    else if i = 2 then hopfIm m hm x
    else x i.succ


-- @@ L86-88 verbatim
@[simp] lemma coreMap_apply_zero (x : E) :
    coreMap m hm x 0 = (CompactBirth.normSq x - 1) / 2 := by
  simp [coreMap]


-- @@ L90-92 verbatim
@[simp] lemma coreMap_apply_one (x : E) :
    coreMap m hm x 1 = hopfRe m hm x := by
  simp [coreMap]


-- @@ L94-105 verbatim
@[simp] lemma coreMap_apply_two (x : E) :
    coreMap m hm x 2 = hopfIm m hm x := by
  have hm2 : 2 < m + 2 := by omega
  have h20 : (2 : Fin (m + 2)) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt hm2] at hv
  have h21 : (2 : Fin (m + 2)) ≠ 1 := by
    intro h
    have hv := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt hm2] at hv
  simp [coreMap, h20, h21]


-- @@ L107-110 verbatim
lemma coreMap_apply_tail (x : E) {i : Fin (m + 2)}
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hi2 : i ≠ 2) :
    coreMap m hm x i = x i.succ := by
  simp [coreMap, hi0, hi1, hi2]


-- @@ L112-126 verbatim
lemma contDiff_coreMap : ContDiff ℝ ∞ (coreMap m hm) := by
  rw [contDiff_piLp]
  intro i
  by_cases hi0 : i = 0
  · subst i
    simpa only [coreMap_apply_zero] using
      (CompactBirth.contDiff_normSq.sub contDiff_const).div_const 2
  · by_cases hi1 : i = 1
    · subst i
      simpa only [coreMap_apply_one] using contDiff_hopfRe m hm
    · by_cases hi2 : i = 2
      · subst i
        simpa only [coreMap_apply_two] using contDiff_hopfIm m hm
      · simp only [coreMap_apply_tail m hm _ hi0 hi1 hi2]
        exact (EuclideanSpace.proj i.succ : E →L[ℝ] ℝ).contDiff


-- @@ L128-132 verbatim
/-- Compactification with the same radius-one/radius-two cutoff as compact
births and compact tubes. -/
def levelMap (x : E) : F :=
  (1 - CompactBirth.cutoff x) • coreMap m hm x +
    CompactBirth.cutoff x • background m hm


-- @@ L134-137 verbatim
lemma contDiff_levelMap : ContDiff ℝ ∞ (levelMap m hm) := by
  exact ((contDiff_const.sub CompactBirth.contDiff_cutoff).smul
    (contDiff_coreMap m hm)).add
    (CompactBirth.contDiff_cutoff.smul contDiff_const)


-- @@ L139-144 verbatim
@[simp] lemma levelMap_apply_zero (x : E) :
    levelMap m hm x 0 =
      (1 - CompactBirth.cutoff x) *
          ((CompactBirth.normSq x - 1) / 2) +
        CompactBirth.cutoff x := by
  simp [levelMap]


-- @@ L146-149 verbatim
lemma levelMap_apply_ne_zero (x : E) {i : Fin (m + 2)} (hi : i ≠ 0) :
    levelMap m hm x i =
      (1 - CompactBirth.cutoff x) * coreMap m hm x i := by
  simp [levelMap, hi]


-- @@ L151-156 verbatim
lemma cutoff_ne_one_of_levelMap_eq_zero {x : E}
    (hx : levelMap m hm x = 0) : CompactBirth.cutoff x ≠ 1 := by
  intro hc
  have h0 := congrArg (fun q : F => q 0) hx
  rw [levelMap_apply_zero, hc] at h0
  norm_num at h0


-- @@ L158-161 verbatim
lemma cutoff_lt_one_of_levelMap_eq_zero {x : E}
    (hx : levelMap m hm x = 0) : CompactBirth.cutoff x < 1 :=
  lt_of_le_of_ne (CompactBirth.cutoff_le_one x)
    (cutoff_ne_one_of_levelMap_eq_zero m hm hx)


-- @@ L163-178 verbatim
/-- There is no transition-annulus zero: the radial core row and the positive
background row have the same sign as soon as the squared norm reaches two. -/
lemma normSq_lt_two_of_levelMap_eq_zero {x : E}
    (hx : levelMap m hm x = 0) : CompactBirth.normSq x < 2 := by
  have hc_lt := cutoff_lt_one_of_levelMap_eq_zero m hm hx
  have hc0 := CompactBirth.cutoff_nonneg x
  have h0 := congrArg (fun q : F => q 0) hx
  rw [levelMap_apply_zero] at h0
  simp only [PiLp.zero_apply] at h0
  by_contra hnot
  have hn : 2 ≤ CompactBirth.normSq x := not_lt.mp hnot
  have hfac : 0 < 1 - CompactBirth.cutoff x := sub_pos.mpr hc_lt
  have hrad : 0 < (CompactBirth.normSq x - 1) / 2 := by linarith
  have hprod : 0 < (1 - CompactBirth.cutoff x) *
      ((CompactBirth.normSq x - 1) / 2) := mul_pos hfac hrad
  linarith


-- @@ L180-183 verbatim
lemma cutoff_eq_zero_of_levelMap_eq_zero {x : E}
    (hx : levelMap m hm x = 0) : CompactBirth.cutoff x = 0 :=
  CompactBirth.cutoff_eq_zero
    (normSq_lt_two_of_levelMap_eq_zero m hm hx).le


-- @@ L185-199 verbatim
/-- The compact blend introduces no zero at all. -/
theorem levelMap_eq_zero_iff_coreMap_eq_zero (x : E) :
    levelMap m hm x = 0 ↔ coreMap m hm x = 0 := by
  constructor
  · intro hx
    have hc := cutoff_eq_zero_of_levelMap_eq_zero m hm hx
    simpa [levelMap, hc] using hx
  · intro hx
    have h0 := congrArg (fun q : F => q 0) hx
    rw [coreMap_apply_zero] at h0
    simp only [PiLp.zero_apply] at h0
    have hn : CompactBirth.normSq x = 1 := by linarith
    have hc : CompactBirth.cutoff x = 0 :=
      CompactBirth.cutoff_eq_zero (by rw [hn]; norm_num)
    simp [levelMap, hc, hx]


-- @@ L201-206 verbatim
lemma normSq_eq_one_of_coreMap_eq_zero {x : E}
    (hx : coreMap m hm x = 0) : CompactBirth.normSq x = 1 := by
  have h0 := congrArg (fun q : F => q 0) hx
  rw [coreMap_apply_zero] at h0
  simp only [PiLp.zero_apply] at h0
  linarith


-- @@ L208-211 verbatim
lemma hopfRe_eq_zero_of_coreMap_eq_zero {x : E}
    (hx : coreMap m hm x = 0) : hopfRe m hm x = 0 := by
  have h := congrArg (fun q : F => q 1) hx
  simpa using h


-- @@ L213-216 verbatim
lemma hopfIm_eq_zero_of_coreMap_eq_zero {x : E}
    (hx : coreMap m hm x = 0) : hopfIm m hm x = 0 := by
  have h := congrArg (fun q : F => q 2) hx
  simpa using h


-- @@ L218-231 verbatim
/-- Hopf-product vanishing gives the two coordinate-plane branches. -/
lemma plane_dichotomy_of_coreMap_eq_zero {x : E}
    (hx : coreMap m hm x = 0) :
    (x 0 = 0 ∧ x 1 = 0) ∨ (x 2 = 0 ∧ x 3 = 0) := by
  have hre := hopfRe_eq_zero_of_coreMap_eq_zero m hm hx
  have him := hopfIm_eq_zero_of_coreMap_eq_zero m hm hx
  have hprod : (x 0 ^ 2 + x 1 ^ 2) * (x 2 ^ 2 + x 3 ^ 2) = 0 := by
    rw [← hopf_normSq m hm x, hre, him]
    norm_num
  rcases mul_eq_zero.mp hprod with hz | hu
  · left
    constructor <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  · right
    constructor <;> nlinarith [sq_nonneg (x 2), sq_nonneg (x 3)]


-- @@ L233-240 verbatim
/-- Literal common-background behavior outside the radius-two ball. -/
theorem levelMap_flatOutside {x : E} (hx : 2 ≤ ‖x‖) :
    levelMap m hm x = background m hm := by
  have hs : 4 ≤ CompactBirth.normSq x := by
    rw [CompactBirth.normSq_eq_norm_sq]
    nlinarith [norm_nonneg x]
  have hc := CompactBirth.cutoff_eq_one hs
  simp [levelMap, hc]


-- @@ L242-242 verbatim
end CompactHopfPairConfiguration

-- @@ L243-243 verbatim
end Submission
