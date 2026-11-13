import Submission.ConcreteZeroPairCassiniTwist
import Submission.StandardSaddleFrameWinding


-- @@ L4-14 verbatim
/-!
# Winding data of the zero-pair Cassini coefficient

This file isolates the endpoint calculation behind the `0,0 -> 1` frame
ledger.  On either incoming oval, `z² - 1` traverses the circle of radius
`sqrt (1/2)` once.  On the outgoing oval it never vanishes and is homotopic,
through the explicit family `z² - s`, to the twice-around polar loop `z²`.

The statements here concern only the complex coefficient.  Turning them into
an equality of intrinsic `frameAt` loops is a separate linear-algebra adapter.
-/


-- @@ L16-16 verbatim
set_option autoImplicit false


-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-20 verbatim
namespace Submission

-- @@ L21-21 verbatim
namespace ConcreteZeroPairCassiniWinding


-- @@ L23-23 verbatim
open Set Function

-- @@ L24-24 verbatim
open scoped Topology ContDiff RealInnerProductSpace unitInterval


-- @@ L26-26 verbatim
variable (m : ℕ)


-- @@ L28-28 verbatim
local notation "A" => EuclideanSpace ℝ (Fin (m + 4))

-- @@ L29-29 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 3))


-- @@ L31-31 verbatim
open ConcreteZeroPairCassiniTwist


-- @@ L33-40 verbatim
lemma twistRe_spaceTime_eq_spatial (x : E) (t : ℝ) :
    twistRe m (spaceTime x t) =
      x (StandardSaddle.planeFirst m) ^ 2 -
        x (StandardSaddle.planeSecond m) ^ 2 - 1 := by
  change
    initCLM (m + 3) (spaceTime x t) (StandardSaddle.planeFirst m) ^ 2 -
          initCLM (m + 3) (spaceTime x t) (StandardSaddle.planeSecond m) ^ 2 - 1 = _
  rw [initCLM_spaceTime]


-- @@ L42-49 verbatim
lemma twistIm_spaceTime_eq_spatial (x : E) (t : ℝ) :
    twistIm m (spaceTime x t) =
      2 * x (StandardSaddle.planeFirst m) *
        x (StandardSaddle.planeSecond m) := by
  change
    2 * initCLM (m + 3) (spaceTime x t) (StandardSaddle.planeFirst m) *
        initCLM (m + 3) (spaceTime x t) (StandardSaddle.planeSecond m) = _
  rw [initCLM_spaceTime]


-- @@ L51-54 verbatim
lemma transverseSq_eq_zero_of_standard_zero {v : A}
    (hv : StandardSaddle.eventMap m v = 0) :
    transverseSq m v = 0 := by
  simp [transverseSq, hv]


-- @@ L56-59 verbatim
lemma twistShift_eq_zero_of_standard_zero {v : A}
    (hv : StandardSaddle.eventMap m v = 0) :
    twistShift m v = 0 := by
  simp [twistShift, transverseSq_eq_zero_of_standard_zero m hv]


-- @@ L61-65 verbatim
lemma standard_eventMap_sourceRight_zero (theta : ℝ) :
    StandardSaddle.eventMap m
      (spaceTime (StandardSaddle.sourcePointRight m theta) 0) = 0 := by
  rw [StandardSaddle.eventMap_collar_zero m _ (by norm_num)]
  exact StandardSaddle.sourcePointRight_mem_source_fiber m theta


-- @@ L67-71 verbatim
lemma standard_eventMap_sourceLeft_zero (theta : ℝ) :
    StandardSaddle.eventMap m
      (spaceTime (StandardSaddle.sourcePointLeft m theta) 0) = 0 := by
  rw [StandardSaddle.eventMap_collar_zero m _ (by norm_num)]
  exact StandardSaddle.sourcePointLeft_mem_source_fiber m theta


-- @@ L73-77 verbatim
lemma standard_eventMap_target_zero (theta : ℝ) :
    StandardSaddle.eventMap m
      (spaceTime (StandardSaddle.targetPoint m theta) 1) = 0 := by
  rw [StandardSaddle.eventMap_collar_one m _ (by norm_num)]
  exact StandardSaddle.targetPoint_mem_target_fiber m theta


-- @@ L79-79 verbatim
/-! ## Incoming coefficient: exactly one turn -/


-- @@ L81-88 verbatim
theorem twistRe_sourceRight (theta : ℝ) :
    twistRe m (spaceTime (StandardSaddle.sourcePointRight m theta) 0) =
      StandardSaddle.sourceScale * Real.cos theta := by
  rw [twistRe_spaceTime_eq_spatial,
    StandardSaddle.sourcePointRight_apply_planeFirst,
    StandardSaddle.sourcePointRight_apply_planeSecond,
    StandardSaddle.sourceRoot_sq_sub_sq]
  simp [StandardSaddle.sourceRadicandFirst]


-- @@ L90-97 verbatim
theorem twistIm_sourceRight (theta : ℝ) :
    twistIm m (spaceTime (StandardSaddle.sourcePointRight m theta) 0) =
      StandardSaddle.sourceScale * Real.sin theta := by
  rw [twistIm_spaceTime_eq_spatial,
    StandardSaddle.sourcePointRight_apply_planeFirst,
    StandardSaddle.sourcePointRight_apply_planeSecond,
    StandardSaddle.two_mul_sourceRootFirst_mul_sourceRootSecond]
  rfl


-- @@ L99-106 verbatim
theorem twistRe_sourceLeft (theta : ℝ) :
    twistRe m (spaceTime (StandardSaddle.sourcePointLeft m theta) 0) =
      StandardSaddle.sourceScale * Real.cos theta := by
  rw [twistRe_spaceTime_eq_spatial,
    StandardSaddle.sourcePointLeft_apply_planeFirst,
    StandardSaddle.sourcePointLeft_apply_planeSecond]
  rw [neg_sq, neg_sq, StandardSaddle.sourceRoot_sq_sub_sq]
  simp [StandardSaddle.sourceRadicandFirst]


-- @@ L108-121 verbatim
theorem twistIm_sourceLeft (theta : ℝ) :
    twistIm m (spaceTime (StandardSaddle.sourcePointLeft m theta) 0) =
      StandardSaddle.sourceScale * Real.sin theta := by
  rw [twistIm_spaceTime_eq_spatial,
    StandardSaddle.sourcePointLeft_apply_planeFirst,
    StandardSaddle.sourcePointLeft_apply_planeSecond]
  calc
    2 * -StandardSaddle.sourceRootFirst theta *
          -StandardSaddle.sourceRootSecond theta =
        2 * StandardSaddle.sourceRootFirst theta *
          StandardSaddle.sourceRootSecond theta := by ring
    _ = StandardSaddle.sourceRadicandSecond theta :=
      StandardSaddle.two_mul_sourceRootFirst_mul_sourceRootSecond theta
    _ = StandardSaddle.sourceScale * Real.sin theta := rfl


-- @@ L123-126 verbatim
theorem twistShift_sourceRight (theta : ℝ) :
    twistShift m (spaceTime (StandardSaddle.sourcePointRight m theta) 0) = 0 :=
  twistShift_eq_zero_of_standard_zero m
    (standard_eventMap_sourceRight_zero m theta)


-- @@ L128-131 verbatim
theorem twistShift_sourceLeft (theta : ℝ) :
    twistShift m (spaceTime (StandardSaddle.sourcePointLeft m theta) 0) = 0 :=
  twistShift_eq_zero_of_standard_zero m
    (standard_eventMap_sourceLeft_zero m theta)


-- @@ L133-144 verbatim
theorem source_coefficient_normSq (theta : ℝ) :
    twistRe m (spaceTime (StandardSaddle.sourcePointRight m theta) 0) ^ 2 +
        twistIm m (spaceTime (StandardSaddle.sourcePointRight m theta) 0) ^ 2 =
      1 / 2 := by
  rw [twistRe_sourceRight, twistIm_sourceRight]
  calc
    (StandardSaddle.sourceScale * Real.cos theta) ^ 2 +
        (StandardSaddle.sourceScale * Real.sin theta) ^ 2 =
      StandardSaddle.sourceScale ^ 2 *
        (Real.cos theta ^ 2 + Real.sin theta ^ 2) := by ring
    _ = 1 / 2 := by
      rw [Real.cos_sq_add_sin_sq, mul_one, StandardSaddle.sourceScale_sq]


-- @@ L146-146 verbatim
/-! ## Outgoing coefficient and its explicit nonzero homotopy -/


-- @@ L148-151 verbatim
/-- The real part of `z² - s` along the outgoing polar parametrization. -/
def targetCoeffRe (s theta : ℝ) : ℝ :=
  StandardSaddle.targetRadius theta ^ 2 *
      (Real.cos theta ^ 2 - Real.sin theta ^ 2) - s


-- @@ L153-156 verbatim
/-- The imaginary part of `z² - s` along the outgoing polar parametrization. -/
def targetCoeffIm (theta : ℝ) : ℝ :=
  2 * StandardSaddle.targetRadius theta ^ 2 *
    Real.cos theta * Real.sin theta


-- @@ L158-165 verbatim
theorem twistRe_target (theta : ℝ) :
    twistRe m (spaceTime (StandardSaddle.targetPoint m theta) 1) =
      targetCoeffRe 1 theta := by
  rw [twistRe_spaceTime_eq_spatial,
    StandardSaddle.targetPoint_apply_planeFirst,
    StandardSaddle.targetPoint_apply_planeSecond]
  simp only [targetCoeffRe]
  ring


-- @@ L167-174 verbatim
theorem twistIm_target (theta : ℝ) :
    twistIm m (spaceTime (StandardSaddle.targetPoint m theta) 1) =
      targetCoeffIm theta := by
  rw [twistIm_spaceTime_eq_spatial,
    StandardSaddle.targetPoint_apply_planeFirst,
    StandardSaddle.targetPoint_apply_planeSecond]
  simp only [targetCoeffIm]
  ring


-- @@ L176-179 verbatim
theorem twistShift_target (theta : ℝ) :
    twistShift m (spaceTime (StandardSaddle.targetPoint m theta) 1) = 0 :=
  twistShift_eq_zero_of_standard_zero m
    (standard_eventMap_target_zero m theta)


-- @@ L181-181 verbatim
include m

-- @@ L182-189 verbatim
theorem target_coefficient_normSq (theta : ℝ) :
    targetCoeffRe 1 theta ^ 2 + targetCoeffIm theta ^ 2 = 3 / 2 := by
  have hnorm := ConcreteZeroPairCassiniTwist.twist_normSq m
    (spaceTime (StandardSaddle.targetPoint m theta) 1)
  rw [twistRe_target, twistIm_target, initCLM_spaceTime,
    StandardSaddle.cassiniQ_targetPoint] at hnorm
  norm_num at hnorm ⊢
  exact hnorm


-- @@ L191-197 verbatim
theorem target_coefficient_ne_zero (theta : ℝ) :
    targetCoeffRe 1 theta ≠ 0 ∨ targetCoeffIm theta ≠ 0 := by
  by_contra h
  push_neg at h
  have hnorm := target_coefficient_normSq m theta
  rw [h.1, h.2] at hnorm
  norm_num at hnorm


-- @@ L199-215 verbatim
/-- Along `z²-s`, `0 ≤ s ≤ 1` cannot hit zero on the outgoing Cassini oval.
Indeed a zero would have `z²=s`, whereas the endpoint equation forces
`|z²-1|²=3/2`, incompatible with `s∈[0,1]`. -/
theorem targetCoeff_ne_zero_during_homotopy {s theta : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    targetCoeffRe s theta ≠ 0 ∨ targetCoeffIm theta ≠ 0 := by
  by_contra h
  push_neg at h
  have hwSq : targetCoeffRe 1 theta ^ 2 + targetCoeffIm theta ^ 2 =
      (s - 1) ^ 2 := by
    have hre : targetCoeffRe 1 theta = s - 1 := by
      dsimp only [targetCoeffRe] at h ⊢
      linarith [h.1]
    rw [hre, h.2]
    ring
  rw [target_coefficient_normSq m theta] at hwSq
  nlinarith [sq_nonneg (s - 1)]


-- @@ L217-217 verbatim
end ConcreteZeroPairCassiniWinding

-- @@ L218-218 verbatim
end Submission
