import Submission.ConcreteZeroPairSaddle


-- @@ L3-22 verbatim
/-!
# The local singular-off-fiber Cassini twist

For positive stable range parameter `m`, the Cassini saddle has at least two
linear transverse output rows.  Write `z` for its Cassini-plane coordinate and
`w = z² - 1`.  Multiplication of the first two transverse rows by `w` adds one
normal-frame turn on each incoming oval and two turns on the outgoing oval.

A literal linear multiplication is singular at the two foci `w = 0`.  The
bounded nonlinear shift below removes the resulting unwanted zeros without
changing the derivative on the Cassini surface:

`u ↦ (w + |u|² / (2(1+|u|²))) u`.

Any nonzero extra root would force `|w| < 1/2`, whereas every Cassini event
slice has `|w|² ≥ 1/2`.  Thus the twisted map has exactly the old
pair-of-pants zero surface.  This file proves that analytic core directly.
Spatial compactification and the endpoint loop-class calculation are kept as
separate downstream steps.
-/


-- @@ L24-24 verbatim
set_option autoImplicit false


-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-28 verbatim
namespace Submission

-- @@ L29-29 verbatim
namespace ConcreteZeroPairCassiniTwist


-- @@ L31-31 verbatim
open Set Function

-- @@ L32-32 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L34-34 verbatim
variable (m : ℕ)


-- @@ L36-36 verbatim
local notation "A" => EuclideanSpace ℝ (Fin (m + 4))

-- @@ L37-37 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 3))

-- @@ L38-38 verbatim
local notation "F" => EuclideanSpace ℝ (Fin (m + 2))


-- @@ L40-41 verbatim
/-- First output row used by the transverse complex multiplication. -/
def rowZero : Fin (m + 2) := 0


-- @@ L43-44 verbatim
/-- Second output row used by the transverse complex multiplication. -/
def rowOne : Fin (m + 2) := 1


-- @@ L46-49 verbatim
/-- Real part of `z² - 1` on the Cassini plane. -/
def twistRe (v : A) : ℝ :=
  v (StandardSaddle.planeFirst m).castSucc ^ 2 -
    v (StandardSaddle.planeSecond m).castSucc ^ 2 - 1


-- @@ L51-54 verbatim
/-- Imaginary part of `z² - 1` on the Cassini plane. -/
def twistIm (v : A) : ℝ :=
  2 * v (StandardSaddle.planeFirst m).castSucc *
    v (StandardSaddle.planeSecond m).castSucc


-- @@ L56-59 verbatim
/-- Squared norm of the two selected rows of the original Cassini map. -/
def transverseSq (v : A) : ℝ :=
  StandardSaddle.eventMap m v (rowZero m) ^ 2 +
    StandardSaddle.eventMap m v (rowOne m) ^ 2


-- @@ L61-64 verbatim
/-- A bounded nonnegative desingularizing shift.  It vanishes to second order
on the original zero surface and is always strictly less than `1/2`. -/
def twistShift (v : A) : ℝ :=
  transverseSq m v / (2 * (1 + transverseSq m v))


-- @@ L66-67 verbatim
lemma transverseSq_nonneg (v : A) : 0 ≤ transverseSq m v := by
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)


-- @@ L69-71 verbatim
lemma twistShift_nonneg (v : A) : 0 ≤ twistShift m v := by
  have hr := transverseSq_nonneg m v
  exact div_nonneg hr (by positivity)


-- @@ L73-77 verbatim
lemma twistShift_lt_half (v : A) : twistShift m v < 1 / 2 := by
  have hr := transverseSq_nonneg m v
  have hden : 0 < 2 * (1 + transverseSq m v) := by positivity
  rw [twistShift, div_lt_iff₀ hden]
  linarith


-- @@ L79-91 verbatim
/-- The singular-off-fiber twist of the polynomial Cassini event map. -/
def eventMap (v : A) : F :=
  WithLp.toLp 2 fun i =>
    if i = rowZero m then
      (twistRe m v + twistShift m v) *
          StandardSaddle.eventMap m v (rowZero m) -
        twistIm m v * StandardSaddle.eventMap m v (rowOne m)
    else if i = rowOne m then
      twistIm m v * StandardSaddle.eventMap m v (rowZero m) +
        (twistRe m v + twistShift m v) *
          StandardSaddle.eventMap m v (rowOne m)
    else
      StandardSaddle.eventMap m v i


-- @@ L93-98 verbatim
@[simp] lemma eventMap_apply_rowZero (v : A) :
    eventMap m v (rowZero m) =
      (twistRe m v + twistShift m v) *
          StandardSaddle.eventMap m v (rowZero m) -
        twistIm m v * StandardSaddle.eventMap m v (rowOne m) := by
  simp [eventMap, rowZero, rowOne]


-- @@ L100-105 verbatim
@[simp] lemma eventMap_apply_rowOne (v : A) :
    eventMap m v (rowOne m) =
      twistIm m v * StandardSaddle.eventMap m v (rowZero m) +
        (twistRe m v + twistShift m v) *
          StandardSaddle.eventMap m v (rowOne m) := by
  simp [eventMap, rowZero, rowOne]


-- @@ L107-110 verbatim
lemma eventMap_apply_of_ne {i : Fin (m + 2)}
    (hi₀ : i ≠ rowZero m) (hi₁ : i ≠ rowOne m) (v : A) :
    eventMap m v i = StandardSaddle.eventMap m v i := by
  simp [eventMap, hi₀, hi₁]


-- @@ L112-118 verbatim
lemma twist_normSq (v : A) :
    twistRe m v ^ 2 + twistIm m v ^ 2 =
      StandardSaddle.cassiniQ m (initCLM (m + 3) v) + 1 := by
  rw [StandardSaddle.cassiniQ_eq]
  simp only [StandardSaddle.radiusSq, initCLM_apply]
  simp only [twistRe, twistIm]
  ring


-- @@ L120-125 verbatim
lemma contDiff_twistRe : ContDiff ℝ ∞ (twistRe m) := by
  exact ((((EuclideanSpace.proj
      (StandardSaddle.planeFirst m).castSucc : A →L[ℝ] ℝ).contDiff.pow 2).sub
    ((EuclideanSpace.proj
      (StandardSaddle.planeSecond m).castSucc : A →L[ℝ] ℝ).contDiff.pow 2)).sub
    contDiff_const)


-- @@ L127-132 verbatim
lemma contDiff_twistIm : ContDiff ℝ ∞ (twistIm m) := by
  exact (contDiff_const.mul
    ((EuclideanSpace.proj
      (StandardSaddle.planeFirst m).castSucc : A →L[ℝ] ℝ).contDiff)).mul
    ((EuclideanSpace.proj
      (StandardSaddle.planeSecond m).castSucc : A →L[ℝ] ℝ).contDiff)


-- @@ L134-137 verbatim
lemma contDiff_eventMap_coord (i : Fin (m + 2)) :
    ContDiff ℝ ∞ (fun v => StandardSaddle.eventMap m v i) := by
  exact (EuclideanSpace.proj i : F →L[ℝ] ℝ).contDiff.comp
    (StandardSaddle.contDiff_eventMap m)


-- @@ L139-141 verbatim
lemma contDiff_transverseSq : ContDiff ℝ ∞ (transverseSq m) := by
  exact ((contDiff_eventMap_coord m (rowZero m)).pow 2).add
    ((contDiff_eventMap_coord m (rowOne m)).pow 2)


-- @@ L143-146 verbatim
lemma one_add_transverseSq_ne_zero (v : A) :
    1 + transverseSq m v ≠ 0 := by
  have hr := transverseSq_nonneg m v
  linarith


-- @@ L148-154 verbatim
lemma contDiff_twistShift : ContDiff ℝ ∞ (twistShift m) := by
  have hden : ContDiff ℝ ∞ (fun v : A => 2 * (1 + transverseSq m v)) :=
    contDiff_const.mul (contDiff_const.add (contDiff_transverseSq m))
  have hden0 : ∀ v : A, 2 * (1 + transverseSq m v) ≠ 0 := by
    intro v
    exact mul_ne_zero (by norm_num) (one_add_transverseSq_ne_zero m v)
  exact (contDiff_transverseSq m).div hden hden0


-- @@ L156-173 verbatim
theorem contDiff_eventMap : ContDiff ℝ ∞ (eventMap m) := by
  rw [contDiff_piLp]
  intro i
  by_cases hi₀ : i = rowZero m
  · subst i
    simp only [eventMap_apply_rowZero]
    exact ((contDiff_twistRe m).add (contDiff_twistShift m)).mul
        (contDiff_eventMap_coord m (rowZero m)) |>.sub
      ((contDiff_twistIm m).mul (contDiff_eventMap_coord m (rowOne m)))
  · by_cases hi₁ : i = rowOne m
    · subst i
      simp only [eventMap_apply_rowOne]
      exact (contDiff_twistIm m).mul
          (contDiff_eventMap_coord m (rowZero m)) |>.add
        (((contDiff_twistRe m).add (contDiff_twistShift m)).mul
          (contDiff_eventMap_coord m (rowOne m)))
    · simpa only [eventMap_apply_of_ne m hi₀ hi₁] using
        contDiff_eventMap_coord m i


-- @@ L175-175 verbatim
/-! ## Exact time collars -/


-- @@ L177-184 verbatim
lemma twistRe_spaceTime (x : E) (t s : ℝ) :
    twistRe m (spaceTime x t) = twistRe m (spaceTime x s) := by
  change
    initCLM (m + 3) (spaceTime x t) (StandardSaddle.planeFirst m) ^ 2 -
          initCLM (m + 3) (spaceTime x t) (StandardSaddle.planeSecond m) ^ 2 - 1 =
      initCLM (m + 3) (spaceTime x s) (StandardSaddle.planeFirst m) ^ 2 -
          initCLM (m + 3) (spaceTime x s) (StandardSaddle.planeSecond m) ^ 2 - 1
  rw [initCLM_spaceTime, initCLM_spaceTime]


-- @@ L186-193 verbatim
lemma twistIm_spaceTime (x : E) (t s : ℝ) :
    twistIm m (spaceTime x t) = twistIm m (spaceTime x s) := by
  change
    2 * initCLM (m + 3) (spaceTime x t) (StandardSaddle.planeFirst m) *
          initCLM (m + 3) (spaceTime x t) (StandardSaddle.planeSecond m) =
      2 * initCLM (m + 3) (spaceTime x s) (StandardSaddle.planeFirst m) *
          initCLM (m + 3) (spaceTime x s) (StandardSaddle.planeSecond m)
  rw [initCLM_spaceTime, initCLM_spaceTime]


-- @@ L195-199 verbatim
lemma transverseSq_spaceTime_eq_of_standard_eq (x : E) (t s : ℝ)
    (hstd : StandardSaddle.eventMap m (spaceTime x t) =
      StandardSaddle.eventMap m (spaceTime x s)) :
    transverseSq m (spaceTime x t) = transverseSq m (spaceTime x s) := by
  simp only [transverseSq, hstd]


-- @@ L201-206 verbatim
lemma twistShift_spaceTime_eq_of_standard_eq (x : E) (t s : ℝ)
    (hstd : StandardSaddle.eventMap m (spaceTime x t) =
      StandardSaddle.eventMap m (spaceTime x s)) :
    twistShift m (spaceTime x t) = twistShift m (spaceTime x s) := by
  simp only [twistShift,
    transverseSq_spaceTime_eq_of_standard_eq m x t s hstd]


-- @@ L208-223 verbatim
lemma eventMap_spaceTime_eq_of_standard_eq (x : E) (t s : ℝ)
    (hstd : StandardSaddle.eventMap m (spaceTime x t) =
      StandardSaddle.eventMap m (spaceTime x s)) :
    eventMap m (spaceTime x t) = eventMap m (spaceTime x s) := by
  have hre := twistRe_spaceTime m x t s
  have him := twistIm_spaceTime m x t s
  have hshift := twistShift_spaceTime_eq_of_standard_eq m x t s hstd
  ext i
  by_cases hi₀ : i = rowZero m
  · subst i
    simp only [eventMap_apply_rowZero, hre, him, hshift, hstd]
  · by_cases hi₁ : i = rowOne m
    · subst i
      simp only [eventMap_apply_rowOne, hre, him, hshift, hstd]
    · rw [eventMap_apply_of_ne m hi₀ hi₁,
        eventMap_apply_of_ne m hi₀ hi₁, hstd]


-- @@ L225-229 verbatim
lemma eventMap_collar_zero (x : E) {t : ℝ} (ht : t ≤ 1 / 4) :
    eventMap m (spaceTime x t) = eventMap m (spaceTime x 0) := by
  apply eventMap_spaceTime_eq_of_standard_eq m x t 0
  rw [StandardSaddle.eventMap_collar_zero m x ht,
    StandardSaddle.eventMap_collar_zero m x (by norm_num)]


-- @@ L231-235 verbatim
lemma eventMap_collar_one (x : E) {t : ℝ} (ht : 3 / 4 ≤ t) :
    eventMap m (spaceTime x t) = eventMap m (spaceTime x 1) := by
  apply eventMap_spaceTime_eq_of_standard_eq m x t 1
  rw [StandardSaddle.eventMap_collar_one m x ht,
    StandardSaddle.eventMap_collar_one m x (by norm_num)]


-- @@ L237-263 verbatim
/-- At a zero of the twisted map, the unchanged Cassini row forces
`|z²-1|² ≥ 1/2`. -/
lemma twist_normSq_ge_half_of_eventMap_eq_zero
    (hm : 0 < m) {v : A} (hv : eventMap m v = 0) :
    1 / 2 ≤ twistRe m v ^ 2 + twistIm m v ^ 2 := by
  let ilast : Fin (m + 2) := Fin.last (m + 1)
  have hilast₀ : ilast ≠ rowZero m := by
    intro h
    have := congrArg Fin.val h
    simp [ilast, rowZero] at this
  have hilast₁ : ilast ≠ rowOne m := by
    intro h
    have := congrArg Fin.val h
    simp [ilast, rowOne] at this
    omega
  have hlast : StandardSaddle.eventMap m v ilast = 0 := by
    have h := congrArg (fun q : F => q ilast) hv
    rw [eventMap_apply_of_ne m hilast₀ hilast₁] at h
    simpa using h
  have hq : StandardSaddle.cassiniQ m (initCLM (m + 3) v) =
      StandardSaddle.height (vertC v) / 2 := by
    have h := hlast
    simp [ilast, StandardSaddle.eventMap] at h
    linarith
  rw [twist_normSq, hq]
  have hheight := StandardSaddle.neg_one_le_height (vertC v)
  linarith


-- @@ L265-286 verbatim
/-- The shifted complex coefficient is nonzero at every zero of the twisted
event map. -/
lemma twistCoefficient_normSq_pos_of_eventMap_eq_zero
    (hm : 0 < m) {v : A} (hv : eventMap m v = 0) :
    0 < (twistRe m v + twistShift m v) ^ 2 + twistIm m v ^ 2 := by
  have hlarge := twist_normSq_ge_half_of_eventMap_eq_zero m hm hv
  have hs₀ := twistShift_nonneg m v
  have hs₁ := twistShift_lt_half m v
  have hnonneg : 0 ≤
      (twistRe m v + twistShift m v) ^ 2 + twistIm m v ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  refine lt_of_le_of_ne hnonneg ?_
  intro hzero
  have ha : twistRe m v + twistShift m v = 0 := by
    nlinarith [sq_nonneg (twistRe m v + twistShift m v),
      sq_nonneg (twistIm m v)]
  have hb : twistIm m v = 0 := by
    nlinarith [sq_nonneg (twistRe m v + twistShift m v),
      sq_nonneg (twistIm m v)]
  have hre : twistRe m v = -twistShift m v := by linarith
  rw [hre, hb] at hlarge
  nlinarith


-- @@ L288-342 verbatim
/-- **Exact local analytic result.**  In the stable range `m > 0`, the
singular-off-fiber twist introduces no new point of the Cassini event surface
and removes none. -/
theorem eventMap_eq_zero_iff (hm : 0 < m) (v : A) :
    eventMap m v = 0 ↔ StandardSaddle.eventMap m v = 0 := by
  constructor
  · intro hv
    let a := twistRe m v + twistShift m v
    let b := twistIm m v
    let u := StandardSaddle.eventMap m v (rowZero m)
    let w := StandardSaddle.eventMap m v (rowOne m)
    have h₀ : a * u - b * w = 0 := by
      have h := congrArg (fun q : F => q (rowZero m)) hv
      simpa [a, b, u, w] using h
    have h₁ : b * u + a * w = 0 := by
      have h := congrArg (fun q : F => q (rowOne m)) hv
      simpa [a, b, u, w] using h
    have hdet : 0 < a ^ 2 + b ^ 2 := by
      simpa [a, b] using
        twistCoefficient_normSq_pos_of_eventMap_eq_zero m hm hv
    have huProd : (a ^ 2 + b ^ 2) * u = 0 := by
      calc
        (a ^ 2 + b ^ 2) * u = a * (a * u - b * w) +
            b * (b * u + a * w) := by ring
        _ = 0 := by rw [h₀, h₁]; ring
    have hwProd : (a ^ 2 + b ^ 2) * w = 0 := by
      calc
        (a ^ 2 + b ^ 2) * w = -b * (a * u - b * w) +
            a * (b * u + a * w) := by ring
        _ = 0 := by rw [h₀, h₁]; ring
    have hu : u = 0 :=
      (mul_eq_zero.mp huProd).resolve_left hdet.ne'
    have hw : w = 0 :=
      (mul_eq_zero.mp hwProd).resolve_left hdet.ne'
    apply (WithLp.equiv 2 _).injective
    funext i
    by_cases hi₀ : i = rowZero m
    · subst i
      simpa [u] using hu
    · by_cases hi₁ : i = rowOne m
      · subst i
        simpa [w] using hw
      · have hi := congrArg (fun q : F => q i) hv
        rw [eventMap_apply_of_ne m hi₀ hi₁] at hi
        simpa using hi
  · intro hv
    ext i
    by_cases hi₀ : i = rowZero m
    · subst i
      simp [hv]
    · by_cases hi₁ : i = rowOne m
      · subst i
        simp [hv]
      · rw [eventMap_apply_of_ne m hi₀ hi₁]
        simpa using congrArg (fun q : F => q i) hv


-- @@ L344-344 verbatim
/-! ## Differential on the unchanged Cassini surface -/


-- @@ L346-357 verbatim
private lemma fderiv_coord_apply
    (G : A → F) (hG : ContDiff ℝ ∞ G)
    (i : Fin (m + 2)) (v h : A) :
    fderiv ℝ (fun q => G q i) v h = fderiv ℝ G v h i := by
  let outProj : F →L[ℝ] ℝ := EuclideanSpace.proj i
  have hG' : HasFDerivAt G (fderiv ℝ G v) v :=
    (hG.differentiable infty_ne_zero v).hasFDerivAt
  have hcomp : HasFDerivAt (fun q => G q i)
      (outProj.comp (fderiv ℝ G v)) v := by
    exact (PiLp.hasFDerivAt_apply 2 (G v) i).comp v hG'
  have happ := congrArg (fun L : A →L[ℝ] ℝ => L h) hcomp.fderiv
  simpa [outProj] using happ


-- @@ L359-407 verbatim
lemma fderiv_eventMap_apply_rowZero_of_standard_zero
    {v : A} (hv : StandardSaddle.eventMap m v = 0) (h : A) :
    fderiv ℝ (eventMap m) v h (rowZero m) =
      (twistRe m v + twistShift m v) *
          fderiv ℝ (StandardSaddle.eventMap m) v h (rowZero m) -
        twistIm m v *
          fderiv ℝ (StandardSaddle.eventMap m) v h (rowOne m) := by
  let aa : A → ℝ := fun q => twistRe m q + twistShift m q
  let bb : A → ℝ := twistIm m
  let g₀ : A → ℝ := fun q => StandardSaddle.eventMap m q (rowZero m)
  let g₁ : A → ℝ := fun q => StandardSaddle.eventMap m q (rowOne m)
  have haa : DifferentiableAt ℝ aa v :=
    (((contDiff_twistRe m).add (contDiff_twistShift m)).differentiable
      infty_ne_zero).differentiableAt
  have hbb : DifferentiableAt ℝ bb v :=
    ((contDiff_twistIm m).differentiable infty_ne_zero).differentiableAt
  have hg₀ : DifferentiableAt ℝ g₀ v :=
    ((contDiff_eventMap_coord m (rowZero m)).differentiable
      infty_ne_zero).differentiableAt
  have hg₁ : DifferentiableAt ℝ g₁ v :=
    ((contDiff_eventMap_coord m (rowOne m)).differentiable
      infty_ne_zero).differentiableAt
  have hg₀v : g₀ v = 0 := by
    simpa [g₀] using congrArg (fun q : F => q (rowZero m)) hv
  have hg₁v : g₁ v = 0 := by
    simpa [g₁] using congrArg (fun q : F => q (rowOne m)) hv
  rw [← fderiv_coord_apply m (eventMap m) (contDiff_eventMap m)
    (rowZero m) v h]
  have hfun : (fun q => eventMap m q (rowZero m)) =
      fun q => aa q • g₀ q - bb q • g₁ q := by
    funext q
    simp [aa, bb, g₀, g₁, smul_eq_mul]
  rw [hfun]
  change (fderiv ℝ
    (fun q => aa q • g₀ q - bb q • g₁ q) v) h = _
  have hd₀ : DifferentiableAt ℝ (fun q => aa q • g₀ q) v :=
    haa.smul hg₀
  have hd₁ : DifferentiableAt ℝ (fun q => bb q • g₁ q) v :=
    hbb.smul hg₁
  rw [fderiv_fun_sub hd₀ hd₁,
    fderiv_fun_smul haa hg₀, fderiv_fun_smul hbb hg₁]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    hg₀v, hg₁v, smul_zero, add_zero]
  rw [fderiv_coord_apply m (StandardSaddle.eventMap m)
    (StandardSaddle.contDiff_eventMap m) (rowZero m) v h,
    fderiv_coord_apply m (StandardSaddle.eventMap m)
      (StandardSaddle.contDiff_eventMap m) (rowOne m) v h]
  rfl


-- @@ L409-457 verbatim
lemma fderiv_eventMap_apply_rowOne_of_standard_zero
    {v : A} (hv : StandardSaddle.eventMap m v = 0) (h : A) :
    fderiv ℝ (eventMap m) v h (rowOne m) =
      twistIm m v *
          fderiv ℝ (StandardSaddle.eventMap m) v h (rowZero m) +
        (twistRe m v + twistShift m v) *
          fderiv ℝ (StandardSaddle.eventMap m) v h (rowOne m) := by
  let aa : A → ℝ := fun q => twistRe m q + twistShift m q
  let bb : A → ℝ := twistIm m
  let g₀ : A → ℝ := fun q => StandardSaddle.eventMap m q (rowZero m)
  let g₁ : A → ℝ := fun q => StandardSaddle.eventMap m q (rowOne m)
  have haa : DifferentiableAt ℝ aa v :=
    (((contDiff_twistRe m).add (contDiff_twistShift m)).differentiable
      infty_ne_zero).differentiableAt
  have hbb : DifferentiableAt ℝ bb v :=
    ((contDiff_twistIm m).differentiable infty_ne_zero).differentiableAt
  have hg₀ : DifferentiableAt ℝ g₀ v :=
    ((contDiff_eventMap_coord m (rowZero m)).differentiable
      infty_ne_zero).differentiableAt
  have hg₁ : DifferentiableAt ℝ g₁ v :=
    ((contDiff_eventMap_coord m (rowOne m)).differentiable
      infty_ne_zero).differentiableAt
  have hg₀v : g₀ v = 0 := by
    simpa [g₀] using congrArg (fun q : F => q (rowZero m)) hv
  have hg₁v : g₁ v = 0 := by
    simpa [g₁] using congrArg (fun q : F => q (rowOne m)) hv
  rw [← fderiv_coord_apply m (eventMap m) (contDiff_eventMap m)
    (rowOne m) v h]
  have hfun : (fun q => eventMap m q (rowOne m)) =
      fun q => bb q • g₀ q + aa q • g₁ q := by
    funext q
    simp [aa, bb, g₀, g₁, smul_eq_mul]
  rw [hfun]
  change (fderiv ℝ
    (fun q => bb q • g₀ q + aa q • g₁ q) v) h = _
  have hd₀ : DifferentiableAt ℝ (fun q => bb q • g₀ q) v :=
    hbb.smul hg₀
  have hd₁ : DifferentiableAt ℝ (fun q => aa q • g₁ q) v :=
    haa.smul hg₁
  rw [fderiv_fun_add hd₀ hd₁,
    fderiv_fun_smul hbb hg₀, fderiv_fun_smul haa hg₁]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, hg₀v, hg₁v, smul_zero,
    add_zero]
  rw [fderiv_coord_apply m (StandardSaddle.eventMap m)
    (StandardSaddle.contDiff_eventMap m) (rowZero m) v h,
    fderiv_coord_apply m (StandardSaddle.eventMap m)
      (StandardSaddle.contDiff_eventMap m) (rowOne m) v h]
  rfl


-- @@ L459-469 verbatim
lemma fderiv_eventMap_apply_of_ne {i : Fin (m + 2)}
    (hi₀ : i ≠ rowZero m) (hi₁ : i ≠ rowOne m) (v h : A) :
    fderiv ℝ (eventMap m) v h i =
      fderiv ℝ (StandardSaddle.eventMap m) v h i := by
  have hfun : (fun q => eventMap m q i) =
      fun q => StandardSaddle.eventMap m q i := by
    funext q
    exact eventMap_apply_of_ne m hi₀ hi₁ q
  rw [← fderiv_coord_apply m (eventMap m) (contDiff_eventMap m) i v h,
    ← fderiv_coord_apply m (StandardSaddle.eventMap m)
      (StandardSaddle.contDiff_eventMap m) i v h, hfun]


-- @@ L471-479 verbatim
/-- Inverse of the two-row complex coefficient, leaving all other target
coordinates unchanged. -/
def untwistTarget (a b : ℝ) (y : F) : F :=
  WithLp.toLp 2 fun i =>
    if i = rowZero m then
      (a * y (rowZero m) + b * y (rowOne m)) / (a ^ 2 + b ^ 2)
    else if i = rowOne m then
      (-b * y (rowZero m) + a * y (rowOne m)) / (a ^ 2 + b ^ 2)
    else y i


-- @@ L481-484 verbatim
@[simp] lemma untwistTarget_apply_rowZero (a b : ℝ) (y : F) :
    untwistTarget m a b y (rowZero m) =
      (a * y (rowZero m) + b * y (rowOne m)) / (a ^ 2 + b ^ 2) := by
  simp [untwistTarget, rowZero, rowOne]


-- @@ L486-489 verbatim
@[simp] lemma untwistTarget_apply_rowOne (a b : ℝ) (y : F) :
    untwistTarget m a b y (rowOne m) =
      (-b * y (rowZero m) + a * y (rowOne m)) / (a ^ 2 + b ^ 2) := by
  simp [untwistTarget, rowZero, rowOne]


-- @@ L491-494 verbatim
lemma untwistTarget_apply_of_ne {i : Fin (m + 2)}
    (hi₀ : i ≠ rowZero m) (hi₁ : i ≠ rowOne m) (a b : ℝ) (y : F) :
    untwistTarget m a b y i = y i := by
  simp [untwistTarget, hi₀, hi₁]


-- @@ L496-537 verbatim
/-- The local twisted Cassini map is a submersion on its exact zero surface. -/
theorem eventMap_regular (hm : 0 < m) {v : A} (hv : eventMap m v = 0) :
    Function.Surjective (fderiv ℝ (eventMap m) v) := by
  have hvStd : StandardSaddle.eventMap m v = 0 :=
    (eventMap_eq_zero_iff m hm v).mp hv
  let a := twistRe m v + twistShift m v
  let b := twistIm m v
  have hdet : 0 < a ^ 2 + b ^ 2 := by
    simpa [a, b] using
      twistCoefficient_normSq_pos_of_eventMap_eq_zero m hm hv
  intro y
  obtain ⟨h, hh⟩ := StandardSaddle.eventMap_regular m v hvStd
    (untwistTarget m a b y)
  refine ⟨h, ?_⟩
  ext i
  by_cases hi₀ : i = rowZero m
  · subst i
    have hh₀ := congrArg (fun q : F => q (rowZero m)) hh
    have hh₁ := congrArg (fun q : F => q (rowOne m)) hh
    rw [fderiv_eventMap_apply_rowZero_of_standard_zero m hvStd h, hh₀, hh₁,
      untwistTarget_apply_rowZero, untwistTarget_apply_rowOne]
    change a * ((a * y (rowZero m) + b * y (rowOne m)) /
          (a ^ 2 + b ^ 2)) -
        b * ((-b * y (rowZero m) + a * y (rowOne m)) /
          (a ^ 2 + b ^ 2)) = y (rowZero m)
    field_simp [hdet.ne']
    ring
  · by_cases hi₁ : i = rowOne m
    · subst i
      have hh₀ := congrArg (fun q : F => q (rowZero m)) hh
      have hh₁ := congrArg (fun q : F => q (rowOne m)) hh
      rw [fderiv_eventMap_apply_rowOne_of_standard_zero m hvStd h, hh₀, hh₁,
        untwistTarget_apply_rowZero, untwistTarget_apply_rowOne]
      change b * ((a * y (rowZero m) + b * y (rowOne m)) /
            (a ^ 2 + b ^ 2)) +
          a * ((-b * y (rowZero m) + a * y (rowOne m)) /
            (a ^ 2 + b ^ 2)) = y (rowOne m)
      field_simp [hdet.ne']
      ring
    · have hhi := congrArg (fun q : F => q i) hh
      rw [fderiv_eventMap_apply_of_ne m hi₀ hi₁ v h, hhi,
        untwistTarget_apply_of_ne m hi₀ hi₁]


-- @@ L539-539 verbatim
/-! ## The uncompactified framed Cassini cobordism -/


-- @@ L541-543 verbatim
/-- Incoming fixed-time presentation of the twisted Cassini map. -/
def sourceLevelMap (x : E) : F :=
  eventMap m (spaceTime x 0)


-- @@ L545-547 verbatim
/-- Outgoing fixed-time presentation of the twisted Cassini map. -/
def targetLevelMap (x : E) : F :=
  eventMap m (spaceTime x 1)


-- @@ L549-556 verbatim
private lemma contDiff_spaceTime_fixed (t : ℝ) :
    ContDiff ℝ ∞ (fun x : E => spaceTime x t) := by
  have heq : (fun x : E => spaceTime x t) =
      fun x => embedCLM (m + 3) x + t • eLast (m + 3) := by
    funext x
    exact spaceTime_eq_affine x t
  rw [heq]
  exact (embedCLM (m + 3)).contDiff.add contDiff_const


-- @@ L558-559 verbatim
lemma contDiff_sourceLevelMap : ContDiff ℝ ∞ (sourceLevelMap m) :=
  (contDiff_eventMap m).comp (contDiff_spaceTime_fixed m 0)


-- @@ L561-562 verbatim
lemma contDiff_targetLevelMap : ContDiff ℝ ∞ (targetLevelMap m) :=
  (contDiff_eventMap m).comp (contDiff_spaceTime_fixed m 1)


-- @@ L564-568 verbatim
lemma sourceLevelMap_zero_iff (hm : 0 < m) (x : E) :
    sourceLevelMap m x = 0 ↔ (StandardSaddle.sourceFLS m).g x = 0 := by
  rw [sourceLevelMap, eventMap_eq_zero_iff m hm,
    StandardSaddle.eventMap_collar_zero m x (by norm_num)]
  rfl


-- @@ L570-574 verbatim
lemma targetLevelMap_zero_iff (hm : 0 < m) (x : E) :
    targetLevelMap m x = 0 ↔ (StandardSaddle.targetFLS m).g x = 0 := by
  rw [targetLevelMap, eventMap_eq_zero_iff m hm,
    StandardSaddle.eventMap_collar_one m x (by norm_num)]
  rfl


-- @@ L576-617 verbatim
/-- The incoming two-oval Cassini fiber with the twisted normal framing. -/
def sourceFLS (hm : 0 < m) : FramedLevelSet (m + 2) where
  g := sourceLevelMap m
  smooth := contDiff_sourceLevelMap m
  fiber_bounded := by
    rw [show {x : E | sourceLevelMap m x = 0} =
        (StandardSaddle.sourceFLS m).fiber by
      ext x
      exact sourceLevelMap_zero_iff m hm x]
    exact (StandardSaddle.sourceFLS m).fiber_bounded
  regular := by
    intro x hx
    let v : A := spaceTime x 0
    have hv : eventMap m v = 0 := by
      simpa [v, sourceLevelMap] using hx
    have hsurj : Function.Surjective (fderiv ℝ (eventMap m) v) :=
      eventMap_regular m hm hv
    have htime : vertC v < 1 / 4 := by
      dsimp [v]
      rw [vertC_spaceTime]
      norm_num
    have hEv : eventMap m =ᶠ[𝓝 v]
        fun w => sourceLevelMap m (initCLM (m + 3) w) := by
      apply Filter.eventuallyEq_of_mem ((isOpen_vert_lt (1 / 4)).mem_nhds htime)
      intro w hw
      conv_lhs => rw [← spaceTime_init_vert w]
      exact eventMap_collar_zero m _ hw.le
    have hsource : HasFDerivAt (sourceLevelMap m)
        (fderiv ℝ (sourceLevelMap m) x) x :=
      ((contDiff_sourceLevelMap m).differentiable infty_ne_zero x).hasFDerivAt
    have hcomp : fderiv ℝ (eventMap m) v =
        (fderiv ℝ (sourceLevelMap m) x).comp (initCLM (m + 3)) := by
      rw [hEv.fderiv_eq]
      have hvx : initCLM (m + 3) v = x := by
        dsimp [v]
        rw [initCLM_spaceTime]
      have hsourcev : HasFDerivAt (sourceLevelMap m)
          (fderiv ℝ (sourceLevelMap m) x) (initCLM (m + 3) v) := by
        simpa [hvx] using hsource
      exact (hsourcev.comp v (initCLM (m + 3)).hasFDerivAt).fderiv
    rw [hcomp, ContinuousLinearMap.coe_comp] at hsurj
    exact hsurj.of_comp


-- @@ L619-660 verbatim
/-- The outgoing one-oval Cassini fiber with the twisted normal framing. -/
def targetFLS (hm : 0 < m) : FramedLevelSet (m + 2) where
  g := targetLevelMap m
  smooth := contDiff_targetLevelMap m
  fiber_bounded := by
    rw [show {x : E | targetLevelMap m x = 0} =
        (StandardSaddle.targetFLS m).fiber by
      ext x
      exact targetLevelMap_zero_iff m hm x]
    exact (StandardSaddle.targetFLS m).fiber_bounded
  regular := by
    intro x hx
    let v : A := spaceTime x 1
    have hv : eventMap m v = 0 := by
      simpa [v, targetLevelMap] using hx
    have hsurj : Function.Surjective (fderiv ℝ (eventMap m) v) :=
      eventMap_regular m hm hv
    have htime : (3 / 4 : ℝ) < vertC v := by
      dsimp [v]
      rw [vertC_spaceTime]
      norm_num
    have hEv : eventMap m =ᶠ[𝓝 v]
        fun w => targetLevelMap m (initCLM (m + 3) w) := by
      apply Filter.eventuallyEq_of_mem ((isOpen_lt_vert (3 / 4)).mem_nhds htime)
      intro w hw
      conv_lhs => rw [← spaceTime_init_vert w]
      exact eventMap_collar_one m _ hw.le
    have htarget : HasFDerivAt (targetLevelMap m)
        (fderiv ℝ (targetLevelMap m) x) x :=
      ((contDiff_targetLevelMap m).differentiable infty_ne_zero x).hasFDerivAt
    have hcomp : fderiv ℝ (eventMap m) v =
        (fderiv ℝ (targetLevelMap m) x).comp (initCLM (m + 3)) := by
      rw [hEv.fderiv_eq]
      have hvx : initCLM (m + 3) v = x := by
        dsimp [v]
        rw [initCLM_spaceTime]
      have htargetv : HasFDerivAt (targetLevelMap m)
          (fderiv ℝ (targetLevelMap m) x) (initCLM (m + 3) v) := by
        simpa [hvx] using htarget
      exact (htargetv.comp v (initCLM (m + 3)).hasFDerivAt).fderiv
    rw [hcomp, ContinuousLinearMap.coe_comp] at hsurj
    exact hsurj.of_comp


-- @@ L662-665 verbatim
theorem source_fiber_eq_standard (hm : 0 < m) :
    (sourceFLS m hm).fiber = (StandardSaddle.sourceFLS m).fiber := by
  ext x
  exact sourceLevelMap_zero_iff m hm x


-- @@ L667-670 verbatim
theorem target_fiber_eq_standard (hm : 0 < m) :
    (targetFLS m hm).fiber = (StandardSaddle.targetFLS m).fiber := by
  ext x
  exact targetLevelMap_zero_iff m hm x


-- @@ L672-684 verbatim
/-- The genuine uncompactified zero-pair saddle.  It has the exact Cassini
pair-of-pants fiber and the desired singular-off-fiber frame twist. -/
def cobordism (hm : 0 < m) : FramedLevelCobordism (m + 2) where
  X₀ := sourceFLS m hm
  X₁ := targetFLS m hm
  G := eventMap m
  smooth := contDiff_eventMap m
  spatial_bounded := by
    obtain ⟨R, hR⟩ := StandardSaddle.eventMap_spatial_bounded m
    exact ⟨R, fun v hv => hR v ((eventMap_eq_zero_iff m hm v).mp hv)⟩
  regular := fun _ hv => eventMap_regular m hm hv
  collar_zero := eventMap_collar_zero m
  collar_one := eventMap_collar_one m


-- @@ L686-686 verbatim
end ConcreteZeroPairCassiniTwist

-- @@ L687-687 verbatim
end Submission
