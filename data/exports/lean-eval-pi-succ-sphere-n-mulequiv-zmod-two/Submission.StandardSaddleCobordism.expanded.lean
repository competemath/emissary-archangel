import Mathlib
import Submission.FiberSign
import Submission.SignedCobordismCategory


-- @@ L5-17 verbatim
/-!
# The explicit Cassini saddle cobordism

This file constructs the standard indefinite Morse event directly as a regular
level-set cobordism.  The last equation is the Cassini polynomial

`(((x - 1)^2 + y^2) * ((x + 1)^2 + y^2) - 1) - H(t)/2`,

where `H` is constant on the end collars and literally `t - 1/2` around its
unique zero.  The remaining equations are coordinate projections.  Thus the
zero fiber is one-dimensional, and at the unique spatial saddle the time
derivative supplies the missing normal direction.
-/


-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
open Set Function Metric

-- @@ L22-22 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L24-24 verbatim
namespace Submission

-- @@ L25-25 verbatim
namespace StandardSaddle


-- @@ L27-27 verbatim
/-! ## A private collar-flat event height -/


-- @@ L29-30 verbatim
def leftCutoff (t : ℝ) : ℝ :=
  Real.smoothTransition (8 * (t - 1 / 4))


-- @@ L32-33 verbatim
def rightCutoff (t : ℝ) : ℝ :=
  Real.smoothTransition (8 * (t - 5 / 8))


-- @@ L35-36 verbatim
def heightLeft (t : ℝ) : ℝ :=
  (1 - leftCutoff t) * (-1) + leftCutoff t * (t - 1 / 2)


-- @@ L38-39 verbatim
def heightRight (t : ℝ) : ℝ :=
  (1 - rightCutoff t) * (t - 1 / 2) + rightCutoff t


-- @@ L41-43 verbatim
/-- Collar-flat height, with a single transverse zero at `t = 1/2`. -/
def height (t : ℝ) : ℝ :=
  if t < 1 / 2 then heightLeft t else heightRight t


-- @@ L45-47 verbatim
lemma contDiff_leftCutoff : ContDiff ℝ ∞ leftCutoff := by
  exact Real.smoothTransition.contDiff.comp
    (contDiff_const.mul (contDiff_id.sub contDiff_const))


-- @@ L49-51 verbatim
lemma contDiff_rightCutoff : ContDiff ℝ ∞ rightCutoff := by
  exact Real.smoothTransition.contDiff.comp
    (contDiff_const.mul (contDiff_id.sub contDiff_const))


-- @@ L53-55 verbatim
lemma contDiff_heightLeft : ContDiff ℝ ∞ heightLeft := by
  exact ((contDiff_const.sub contDiff_leftCutoff).mul contDiff_const).add
    (contDiff_leftCutoff.mul (contDiff_id.sub contDiff_const))


-- @@ L57-59 verbatim
lemma contDiff_heightRight : ContDiff ℝ ∞ heightRight := by
  exact ((contDiff_const.sub contDiff_rightCutoff).mul
    (contDiff_id.sub contDiff_const)).add contDiff_rightCutoff


-- @@ L61-63 verbatim
lemma leftCutoff_eq_one {t : ℝ} (ht : 3 / 8 ≤ t) : leftCutoff t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  linarith


-- @@ L65-67 verbatim
lemma rightCutoff_eq_zero {t : ℝ} (ht : t ≤ 5 / 8) : rightCutoff t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  linarith


-- @@ L69-72 verbatim
lemma heightLeft_eq_linear {t : ℝ} (ht : 3 / 8 ≤ t) :
    heightLeft t = t - 1 / 2 := by
  rw [heightLeft, leftCutoff_eq_one ht]
  ring


-- @@ L74-77 verbatim
lemma heightRight_eq_linear {t : ℝ} (ht : t ≤ 5 / 8) :
    heightRight t = t - 1 / 2 := by
  rw [heightRight, rightCutoff_eq_zero ht]
  ring


-- @@ L79-84 verbatim
lemma height_eq_linear {t : ℝ} (ht₀ : 3 / 8 ≤ t) (ht₁ : t ≤ 5 / 8) :
    height t = t - 1 / 2 := by
  rw [height]
  split_ifs
  · exact heightLeft_eq_linear ht₀
  · exact heightRight_eq_linear ht₁


-- @@ L86-104 verbatim
theorem contDiff_height : ContDiff ℝ ∞ height := by
  rw [contDiff_iff_contDiffAt]
  intro t
  rcases lt_trichotomy t (1 / 2) with ht | ht | ht
  · refine contDiff_heightLeft.contDiffAt.congr_of_eventuallyEq ?_
    exact Filter.eventuallyEq_of_mem (Iio_mem_nhds ht) fun s hs => by
      change s < 1 / 2 at hs
      rw [height, if_pos hs]
  · have hlinear : ContDiff ℝ ∞ (fun s : ℝ => s - 1 / 2) :=
      contDiff_id.sub contDiff_const
    refine hlinear.contDiffAt.congr_of_eventuallyEq ?_
    have hmem : t ∈ Ioo (3 / 8 : ℝ) (5 / 8 : ℝ) := by
      rw [ht]
      norm_num
    exact Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hmem) fun s hs => by
      rw [height_eq_linear hs.1.le hs.2.le]
  · refine contDiff_heightRight.contDiffAt.congr_of_eventuallyEq ?_
    exact Filter.eventuallyEq_of_mem (Ioi_mem_nhds ht) fun s hs => by
      rw [height, if_neg (not_lt.mpr hs.le)]


-- @@ L106-112 verbatim
lemma height_of_le_quarter {t : ℝ} (ht : t ≤ 1 / 4) : height t = -1 := by
  have hhalf : t < 1 / 2 := by linarith
  have hcut : leftCutoff t = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    linarith
  rw [height, if_pos hhalf, heightLeft, hcut]
  ring


-- @@ L114-120 verbatim
lemma height_of_threeQuarter_le {t : ℝ} (ht : 3 / 4 ≤ t) : height t = 1 := by
  have hhalf : ¬ t < 1 / 2 := by linarith
  have hcut : rightCutoff t = 1 := by
    apply Real.smoothTransition.one_of_one_le
    linarith
  rw [height, if_neg hhalf, heightRight, hcut]
  ring


-- @@ L122-136 verbatim
lemma height_neg_of_lt_half {t : ℝ} (ht : t < 1 / 2) : height t < 0 := by
  rw [height, if_pos ht, heightLeft]
  have hc0 := Real.smoothTransition.nonneg (8 * (t - 1 / 4))
  have hc1 := Real.smoothTransition.le_one (8 * (t - 1 / 4))
  change (1 - leftCutoff t) * (-1) + leftCutoff t * (t - 1 / 2) < 0
  have htlin : t - 1 / 2 < 0 := sub_neg.mpr ht
  by_cases hc : leftCutoff t = 1
  · rw [hc]
    simpa using htlin
  · have hc' : leftCutoff t < 1 := lt_of_le_of_ne hc1 hc
    have hfirst : (1 - leftCutoff t) * (-1) < 0 :=
      mul_neg_of_pos_of_neg (sub_pos.mpr hc') (by norm_num)
    have hsecond : leftCutoff t * (t - 1 / 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hc0 htlin.le
    linarith


-- @@ L138-151 verbatim
lemma height_pos_of_half_lt {t : ℝ} (ht : 1 / 2 < t) : 0 < height t := by
  rw [height, if_neg (not_lt.mpr ht.le), heightRight]
  have hc0 := Real.smoothTransition.nonneg (8 * (t - 5 / 8))
  have hc1 := Real.smoothTransition.le_one (8 * (t - 5 / 8))
  change 0 < (1 - rightCutoff t) * (t - 1 / 2) + rightCutoff t
  have htlin : 0 < t - 1 / 2 := sub_pos.mpr ht
  by_cases hc : rightCutoff t = 1
  · rw [hc]
    norm_num
  · have hc' : rightCutoff t < 1 := lt_of_le_of_ne hc1 hc
    have hfirst : 0 < (1 - rightCutoff t) * (t - 1 / 2) :=
      mul_pos (sub_pos.mpr hc') htlin
    have hsecond : 0 ≤ rightCutoff t := hc0
    exact add_pos_of_pos_of_nonneg hfirst hsecond


-- @@ L153-155 verbatim
@[simp] lemma height_half : height (1 / 2) = 0 := by
  rw [height_eq_linear (by norm_num) (by norm_num)]
  ring


-- @@ L157-165 verbatim
lemma height_eq_zero_iff {t : ℝ} : height t = 0 ↔ t = 1 / 2 := by
  constructor
  · intro h
    rcases lt_trichotomy t (1 / 2) with ht | ht | ht
    · exact False.elim ((height_neg_of_lt_half ht).ne h)
    · exact ht
    · exact False.elim ((height_pos_of_half_lt ht).ne' h)
  · rintro rfl
    exact height_half


-- @@ L167-171 verbatim
lemma hasDerivAt_height_half : HasDerivAt height 1 (1 / 2) := by
  apply (hasDerivAt_id (1 / 2)).sub_const (1 / 2) |>.congr_of_eventuallyEq
  exact Filter.eventuallyEq_of_mem
    (isOpen_Ioo.mem_nhds (show (1 / 2 : ℝ) ∈ Ioo (3 / 8) (5 / 8) by norm_num))
    fun t ht => height_eq_linear ht.1.le ht.2.le


-- @@ L173-189 verbatim
lemma neg_one_le_height (t : ℝ) : -1 ≤ height t := by
  by_cases ht : t ≤ 1 / 4
  · rw [height_of_le_quarter ht]
  · by_cases hh : t < 1 / 2
    · rw [height, if_pos hh, heightLeft]
      have hc0 : 0 ≤ leftCutoff t := Real.smoothTransition.nonneg _
      have hc1 : leftCutoff t ≤ 1 := Real.smoothTransition.le_one _
      have hlin : 0 ≤ t - 1 / 2 + 1 := by linarith
      have hp : 0 ≤ leftCutoff t * (t - 1 / 2 + 1) := mul_nonneg hc0 hlin
      nlinarith
    · rw [height, if_neg hh, heightRight]
      have hc0 : 0 ≤ rightCutoff t := Real.smoothTransition.nonneg _
      have hc1 : rightCutoff t ≤ 1 := Real.smoothTransition.le_one _
      have hlin : 0 ≤ t - 1 / 2 := by linarith
      have hfirst : 0 ≤ (1 - rightCutoff t) * (t - 1 / 2) :=
        mul_nonneg (sub_nonneg.mpr hc1) hlin
      linarith


-- @@ L191-203 verbatim
lemma height_le_one (t : ℝ) : height t ≤ 1 := by
  by_cases ht : 3 / 4 ≤ t
  · rw [height_of_threeQuarter_le ht]
  · by_cases hh : t < 1 / 2
    · exact (height_neg_of_lt_half hh).le.trans (by norm_num)
    · rw [height, if_neg hh, heightRight]
      have hc0 : 0 ≤ rightCutoff t := Real.smoothTransition.nonneg _
      have hc1 : rightCutoff t ≤ 1 := Real.smoothTransition.le_one _
      have hlin0 : 0 ≤ t - 1 / 2 := by linarith
      have hlin1 : t - 1 / 2 ≤ 1 := by linarith
      have hp : 0 ≤ (1 - rightCutoff t) * (1 - (t - 1 / 2)) :=
        mul_nonneg (sub_nonneg.mpr hc1) (sub_nonneg.mpr hlin1)
      nlinarith


-- @@ L205-205 verbatim
/-! ## Cassini equations -/


-- @@ L207-207 verbatim
variable (m : ℕ)


-- @@ L209-209 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 3))

-- @@ L210-210 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (m + 4))

-- @@ L211-211 verbatim
local notation "F" => EuclideanSpace ℝ (Fin (m + 2))


-- @@ L213-214 verbatim
/-- The first Cassini-plane coordinate, after the `m+1` transverse coordinates. -/
def planeFirst : Fin (m + 3) := (Fin.last (m + 1)).castSucc


-- @@ L216-217 verbatim
/-- The second Cassini-plane coordinate. -/
def planeSecond : Fin (m + 3) := Fin.last (m + 2)


-- @@ L219-219 verbatim
def radiusSq (x : E) : ℝ := x (planeFirst m) ^ 2 + x (planeSecond m) ^ 2


-- @@ L221-224 verbatim
/-- The Cassini quartic, normalized to have its saddle at level zero. -/
def cassiniQ (x : E) : ℝ :=
  ((x (planeFirst m) - 1) ^ 2 + x (planeSecond m) ^ 2) *
    ((x (planeFirst m) + 1) ^ 2 + x (planeSecond m) ^ 2) - 1


-- @@ L226-230 verbatim
lemma cassiniQ_eq (x : E) :
    cassiniQ m x = radiusSq m x ^ 2 - 2 * x (planeFirst m) ^ 2 +
      2 * x (planeSecond m) ^ 2 := by
  simp only [cassiniQ, radiusSq]
  ring


-- @@ L232-235 verbatim
/-- The `m+2`-codimensional spatial Cassini presentation at level `a`. -/
def levelMap (a : ℝ) (x : E) : F :=
  WithLp.toLp 2 (Fin.lastCases (cassiniQ m x - a)
    (fun j : Fin (m + 1) => x j.castSucc.castSucc))


-- @@ L237-239 verbatim
@[simp] lemma levelMap_apply_last (a : ℝ) (x : E) :
    levelMap m a x (Fin.last (m + 1)) = cassiniQ m x - a := by
  simp [levelMap]


-- @@ L241-243 verbatim
@[simp] lemma levelMap_apply_castSucc (a : ℝ) (x : E) (j : Fin (m + 1)) :
    levelMap m a x j.castSucc = x j.castSucc.castSucc := by
  simp [levelMap]


-- @@ L245-252 verbatim
lemma contDiff_cassiniQ : ContDiff ℝ ∞ (cassiniQ m) := by
  exact (((((EuclideanSpace.proj (planeFirst m) : E →L[ℝ] ℝ).contDiff.sub
      contDiff_const).pow 2).add
      ((EuclideanSpace.proj (planeSecond m) : E →L[ℝ] ℝ).contDiff.pow 2)).mul
    ((((EuclideanSpace.proj (planeFirst m) : E →L[ℝ] ℝ).contDiff.add
      contDiff_const).pow 2).add
      ((EuclideanSpace.proj (planeSecond m) : E →L[ℝ] ℝ).contDiff.pow 2))).sub
    contDiff_const


-- @@ L254-260 verbatim
lemma contDiff_levelMap (a : ℝ) : ContDiff ℝ ∞ (levelMap m a) := by
  rw [contDiff_piLp]
  intro i
  induction i using Fin.lastCases with
  | last => simpa using (contDiff_cassiniQ m).sub contDiff_const
  | cast j =>
      simpa using (EuclideanSpace.proj j.castSucc.castSucc : E →L[ℝ] ℝ).contDiff


-- @@ L262-264 verbatim
/-- Space-time Cassini saddle equation. -/
def eventMap (v : E') : F :=
  levelMap m (height (vertC v) / 2) (initCLM (m + 3) v)


-- @@ L266-268 verbatim
lemma eventMap_spaceTime (x : E) (t : ℝ) :
    eventMap m (spaceTime x t) = levelMap m (height t / 2) x := by
  rw [eventMap, initCLM_spaceTime, vertC_spaceTime]


-- @@ L270-280 verbatim
lemma contDiff_eventMap : ContDiff ℝ ∞ (eventMap m) := by
  rw [contDiff_piLp]
  intro i
  induction i using Fin.lastCases with
  | last =>
      simp only [eventMap, levelMap_apply_last]
      exact (contDiff_cassiniQ m).comp (initCLM (m + 3)).contDiff |>.sub
        ((contDiff_height.comp contDiff_vertC).div_const 2)
  | cast j =>
      simp only [eventMap, levelMap_apply_castSucc, initCLM_apply]
      exact (EuclideanSpace.proj j.castSucc.castSucc.castSucc : E' →L[ℝ] ℝ).contDiff


-- @@ L282-284 verbatim
lemma eventMap_collar_zero (x : E) {t : ℝ} (ht : t ≤ 1 / 4) :
    eventMap m (spaceTime x t) = levelMap m (-1 / 2) x := by
  rw [eventMap_spaceTime, height_of_le_quarter ht]


-- @@ L286-288 verbatim
lemma eventMap_collar_one (x : E) {t : ℝ} (ht : 3 / 4 ≤ t) :
    eventMap m (spaceTime x t) = levelMap m (1 / 2) x := by
  rw [eventMap_spaceTime, height_of_threeQuarter_le ht]


-- @@ L290-294 verbatim
lemma transverse_eq_zero_of_eventMap_eq_zero {v : E'}
    (hv : eventMap m v = 0) (j : Fin (m + 1)) :
    v j.castSucc.castSucc.castSucc = 0 := by
  have h := congrArg (fun q : F => q j.castSucc) hv
  simpa [eventMap] using h


-- @@ L296-301 verbatim
lemma cassiniQ_eq_height_of_eventMap_eq_zero {v : E'}
    (hv : eventMap m v = 0) :
    cassiniQ m (initCLM (m + 3) v) = height (vertC v) / 2 := by
  have h := congrArg (fun q : F => q (Fin.last (m + 1))) hv
  simp [eventMap] at h
  linarith


-- @@ L303-303 verbatim
/-! ## Explicit differential -/


-- @@ L305-322 verbatim
lemma fderiv_eventMap_apply_castSucc (v h : E') (j : Fin (m + 1)) :
    fderiv ℝ (eventMap m) v h j.castSucc = h j.castSucc.castSucc.castSucc := by
  let outProj : F →L[ℝ] ℝ := EuclideanSpace.proj j.castSucc
  let inProj : E' →L[ℝ] ℝ := EuclideanSpace.proj j.castSucc.castSucc.castSucc
  have hG : HasFDerivAt (eventMap m) (fderiv ℝ (eventMap m) v) v :=
    ((contDiff_eventMap m).differentiable infty_ne_zero v).hasFDerivAt
  have hcomp : HasFDerivAt (fun w => eventMap m w j.castSucc)
      (outProj.comp (fderiv ℝ (eventMap m) v)) v :=
    by exact (PiLp.hasFDerivAt_apply 2 (eventMap m v) j.castSucc).comp v hG
  have hcoord : HasFDerivAt (fun w : E' => w j.castSucc.castSucc.castSucc)
      inProj v := inProj.hasFDerivAt
  have hfun : (fun w => eventMap m w j.castSucc) =
      fun w : E' => w j.castSucc.castSucc.castSucc := by
    funext w
    simp [eventMap]
  have hmaps : outProj.comp (fderiv ℝ (eventMap m) v) = inProj := by
    rw [← hcomp.fderiv, hfun, hcoord.fderiv]
  exact congrArg (fun A : E' →L[ℝ] ℝ => A h) hmaps


-- @@ L324-367 verbatim
lemma fderiv_eventMap_apply_last (v h : E') :
    fderiv ℝ (eventMap m) v h (Fin.last (m + 1)) =
      4 * v (planeFirst m).castSucc *
          ((v (planeFirst m).castSucc) ^ 2 + (v (planeSecond m).castSucc) ^ 2 - 1) *
          h (planeFirst m).castSucc +
        4 * v (planeSecond m).castSucc *
          ((v (planeFirst m).castSucc) ^ 2 + (v (planeSecond m).castSucc) ^ 2 + 1) *
          h (planeSecond m).castSucc -
        (deriv height (vertC v) / 2) * h (Fin.last (m + 3)) := by
  let outProj : F →L[ℝ] ℝ := EuclideanSpace.proj (Fin.last (m + 1))
  have hG : HasFDerivAt (eventMap m) (fderiv ℝ (eventMap m) v) v :=
    ((contDiff_eventMap m).differentiable infty_ne_zero v).hasFDerivAt
  have hcomp : HasFDerivAt (fun w => eventMap m w (Fin.last (m + 1)))
      (outProj.comp (fderiv ℝ (eventMap m) v)) v :=
    by exact (PiLp.hasFDerivAt_apply 2 (eventMap m v) (Fin.last (m + 1))).comp v hG
  let pA : E' →L[ℝ] ℝ := EuclideanSpace.proj (planeFirst m).castSucc
  let pB : E' →L[ℝ] ℝ := EuclideanSpace.proj (planeSecond m).castSucc
  let pT : E' →L[ℝ] ℝ := EuclideanSpace.proj (Fin.last (m + 3))
  have hA := (pA.hasFDerivAt : HasFDerivAt pA pA v)
  have hB := (pB.hasFDerivAt : HasFDerivAt pB pB v)
  have hq :=
    ((((hA.sub_const 1).pow 2).add (hB.pow 2)).mul
      (((hA.add_const 1).pow 2).add (hB.pow 2))).sub_const 1
  change HasFDerivAt
    (fun w : E' =>
      ((pA w - 1) ^ 2 + pB w ^ 2) * ((pA w + 1) ^ 2 + pB w ^ 2) - 1) _ v at hq
  have hb : HasDerivAt height (deriv height (vertC v)) (vertC v) :=
    (contDiff_height.differentiable infty_ne_zero (vertC v)).hasDerivAt
  have hT := (hb.div_const 2).hasFDerivAt.comp v
    (pT.hasFDerivAt : HasFDerivAt pT pT v)
  have hdirect := hq.sub hT
  change HasFDerivAt
    (fun w : E' =>
      ((pA w - 1) ^ 2 + pB w ^ 2) * ((pA w + 1) ^ 2 + pB w ^ 2) - 1 -
        height (vertC w) / 2) _ v at hdirect
  have hfun : (fun w => eventMap m w (Fin.last (m + 1))) = fun w : E' =>
      (((pA w - 1) ^ 2 + (pB w) ^ 2) * ((pA w + 1) ^ 2 + (pB w) ^ 2) - 1) -
        height (vertC w) / 2 := by
    funext w
    simp [eventMap, cassiniQ, pA, pB]
  have happ := congrArg (fun A : E' →L[ℝ] ℝ => A h) hcomp.fderiv.symm
  rw [hfun, hdirect.fderiv] at happ
  simp [outProj, pA, pB, pT] at happ
  convert happ using 1 <;> ring


-- @@ L369-372 verbatim
/-- Lift the transverse target coordinates. -/
def transverseLift (y : F) : E' :=
  ∑ j : Fin (m + 1), y j.castSucc •
    EuclideanSpace.single j.castSucc.castSucc.castSucc 1


-- @@ L374-376 verbatim
@[simp] lemma transverseLift_apply_castSucc (y : F) (j : Fin (m + 1)) :
    transverseLift m y j.castSucc.castSucc.castSucc = y j.castSucc := by
  simp [transverseLift, Pi.single_apply]


-- @@ L378-384 verbatim
@[simp] lemma transverseLift_apply_planeFirst (y : F) :
    transverseLift m y (planeFirst m).castSucc = 0 := by
  simp [transverseLift, Pi.single_apply, planeFirst, Fin.ext_iff]
  apply Finset.sum_eq_zero
  intro j _
  rw [if_neg]
  omega


-- @@ L386-392 verbatim
@[simp] lemma transverseLift_apply_planeSecond (y : F) :
    transverseLift m y (planeSecond m).castSucc = 0 := by
  simp [transverseLift, Pi.single_apply, planeSecond, Fin.ext_iff]
  apply Finset.sum_eq_zero
  intro j _
  rw [if_neg]
  omega


-- @@ L394-400 verbatim
@[simp] lemma transverseLift_apply_time (y : F) :
    transverseLift m y (Fin.last (m + 3)) = 0 := by
  simp [transverseLift, Pi.single_apply, Fin.ext_iff]
  apply Finset.sum_eq_zero
  intro j _
  rw [if_neg]
  omega


-- @@ L402-538 verbatim
/-- The Cassini space-time equation is a submersion on its zero fiber.  If one
spatial partial is nonzero it supplies the last target coordinate.  If both
vanish, the height range excludes the two minima `(±1,0)` and leaves only the
saddle `(0,0,1/2)`, where the time partial is `-1/2`. -/
theorem eventMap_regular (v : E') (hv : eventMap m v = 0) :
    Function.Surjective (fderiv ℝ (eventMap m) v) := by
  intro y
  let a : ℝ := v (planeFirst m).castSucc
  let b : ℝ := v (planeSecond m).castSucc
  let r : ℝ := a ^ 2 + b ^ 2
  let ca : ℝ := 4 * a * (r - 1)
  let cb : ℝ := 4 * b * (r + 1)
  by_cases ha : ca ≠ 0
  · let h : E' := transverseLift m y +
        EuclideanSpace.single (planeFirst m).castSucc (y (Fin.last (m + 1)) / ca)
    refine ⟨h, ?_⟩
    apply (WithLp.equiv 2 _).injective
    funext i
    induction i using Fin.lastCases with
    | cast j =>
        change fderiv ℝ (eventMap m) v h j.castSucc = y j.castSucc
        rw [fderiv_eventMap_apply_castSucc]
        have hjA : (j.castSucc.castSucc.castSucc : Fin (m + 4)) ≠
            (planeFirst m).castSucc := by
          simp [planeFirst, Fin.ext_iff]
          omega
        simp [h, PiLp.single_apply, hjA]
    | last =>
        change fderiv ℝ (eventMap m) v h (Fin.last (m + 1)) = y (Fin.last (m + 1))
        rw [fderiv_eventMap_apply_last]
        simp only [h, PiLp.add_apply, transverseLift_apply_planeFirst,
          transverseLift_apply_planeSecond, transverseLift_apply_time,
          PiLp.single_apply]
        have hAB : ((planeFirst m).castSucc : Fin (m + 4)) ≠
            (planeSecond m).castSucc := by
          simp [planeFirst, planeSecond, Fin.ext_iff]
        have hAT : ((planeFirst m).castSucc : Fin (m + 4)) ≠ Fin.last (m + 3) := by
          simp [planeFirst, Fin.ext_iff]
        simp only [if_true, zero_add]
        rw [if_neg hAB.symm, if_neg hAT.symm]
        simp only [mul_zero, add_zero, sub_zero]
        change ca * (y (Fin.last (m + 1)) / ca) = y (Fin.last (m + 1))
        field_simp
  · by_cases hb : cb ≠ 0
    · let h : E' := transverseLift m y +
          EuclideanSpace.single (planeSecond m).castSucc (y (Fin.last (m + 1)) / cb)
      refine ⟨h, ?_⟩
      apply (WithLp.equiv 2 _).injective
      funext i
      induction i using Fin.lastCases with
      | cast j =>
          change fderiv ℝ (eventMap m) v h j.castSucc = y j.castSucc
          rw [fderiv_eventMap_apply_castSucc]
          have hjB : (j.castSucc.castSucc.castSucc : Fin (m + 4)) ≠
              (planeSecond m).castSucc := by
            simp [planeSecond, Fin.ext_iff]
            omega
          simp [h, PiLp.single_apply, hjB]
      | last =>
          change fderiv ℝ (eventMap m) v h (Fin.last (m + 1)) = y (Fin.last (m + 1))
          rw [fderiv_eventMap_apply_last]
          simp only [h, PiLp.add_apply, transverseLift_apply_planeFirst,
            transverseLift_apply_planeSecond, transverseLift_apply_time,
            PiLp.single_apply]
          have hBA : ((planeSecond m).castSucc : Fin (m + 4)) ≠
              (planeFirst m).castSucc := by
            simp [planeFirst, planeSecond, Fin.ext_iff]
          have hBT : ((planeSecond m).castSucc : Fin (m + 4)) ≠ Fin.last (m + 3) := by
            simp [planeSecond, Fin.ext_iff]
          simp only [if_true, zero_add]
          rw [if_neg hBA.symm, if_neg hBT.symm]
          simp only [mul_zero, add_zero, zero_add, sub_zero]
          change cb * (y (Fin.last (m + 1)) / cb) = y (Fin.last (m + 1))
          field_simp
    · have hca : ca = 0 := not_ne_iff.mp ha
      have hcb : cb = 0 := not_ne_iff.mp hb
      have hr_nonneg : 0 ≤ r := by
        dsimp [r]
        positivity
      have hb0 : b = 0 := by
        dsimp [cb] at hcb
        have hrp : 0 < r + 1 := by linarith
        rcases mul_eq_zero.mp hcb with h4 | hrest
        · norm_num at h4
          exact h4
        · exact False.elim ((ne_of_gt hrp) hrest)
      have ha0 : a = 0 := by
        by_contra hane
        have hr1 : r = 1 := by
          dsimp [ca] at hca
          rcases mul_eq_zero.mp hca with h4 | hrest
          · norm_num at h4
            exact False.elim (hane h4)
          · exact sub_eq_zero.mp hrest
        have hq := cassiniQ_eq_height_of_eventMap_eq_zero m hv
        have hqform := cassiniQ_eq m (initCLM (m + 3) v)
        have hlow := neg_one_le_height (vertC v)
        dsimp [a, b, r] at hr1 hb0
        rw [hqform] at hq
        simp [radiusSq] at hq
        nlinarith
      have ht : vertC v = 1 / 2 := by
        apply height_eq_zero_iff.mp
        have hq := cassiniQ_eq_height_of_eventMap_eq_zero m hv
        have hqform := cassiniQ_eq m (initCLM (m + 3) v)
        rw [hqform] at hq
        simp [radiusSq] at hq
        dsimp [a, b] at ha0 hb0
        rw [ha0, hb0] at hq
        linarith
      let h : E' := transverseLift m y +
        EuclideanSpace.single (Fin.last (m + 3)) (-2 * y (Fin.last (m + 1)))
      refine ⟨h, ?_⟩
      apply (WithLp.equiv 2 _).injective
      funext i
      induction i using Fin.lastCases with
      | cast j =>
          change fderiv ℝ (eventMap m) v h j.castSucc = y j.castSucc
          rw [fderiv_eventMap_apply_castSucc]
          have hjT : (j.castSucc.castSucc.castSucc : Fin (m + 4)) ≠
              Fin.last (m + 3) := by
            simp [Fin.ext_iff]
            omega
          simp [h, PiLp.single_apply, hjT]
      | last =>
          change fderiv ℝ (eventMap m) v h (Fin.last (m + 1)) = y (Fin.last (m + 1))
          rw [fderiv_eventMap_apply_last]
          simp only [h, PiLp.add_apply, transverseLift_apply_planeFirst,
            transverseLift_apply_planeSecond, transverseLift_apply_time,
            PiLp.single_apply]
          have hTA : (Fin.last (m + 3) : Fin (m + 4)) ≠ (planeFirst m).castSucc := by
            simp [planeFirst, Fin.ext_iff]
          have hTB : (Fin.last (m + 3) : Fin (m + 4)) ≠ (planeSecond m).castSucc := by
            simp [planeSecond, Fin.ext_iff]
          simp [hTA, hTB]
          rw [ht, hasDerivAt_height_half.deriv]
          ring


-- @@ L540-570 verbatim
/-- The zero surface is uniformly spatially bounded. -/
lemma eventMap_spatial_bounded :
    ∃ R : ℝ, ∀ v, eventMap m v = 0 → ‖initCLM (m + 3) v‖ ≤ R := by
  refine ⟨2, ?_⟩
  intro v hv
  have hq := cassiniQ_eq_height_of_eventMap_eq_zero m hv
  have hqform := cassiniQ_eq m (initCLM (m + 3) v)
  rw [hqform] at hq
  simp [radiusSq] at hq
  have hupper := height_le_one (vertC v)
  let a : ℝ := v (planeFirst m).castSucc
  let b : ℝ := v (planeSecond m).castSucc
  let r : ℝ := a ^ 2 + b ^ 2
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    positivity
  have hr_le : r ≤ 3 := by
    by_contra hnot
    have hr_gt : 3 < r := lt_of_not_ge hnot
    dsimp [a, b, r] at hr_gt ⊢
    nlinarith [sq_nonneg (v (planeFirst m).castSucc),
      sq_nonneg (v (planeSecond m).castSucc)]
  have hnormsq : ‖initCLM (m + 3) v‖ ^ 2 = r := by
    rw [norm_sq_eq_sum, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [initCLM_apply]
    have hz : ∀ j : Fin (m + 1), v j.castSucc.castSucc.castSucc ^ 2 = 0 :=
      fun j => by
        rw [transverse_eq_zero_of_eventMap_eq_zero m hv j, zero_pow (by norm_num)]
    simp only [hz, Finset.sum_const_zero, zero_add]
    rfl
  nlinarith [norm_nonneg (initCLM (m + 3) v)]


-- @@ L572-572 verbatim
/-! ## Endpoint framed level sets -/


-- @@ L574-620 verbatim
/-- Before the saddle the zero fiber is the two-oval Cassini level `-1/2`. -/
def sourceFLS : FramedLevelSet (m + 2) where
  g := levelMap m (-1 / 2)
  smooth := contDiff_levelMap m (-1 / 2)
  fiber_bounded := by
    obtain ⟨R, hR⟩ := eventMap_spatial_bounded m
    apply (Metric.isBounded_closedBall (x := (0 : E)) (r := R)).subset
    intro x hx
    rw [mem_closedBall, dist_zero_right]
    have hx' : levelMap m (-1 / 2) x = 0 := hx
    have hv : eventMap m (spaceTime x 0) = 0 :=
      (eventMap_collar_zero m x (by norm_num)).trans hx'
    have hbound := hR (spaceTime x 0) hv
    rwa [initCLM_spaceTime] at hbound
  regular := by
    intro x hx
    let v : E' := spaceTime x 0
    have hv : eventMap m v = 0 :=
      (eventMap_collar_zero m x (by norm_num)).trans hx
    have hsurj : Function.Surjective (fderiv ℝ (eventMap m) v) :=
      eventMap_regular m v hv
    have htime : vertC v < 1 / 4 := by
      dsimp [v]
      rw [vertC_spaceTime]
      norm_num
    have hEv : eventMap m =ᶠ[𝓝 v]
        fun w => levelMap m (-1 / 2) (initCLM (m + 3) w) := by
      apply Filter.eventuallyEq_of_mem ((isOpen_vert_lt (1 / 4)).mem_nhds htime)
      intro w hw
      rw [eventMap]
      congr 1
      rw [height_of_le_quarter hw.le]
    have hlevel : HasFDerivAt (levelMap m (-1 / 2))
        (fderiv ℝ (levelMap m (-1 / 2)) x) x :=
      ((contDiff_levelMap m (-1 / 2)).differentiable infty_ne_zero x).hasFDerivAt
    have hcomp : fderiv ℝ (eventMap m) v =
        (fderiv ℝ (levelMap m (-1 / 2)) x).comp (initCLM (m + 3)) := by
      rw [hEv.fderiv_eq]
      have hvx : initCLM (m + 3) v = x := by
        dsimp [v]
        rw [initCLM_spaceTime]
      have hlevelv : HasFDerivAt (levelMap m (-1 / 2))
          (fderiv ℝ (levelMap m (-1 / 2)) x) (initCLM (m + 3) v) := by
        simpa [hvx] using hlevel
      exact (hlevelv.comp v (initCLM (m + 3)).hasFDerivAt).fderiv
    rw [hcomp, ContinuousLinearMap.coe_comp] at hsurj
    exact hsurj.of_comp


-- @@ L622-668 verbatim
/-- After the saddle the zero fiber is the single-curve Cassini level `1/2`. -/
def targetFLS : FramedLevelSet (m + 2) where
  g := levelMap m (1 / 2)
  smooth := contDiff_levelMap m (1 / 2)
  fiber_bounded := by
    obtain ⟨R, hR⟩ := eventMap_spatial_bounded m
    apply (Metric.isBounded_closedBall (x := (0 : E)) (r := R)).subset
    intro x hx
    rw [mem_closedBall, dist_zero_right]
    have hx' : levelMap m (1 / 2) x = 0 := hx
    have hv : eventMap m (spaceTime x 1) = 0 :=
      (eventMap_collar_one m x (by norm_num)).trans hx'
    have hbound := hR (spaceTime x 1) hv
    rwa [initCLM_spaceTime] at hbound
  regular := by
    intro x hx
    let v : E' := spaceTime x 1
    have hv : eventMap m v = 0 :=
      (eventMap_collar_one m x (by norm_num)).trans hx
    have hsurj : Function.Surjective (fderiv ℝ (eventMap m) v) :=
      eventMap_regular m v hv
    have htime : (3 / 4 : ℝ) < vertC v := by
      dsimp [v]
      rw [vertC_spaceTime]
      norm_num
    have hEv : eventMap m =ᶠ[𝓝 v]
        fun w => levelMap m (1 / 2) (initCLM (m + 3) w) := by
      apply Filter.eventuallyEq_of_mem ((isOpen_lt_vert (3 / 4)).mem_nhds htime)
      intro w hw
      rw [eventMap]
      congr 1
      rw [height_of_threeQuarter_le hw.le]
    have hlevel : HasFDerivAt (levelMap m (1 / 2))
        (fderiv ℝ (levelMap m (1 / 2)) x) x :=
      ((contDiff_levelMap m (1 / 2)).differentiable infty_ne_zero x).hasFDerivAt
    have hcomp : fderiv ℝ (eventMap m) v =
        (fderiv ℝ (levelMap m (1 / 2)) x).comp (initCLM (m + 3)) := by
      rw [hEv.fderiv_eq]
      have hvx : initCLM (m + 3) v = x := by
        dsimp [v]
        rw [initCLM_spaceTime]
      have hlevelv : HasFDerivAt (levelMap m (1 / 2))
          (fderiv ℝ (levelMap m (1 / 2)) x) (initCLM (m + 3) v) := by
        simpa [hvx] using hlevel
      exact (hlevelv.comp v (initCLM (m + 3)).hasFDerivAt).fderiv
    rw [hcomp, ContinuousLinearMap.coe_comp] at hsurj
    exact hsurj.of_comp


-- @@ L670-670 verbatim
/-! ## The framed cobordism and its constant-positive signed package -/


-- @@ L672-681 verbatim
/-- The literal framed cobordism carrying the standard saddle. -/
def cobordism : FramedLevelCobordism (m + 2) where
  X₀ := sourceFLS m
  X₁ := targetFLS m
  G := eventMap m
  smooth := contDiff_eventMap m
  spatial_bounded := eventMap_spatial_bounded m
  regular := eventMap_regular m
  collar_zero := eventMap_collar_zero m
  collar_one := eventMap_collar_one m


-- @@ L683-687 verbatim
/-- Constant positive sign on the two incoming ovals. -/
def sourceSign : FiberSign (sourceFLS m) where
  toFun := fun _ => 1
  continuous := continuous_const
  nonzero := by simp


-- @@ L689-693 verbatim
/-- Constant positive sign on the outgoing single curve. -/
def targetSign : FiberSign (targetFLS m) where
  toFun := fun _ => 1
  continuous := continuous_const
  nonzero := by simp


-- @@ L695-705 verbatim
/-- The standard saddle merge as an actual signed framed level cobordism, with
the constant positive label. -/
def signedCobordism : SignedFramedLevelCobordism (sourceSign m) (targetSign m) where
  cobordism := cobordism m
  source_eq := rfl
  target_eq := rfl
  toFun := fun _ => 1
  continuous := continuous_const
  nonzero := by simp
  collar_zero := by simp [sourceSign]
  collar_one := by simp [targetSign]


-- @@ L707-710 verbatim
/-- The saddle split is the literal time reversal of the saddle merge. -/
def signedSplitCobordism :
    SignedFramedLevelCobordism (targetSign m) (sourceSign m) :=
  (signedCobordism m).reverse


-- @@ L712-714 verbatim
theorem nonempty_signedSaddleCobordism :
    Nonempty (SignedFramedLevelCobordism (sourceSign m) (targetSign m)) :=
  ⟨signedCobordism m⟩


-- @@ L716-718 verbatim
theorem nonempty_signedSaddleSplit :
    Nonempty (SignedFramedLevelCobordism (targetSign m) (sourceSign m)) :=
  ⟨signedSplitCobordism m⟩


-- @@ L720-720 verbatim
end StandardSaddle


-- @@ L722-734 verbatim
/-- Dimension-independent adapter: every codimension at least two carries a
literal standard signed saddle generator with constant positive signs on both
ends, in both time directions. -/
theorem exists_standardSignedSaddle (n : ℕ) (hn : 2 ≤ n) :
    ∃ X₀ : FramedLevelSet n, ∃ X₁ : FramedLevelSet n,
      ∃ S₀ : FiberSign X₀, ∃ S₁ : FiberSign X₁,
        Nonempty (SignedFramedLevelCobordism S₀ S₁) ∧
          Nonempty (SignedFramedLevelCobordism S₁ S₀) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact ⟨StandardSaddle.sourceFLS m, StandardSaddle.targetFLS m,
    StandardSaddle.sourceSign m, StandardSaddle.targetSign m,
    StandardSaddle.nonempty_signedSaddleCobordism m,
    StandardSaddle.nonempty_signedSaddleSplit m⟩


-- @@ L736-736 verbatim
end Submission
