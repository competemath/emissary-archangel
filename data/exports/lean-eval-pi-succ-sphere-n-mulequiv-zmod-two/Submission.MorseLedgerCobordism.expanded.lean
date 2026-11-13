import Mathlib
import Submission.MorseLedgerNormalization


-- @@ L4-16 verbatim
/-!
# Geometric realization of finite Morse ledgers

`MorseLedgerNormalization` already supplies the signed cylinder, permutation
bookkeeping, and chronological trace splicing.  This file supplies one of its
missing genuinely geometric generators: a literal definite birth (and, by time
reversal, death) in every positive codimension.

The final section constructs the scalar height used by a standard definite Morse
birth.  Unlike a bare `smoothTransition`, it is *literally linear* near its unique
zero.  This avoids hiding the regularity of the birth surface in a derivative
calculation for the flat transition function.
-/


-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-20 verbatim
open Set Function Metric

-- @@ L21-21 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L23-23 verbatim
namespace Submission


-- @@ L25-25 verbatim
/-! ## A collar-flat height with one transverse zero -/


-- @@ L27-29 verbatim
/-- Left cutoff: zero through `1/4` and one from `3/8` onward. -/
def birthLeftCutoff (t : ℝ) : ℝ :=
  Real.smoothTransition (8 * (t - 1 / 4))


-- @@ L31-33 verbatim
/-- Right cutoff: zero through `5/8` and one from `3/4` onward. -/
def birthRightCutoff (t : ℝ) : ℝ :=
  Real.smoothTransition (8 * (t - 5 / 8))


-- @@ L35-37 verbatim
/-- Negative-to-linear interpolation on the left of the event. -/
def birthHeightLeft (t : ℝ) : ℝ :=
  (1 - birthLeftCutoff t) * (-1) + birthLeftCutoff t * (t - 1 / 2)


-- @@ L39-41 verbatim
/-- Linear-to-positive interpolation on the right of the event. -/
def birthHeightRight (t : ℝ) : ℝ :=
  (1 - birthRightCutoff t) * (t - 1 / 2) + birthRightCutoff t


-- @@ L43-46 verbatim
/-- Standard definite-event height.  Both branches are exactly `t - 1/2` on
a neighborhood of the switching point, so the piecewise definition is smooth. -/
def birthHeight (t : ℝ) : ℝ :=
  if t < 1 / 2 then birthHeightLeft t else birthHeightRight t


-- @@ L48-50 verbatim
lemma contDiff_birthLeftCutoff : ContDiff ℝ ∞ birthLeftCutoff := by
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul (contDiff_id.sub contDiff_const)))


-- @@ L52-54 verbatim
lemma contDiff_birthRightCutoff : ContDiff ℝ ∞ birthRightCutoff := by
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul (contDiff_id.sub contDiff_const)))


-- @@ L56-58 verbatim
lemma contDiff_birthHeightLeft : ContDiff ℝ ∞ birthHeightLeft := by
  exact ((contDiff_const.sub contDiff_birthLeftCutoff).mul contDiff_const).add
    (contDiff_birthLeftCutoff.mul (contDiff_id.sub contDiff_const))


-- @@ L60-62 verbatim
lemma contDiff_birthHeightRight : ContDiff ℝ ∞ birthHeightRight := by
  exact ((contDiff_const.sub contDiff_birthRightCutoff).mul
    (contDiff_id.sub contDiff_const)).add contDiff_birthRightCutoff


-- @@ L64-67 verbatim
lemma birthLeftCutoff_eq_one {t : ℝ} (ht : 3 / 8 ≤ t) :
    birthLeftCutoff t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  linarith


-- @@ L69-72 verbatim
lemma birthRightCutoff_eq_zero {t : ℝ} (ht : t ≤ 5 / 8) :
    birthRightCutoff t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  linarith


-- @@ L74-77 verbatim
lemma birthHeightLeft_eq_linear {t : ℝ} (ht : 3 / 8 ≤ t) :
    birthHeightLeft t = t - 1 / 2 := by
  rw [birthHeightLeft, birthLeftCutoff_eq_one ht]
  ring


-- @@ L79-82 verbatim
lemma birthHeightRight_eq_linear {t : ℝ} (ht : t ≤ 5 / 8) :
    birthHeightRight t = t - 1 / 2 := by
  rw [birthHeightRight, birthRightCutoff_eq_zero ht]
  ring


-- @@ L84-89 verbatim
lemma birthHeight_eq_linear {t : ℝ} (ht₀ : 3 / 8 ≤ t) (ht₁ : t ≤ 5 / 8) :
    birthHeight t = t - 1 / 2 := by
  rw [birthHeight]
  split_ifs
  · exact birthHeightLeft_eq_linear ht₀
  · exact birthHeightRight_eq_linear ht₁


-- @@ L91-109 verbatim
theorem contDiff_birthHeight : ContDiff ℝ ∞ birthHeight := by
  rw [contDiff_iff_contDiffAt]
  intro t
  rcases lt_trichotomy t (1 / 2) with ht | ht | ht
  · refine contDiff_birthHeightLeft.contDiffAt.congr_of_eventuallyEq ?_
    exact Filter.eventuallyEq_of_mem (Iio_mem_nhds ht) fun s hs => by
      change s < 1 / 2 at hs
      simp only [birthHeight, if_pos hs]
  · have hlinear : ContDiff ℝ ∞ (fun s : ℝ => s - 1 / 2) :=
      contDiff_id.sub contDiff_const
    refine hlinear.contDiffAt.congr_of_eventuallyEq ?_
    have hmem : t ∈ Set.Ioo (3 / 8 : ℝ) (5 / 8 : ℝ) := by
      rw [ht]
      norm_num
    exact Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hmem) fun s hs => by
      rw [birthHeight_eq_linear hs.1.le hs.2.le]
  · refine contDiff_birthHeightRight.contDiffAt.congr_of_eventuallyEq ?_
    exact Filter.eventuallyEq_of_mem (Ioi_mem_nhds ht) fun s hs => by
      rw [birthHeight, if_neg (not_lt.mpr hs.le)]


-- @@ L111-118 verbatim
lemma birthHeight_of_le_quarter {t : ℝ} (ht : t ≤ 1 / 4) :
    birthHeight t = -1 := by
  have hhalf : t < 1 / 2 := by linarith
  have hcut : birthLeftCutoff t = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    linarith
  rw [birthHeight, if_pos hhalf, birthHeightLeft, hcut]
  ring


-- @@ L120-127 verbatim
lemma birthHeight_of_threeQuarter_le {t : ℝ} (ht : 3 / 4 ≤ t) :
    birthHeight t = 1 := by
  have hhalf : ¬t < 1 / 2 := by linarith
  have hcut : birthRightCutoff t = 1 := by
    apply Real.smoothTransition.one_of_one_le
    linarith
  rw [birthHeight, if_neg hhalf, birthHeightRight, hcut]
  ring


-- @@ L129-144 verbatim
lemma birthHeight_neg_of_lt_half {t : ℝ} (ht : t < 1 / 2) :
    birthHeight t < 0 := by
  rw [birthHeight, if_pos ht, birthHeightLeft]
  have hc0 := Real.smoothTransition.nonneg (8 * (t - 1 / 4))
  have hc1 := Real.smoothTransition.le_one (8 * (t - 1 / 4))
  change (1 - birthLeftCutoff t) * (-1) + birthLeftCutoff t * (t - 1 / 2) < 0
  have htlin : t - 1 / 2 < 0 := sub_neg.mpr ht
  by_cases hc : birthLeftCutoff t = 1
  · rw [hc]
    simpa using htlin
  · have hc' : birthLeftCutoff t < 1 := lt_of_le_of_ne hc1 hc
    have hfirst : (1 - birthLeftCutoff t) * (-1) < 0 := by
      exact mul_neg_of_pos_of_neg (sub_pos.mpr hc') (by norm_num)
    have hsecond : birthLeftCutoff t * (t - 1 / 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hc0 htlin.le
    linarith


-- @@ L146-160 verbatim
lemma birthHeight_pos_of_half_lt {t : ℝ} (ht : 1 / 2 < t) :
    0 < birthHeight t := by
  rw [birthHeight, if_neg (not_lt.mpr ht.le), birthHeightRight]
  have hc0 := Real.smoothTransition.nonneg (8 * (t - 5 / 8))
  have hc1 := Real.smoothTransition.le_one (8 * (t - 5 / 8))
  change 0 < (1 - birthRightCutoff t) * (t - 1 / 2) + birthRightCutoff t
  have htlin : 0 < t - 1 / 2 := sub_pos.mpr ht
  by_cases hc : birthRightCutoff t = 1
  · rw [hc]
    norm_num
  · have hc' : birthRightCutoff t < 1 := lt_of_le_of_ne hc1 hc
    have hc0' : 0 ≤ birthRightCutoff t := hc0
    have hfirst : 0 < (1 - birthRightCutoff t) * (t - 1 / 2) :=
      mul_pos (sub_pos.mpr hc') htlin
    linarith


-- @@ L162-164 verbatim
@[simp] lemma birthHeight_half : birthHeight (1 / 2) = 0 := by
  rw [birthHeight_eq_linear (by norm_num) (by norm_num)]
  ring


-- @@ L166-175 verbatim
theorem birthHeight_eq_zero_iff {t : ℝ} :
    birthHeight t = 0 ↔ t = 1 / 2 := by
  constructor
  · intro h
    rcases lt_trichotomy t (1 / 2) with ht | ht | ht
    · exact False.elim ((birthHeight_neg_of_lt_half ht).ne h)
    · exact ht
    · exact False.elim ((birthHeight_pos_of_half_lt ht).ne' h)
  · rintro rfl
    exact birthHeight_half


-- @@ L177-184 verbatim
/-- The derivative at the unique event time is one, because the height is
literally linear on an open neighborhood there. -/
theorem hasDerivAt_birthHeight_half :
    HasDerivAt birthHeight 1 (1 / 2) := by
  apply (hasDerivAt_id (1 / 2)).sub_const (1 / 2) |>.congr_of_eventuallyEq
  exact Filter.eventuallyEq_of_mem
    (isOpen_Ioo.mem_nhds (show (1 / 2 : ℝ) ∈ Ioo (3 / 8) (5 / 8) by norm_num))
    fun t ht => birthHeight_eq_linear ht.1.le ht.2.le


-- @@ L186-186 verbatim
/-! ## The literal positive-codimension definite birth model -/


-- @@ L188-188 verbatim
namespace StandardBirth


-- @@ L190-190 verbatim
variable (m : ℕ)


-- @@ L192-192 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 2))

-- @@ L193-193 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (m + 3))

-- @@ L194-194 verbatim
local notation "F" => EuclideanSpace ℝ (Fin (m + 1))


-- @@ L196-197 verbatim
/-- First of the two unconstrained spatial coordinates. -/
def radialFirst : Fin (m + 2) := (Fin.last m).castSucc


-- @@ L199-200 verbatim
/-- Second of the two unconstrained spatial coordinates. -/
def radialSecond : Fin (m + 2) := Fin.last (m + 1)


-- @@ L202-204 verbatim
/-- Squared radius in the final spatial two-plane. -/
def radialSq (x : E) : ℝ :=
  x (radialFirst m) ^ 2 + x (radialSecond m) ^ 2


-- @@ L206-210 verbatim
/-- The standard framed circle presentation.  The first `m` coordinates are
cut out linearly and the last equation is `r₁²+r₂²=a`. -/
def circleMap (a : ℝ) (x : E) : F :=
  WithLp.toLp 2 (Fin.lastCases (radialSq m x - a)
    (fun j : Fin m => x j.castSucc.castSucc))


-- @@ L212-214 verbatim
@[simp] lemma circleMap_apply_last (a : ℝ) (x : E) :
    circleMap m a x (Fin.last m) = radialSq m x - a := by
  simp [circleMap]


-- @@ L216-218 verbatim
@[simp] lemma circleMap_apply_castSucc (a : ℝ) (x : E) (j : Fin m) :
    circleMap m a x j.castSucc = x j.castSucc.castSucc := by
  simp [circleMap]


-- @@ L220-222 verbatim
lemma contDiff_radialSq : ContDiff ℝ ∞ (radialSq m) := by
  exact (((EuclideanSpace.proj (radialFirst m) : E →L[ℝ] ℝ).contDiff.pow 2).add
    ((EuclideanSpace.proj (radialSecond m) : E →L[ℝ] ℝ).contDiff.pow 2))


-- @@ L224-231 verbatim
lemma contDiff_circleMap (a : ℝ) : ContDiff ℝ ∞ (circleMap m a) := by
  rw [contDiff_piLp]
  intro i
  induction i using Fin.lastCases with
  | last => simpa using (contDiff_radialSq m).sub contDiff_const
  | cast j =>
      simpa using
        (EuclideanSpace.proj j.castSucc.castSucc : E →L[ℝ] ℝ).contDiff


-- @@ L233-235 verbatim
/-- The space-time birth equation. -/
def eventMap (v : E') : F :=
  circleMap m (birthHeight (vertC v)) (initCLM (m + 2) v)


-- @@ L237-239 verbatim
lemma eventMap_spaceTime (x : E) (t : ℝ) :
    eventMap m (spaceTime x t) = circleMap m (birthHeight t) x := by
  rw [eventMap, initCLM_spaceTime, vertC_spaceTime]


-- @@ L241-252 verbatim
lemma contDiff_eventMap : ContDiff ℝ ∞ (eventMap m) := by
  rw [contDiff_piLp]
  intro i
  induction i using Fin.lastCases with
  | last =>
      simp only [eventMap, circleMap_apply_last, radialSq]
      exact ((((EuclideanSpace.proj ((radialFirst m).castSucc) : E' →L[ℝ] ℝ).contDiff.pow 2).add
        ((EuclideanSpace.proj ((radialSecond m).castSucc) : E' →L[ℝ] ℝ).contDiff.pow 2)).sub
          (contDiff_birthHeight.comp contDiff_vertC))
  | cast j =>
      simp only [eventMap, circleMap_apply_castSucc, initCLM_apply]
      exact (EuclideanSpace.proj j.castSucc.castSucc.castSucc : E' →L[ℝ] ℝ).contDiff


-- @@ L254-256 verbatim
lemma eventMap_collar_zero (x : E) {t : ℝ} (ht : t ≤ 1 / 4) :
    eventMap m (spaceTime x t) = circleMap m (-1) x := by
  rw [eventMap_spaceTime, birthHeight_of_le_quarter ht]


-- @@ L258-260 verbatim
lemma eventMap_collar_one (x : E) {t : ℝ} (ht : 3 / 4 ≤ t) :
    eventMap m (spaceTime x t) = circleMap m 1 x := by
  rw [eventMap_spaceTime, birthHeight_of_threeQuarter_le ht]


-- @@ L262-267 verbatim
/-- A zero of the birth equation has all transverse coordinates zero. -/
lemma transverse_eq_zero_of_eventMap_eq_zero {v : E'}
    (hv : eventMap m v = 0) (j : Fin m) :
    v j.castSucc.castSucc.castSucc = 0 := by
  have h := congrArg (fun q : F => q j.castSucc) hv
  simpa [eventMap] using h


-- @@ L269-277 verbatim
/-- Radial equation on the birth surface. -/
lemma radialSq_eq_birthHeight_of_eventMap_eq_zero {v : E'}
    (hv : eventMap m v = 0) :
    (v (radialFirst m).castSucc) ^ 2 +
      (v (radialSecond m).castSucc) ^ 2 = birthHeight (vertC v) := by
  have h := congrArg (fun q : F => q (Fin.last m)) hv
  simp only [eventMap, circleMap_apply_last, radialSq, PiLp.zero_apply,
    initCLM_apply] at h
  linarith


-- @@ L279-300 verbatim
/-- The linear transverse coordinates have the expected derivative. -/
lemma fderiv_eventMap_apply_castSucc (v h : E') (j : Fin m) :
    fderiv ℝ (eventMap m) v h j.castSucc =
      h j.castSucc.castSucc.castSucc := by
  let outProj : F →L[ℝ] ℝ := EuclideanSpace.proj j.castSucc
  let inProj : E' →L[ℝ] ℝ :=
    EuclideanSpace.proj j.castSucc.castSucc.castSucc
  have hG : HasFDerivAt (eventMap m) (fderiv ℝ (eventMap m) v) v :=
    ((contDiff_eventMap m).differentiable infty_ne_zero v).hasFDerivAt
  have hcomp : HasFDerivAt (fun w => eventMap m w j.castSucc)
      (outProj.comp (fderiv ℝ (eventMap m) v)) v := by
    exact (PiLp.hasFDerivAt_apply 2 (eventMap m v) j.castSucc).comp v hG
  have hcoord : HasFDerivAt (fun w : E' => w j.castSucc.castSucc.castSucc)
      inProj v := inProj.hasFDerivAt
  have hfun : (fun w => eventMap m w j.castSucc) =
      fun w : E' => w j.castSucc.castSucc.castSucc := by
    funext w
    simp [eventMap]
  have hmaps : outProj.comp (fderiv ℝ (eventMap m) v) = inProj := by
    rw [← hcomp.fderiv, hfun, hcoord.fderiv]
  have happ := congrArg (fun A : E' →L[ℝ] ℝ => A h) hmaps
  exact happ


-- @@ L302-340 verbatim
/-- Derivative of the radial equation. -/
lemma fderiv_eventMap_apply_last (v h : E') :
    fderiv ℝ (eventMap m) v h (Fin.last m) =
      2 * v (radialFirst m).castSucc * h (radialFirst m).castSucc +
        2 * v (radialSecond m).castSucc * h (radialSecond m).castSucc -
          deriv birthHeight (vertC v) * h (Fin.last (m + 2)) := by
  let outProj : F →L[ℝ] ℝ := EuclideanSpace.proj (Fin.last m)
  have hG : HasFDerivAt (eventMap m) (fderiv ℝ (eventMap m) v) v :=
    ((contDiff_eventMap m).differentiable infty_ne_zero v).hasFDerivAt
  have hcomp : HasFDerivAt (fun w => eventMap m w (Fin.last m))
      (outProj.comp (fderiv ℝ (eventMap m) v)) v := by
    exact (PiLp.hasFDerivAt_apply 2 (eventMap m v) (Fin.last m)).comp v hG
  have hfun : (fun w => eventMap m w (Fin.last m)) = fun w : E' =>
      w (radialFirst m).castSucc ^ 2 + w (radialSecond m).castSucc ^ 2 -
        birthHeight (vertC w) := by
    funext w
    simp [eventMap, radialSq]
  have happ := congrArg (fun A : E' →L[ℝ] ℝ => A h) hcomp.fderiv.symm
  rw [hfun] at happ
  let pA : E' →L[ℝ] ℝ := EuclideanSpace.proj (radialFirst m).castSucc
  let pB : E' →L[ℝ] ℝ := EuclideanSpace.proj (radialSecond m).castSucc
  let pT : E' →L[ℝ] ℝ := EuclideanSpace.proj (Fin.last (m + 2))
  have hA := (pA.hasFDerivAt : HasFDerivAt pA pA v).pow 2
  have hB := (pB.hasFDerivAt : HasFDerivAt pB pB v).pow 2
  have hb : HasDerivAt birthHeight (deriv birthHeight (vertC v)) (vertC v) :=
    (contDiff_birthHeight.differentiable infty_ne_zero (vertC v)).hasDerivAt
  have hT := hb.hasFDerivAt.comp v
    (pT.hasFDerivAt : HasFDerivAt pT pT v)
  have hdirect := (hA.add hB).sub hT
  have hscalarEq :
      (((fun x => pA x ^ 2) + fun x => pB x ^ 2) - birthHeight ∘ vertC) =
        (fun w : E' =>
          w (radialFirst m).castSucc ^ 2 + w (radialSecond m).castSucc ^ 2 -
            birthHeight (vertC w)) := by
    funext w
    rfl
  rw [hscalarEq] at hdirect
  rw [hdirect.fderiv] at happ
  simpa [outProj, pA, pB, pT, mul_comm, mul_left_comm, mul_assoc] using happ


-- @@ L342-345 verbatim
/-- Lift the first `m` target coordinates to their spatial normal directions. -/
def transverseLift (y : F) : E' :=
  ∑ j : Fin m, y j.castSucc •
    EuclideanSpace.single j.castSucc.castSucc.castSucc 1


-- @@ L347-349 verbatim
@[simp] lemma transverseLift_apply_castSucc (y : F) (j : Fin m) :
    transverseLift m y j.castSucc.castSucc.castSucc = y j.castSucc := by
  simp [transverseLift, Pi.single_apply]


-- @@ L351-357 verbatim
@[simp] lemma transverseLift_apply_radialFirst (y : F) :
    transverseLift m y (radialFirst m).castSucc = 0 := by
  simp [transverseLift, Pi.single_apply, radialFirst, Fin.ext_iff]
  apply Finset.sum_eq_zero
  intro j _
  rw [if_neg]
  omega


-- @@ L359-365 verbatim
@[simp] lemma transverseLift_apply_radialSecond (y : F) :
    transverseLift m y (radialSecond m).castSucc = 0 := by
  simp [transverseLift, Pi.single_apply, radialSecond, Fin.ext_iff]
  apply Finset.sum_eq_zero
  intro j _
  rw [if_neg]
  omega


-- @@ L367-373 verbatim
@[simp] lemma transverseLift_apply_time (y : F) :
    transverseLift m y (Fin.last (m + 2)) = 0 := by
  simp [transverseLift, Pi.single_apply, Fin.ext_iff]
  apply Finset.sum_eq_zero
  intro j _
  rw [if_neg]
  omega


-- @@ L375-378 verbatim
lemma transverseIndex_lt_radialFirst (j : Fin m) :
    j.castSucc.castSucc.castSucc < (radialFirst m).castSucc := by
  change j.val < m
  exact j.isLt


-- @@ L380-383 verbatim
lemma radialFirst_lt_radialSecond :
    (radialFirst m).castSucc < (radialSecond m).castSucc := by
  change m < m + 1
  omega


-- @@ L385-388 verbatim
lemma radialSecond_lt_time :
    (radialSecond m).castSucc < Fin.last (m + 2) := by
  change m + 1 < m + 2
  omega


-- @@ L390-476 verbatim
/-- The birth equation is a submersion along its zero surface.  Away from the
event center one of the two radial derivatives is nonzero; at the center the
time derivative is `-1`. -/
theorem eventMap_regular (v : E') (hv : eventMap m v = 0) :
    Function.Surjective (fderiv ℝ (eventMap m) v) := by
  intro y
  by_cases ha : v (radialFirst m).castSucc ≠ 0
  · let h : E' := transverseLift m y +
        EuclideanSpace.single (radialFirst m).castSucc
          (y (Fin.last m) / (2 * v (radialFirst m).castSucc))
    refine ⟨h, ?_⟩
    apply (WithLp.equiv 2 _).injective
    funext i
    induction i using Fin.lastCases with
    | cast j =>
        change fderiv ℝ (eventMap m) v h j.castSucc = y j.castSucc
        rw [fderiv_eventMap_apply_castSucc]
        have hjA : j.castSucc.castSucc.castSucc ≠ (radialFirst m).castSucc :=
          (transverseIndex_lt_radialFirst m j).ne
        simp [h, hjA]
    | last =>
        change fderiv ℝ (eventMap m) v h (Fin.last m) = y (Fin.last m)
        rw [fderiv_eventMap_apply_last]
        simp only [h, PiLp.add_apply, transverseLift_apply_radialFirst,
          transverseLift_apply_radialSecond, transverseLift_apply_time,
          PiLp.single_apply]
        have hBA : (radialSecond m).castSucc ≠ (radialFirst m).castSucc :=
          (radialFirst_lt_radialSecond m).ne'
        have hTA : Fin.last (m + 2) ≠ (radialFirst m).castSucc :=
          ((radialFirst_lt_radialSecond m).trans (radialSecond_lt_time m)).ne'
        simp [hBA, hTA]
        field_simp [ha]
  · by_cases hb : v (radialSecond m).castSucc ≠ 0
    · let h : E' := transverseLift m y +
          EuclideanSpace.single (radialSecond m).castSucc
            (y (Fin.last m) / (2 * v (radialSecond m).castSucc))
      refine ⟨h, ?_⟩
      apply (WithLp.equiv 2 _).injective
      funext i
      induction i using Fin.lastCases with
      | cast j =>
          change fderiv ℝ (eventMap m) v h j.castSucc = y j.castSucc
          rw [fderiv_eventMap_apply_castSucc]
          have hjB : j.castSucc.castSucc.castSucc ≠ (radialSecond m).castSucc :=
            ((transverseIndex_lt_radialFirst m j).trans
              (radialFirst_lt_radialSecond m)).ne
          simp [h, hjB]
      | last =>
          change fderiv ℝ (eventMap m) v h (Fin.last m) = y (Fin.last m)
          rw [fderiv_eventMap_apply_last]
          simp only [h, PiLp.add_apply, transverseLift_apply_radialFirst,
            transverseLift_apply_radialSecond, transverseLift_apply_time,
            PiLp.single_apply]
          have hAB : (radialFirst m).castSucc ≠ (radialSecond m).castSucc :=
            (radialFirst_lt_radialSecond m).ne
          have hTB : Fin.last (m + 2) ≠ (radialSecond m).castSucc :=
            (radialSecond_lt_time m).ne'
          simp [hAB, hTB]
          field_simp [hb]
    · have ht : vertC v = 1 / 2 := by
        apply birthHeight_eq_zero_iff.mp
        have hr := radialSq_eq_birthHeight_of_eventMap_eq_zero m hv
        rw [not_ne_iff.mp ha, not_ne_iff.mp hb] at hr
        norm_num at hr ⊢
        exact hr.symm
      let h : E' := transverseLift m y +
        EuclideanSpace.single (Fin.last (m + 2)) (-y (Fin.last m))
      refine ⟨h, ?_⟩
      apply (WithLp.equiv 2 _).injective
      funext i
      induction i using Fin.lastCases with
      | cast j =>
          change fderiv ℝ (eventMap m) v h j.castSucc = y j.castSucc
          rw [fderiv_eventMap_apply_castSucc]
          have hjT : j.castSucc.castSucc.castSucc ≠ Fin.last (m + 2) :=
            ((transverseIndex_lt_radialFirst m j).trans
              ((radialFirst_lt_radialSecond m).trans (radialSecond_lt_time m))).ne
          simp [h, hjT]
      | last =>
          change fderiv ℝ (eventMap m) v h (Fin.last m) = y (Fin.last m)
          rw [fderiv_eventMap_apply_last]
          simp only [h, PiLp.add_apply, transverseLift_apply_radialFirst,
            transverseLift_apply_radialSecond, transverseLift_apply_time,
            PiLp.single_apply]
          rw [not_ne_iff.mp ha, not_ne_iff.mp hb, ht,
            hasDerivAt_birthHeight_half.deriv]
          simp [radialFirst, radialSecond, Fin.ext_iff]


-- @@ L478-514 verbatim
/-- Every point of the event surface lies over the closed spatial unit ball. -/
lemma eventMap_spatial_bound_one (v : E') (hv : eventMap m v = 0) :
    ‖initCLM (m + 2) v‖ ≤ 1 := by
  have hr := radialSq_eq_birthHeight_of_eventMap_eq_zero m hv
  have hheight : birthHeight (vertC v) ≤ 1 := by
    by_cases ht : vertC v < 1 / 2
    · exact (birthHeight_neg_of_lt_half ht).le.trans (by norm_num)
    · rcases eq_or_lt_of_le (not_lt.mp ht) with heq | hgt
      · rw [← heq]
        rw [birthHeight_half]
        norm_num
      · rw [birthHeight, if_neg (not_lt.mpr hgt.le), birthHeightRight]
        have hc0 := Real.smoothTransition.nonneg (8 * (vertC v - 5 / 8))
        have hc1 := Real.smoothTransition.le_one (8 * (vertC v - 5 / 8))
        change (1 - birthRightCutoff (vertC v)) * (vertC v - 1 / 2) +
          birthRightCutoff (vertC v) ≤ 1
        by_cases ht1 : vertC v ≤ 3 / 4
        · have hlin : vertC v - 1 / 2 ≤ 1 := by linarith
          have hc0' : 0 ≤ birthRightCutoff (vertC v) := hc0
          have hc1' : birthRightCutoff (vertC v) ≤ 1 := hc1
          nlinarith
        · rw [birthRightCutoff]
          rw [Real.smoothTransition.one_of_one_le (by linarith)]
          norm_num
  have hnormsq : ‖initCLM (m + 2) v‖ ^ 2 =
      (v (radialFirst m).castSucc) ^ 2 +
        (v (radialSecond m).castSucc) ^ 2 := by
    rw [norm_sq_eq_sum]
    rw [Fin.sum_univ_castSucc]
    simp only [initCLM_apply]
    have hz : ∀ j : Fin m, v j.castSucc.castSucc.castSucc ^ 2 = 0 :=
      fun j => by rw [transverse_eq_zero_of_eventMap_eq_zero m hv j, zero_pow (by norm_num)]
    rw [Fin.sum_univ_castSucc]
    simp only [hz, Finset.sum_const_zero, zero_add]
    rfl
  nlinarith [norm_nonneg (initCLM (m + 2) v), sq_nonneg (v (radialFirst m).castSucc),
    sq_nonneg (v (radialSecond m).castSucc)]


-- @@ L516-519 verbatim
/-- The event surface is spatially bounded, uniformly in time. -/
lemma eventMap_spatial_bounded :
    ∃ R : ℝ, ∀ v, eventMap m v = 0 → ‖initCLM (m + 2) v‖ ≤ R :=
  ⟨1, eventMap_spatial_bound_one m⟩


-- @@ L521-540 verbatim
/-- Before the definite event the model has empty zero fiber. -/
def sourceFLS : FramedLevelSet (m + 1) where
  g := circleMap m (-1)
  smooth := contDiff_circleMap m (-1)
  fiber_bounded := by
    have hempty : {x : E | circleMap m (-1) x = 0} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hx
      have h := congrArg (fun q : F => q (Fin.last m)) hx
      simp only [circleMap_apply_last, PiLp.zero_apply, radialSq] at h
      nlinarith [sq_nonneg (x (radialFirst m)), sq_nonneg (x (radialSecond m))]
    rw [hempty]
    exact Bornology.isBounded_empty
  regular := by
    intro x hx
    have h := congrArg (fun q : F => q (Fin.last m)) hx
    simp only [circleMap_apply_last, PiLp.zero_apply, radialSq] at h
    exfalso
    nlinarith [sq_nonneg (x (radialFirst m)), sq_nonneg (x (radialSecond m))]


-- @@ L542-590 verbatim
/-- After the definite event the zero fiber is the unit circle in the final
two-plane, with the first `m` coordinates zero. -/
def targetFLS : FramedLevelSet (m + 1) where
  g := circleMap m 1
  smooth := contDiff_circleMap m 1
  fiber_bounded := by
    apply (Metric.isBounded_closedBall (x := (0 : E)) (r := 1)).subset
    intro x hx
    rw [mem_closedBall, dist_zero_right]
    have hv : eventMap m (spaceTime x 1) = 0 := by
      rw [eventMap_spaceTime, birthHeight_of_threeQuarter_le (by norm_num)]
      exact hx
    have hbound := eventMap_spatial_bound_one m (spaceTime x 1) hv
    rwa [initCLM_spaceTime] at hbound
  regular := by
    intro x hx
    let v : E' := spaceTime x 1
    have hv : eventMap m v = 0 := by
      dsimp [v]
      rw [eventMap_spaceTime, birthHeight_of_threeQuarter_le (by norm_num)]
      exact hx
    have hsurj : Function.Surjective (fderiv ℝ (eventMap m) v) :=
      eventMap_regular m v hv
    have htime : (3 / 4 : ℝ) < vertC v := by
      dsimp [v]
      rw [vertC_spaceTime]
      norm_num
    have hEv : eventMap m =ᶠ[𝓝 v]
        fun w => circleMap m 1 (initCLM (m + 2) w) := by
      apply Filter.eventuallyEq_of_mem ((isOpen_lt_vert (3 / 4)).mem_nhds htime)
      intro w hw
      rw [eventMap]
      congr 1
      exact birthHeight_of_threeQuarter_le hw.le
    have hcircle : HasFDerivAt (circleMap m 1)
        (fderiv ℝ (circleMap m 1) x) x :=
      ((contDiff_circleMap m 1).differentiable infty_ne_zero x).hasFDerivAt
    have hcomp : fderiv ℝ (eventMap m) v =
        (fderiv ℝ (circleMap m 1) x).comp (initCLM (m + 2)) := by
      rw [hEv.fderiv_eq]
      have hvx : initCLM (m + 2) v = x := by
        dsimp [v]
        rw [initCLM_spaceTime]
      have hcirclev : HasFDerivAt (circleMap m 1)
          (fderiv ℝ (circleMap m 1) x) (initCLM (m + 2) v) := by
        simpa [hvx] using hcircle
      exact (hcirclev.comp v (initCLM (m + 2)).hasFDerivAt).fderiv
    rw [hcomp, ContinuousLinearMap.coe_comp] at hsurj
    exact hsurj.of_comp


-- @@ L592-601 verbatim
/-- The literal framed cobordism carrying the standard birth. -/
def cobordism : FramedLevelCobordism (m + 1) where
  X₀ := sourceFLS m
  X₁ := targetFLS m
  G := eventMap m
  smooth := contDiff_eventMap m
  spatial_bounded := eventMap_spatial_bounded m
  regular := eventMap_regular m
  collar_zero := eventMap_collar_zero m
  collar_one := eventMap_collar_one m


-- @@ L603-607 verbatim
/-- Constant positive sign on the empty source. -/
def sourceSign : FiberSign (sourceFLS m) where
  toFun := fun _ => 1
  continuous := continuous_const
  nonzero := by simp


-- @@ L609-613 verbatim
/-- Constant positive sign on the born circle. -/
def targetSign : FiberSign (targetFLS m) where
  toFun := fun _ => 1
  continuous := continuous_const
  nonzero := by simp


-- @@ L615-624 verbatim
/-- The standard birth as an actual signed framed level cobordism. -/
def signedCobordism : SignedFramedLevelCobordism (sourceSign m) (targetSign m) where
  cobordism := cobordism m
  source_eq := rfl
  target_eq := rfl
  toFun := fun _ => 1
  continuous := continuous_const
  nonzero := by simp
  collar_zero := by simp [sourceSign]
  collar_one := by simp [targetSign]


-- @@ L626-629 verbatim
/-- Death is the literal time reversal of the standard birth. -/
def signedDeathCobordism :
    SignedFramedLevelCobordism (targetSign m) (sourceSign m) :=
  (signedCobordism m).reverse


-- @@ L631-633 verbatim
theorem nonempty_signedBirthCobordism :
    Nonempty (SignedFramedLevelCobordism (sourceSign m) (targetSign m)) :=
  ⟨signedCobordism m⟩


-- @@ L635-637 verbatim
theorem nonempty_signedDeathCobordism :
    Nonempty (SignedFramedLevelCobordism (targetSign m) (sourceSign m)) :=
  ⟨signedDeathCobordism m⟩


-- @@ L639-639 verbatim
end StandardBirth


-- @@ L641-653 verbatim
/-- Dimension-independent adapter: every positive codimension has a literal
standard signed birth generator.  `MorseLedgerGeometricGenerators.realizeStep`
can use this term after adjoining the unchanged tail presentation. -/
theorem exists_standardSignedBirth (n : ℕ) (hn : 0 < n) :
    ∃ X₀ : FramedLevelSet n, ∃ X₁ : FramedLevelSet n,
      ∃ S₀ : FiberSign X₀, ∃ S₁ : FiberSign X₁,
        Nonempty (SignedFramedLevelCobordism S₀ S₁) := by
  cases n with
  | zero => omega
  | succ m =>
      exact ⟨StandardBirth.sourceFLS m, StandardBirth.targetFLS m,
        StandardBirth.sourceSign m, StandardBirth.targetSign m,
        StandardBirth.nonempty_signedBirthCobordism m⟩


-- @@ L655-666 verbatim
/-! ## Spatial flatness and juxtaposition of framed presentations

External direct sum of framed level sets.  Two presentations which agree with
one common nonzero constant `c` outside disjoint balls are juxtaposed by the
sum `g₁ + g₂ - c`: near either ball the sum is literally the corresponding
piece, so the fiber is the disjoint union and pointwise regularity is
inherited.  The same formula juxtaposes framed level cobordisms with spatially
separated supports, and blending the two sign labels by the metric weight
`sepWeight` juxtaposes signed data.  Taking the cylinder on one side adjoins an
unchanged tail presentation to any signed cobordism.  This is the geometric
splice operator consumed by the parity-indexed normalization contract
(`SignedDeltaNormalizationData`). -/


-- @@ L668-668 verbatim
section Juxtaposition


-- @@ L670-671 verbatim
variable {n : ℕ} {c : EuclideanSpace ℝ (Fin n)}
  {p p₁ p₂ : EuclideanSpace ℝ (Fin (n + 1))} {R R₁ R₂ : ℝ}


-- @@ L673-680 verbatim
/-- Separation: a point within the first ball is at distance `> R₂` from the
second center. -/
theorem sep_dist_right (hsep : R₁ + R₂ < dist p₁ p₂)
    {v : EuclideanSpace ℝ (Fin (n + 1))} (hv : dist v p₁ ≤ R₁) :
    R₂ < dist v p₂ := by
  have htri := dist_triangle p₁ v p₂
  rw [dist_comm p₁ v] at htri
  linarith


-- @@ L682-689 verbatim
/-- Separation: a point within the second ball is at distance `> R₁` from the
first center. -/
theorem sep_dist_left (hsep : R₁ + R₂ < dist p₁ p₂)
    {v : EuclideanSpace ℝ (Fin (n + 1))} (hv : dist v p₂ ≤ R₂) :
    R₁ < dist v p₁ := by
  have htri := dist_triangle p₁ v p₂
  rw [dist_comm p₁ v] at htri
  linarith


-- @@ L691-691 verbatim
namespace FramedLevelSet


-- @@ L693-696 verbatim
/-- The presentation equals the constant `c` at distance `≥ R` from `p`. -/
def FlatOutside (X : FramedLevelSet n) (c : EuclideanSpace ℝ (Fin n))
    (p : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ) : Prop :=
  ∀ v, R ≤ dist v p → X.g v = c


-- @@ L698-700 verbatim
theorem FlatOutside.mono {X : FramedLevelSet n} (h : X.FlatOutside c p R)
    {R' : ℝ} (hR : R ≤ R') : X.FlatOutside c p R' :=
  fun v hv => h v (hR.trans hv)


-- @@ L702-711 verbatim
/-- A presentation which is flat with nonzero background has its fiber inside
the flatness ball. -/
theorem FlatOutside.fiber_subset_ball {X : FramedLevelSet n}
    (h : X.FlatOutside c p R) (hc : c ≠ 0) : X.fiber ⊆ Metric.ball p R := by
  intro v hv
  rw [Metric.mem_ball]
  by_contra hlt
  have hcv := h v (not_lt.mp hlt)
  have hv0 : X.g v = 0 := hv
  exact hc (hcv.symm.trans hv0)


-- @@ L713-717 verbatim
/-- The raw juxtaposition map: sum of the two presentations minus the shared
background constant. -/
def juxtMap (X₁ X₂ : FramedLevelSet n) (c : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n) :=
  fun v => X₁.g v + X₂.g v - c


-- @@ L719-722 verbatim
theorem juxtMap_eq_left (X₁ X₂ : FramedLevelSet n)
    (h₂ : X₂.FlatOutside c p₂ R₂) {v : EuclideanSpace ℝ (Fin (n + 1))}
    (hv : R₂ ≤ dist v p₂) : juxtMap X₁ X₂ c v = X₁.g v := by
  rw [juxtMap, h₂ v hv, add_sub_cancel_right]


-- @@ L724-727 verbatim
theorem juxtMap_eq_right (X₁ X₂ : FramedLevelSet n)
    (h₁ : X₁.FlatOutside c p₁ R₁) {v : EuclideanSpace ℝ (Fin (n + 1))}
    (hv : R₁ ≤ dist v p₁) : juxtMap X₁ X₂ c v = X₂.g v := by
  rw [juxtMap, h₁ v hv, add_sub_cancel_left]


-- @@ L729-745 verbatim
/-- Zeros of the juxtaposition map lie in exactly one of the two balls and are
zeros of the corresponding piece. -/
theorem juxtMap_zero_cases (X₁ X₂ : FramedLevelSet n) (hc : c ≠ 0)
    (h₁ : X₁.FlatOutside c p₁ R₁) (h₂ : X₂.FlatOutside c p₂ R₂)
    (hsep : R₁ + R₂ < dist p₁ p₂) {v : EuclideanSpace ℝ (Fin (n + 1))}
    (hv : juxtMap X₁ X₂ c v = 0) :
    (dist v p₁ < R₁ ∧ X₁.g v = 0) ∨ (dist v p₂ < R₂ ∧ X₂.g v = 0) := by
  by_cases hd₁ : dist v p₁ < R₁
  · refine Or.inl ⟨hd₁, ?_⟩
    rw [← juxtMap_eq_left X₁ X₂ h₂ (sep_dist_right hsep hd₁.le).le]
    exact hv
  · have hg₂ : X₂.g v = 0 := by
      rw [← juxtMap_eq_right X₁ X₂ h₁ (not_lt.mp hd₁)]
      exact hv
    refine Or.inr ⟨?_, hg₂⟩
    by_contra hd₂
    exact hc ((h₂ v (not_lt.mp hd₂)).symm.trans hg₂)


-- @@ L747-780 verbatim
/-- Juxtaposition (external direct sum) of two spatially separated flat framed
level sets. -/
def juxtapose (X₁ X₂ : FramedLevelSet n) (hc : c ≠ 0)
    (h₁ : X₁.FlatOutside c p₁ R₁) (h₂ : X₂.FlatOutside c p₂ R₂)
    (hsep : R₁ + R₂ < dist p₁ p₂) : FramedLevelSet n where
  g := juxtMap X₁ X₂ c
  smooth := (X₁.smooth.add X₂.smooth).sub contDiff_const
  fiber_bounded := by
    refine (X₁.fiber_bounded.union X₂.fiber_bounded).subset ?_
    intro v hv
    rcases juxtMap_zero_cases X₁ X₂ hc h₁ h₂ hsep hv with ⟨-, hg⟩ | ⟨-, hg⟩
    · exact Set.mem_union_left _ hg
    · exact Set.mem_union_right _ hg
  regular := by
    intro v hv
    rcases juxtMap_zero_cases X₁ X₂ hc h₁ h₂ hsep hv with ⟨hd, hg⟩ | ⟨hd, hg⟩
    · have hopen : IsOpen {w : EuclideanSpace ℝ (Fin (n + 1)) |
          R₂ < dist w p₂} :=
        isOpen_lt continuous_const (continuous_id.dist continuous_const)
      have hvU : R₂ < dist v p₂ := sep_dist_right hsep hd.le
      have hEv : juxtMap X₁ X₂ c =ᶠ[𝓝 v] X₁.g :=
        Filter.eventuallyEq_of_mem (hopen.mem_nhds hvU) fun w hw =>
          juxtMap_eq_left X₁ X₂ h₂ (le_of_lt hw)
      rw [hEv.fderiv_eq]
      exact X₁.regular v hg
    · have hopen : IsOpen {w : EuclideanSpace ℝ (Fin (n + 1)) |
          R₁ < dist w p₁} :=
        isOpen_lt continuous_const (continuous_id.dist continuous_const)
      have hvU : R₁ < dist v p₁ := sep_dist_left hsep hd.le
      have hEv : juxtMap X₁ X₂ c =ᶠ[𝓝 v] X₂.g :=
        Filter.eventuallyEq_of_mem (hopen.mem_nhds hvU) fun w hw =>
          juxtMap_eq_right X₁ X₂ h₁ (le_of_lt hw)
      rw [hEv.fderiv_eq]
      exact X₂.regular v hg


-- @@ L782-805 verbatim
/-- The fiber of the juxtaposition is the (disjoint) union of the two fibers. -/
theorem fiber_juxtapose (X₁ X₂ : FramedLevelSet n) (hc : c ≠ 0)
    (h₁ : X₁.FlatOutside c p₁ R₁) (h₂ : X₂.FlatOutside c p₂ R₂)
    (hsep : R₁ + R₂ < dist p₁ p₂) :
    (X₁.juxtapose X₂ hc h₁ h₂ hsep).fiber = X₁.fiber ∪ X₂.fiber := by
  ext v
  constructor
  · intro hv
    have hv' : juxtMap X₁ X₂ c v = 0 := hv
    rcases juxtMap_zero_cases X₁ X₂ hc h₁ h₂ hsep hv' with ⟨-, hg⟩ | ⟨-, hg⟩
    · exact Set.mem_union_left _ hg
    · exact Set.mem_union_right _ hg
  · intro hv
    rcases hv with hv | hv
    · have hd : dist v p₁ < R₁ :=
        Metric.mem_ball.mp (h₁.fiber_subset_ball hc hv)
      show juxtMap X₁ X₂ c v = 0
      rw [juxtMap_eq_left X₁ X₂ h₂ (sep_dist_right hsep hd.le).le]
      exact hv
    · have hd : dist v p₂ < R₂ :=
        Metric.mem_ball.mp (h₂.fiber_subset_ball hc hv)
      show juxtMap X₁ X₂ c v = 0
      rw [juxtMap_eq_right X₁ X₂ h₁ (sep_dist_left hsep hd.le).le]
      exact hv


-- @@ L807-820 verbatim
/-- The juxtaposition is itself flat outside one large ball, so the operation
iterates. -/
theorem flatOutside_juxtapose (X₁ X₂ : FramedLevelSet n) (hc : c ≠ 0)
    (h₁ : X₁.FlatOutside c p₁ R₁) (h₂ : X₂.FlatOutside c p₂ R₂)
    (hsep : R₁ + R₂ < dist p₁ p₂) (hR₂ : 0 ≤ R₂) :
    (X₁.juxtapose X₂ hc h₁ h₂ hsep).FlatOutside c p₁ (dist p₁ p₂ + R₂) := by
  intro v hv
  have hd₁ : R₁ ≤ dist v p₁ := by linarith
  have hd₂ : R₂ ≤ dist v p₂ := by
    have htri := dist_triangle v p₂ p₁
    rw [dist_comm p₂ p₁] at htri
    linarith
  show juxtMap X₁ X₂ c v = c
  rw [juxtMap, h₁ v hd₁, h₂ v hd₂, add_sub_cancel_right]


-- @@ L822-822 verbatim
end FramedLevelSet


-- @@ L824-824 verbatim
/-! ### The separation weight blending two sign labels -/


-- @@ L826-832 verbatim
/-- Metric partition weight: `1` on the closed ball around `p₁`, `0` on the
closed ball around `p₂`, continuous in between as long as the closed balls are
disjoint. -/
def sepWeight (p₁ p₂ : EuclideanSpace ℝ (Fin (n + 1))) (R₁ R₂ : ℝ)
    (v : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  max (dist v p₂ - R₂) 0 /
    (max (dist v p₁ - R₁) 0 + max (dist v p₂ - R₂) 0)


-- @@ L834-847 verbatim
theorem sepWeight_denom_pos (hsep : R₁ + R₂ < dist p₁ p₂)
    (v : EuclideanSpace ℝ (Fin (n + 1))) :
    0 < max (dist v p₁ - R₁) 0 + max (dist v p₂ - R₂) 0 := by
  by_cases h1 : dist v p₁ ≤ R₁
  · have h2 : R₂ < dist v p₂ := sep_dist_right hsep h1
    have hb : 0 < max (dist v p₂ - R₂) 0 :=
      lt_max_iff.mpr (Or.inl (by linarith))
    have ha : 0 ≤ max (dist v p₁ - R₁) 0 := le_max_right _ _
    linarith
  · have h1' : R₁ < dist v p₁ := not_le.mp h1
    have ha : 0 < max (dist v p₁ - R₁) 0 :=
      lt_max_iff.mpr (Or.inl (by linarith))
    have hb : 0 ≤ max (dist v p₂ - R₂) 0 := le_max_right _ _
    linarith


-- @@ L849-855 verbatim
theorem sepWeight_eq_one (hsep : R₁ + R₂ < dist p₁ p₂)
    {v : EuclideanSpace ℝ (Fin (n + 1))} (hv : dist v p₁ ≤ R₁) :
    sepWeight p₁ p₂ R₁ R₂ v = 1 := by
  have h2 : R₂ < dist v p₂ := sep_dist_right hsep hv
  have ha : max (dist v p₁ - R₁) 0 = 0 := max_eq_right (by linarith)
  rw [sepWeight, ha, zero_add, div_self]
  exact ne_of_gt (lt_max_iff.mpr (Or.inl (by linarith)))


-- @@ L857-860 verbatim
theorem sepWeight_eq_zero {v : EuclideanSpace ℝ (Fin (n + 1))}
    (hv : dist v p₂ ≤ R₂) : sepWeight p₁ p₂ R₁ R₂ v = 0 := by
  have hb : max (dist v p₂ - R₂) 0 = 0 := max_eq_right (by linarith)
  rw [sepWeight, hb, zero_div]


-- @@ L862-871 verbatim
theorem continuous_sepWeight (hsep : R₁ + R₂ < dist p₁ p₂) :
    Continuous (sepWeight p₁ p₂ R₁ R₂) := by
  apply Continuous.div
  · exact ((continuous_id.dist continuous_const).sub continuous_const).max
      continuous_const
  · exact (((continuous_id.dist continuous_const).sub continuous_const).max
      continuous_const).add
      (((continuous_id.dist continuous_const).sub continuous_const).max
        continuous_const)
  · exact fun v => (sepWeight_denom_pos hsep v).ne'


-- @@ L873-873 verbatim
namespace FiberSign


-- @@ L875-875 verbatim
variable {X₁ X₂ : FramedLevelSet n}


-- @@ L877-898 verbatim
/-- Juxtaposition of two fiber signs over the juxtaposition of their
presentations, blended by the separation weight. -/
def juxtapose (S₁ : FiberSign X₁) (S₂ : FiberSign X₂) (hc : c ≠ 0)
    (h₁ : X₁.FlatOutside c p₁ R₁) (h₂ : X₂.FlatOutside c p₂ R₂)
    (hsep : R₁ + R₂ < dist p₁ p₂) :
    FiberSign (X₁.juxtapose X₂ hc h₁ h₂ hsep) where
  toFun v := sepWeight p₁ p₂ R₁ R₂ v * S₁ v +
    (1 - sepWeight p₁ p₂ R₁ R₂ v) * S₂ v
  continuous := ((continuous_sepWeight hsep).mul S₁.continuous).add
    ((continuous_const.sub (continuous_sepWeight hsep)).mul S₂.continuous)
  nonzero := by
    intro v hv
    rw [FramedLevelSet.fiber_juxtapose X₁ X₂ hc h₁ h₂ hsep] at hv
    rcases hv with hv | hv
    · have hd : dist v p₁ ≤ R₁ :=
        (Metric.mem_ball.mp (h₁.fiber_subset_ball hc hv)).le
      rw [sepWeight_eq_one hsep hd, one_mul, sub_self, zero_mul, add_zero]
      exact S₁.nonzero v hv
    · have hd : dist v p₂ ≤ R₂ :=
        (Metric.mem_ball.mp (h₂.fiber_subset_ball hc hv)).le
      rw [sepWeight_eq_zero hd, zero_mul, zero_add, sub_zero, one_mul]
      exact S₂.nonzero v hv


-- @@ L900-908 verbatim
theorem juxtapose_apply_left (S₁ : FiberSign X₁) (S₂ : FiberSign X₂)
    (hc : c ≠ 0) (h₁ : X₁.FlatOutside c p₁ R₁) (h₂ : X₂.FlatOutside c p₂ R₂)
    (hsep : R₁ + R₂ < dist p₁ p₂) {v : EuclideanSpace ℝ (Fin (n + 1))}
    (hv : dist v p₁ ≤ R₁) :
    S₁.juxtapose S₂ hc h₁ h₂ hsep v = S₁ v := by
  show sepWeight p₁ p₂ R₁ R₂ v * S₁ v +
    (1 - sepWeight p₁ p₂ R₁ R₂ v) * S₂ v = S₁ v
  rw [sepWeight_eq_one hsep hv]
  ring


-- @@ L910-918 verbatim
theorem juxtapose_apply_right (S₁ : FiberSign X₁) (S₂ : FiberSign X₂)
    (hc : c ≠ 0) (h₁ : X₁.FlatOutside c p₁ R₁) (h₂ : X₂.FlatOutside c p₂ R₂)
    (hsep : R₁ + R₂ < dist p₁ p₂) {v : EuclideanSpace ℝ (Fin (n + 1))}
    (hv : dist v p₂ ≤ R₂) :
    S₁.juxtapose S₂ hc h₁ h₂ hsep v = S₂ v := by
  show sepWeight p₁ p₂ R₁ R₂ v * S₁ v +
    (1 - sepWeight p₁ p₂ R₁ R₂ v) * S₂ v = S₂ v
  rw [sepWeight_eq_zero hv]
  ring


-- @@ L920-955 verbatim
/-- The positive components of a juxtaposition are the union of the positive
components of the pieces. -/
theorem positivePart_juxtapose (S₁ : FiberSign X₁) (S₂ : FiberSign X₂)
    (hc : c ≠ 0) (h₁ : X₁.FlatOutside c p₁ R₁) (h₂ : X₂.FlatOutside c p₂ R₂)
    (hsep : R₁ + R₂ < dist p₁ p₂) :
    (S₁.juxtapose S₂ hc h₁ h₂ hsep).positivePart =
      S₁.positivePart ∪ S₂.positivePart := by
  ext v
  constructor
  · rintro ⟨hfib, hpos⟩
    rw [FramedLevelSet.fiber_juxtapose X₁ X₂ hc h₁ h₂ hsep] at hfib
    rcases hfib with hv | hv
    · have hd : dist v p₁ ≤ R₁ :=
        (Metric.mem_ball.mp (h₁.fiber_subset_ball hc hv)).le
      rw [juxtapose_apply_left S₁ S₂ hc h₁ h₂ hsep hd] at hpos
      exact Or.inl ⟨hv, hpos⟩
    · have hd : dist v p₂ ≤ R₂ :=
        (Metric.mem_ball.mp (h₂.fiber_subset_ball hc hv)).le
      rw [juxtapose_apply_right S₁ S₂ hc h₁ h₂ hsep hd] at hpos
      exact Or.inr ⟨hv, hpos⟩
  · intro hv
    rcases hv with ⟨hfib, hpos⟩ | ⟨hfib, hpos⟩
    · have hd : dist v p₁ ≤ R₁ :=
        (Metric.mem_ball.mp (h₁.fiber_subset_ball hc hfib)).le
      refine ⟨?_, ?_⟩
      · rw [FramedLevelSet.fiber_juxtapose X₁ X₂ hc h₁ h₂ hsep]
        exact Set.mem_union_left _ hfib
      · rw [juxtapose_apply_left S₁ S₂ hc h₁ h₂ hsep hd]
        exact hpos
    · have hd : dist v p₂ ≤ R₂ :=
        (Metric.mem_ball.mp (h₂.fiber_subset_ball hc hfib)).le
      refine ⟨?_, ?_⟩
      · rw [FramedLevelSet.fiber_juxtapose X₁ X₂ hc h₁ h₂ hsep]
        exact Set.mem_union_right _ hfib
      · rw [juxtapose_apply_right S₁ S₂ hc h₁ h₂ hsep hd]
        exact hpos


-- @@ L957-957 verbatim
end FiberSign


-- @@ L959-959 verbatim
/-! ### Translation equivariance -/


-- @@ L961-961 verbatim
namespace FramedLevelSet


-- @@ L963-988 verbatim
/-- Translation of a framed level-set presentation by a vector `w`. -/
def translate (X : FramedLevelSet n) (w : EuclideanSpace ℝ (Fin (n + 1))) :
    FramedLevelSet n where
  g v := X.g (v - w)
  smooth := X.smooth.comp (contDiff_id.sub contDiff_const)
  fiber_bounded := by
    obtain ⟨r, hr⟩ := X.fiber_bounded.subset_closedBall 0
    apply (Metric.isBounded_closedBall (x := w) (r := r)).subset
    intro v hv
    have hv' : X.g (v - w) = 0 := hv
    have hmem := hr (show v - w ∈ {u | X.g u = 0} from hv')
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hmem
  regular := by
    intro v hv
    have hgd : HasFDerivAt X.g (fderiv ℝ X.g (v - w)) (v - w) :=
      (X.smooth.differentiable infty_ne_zero _).hasFDerivAt
    have haff : HasFDerivAt
        (fun u : EuclideanSpace ℝ (Fin (n + 1)) => u - w)
        (ContinuousLinearMap.id ℝ _) v := (hasFDerivAt_id v).sub_const w
    have hEq : fderiv ℝ (fun u => X.g (u - w)) v =
        (fderiv ℝ X.g (v - w)).comp (ContinuousLinearMap.id ℝ _) :=
      (hgd.comp v haff).fderiv
    rw [hEq, ContinuousLinearMap.comp_id]
    exact X.regular _ hv


-- @@ L990-993 verbatim
@[simp] theorem translate_g (X : FramedLevelSet n)
    (w v : EuclideanSpace ℝ (Fin (n + 1))) :
    (X.translate w).g v = X.g (v - w) :=
  rfl


-- @@ L995-998 verbatim
theorem mem_fiber_translate (X : FramedLevelSet n)
    {w v : EuclideanSpace ℝ (Fin (n + 1))} :
    v ∈ (X.translate w).fiber ↔ v - w ∈ X.fiber :=
  Iff.rfl


-- @@ L1000-1009 verbatim
/-- Translation moves the flatness ball along. -/
theorem FlatOutside.translate {X : FramedLevelSet n}
    (h : X.FlatOutside c p R) (w : EuclideanSpace ℝ (Fin (n + 1))) :
    (X.translate w).FlatOutside c (p + w) R := by
  intro v hv
  show X.g (v - w) = c
  apply h
  have hdist : dist (v - w) p = dist v (p + w) := by
    rw [← dist_add_right (v - w) p w, sub_add_cancel]
  rwa [hdist]


-- @@ L1011-1011 verbatim
end FramedLevelSet


-- @@ L1013-1013 verbatim
namespace FiberSign


-- @@ L1015-1020 verbatim
/-- Translation of a fiber sign. -/
def translate {X : FramedLevelSet n} (S : FiberSign X)
    (w : EuclideanSpace ℝ (Fin (n + 1))) : FiberSign (X.translate w) where
  toFun v := S (v - w)
  continuous := S.continuous.comp (continuous_id.sub continuous_const)
  nonzero v hv := S.nonzero _ hv


-- @@ L1022-1025 verbatim
@[simp] theorem translate_apply {X : FramedLevelSet n} (S : FiberSign X)
    (w v : EuclideanSpace ℝ (Fin (n + 1))) :
    S.translate w v = S (v - w) :=
  rfl


-- @@ L1027-1030 verbatim
theorem mem_positivePart_translate {X : FramedLevelSet n} (S : FiberSign X)
    {w v : EuclideanSpace ℝ (Fin (n + 1))} :
    v ∈ (S.translate w).positivePart ↔ v - w ∈ S.positivePart :=
  Iff.rfl


-- @@ L1032-1032 verbatim
end FiberSign


-- @@ L1034-1034 verbatim
/-! ### Juxtaposition and translation of signed cobordisms -/


-- @@ L1036-1036 verbatim
namespace FramedLevelCobordism


-- @@ L1038-1043 verbatim
/-- The cobordism map equals `c` whenever the spatial part is at distance
`≥ R` from `p`, at every time. -/
def SpatialFlatOutside (C : FramedLevelCobordism n)
    (c : EuclideanSpace ℝ (Fin n)) (p : EuclideanSpace ℝ (Fin (n + 1)))
    (R : ℝ) : Prop :=
  ∀ v, R ≤ dist (initCLM (n + 1) v) p → C.G v = c


-- @@ L1045-1049 verbatim
theorem SpatialFlatOutside.flatOutside_X₀ {C : FramedLevelCobordism n}
    (h : C.SpatialFlatOutside c p R) : C.X₀.FlatOutside c p R := by
  intro x hx
  have h0 := h (spaceTime x 0) (by rwa [initCLM_spaceTime])
  rwa [C.collar_zero x 0 (by norm_num)] at h0


-- @@ L1051-1055 verbatim
theorem SpatialFlatOutside.flatOutside_X₁ {C : FramedLevelCobordism n}
    (h : C.SpatialFlatOutside c p R) : C.X₁.FlatOutside c p R := by
  intro x hx
  have h1 := h (spaceTime x 1) (by rwa [initCLM_spaceTime])
  rwa [C.collar_one x 1 (by norm_num)] at h1


-- @@ L1057-1061 verbatim
/-- The cylinder on a flat presentation is spatially flat. -/
theorem spatialFlatOutside_refl {X : FramedLevelSet n}
    (h : X.FlatOutside c p R) :
    (FramedLevelCobordism.refl X).SpatialFlatOutside c p R :=
  fun v hv => h _ hv


-- @@ L1063-1135 verbatim
/-- Juxtaposition of two spatially separated flat framed level cobordisms. -/
def juxtapose (C D : FramedLevelCobordism n) (hc : c ≠ 0)
    (hC : C.SpatialFlatOutside c p₁ R₁) (hD : D.SpatialFlatOutside c p₂ R₂)
    (hsep : R₁ + R₂ < dist p₁ p₂) : FramedLevelCobordism n where
  X₀ := C.X₀.juxtapose D.X₀ hc hC.flatOutside_X₀ hD.flatOutside_X₀ hsep
  X₁ := C.X₁.juxtapose D.X₁ hc hC.flatOutside_X₁ hD.flatOutside_X₁ hsep
  G v := C.G v + D.G v - c
  smooth := (C.smooth.add D.smooth).sub contDiff_const
  spatial_bounded := by
    refine ⟨max (‖p₁‖ + R₁) (‖p₂‖ + R₂), ?_⟩
    intro v hv
    by_cases hd₁ : dist (initCLM (n + 1) v) p₁ < R₁
    · have h1 : ‖initCLM (n + 1) v‖ ≤ ‖p₁‖ + R₁ := by
        have htri := dist_triangle (initCLM (n + 1) v) p₁ 0
        rw [dist_zero_right, dist_zero_right] at htri
        linarith
      exact h1.trans (le_max_left _ _)
    · by_cases hd₂ : dist (initCLM (n + 1) v) p₂ < R₂
      · have h2 : ‖initCLM (n + 1) v‖ ≤ ‖p₂‖ + R₂ := by
          have htri := dist_triangle (initCLM (n + 1) v) p₂ 0
          rw [dist_zero_right, dist_zero_right] at htri
          linarith
        exact h2.trans (le_max_right _ _)
      · exfalso
        have h1 := hC v (not_lt.mp hd₁)
        have h2 := hD v (not_lt.mp hd₂)
        rw [h1, h2, add_sub_cancel_right] at hv
        exact hc hv
  regular := by
    intro v hv
    by_cases hd₁ : dist (initCLM (n + 1) v) p₁ < R₁
    · have hopen : IsOpen {w : EuclideanSpace ℝ (Fin (n + 1 + 1)) |
          R₂ < dist (initCLM (n + 1) w) p₂} :=
        isOpen_lt continuous_const
          ((initCLM (n + 1)).continuous.dist continuous_const)
      have hvU : R₂ < dist (initCLM (n + 1) v) p₂ :=
        sep_dist_right hsep hd₁.le
      have hEv : (fun w => C.G w + D.G w - c) =ᶠ[𝓝 v] C.G :=
        Filter.eventuallyEq_of_mem (hopen.mem_nhds hvU) fun w hw => by
          rw [hD w (le_of_lt hw), add_sub_cancel_right]
      have hCv : C.G v = 0 := by
        have hDc := hD v hvU.le
        rwa [hDc, add_sub_cancel_right] at hv
      rw [hEv.fderiv_eq]
      exact C.regular v hCv
    · have hDv : D.G v = 0 := by
        have hCc := hC v (not_lt.mp hd₁)
        rwa [hCc, add_sub_cancel_left] at hv
      have hd₂ : dist (initCLM (n + 1) v) p₂ < R₂ := by
        by_contra hd₂
        have hDc := hD v (not_lt.mp hd₂)
        exact hc (hDc.symm.trans hDv)
      have hopen : IsOpen {w : EuclideanSpace ℝ (Fin (n + 1 + 1)) |
          R₁ < dist (initCLM (n + 1) w) p₁} :=
        isOpen_lt continuous_const
          ((initCLM (n + 1)).continuous.dist continuous_const)
      have hvU : R₁ < dist (initCLM (n + 1) v) p₁ :=
        sep_dist_left hsep hd₂.le
      have hEv : (fun w => C.G w + D.G w - c) =ᶠ[𝓝 v] D.G :=
        Filter.eventuallyEq_of_mem (hopen.mem_nhds hvU) fun w hw => by
          rw [hC w (le_of_lt hw), add_sub_cancel_left]
      rw [hEv.fderiv_eq]
      exact D.regular v hDv
  collar_zero := by
    intro x t ht
    show C.G (spaceTime x t) + D.G (spaceTime x t) - c = _
    rw [C.collar_zero x t ht, D.collar_zero x t ht]
    rfl
  collar_one := by
    intro x t ht
    show C.G (spaceTime x t) + D.G (spaceTime x t) - c = _
    rw [C.collar_one x t ht, D.collar_one x t ht]
    rfl


-- @@ L1137-1151 verbatim
/-- The juxtaposed cobordism is itself spatially flat outside one large ball. -/
theorem spatialFlatOutside_juxtapose (C D : FramedLevelCobordism n)
    (hc : c ≠ 0) (hC : C.SpatialFlatOutside c p₁ R₁)
    (hD : D.SpatialFlatOutside c p₂ R₂) (hsep : R₁ + R₂ < dist p₁ p₂)
    (hR₂ : 0 ≤ R₂) :
    (C.juxtapose D hc hC hD hsep).SpatialFlatOutside c p₁
      (dist p₁ p₂ + R₂) := by
  intro v hv
  have hd₁ : R₁ ≤ dist (initCLM (n + 1) v) p₁ := by linarith
  have hd₂ : R₂ ≤ dist (initCLM (n + 1) v) p₂ := by
    have htri := dist_triangle (initCLM (n + 1) v) p₂ p₁
    rw [dist_comm p₂ p₁] at htri
    linarith
  show C.G v + D.G v - c = c
  rw [hC v hd₁, hD v hd₂, add_sub_cancel_right]


-- @@ L1153-1153 verbatim
end FramedLevelCobordism


-- @@ L1155-1155 verbatim
namespace SignedFramedLevelCobordism


-- @@ L1157-1158 verbatim
variable {X₁ Y₁ X₂ Y₂ : FramedLevelSet n} {S₁ : FiberSign X₁}
  {T₁ : FiberSign Y₁} {S₂ : FiberSign X₂} {T₂ : FiberSign Y₂}


-- @@ L1160-1164 verbatim
/-- Spatial flatness of a signed cobordism. -/
def SpatialFlatOutside (C : SignedFramedLevelCobordism S₁ T₁)
    (c : EuclideanSpace ℝ (Fin n)) (p : EuclideanSpace ℝ (Fin (n + 1)))
    (R : ℝ) : Prop :=
  C.cobordism.SpatialFlatOutside c p R


-- @@ L1166-1169 verbatim
theorem SpatialFlatOutside.flatOutside_source
    {C : SignedFramedLevelCobordism S₁ T₁}
    (h : C.SpatialFlatOutside c p R) : X₁.FlatOutside c p R :=
  C.source_eq ▸ FramedLevelCobordism.SpatialFlatOutside.flatOutside_X₀ h


-- @@ L1171-1174 verbatim
theorem SpatialFlatOutside.flatOutside_target
    {C : SignedFramedLevelCobordism S₁ T₁}
    (h : C.SpatialFlatOutside c p R) : Y₁.FlatOutside c p R :=
  C.target_eq ▸ FramedLevelCobordism.SpatialFlatOutside.flatOutside_X₁ h


-- @@ L1176-1180 verbatim
/-- The signed cylinder on a flat presentation is spatially flat. -/
theorem spatialFlatOutside_refl {X : FramedLevelSet n} (S : FiberSign X)
    (h : X.FlatOutside c p R) :
    (SignedFramedLevelCobordism.refl S).SpatialFlatOutside c p R :=
  fun v hv => h _ hv


-- @@ L1182-1244 verbatim
/-- Juxtaposition of two spatially separated signed framed level cobordisms:
the underlying maps are summed against the shared background constant and the
sign labels are blended by the spatial separation weight. -/
def juxtapose (C : SignedFramedLevelCobordism S₁ T₁)
    (D : SignedFramedLevelCobordism S₂ T₂) (hc : c ≠ 0)
    (hC : C.SpatialFlatOutside c p₁ R₁) (hD : D.SpatialFlatOutside c p₂ R₂)
    (hsep : R₁ + R₂ < dist p₁ p₂) :
    SignedFramedLevelCobordism
      (S₁.juxtapose S₂ hc hC.flatOutside_source hD.flatOutside_source hsep)
      (T₁.juxtapose T₂ hc hC.flatOutside_target hD.flatOutside_target hsep)
      where
  cobordism := C.cobordism.juxtapose D.cobordism hc hC hD hsep
  source_eq := by
    apply FramedLevelSet.eq_of_g_eq
    funext v
    show C.cobordism.X₀.g v + D.cobordism.X₀.g v - c = X₁.g v + X₂.g v - c
    rw [C.source_eq, D.source_eq]
  target_eq := by
    apply FramedLevelSet.eq_of_g_eq
    funext v
    show C.cobordism.X₁.g v + D.cobordism.X₁.g v - c = Y₁.g v + Y₂.g v - c
    rw [C.target_eq, D.target_eq]
  toFun v := sepWeight p₁ p₂ R₁ R₂ (initCLM (n + 1) v) * C v +
    (1 - sepWeight p₁ p₂ R₁ R₂ (initCLM (n + 1) v)) * D v
  continuous := (((continuous_sepWeight hsep).comp
      (initCLM (n + 1)).continuous).mul C.continuous).add
    ((continuous_const.sub ((continuous_sepWeight hsep).comp
      (initCLM (n + 1)).continuous)).mul D.continuous)
  nonzero := by
    intro v hv
    change C.cobordism.G v + D.cobordism.G v - c = 0 at hv
    by_cases hd₁ : dist (initCLM (n + 1) v) p₁ < R₁
    · have h2 : R₂ ≤ dist (initCLM (n + 1) v) p₂ :=
        (sep_dist_right hsep hd₁.le).le
      have hCv : C.cobordism.G v = 0 := by
        rw [hD v h2, add_sub_cancel_right] at hv
        exact hv
      rw [sepWeight_eq_one hsep hd₁.le, one_mul, sub_self, zero_mul, add_zero]
      exact C.nonzero v hCv
    · have hDv : D.cobordism.G v = 0 := by
        rw [hC v (not_lt.mp hd₁), add_sub_cancel_left] at hv
        exact hv
      have hd₂ : dist (initCLM (n + 1) v) p₂ < R₂ := by
        by_contra hd₂
        exact hc ((hD v (not_lt.mp hd₂)).symm.trans hDv)
      rw [sepWeight_eq_zero hd₂.le, zero_mul, zero_add, sub_zero, one_mul]
      exact D.nonzero v hDv
  collar_zero := by
    intro x t ht
    show sepWeight p₁ p₂ R₁ R₂ (initCLM (n + 1) (spaceTime x t)) *
        C (spaceTime x t) +
      (1 - sepWeight p₁ p₂ R₁ R₂ (initCLM (n + 1) (spaceTime x t))) *
        D (spaceTime x t) = _
    rw [initCLM_spaceTime, C.collar_zero x t ht, D.collar_zero x t ht]
    rfl
  collar_one := by
    intro x t ht
    show sepWeight p₁ p₂ R₁ R₂ (initCLM (n + 1) (spaceTime x t)) *
        C (spaceTime x t) +
      (1 - sepWeight p₁ p₂ R₁ R₂ (initCLM (n + 1) (spaceTime x t))) *
        D (spaceTime x t) = _
    rw [initCLM_spaceTime, C.collar_one x t ht, D.collar_one x t ht]
    rfl


-- @@ L1246-1257 verbatim
/-- Adjoining an unchanged, spatially separated tail presentation to a signed
cobordism: juxtapose with the signed cylinder on the tail. -/
theorem nonempty_juxtapose_tail (C : SignedFramedLevelCobordism S₁ T₁)
    (hc : c ≠ 0) (hC : C.SpatialFlatOutside c p₁ R₁)
    (S₂ : FiberSign X₂) (h₂ : X₂.FlatOutside c p₂ R₂)
    (hsep : R₁ + R₂ < dist p₁ p₂)
    (hX₁ : X₁.FlatOutside c p₁ R₁) (hY₁ : Y₁.FlatOutside c p₁ R₁) :
    Nonempty (SignedFramedLevelCobordism
      (S₁.juxtapose S₂ hc hX₁ h₂ hsep)
      (T₁.juxtapose S₂ hc hY₁ h₂ hsep)) :=
  ⟨C.juxtapose (SignedFramedLevelCobordism.refl S₂) hc hC
    (spatialFlatOutside_refl S₂ h₂) hsep⟩


-- @@ L1259-1259 verbatim
end SignedFramedLevelCobordism


-- @@ L1261-1261 verbatim
end Juxtaposition


-- @@ L1263-1263 verbatim
end Submission
