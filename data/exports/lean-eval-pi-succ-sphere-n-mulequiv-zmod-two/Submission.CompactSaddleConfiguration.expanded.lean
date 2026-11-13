import Mathlib
import Submission.CompactBirthConfiguration
import Submission.NormalizeMoves
import Submission.StandardSaddleFrameWinding
import Submission.RegularSlabEndpointDelta


-- @@ L7-21 verbatim
/-!
# A spatially flat Cassini saddle

The literal Cassini saddle is polynomial and therefore cannot be fed directly
to the separated-support juxtaposition operation.  Here it is blended with a
common nonzero last-coordinate vector.  The blend is unchanged on the squared
ball of radius `2` and constant outside the ball of radius `3`.

No new zero is introduced in the transition annulus.  Indeed, if all transverse
coordinates vanish and `r² ≥ 4`, then
`cassiniQ ≥ r⁴ - 2r² ≥ 8`, whereas the event height contributes at most
`1/2`.  This also makes the compactified map identical to the original map on
a neighborhood of its whole zero surface, so regularity and endpoint frames
are inherited literally.
-/


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
open Set Function Metric

-- @@ L26-26 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L28-28 verbatim
namespace Submission

-- @@ L29-29 verbatim
namespace CompactSaddle


-- @@ L31-31 verbatim
variable (m : ℕ)


-- @@ L33-33 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 3))

-- @@ L34-34 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (m + 4))

-- @@ L35-35 verbatim
local notation "F" => EuclideanSpace ℝ (Fin (m + 2))


-- @@ L37-40 verbatim
/-- Saddle cutoff: zero for squared norm at most four and one from squared norm
nine onward. -/
def cutoff {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) : ℝ :=
  Real.smoothTransition ((CompactBirth.normSq x - 4) / 5)


-- @@ L42-45 verbatim
lemma contDiff_cutoff {k : ℕ} :
    ContDiff ℝ ∞ (cutoff : EuclideanSpace ℝ (Fin k) → ℝ) := by
  exact Real.smoothTransition.contDiff.comp
    (((CompactBirth.contDiff_normSq).sub contDiff_const).div_const 5)


-- @@ L47-48 verbatim
lemma cutoff_nonneg {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) :
    0 ≤ cutoff x := Real.smoothTransition.nonneg _


-- @@ L50-51 verbatim
lemma cutoff_le_one {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) :
    cutoff x ≤ 1 := Real.smoothTransition.le_one _


-- @@ L53-56 verbatim
lemma cutoff_eq_zero {k : ℕ} {x : EuclideanSpace ℝ (Fin k)}
    (hx : CompactBirth.normSq x ≤ 4) : cutoff x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  linarith


-- @@ L58-61 verbatim
lemma cutoff_eq_one {k : ℕ} {x : EuclideanSpace ℝ (Fin k)}
    (hx : 9 ≤ CompactBirth.normSq x) : cutoff x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  linarith


-- @@ L63-65 verbatim
/-- Common nonzero background vector. -/
def background : F :=
  WithLp.toLp 2 (Fin.lastCases 1 (fun _ : Fin (m + 1) => 0))


-- @@ L67-69 verbatim
@[simp] lemma background_apply_last :
    background m (Fin.last (m + 1)) = 1 := by
  simp [background]


-- @@ L71-73 verbatim
@[simp] lemma background_apply_castSucc (j : Fin (m + 1)) :
    background m j.castSucc = 0 := by
  simp [background]


-- @@ L75-78 verbatim
lemma background_ne_zero : background m ≠ 0 := by
  intro h
  have := congrArg (fun q : F => q (Fin.last (m + 1))) h
  simp at this


-- @@ L80-82 verbatim
/-- Compactified Cassini slice. -/
def levelMap (a : ℝ) (x : E) : F :=
  (1 - cutoff x) • StandardSaddle.levelMap m a x + cutoff x • background m


-- @@ L84-87 verbatim
lemma contDiff_levelMap (a : ℝ) : ContDiff ℝ ∞ (levelMap m a) := by
  exact ((contDiff_const.sub contDiff_cutoff).smul
    (StandardSaddle.contDiff_levelMap m a)).add
    (contDiff_cutoff.smul contDiff_const)


-- @@ L89-91 verbatim
@[simp] lemma levelMap_apply_castSucc (a : ℝ) (x : E) (j : Fin (m + 1)) :
    levelMap m a x j.castSucc = (1 - cutoff x) * x j.castSucc.castSucc := by
  simp [levelMap, StandardSaddle.levelMap_apply_castSucc]


-- @@ L93-96 verbatim
@[simp] lemma levelMap_apply_last (a : ℝ) (x : E) :
    levelMap m a x (Fin.last (m + 1)) =
      (1 - cutoff x) * (StandardSaddle.cassiniQ m x - a) + cutoff x := by
  simp [levelMap, StandardSaddle.levelMap_apply_last]


-- @@ L98-101 verbatim
/-- Compactified Cassini event. -/
def eventMap (v : E') : F :=
  (1 - cutoff (initCLM (m + 3) v)) • StandardSaddle.eventMap m v +
    cutoff (initCLM (m + 3) v) • background m


-- @@ L103-108 verbatim
lemma contDiff_eventMap : ContDiff ℝ ∞ (eventMap m) := by
  have hcut : ContDiff ℝ ∞
      (fun v : E' => cutoff (initCLM (m + 3) v)) :=
    contDiff_cutoff.comp (initCLM (m + 3)).contDiff
  exact ((contDiff_const.sub hcut).smul
    (StandardSaddle.contDiff_eventMap m)).add (hcut.smul contDiff_const)


-- @@ L110-114 verbatim
@[simp] lemma eventMap_apply_castSucc (v : E') (j : Fin (m + 1)) :
    eventMap m v j.castSucc =
      (1 - cutoff (initCLM (m + 3) v)) * v j.castSucc.castSucc.castSucc := by
  simp [eventMap, StandardSaddle.eventMap,
    StandardSaddle.levelMap_apply_castSucc]


-- @@ L116-123 verbatim
@[simp] lemma eventMap_apply_last (v : E') :
    eventMap m v (Fin.last (m + 1)) =
      (1 - cutoff (initCLM (m + 3) v)) *
          (StandardSaddle.cassiniQ m (initCLM (m + 3) v) -
            StandardSaddle.height (vertC v) / 2) +
        cutoff (initCLM (m + 3) v) := by
  simp [eventMap, StandardSaddle.eventMap,
    StandardSaddle.levelMap_apply_last]


-- @@ L125-129 verbatim
lemma eventMap_spaceTime (x : E) (t : ℝ) :
    eventMap m (spaceTime x t) =
      levelMap m (StandardSaddle.height t / 2) x := by
  rw [eventMap, levelMap, initCLM_spaceTime,
    StandardSaddle.eventMap_spaceTime]


-- @@ L131-136 verbatim
lemma eventMap_cutoff_ne_one {v : E'} (hv : eventMap m v = 0) :
    cutoff (initCLM (m + 3) v) ≠ 1 := by
  intro hc
  have hlast := congrArg (fun q : F => q (Fin.last (m + 1))) hv
  rw [eventMap_apply_last, hc] at hlast
  norm_num at hlast


-- @@ L138-146 verbatim
lemma transverse_eq_zero_of_eventMap_eq_zero {v : E'}
    (hv : eventMap m v = 0) (j : Fin (m + 1)) :
    v j.castSucc.castSucc.castSucc = 0 := by
  have hcoord := congrArg (fun q : F => q j.castSucc) hv
  rw [eventMap_apply_castSucc] at hcoord
  simp only [PiLp.zero_apply] at hcoord
  have hc : cutoff (initCLM (m + 3) v) < 1 :=
    lt_of_le_of_ne (cutoff_le_one _) (eventMap_cutoff_ne_one m hv)
  exact (mul_eq_zero.mp hcoord).resolve_left (sub_ne_zero.mpr hc.ne')


-- @@ L148-159 verbatim
lemma normSq_init_eq_radiusSq_of_eventMap_eq_zero {v : E'}
    (hv : eventMap m v = 0) :
    CompactBirth.normSq (initCLM (m + 3) v) =
      StandardSaddle.radiusSq m (initCLM (m + 3) v) := by
  unfold CompactBirth.normSq StandardSaddle.radiusSq
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [initCLM_apply]
  have hz : ∀ j : Fin (m + 1), v j.castSucc.castSucc.castSucc ^ 2 = 0 :=
    fun j => by
      rw [transverse_eq_zero_of_eventMap_eq_zero m hv j, zero_pow (by norm_num)]
  simp only [hz, Finset.sum_const_zero, zero_add]
  rfl


-- @@ L161-183 verbatim
lemma standard_event_normSq_le_three {v : E'}
    (hv : StandardSaddle.eventMap m v = 0) :
    CompactBirth.normSq (initCLM (m + 3) v) ≤ 3 := by
  have hq := StandardSaddle.cassiniQ_eq_height_of_eventMap_eq_zero m hv
  have hqform := StandardSaddle.cassiniQ_eq m (initCLM (m + 3) v)
  rw [hqform] at hq
  have hupper := StandardSaddle.height_le_one (vertC v)
  have hnorm : CompactBirth.normSq (initCLM (m + 3) v) =
      StandardSaddle.radiusSq m (initCLM (m + 3) v) := by
    unfold CompactBirth.normSq StandardSaddle.radiusSq
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [initCLM_apply]
    have hz : ∀ j : Fin (m + 1), v j.castSucc.castSucc.castSucc ^ 2 = 0 :=
      fun j => by
        rw [StandardSaddle.transverse_eq_zero_of_eventMap_eq_zero m hv j,
          zero_pow (by norm_num)]
    simp only [hz, Finset.sum_const_zero, zero_add]
    rfl
  rw [hnorm]
  unfold StandardSaddle.radiusSq at hq ⊢
  simp only [initCLM_apply] at hq ⊢
  nlinarith [sq_nonneg (v (StandardSaddle.planeFirst m).castSucc),
    sq_nonneg (v (StandardSaddle.planeSecond m).castSucc)]


-- @@ L185-225 verbatim
/-- The compactification introduces no event-surface points. -/
theorem eventMap_zero_iff (v : E') :
    eventMap m v = 0 ↔ StandardSaddle.eventMap m v = 0 := by
  constructor
  · intro hv
    have hc_lt : cutoff (initCLM (m + 3) v) < 1 :=
      lt_of_le_of_ne (cutoff_le_one _) (eventMap_cutoff_ne_one m hv)
    have hr := normSq_init_eq_radiusSq_of_eventMap_eq_zero m hv
    have hlast := congrArg (fun q : F => q (Fin.last (m + 1))) hv
    rw [eventMap_apply_last] at hlast
    simp only [PiLp.zero_apply] at hlast
    have hslt : CompactBirth.normSq (initCLM (m + 3) v) < 4 := by
      by_contra hnot
      have hsge : 4 ≤ CompactBirth.normSq (initCLM (m + 3) v) := not_lt.mp hnot
      have hheight := StandardSaddle.height_le_one (vertC v)
      have hc0 := cutoff_nonneg (initCLM (m + 3) v)
      have hqform := StandardSaddle.cassiniQ_eq m (initCLM (m + 3) v)
      rw [hr] at hsge
      unfold StandardSaddle.radiusSq at hsge
      simp only [initCLM_apply] at hsge
      have hqpos : 0 <
          StandardSaddle.cassiniQ m (initCLM (m + 3) v) -
            StandardSaddle.height (vertC v) / 2 := by
        rw [hqform]
        unfold StandardSaddle.radiusSq
        simp only [initCLM_apply]
        nlinarith [sq_nonneg (v (StandardSaddle.planeFirst m).castSucc),
          sq_nonneg (v (StandardSaddle.planeSecond m).castSucc)]
      have hprod : 0 <
          (1 - cutoff (initCLM (m + 3) v)) *
            (StandardSaddle.cassiniQ m (initCLM (m + 3) v) -
              StandardSaddle.height (vertC v) / 2) :=
        mul_pos (sub_pos.mpr hc_lt) hqpos
      nlinarith
    have hc0 : cutoff (initCLM (m + 3) v) = 0 := cutoff_eq_zero hslt.le
    simpa [eventMap, hc0] using hv
  · intro hv
    have hs : CompactBirth.normSq (initCLM (m + 3) v) ≤ 4 :=
      (standard_event_normSq_le_three m hv).trans (by norm_num)
    have hc0 : cutoff (initCLM (m + 3) v) = 0 := cutoff_eq_zero hs
    simp [eventMap, hc0, hv]


-- @@ L227-233 verbatim
theorem levelMap_neg_half_zero_iff (x : E) :
    levelMap m (-1 / 2) x = 0 ↔
      StandardSaddle.levelMap m (-1 / 2) x = 0 := by
  have hh : StandardSaddle.height 0 / 2 = -1 / 2 := by
    rw [StandardSaddle.height_of_le_quarter (by norm_num)]
  rw [← hh, ← eventMap_spaceTime m x 0, eventMap_zero_iff,
    StandardSaddle.eventMap_spaceTime]


-- @@ L235-241 verbatim
theorem levelMap_half_zero_iff (x : E) :
    levelMap m (1 / 2) x = 0 ↔
      StandardSaddle.levelMap m (1 / 2) x = 0 := by
  have hh : StandardSaddle.height 1 / 2 = 1 / 2 := by
    rw [StandardSaddle.height_of_threeQuarter_le (by norm_num)]
  rw [← hh, ← eventMap_spaceTime m x 1, eventMap_zero_iff,
    StandardSaddle.eventMap_spaceTime]


-- @@ L243-251 verbatim
lemma levelMap_eventuallyEq_standard {a : ℝ} {x : E}
    (hx : CompactBirth.normSq x < 4) :
    Filter.EventuallyEq (nhds x) (levelMap m a)
      (StandardSaddle.levelMap m a) := by
  have hopen : IsOpen {y : E | CompactBirth.normSq y < 4} :=
    isOpen_lt CompactBirth.contDiff_normSq.continuous continuous_const
  exact Filter.eventuallyEq_of_mem (hopen.mem_nhds hx) fun y hy => by
    rw [levelMap, cutoff_eq_zero hy.le]
    simp


-- @@ L253-266 verbatim
lemma eventMap_eventuallyEq_standard {v : E'}
    (hv : StandardSaddle.eventMap m v = 0) :
    Filter.EventuallyEq (nhds v) (eventMap m)
      (StandardSaddle.eventMap m) := by
  have hslt : CompactBirth.normSq (initCLM (m + 3) v) < 4 :=
    lt_of_le_of_lt (standard_event_normSq_le_three m hv) (by norm_num)
  have hopen : IsOpen
      {w : E' | CompactBirth.normSq (initCLM (m + 3) w) < 4} :=
    isOpen_lt
      (CompactBirth.contDiff_normSq.continuous.comp
        (initCLM (m + 3)).continuous) continuous_const
  exact Filter.eventuallyEq_of_mem (hopen.mem_nhds hslt) fun w hw => by
    rw [eventMap, cutoff_eq_zero hw.le]
    simp


-- @@ L268-292 verbatim
/-- Flat two-oval incoming presentation. -/
def sourceFLS : FramedLevelSet (m + 2) where
  g := levelMap m (-1 / 2)
  smooth := contDiff_levelMap m (-1 / 2)
  fiber_bounded := by
    have heq : {x : E | levelMap m (-1 / 2) x = 0} =
        {x : E | StandardSaddle.levelMap m (-1 / 2) x = 0} := by
      ext x
      exact levelMap_neg_half_zero_iff m x
    rw [heq]
    exact (StandardSaddle.sourceFLS m).fiber_bounded
  regular := by
    intro x hx
    have hx' : StandardSaddle.levelMap m (-1 / 2) x = 0 :=
      (levelMap_neg_half_zero_iff m x).mp hx
    have hv : StandardSaddle.eventMap m (spaceTime x 0) = 0 := by
      rw [StandardSaddle.eventMap_spaceTime,
        StandardSaddle.height_of_le_quarter (by norm_num)]
      exact hx'
    have hsq : CompactBirth.normSq x < 4 := by
      have hle := standard_event_normSq_le_three m hv
      rw [initCLM_spaceTime] at hle
      linarith
    rw [(levelMap_eventuallyEq_standard m hsq).fderiv_eq]
    exact (StandardSaddle.sourceFLS m).regular x hx'


-- @@ L294-318 verbatim
/-- Flat one-oval outgoing presentation. -/
def targetFLS : FramedLevelSet (m + 2) where
  g := levelMap m (1 / 2)
  smooth := contDiff_levelMap m (1 / 2)
  fiber_bounded := by
    have heq : {x : E | levelMap m (1 / 2) x = 0} =
        {x : E | StandardSaddle.levelMap m (1 / 2) x = 0} := by
      ext x
      exact levelMap_half_zero_iff m x
    rw [heq]
    exact (StandardSaddle.targetFLS m).fiber_bounded
  regular := by
    intro x hx
    have hx' : StandardSaddle.levelMap m (1 / 2) x = 0 :=
      (levelMap_half_zero_iff m x).mp hx
    have hv : StandardSaddle.eventMap m (spaceTime x 1) = 0 := by
      rw [StandardSaddle.eventMap_spaceTime,
        StandardSaddle.height_of_threeQuarter_le (by norm_num)]
      exact hx'
    have hsq : CompactBirth.normSq x < 4 := by
      have hle := standard_event_normSq_le_three m hv
      rw [initCLM_spaceTime] at hle
      linarith
    rw [(levelMap_eventuallyEq_standard m hsq).fderiv_eq]
    exact (StandardSaddle.targetFLS m).regular x hx'


-- @@ L320-323 verbatim
theorem source_fiber_eq_standard :
    (sourceFLS m).fiber = (StandardSaddle.sourceFLS m).fiber := by
  ext x
  exact levelMap_neg_half_zero_iff m x


-- @@ L325-328 verbatim
theorem target_fiber_eq_standard :
    (targetFLS m).fiber = (StandardSaddle.targetFLS m).fiber := by
  ext x
  exact levelMap_half_zero_iff m x


-- @@ L330-348 verbatim
/-- The compact source carries literally the original normal/tangent frame on
its two Cassini ovals. -/
theorem frameAt_source_eq_standard {x : E} (hx : x ∈ (sourceFLS m).fiber) :
    frameAt (sourceFLS m) x = frameAt (StandardSaddle.sourceFLS m) x := by
  have hx' : StandardSaddle.levelMap m (-1 / 2) x = 0 :=
    (levelMap_neg_half_zero_iff m x).mp hx
  have hv : StandardSaddle.eventMap m (spaceTime x 0) = 0 := by
    rw [StandardSaddle.eventMap_spaceTime,
      StandardSaddle.height_of_le_quarter (by norm_num)]
    exact hx'
  have hsq : CompactBirth.normSq x < 4 := by
    have hle := standard_event_normSq_le_three m hv
    rw [initCLM_spaceTime] at hle
    linarith
  have hfd : fderiv ℝ (levelMap m (-1 / 2)) x =
      fderiv ℝ (StandardSaddle.levelMap m (-1 / 2)) x :=
    (levelMap_eventuallyEq_standard m hsq).fderiv_eq
  simp only [frameAt, sourceFLS, StandardSaddle.sourceFLS]
  simp [tauField, kerCross, gradVec, hfd]


-- @@ L350-369 verbatim
/-- The compact target carries literally the original frame on its outgoing
Cassini oval. -/
theorem frameAt_target_eq_standard {x : E} (hx : x ∈ (targetFLS m).fiber) :
    frameAt (targetFLS m) x = frameAt (StandardSaddle.targetFLS m) x := by
  have hx' : StandardSaddle.levelMap m (1 / 2) x = 0 :=
    (levelMap_half_zero_iff m x).mp hx
  have hv : StandardSaddle.eventMap m (spaceTime x 1) = 0 := by
    rw [StandardSaddle.eventMap_spaceTime,
      StandardSaddle.height_of_threeQuarter_le (by norm_num)]
    exact hx'
  have hsq : CompactBirth.normSq x < 4 := by
    have hle := standard_event_normSq_le_three m hv
    rw [initCLM_spaceTime] at hle
    linarith
  have hfd : fderiv ℝ (levelMap m (1 / 2)) x =
      fderiv ℝ (StandardSaddle.levelMap m (1 / 2)) x :=
    (levelMap_eventuallyEq_standard m hsq).fderiv_eq
  simp only [div_eq_mul_inv, one_mul] at hfd
  simp only [frameAt, targetFLS, StandardSaddle.targetFLS]
  simp [tauField, kerCross, gradVec, hfd]


-- @@ L371-392 verbatim
/-- The compactified Cassini merge cobordism. -/
def cobordism : FramedLevelCobordism (m + 2) where
  X₀ := sourceFLS m
  X₁ := targetFLS m
  G := eventMap m
  smooth := contDiff_eventMap m
  spatial_bounded := by
    obtain ⟨R, hR⟩ := StandardSaddle.eventMap_spatial_bounded m
    exact ⟨R, fun v hv => hR v ((eventMap_zero_iff m v).mp hv)⟩
  regular := by
    intro v hv
    have hv' := (eventMap_zero_iff m v).mp hv
    rw [(eventMap_eventuallyEq_standard m hv').fderiv_eq]
    exact StandardSaddle.eventMap_regular m v hv'
  collar_zero := by
    intro x t ht
    rw [eventMap_spaceTime, StandardSaddle.height_of_le_quarter ht]
    rfl
  collar_one := by
    intro x t ht
    rw [eventMap_spaceTime, StandardSaddle.height_of_threeQuarter_le ht]
    rfl


-- @@ L394-404 verbatim
/-- Uniform spatial flatness, with radius three. -/
theorem cobordism_spatialFlatOutside :
    (cobordism m).SpatialFlatOutside (background m) 0 3 := by
  intro v hv
  have hn : 3 ≤ ‖initCLM (m + 3) v‖ := by
    simpa [dist_zero_right] using hv
  have hs : 9 ≤ CompactBirth.normSq (initCLM (m + 3) v) := by
    rw [CompactBirth.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (initCLM (m + 3) v)]
  have hc := cutoff_eq_one hs
  simp [cobordism, eventMap, hc]


-- @@ L406-409 verbatim
def sourceSign : FiberSign (sourceFLS m) where
  toFun := fun _ => 1
  continuous := continuous_const
  nonzero := by simp


-- @@ L411-414 verbatim
def targetSign : FiberSign (targetFLS m) where
  toFun := fun _ => 1
  continuous := continuous_const
  nonzero := by simp


-- @@ L416-426 verbatim
/-- Spatially flat, constant-positive head merge. -/
def signedCobordism :
    SignedFramedLevelCobordism (sourceSign m) (targetSign m) where
  cobordism := cobordism m
  source_eq := rfl
  target_eq := rfl
  toFun := fun _ => 1
  continuous := continuous_const
  nonzero := by simp
  collar_zero := by simp [sourceSign]
  collar_one := by simp [targetSign]


-- @@ L428-430 verbatim
def signedSplitCobordism :
    SignedFramedLevelCobordism (targetSign m) (sourceSign m) :=
  (signedCobordism m).reverse


-- @@ L432-435 verbatim
def sourceNegativeSign : FiberSign (sourceFLS m) where
  toFun := fun _ => -1
  continuous := continuous_const
  nonzero := by norm_num


-- @@ L437-440 verbatim
def targetNegativeSign : FiberSign (targetFLS m) where
  toFun := fun _ => -1
  continuous := continuous_const
  nonzero := by norm_num


-- @@ L442-452 verbatim
/-- The same merge with both local components labelled negative. -/
def signedNegativeCobordism :
    SignedFramedLevelCobordism (sourceNegativeSign m) (targetNegativeSign m) where
  cobordism := cobordism m
  source_eq := rfl
  target_eq := rfl
  toFun := fun _ => -1
  continuous := continuous_const
  nonzero := by norm_num
  collar_zero := by simp [sourceNegativeSign]
  collar_one := by simp [targetNegativeSign]


-- @@ L454-456 verbatim
theorem signedCobordism_spatialFlatOutside :
    (signedCobordism m).SpatialFlatOutside (background m) 0 3 :=
  cobordism_spatialFlatOutside m


-- @@ L458-463 verbatim
theorem signedSplitCobordism_spatialFlatOutside :
    (signedSplitCobordism m).SpatialFlatOutside (background m) 0 3 := by
  intro v hv
  change eventMap m (reparamMap (m + 2) (-1) 1 v) = background m
  apply cobordism_spatialFlatOutside m
  simpa [reparamMap, initCLM_spaceTime] using hv


-- @@ L465-467 verbatim
theorem signedNegativeCobordism_spatialFlatOutside :
    (signedNegativeCobordism m).SpatialFlatOutside (background m) 0 3 :=
  cobordism_spatialFlatOutside m


-- @@ L469-484 verbatim
/-- Concrete head merge with an arbitrary unchanged separated flat tail. -/
theorem nonempty_merge_juxtapose_tail
    {X : FramedLevelSet (m + 2)} (S : FiberSign X)
    {p : EuclideanSpace ℝ (Fin (m + 3))} {R : ℝ}
    (hX : X.FlatOutside (background m) p R)
    (hsep : 3 + R < dist (0 : EuclideanSpace ℝ (Fin (m + 3))) p) :
    Nonempty (SignedFramedLevelCobordism
      ((sourceSign m).juxtapose S (background_ne_zero m)
        (signedCobordism_spatialFlatOutside m).flatOutside_source hX hsep)
      ((targetSign m).juxtapose S (background_ne_zero m)
        (signedCobordism_spatialFlatOutside m).flatOutside_target hX hsep)) := by
  exact SignedFramedLevelCobordism.nonempty_juxtapose_tail
    (signedCobordism m) (background_ne_zero m)
    (signedCobordism_spatialFlatOutside m) S hX hsep
    (signedCobordism_spatialFlatOutside m).flatOutside_source
    (signedCobordism_spatialFlatOutside m).flatOutside_target


-- @@ L486-501 verbatim
/-- Negative head merge with an arbitrary unchanged separated flat tail. -/
theorem nonempty_negativeMerge_juxtapose_tail
    {X : FramedLevelSet (m + 2)} (S : FiberSign X)
    {p : EuclideanSpace ℝ (Fin (m + 3))} {R : ℝ}
    (hX : X.FlatOutside (background m) p R)
    (hsep : 3 + R < dist (0 : EuclideanSpace ℝ (Fin (m + 3))) p) :
    Nonempty (SignedFramedLevelCobordism
      ((sourceNegativeSign m).juxtapose S (background_ne_zero m)
        (signedNegativeCobordism_spatialFlatOutside m).flatOutside_source hX hsep)
      ((targetNegativeSign m).juxtapose S (background_ne_zero m)
        (signedNegativeCobordism_spatialFlatOutside m).flatOutside_target hX hsep)) := by
  exact SignedFramedLevelCobordism.nonempty_juxtapose_tail
    (signedNegativeCobordism m) (background_ne_zero m)
    (signedNegativeCobordism_spatialFlatOutside m) S hX hsep
    (signedNegativeCobordism_spatialFlatOutside m).flatOutside_source
    (signedNegativeCobordism_spatialFlatOutside m).flatOutside_target


-- @@ L503-509 verbatim
/-! ## Transport of the endpoint frame invariant

The following homotopy changes only the defining equations.  Its zero set is
fixed and the map is literally the standard Cassini map on a neighborhood of
that set.  Consequently every time slice is regular; the regular-slab theorem
then transports `positiveDelta` from the already computed polynomial model.
-/


-- @@ L511-514 verbatim
/-- Linear activation of the spatial compactification. -/
def interpolation (a s : ℝ) (x : E) : F :=
  (1 - s * cutoff x) • StandardSaddle.levelMap m a x +
    (s * cutoff x) • background m


-- @@ L516-525 verbatim
lemma contDiff_interpolation (a : ℝ) : ContDiff ℝ ∞
    (fun p : ℝ × E => interpolation m a p.1 p.2) := by
  have ha : ContDiff ℝ ∞
      (fun p : ℝ × E => StandardSaddle.levelMap m a p.2) :=
    (StandardSaddle.contDiff_levelMap m a).comp contDiff_snd
  have hc : ContDiff ℝ ∞ (fun p : ℝ × E => cutoff p.2) :=
    contDiff_cutoff.comp contDiff_snd
  have hs : ContDiff ℝ ∞ (fun p : ℝ × E => p.1 * cutoff p.2) :=
    contDiff_fst.mul hc
  exact ((contDiff_const.sub hs).smul ha).add (hs.smul contDiff_const)


-- @@ L527-531 verbatim
@[simp] lemma interpolation_apply_castSucc (a s : ℝ) (x : E)
    (j : Fin (m + 1)) :
    interpolation m a s x j.castSucc =
      (1 - s * cutoff x) * x j.castSucc.castSucc := by
  simp [interpolation, StandardSaddle.levelMap_apply_castSucc]


-- @@ L533-537 verbatim
@[simp] lemma interpolation_apply_last (a s : ℝ) (x : E) :
    interpolation m a s x (Fin.last (m + 1)) =
      (1 - s * cutoff x) * (StandardSaddle.cassiniQ m x - a) +
        s * cutoff x := by
  simp [interpolation, StandardSaddle.levelMap_apply_last]


-- @@ L539-542 verbatim
lemma interpolation_zero (a : ℝ) :
    interpolation m a 0 = StandardSaddle.levelMap m a := by
  funext x
  simp [interpolation]


-- @@ L544-546 verbatim
lemma interpolation_one (a : ℝ) : interpolation m a 1 = levelMap m a := by
  funext x
  simp [interpolation, levelMap]


-- @@ L548-553 verbatim
lemma interpolation_coeff_ne_one {a s : ℝ} {x : E}
    (hx : interpolation m a s x = 0) : s * cutoff x ≠ 1 := by
  intro hc
  have hlast := congrArg (fun q : F => q (Fin.last (m + 1))) hx
  rw [interpolation_apply_last, hc] at hlast
  norm_num at hlast


-- @@ L555-566 verbatim
lemma interpolation_transverse_eq_zero {a s : ℝ} {x : E}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hx : interpolation m a s x = 0)
    (j : Fin (m + 1)) : x j.castSucc.castSucc = 0 := by
  have hcoord := congrArg (fun q : F => q j.castSucc) hx
  rw [interpolation_apply_castSucc] at hcoord
  simp only [PiLp.zero_apply] at hcoord
  have hcoeff0 : 0 ≤ s * cutoff x := mul_nonneg hs0 (cutoff_nonneg x)
  have hcoeff1 : s * cutoff x ≤ 1 := by
    nlinarith [cutoff_nonneg x, cutoff_le_one x]
  have hcoefflt : s * cutoff x < 1 :=
    lt_of_le_of_ne hcoeff1 (interpolation_coeff_ne_one m hx)
  exact (mul_eq_zero.mp hcoord).resolve_left (sub_ne_zero.mpr hcoefflt.ne')


-- @@ L568-578 verbatim
lemma interpolation_normSq_eq_radiusSq {a s : ℝ} {x : E}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hx : interpolation m a s x = 0) :
    CompactBirth.normSq x = StandardSaddle.radiusSq m x := by
  unfold CompactBirth.normSq StandardSaddle.radiusSq
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have hz : ∀ j : Fin (m + 1), x j.castSucc.castSucc ^ 2 = 0 :=
    fun j => by
      rw [interpolation_transverse_eq_zero m hs0 hs1 hx j,
        zero_pow (by norm_num)]
  simp only [hz, Finset.sum_const_zero, zero_add]
  rfl


-- @@ L580-587 verbatim
lemma standard_source_normSq_le_three {x : E}
    (hx : StandardSaddle.levelMap m (-1 / 2) x = 0) :
    CompactBirth.normSq x ≤ 3 := by
  have hv : StandardSaddle.eventMap m (spaceTime x 0) = 0 := by
    rw [StandardSaddle.eventMap_spaceTime,
      StandardSaddle.height_of_le_quarter (by norm_num)]
    exact hx
  simpa only [initCLM_spaceTime] using standard_event_normSq_le_three m hv


-- @@ L589-596 verbatim
lemma standard_target_normSq_le_three {x : E}
    (hx : StandardSaddle.levelMap m (1 / 2) x = 0) :
    CompactBirth.normSq x ≤ 3 := by
  have hv : StandardSaddle.eventMap m (spaceTime x 1) = 0 := by
    rw [StandardSaddle.eventMap_spaceTime,
      StandardSaddle.height_of_threeQuarter_le (by norm_num)]
    exact hx
  simpa only [initCLM_spaceTime] using standard_event_normSq_le_three m hv


-- @@ L598-632 verbatim
lemma interpolation_zero_iff {a s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ha : a ≤ 1 / 2)
    (hbound : ∀ x : E, StandardSaddle.levelMap m a x = 0 →
      CompactBirth.normSq x ≤ 3) (x : E) :
    interpolation m a s x = 0 ↔ StandardSaddle.levelMap m a x = 0 := by
  constructor
  · intro hx
    have hcoeff0 : 0 ≤ s * cutoff x := mul_nonneg hs0 (cutoff_nonneg x)
    have hcoeff1 : s * cutoff x ≤ 1 := by
      nlinarith [cutoff_nonneg x, cutoff_le_one x]
    have hcoefflt : s * cutoff x < 1 :=
      lt_of_le_of_ne hcoeff1 (interpolation_coeff_ne_one m hx)
    have hr := interpolation_normSq_eq_radiusSq m hs0 hs1 hx
    have hlast := congrArg (fun q : F => q (Fin.last (m + 1))) hx
    rw [interpolation_apply_last] at hlast
    simp only [PiLp.zero_apply] at hlast
    have hslt : CompactBirth.normSq x < 4 := by
      by_contra hnot
      have hsge : 4 ≤ CompactBirth.normSq x := not_lt.mp hnot
      have hqform := StandardSaddle.cassiniQ_eq m x
      rw [hr] at hsge
      have hqpos : 0 < StandardSaddle.cassiniQ m x - a := by
        rw [hqform]
        unfold StandardSaddle.radiusSq at hsge ⊢
        nlinarith [sq_nonneg (x (StandardSaddle.planeFirst m)),
          sq_nonneg (x (StandardSaddle.planeSecond m))]
      have hprod : 0 < (1 - s * cutoff x) *
          (StandardSaddle.cassiniQ m x - a) :=
        mul_pos (sub_pos.mpr hcoefflt) hqpos
      nlinarith
    have hc0 : cutoff x = 0 := cutoff_eq_zero hslt.le
    simpa [interpolation, hc0] using hx
  · intro hx
    have hc0 : cutoff x = 0 := cutoff_eq_zero ((hbound x hx).trans (by norm_num))
    simp [interpolation, hc0, hx]


-- @@ L634-642 verbatim
lemma interpolation_eventuallyEq_standard {a s : ℝ} {x : E}
    (hx : CompactBirth.normSq x < 4) :
    Filter.EventuallyEq (nhds x) (interpolation m a s)
      (StandardSaddle.levelMap m a) := by
  have hopen : IsOpen {y : E | CompactBirth.normSq y < 4} :=
    isOpen_lt CompactBirth.contDiff_normSq.continuous continuous_const
  exact Filter.eventuallyEq_of_mem (hopen.mem_nhds hx) fun y hy => by
    rw [interpolation, cutoff_eq_zero hy.le]
    simp


-- @@ L644-663 verbatim
/-- Fixed-fiber defining-map homotopy for the incoming two-oval slice. -/
def sourceHomotopy :
    DefiningMapHomotopy (StandardSaddle.sourceFLS m) (sourceFLS m) where
  H := interpolation m (-1 / 2)
  smooth := by
    simpa only using contDiff_interpolation m (-1 / 2)
  H_zero := interpolation_zero m (-1 / 2)
  H_one := interpolation_one m (-1 / 2)
  fiber_eq := by
    intro s hs0 hs1
    ext x
    exact interpolation_zero_iff m hs0 hs1 (by norm_num)
      (fun y hy => standard_source_normSq_le_three m hy) x
  regular := by
    intro s hs0 hs1 x hx
    have hx0 : StandardSaddle.levelMap m (-1 / 2) x = 0 := hx
    have hsq : CompactBirth.normSq x < 4 :=
      lt_of_le_of_lt (standard_source_normSq_le_three m hx0) (by norm_num)
    rw [(interpolation_eventuallyEq_standard m hsq).fderiv_eq]
    exact (StandardSaddle.sourceFLS m).regular x hx0


-- @@ L665-684 verbatim
/-- Fixed-fiber defining-map homotopy for the outgoing oval. -/
def targetHomotopy :
    DefiningMapHomotopy (StandardSaddle.targetFLS m) (targetFLS m) where
  H := interpolation m (1 / 2)
  smooth := by
    simpa only using contDiff_interpolation m (1 / 2)
  H_zero := interpolation_zero m (1 / 2)
  H_one := interpolation_one m (1 / 2)
  fiber_eq := by
    intro s hs0 hs1
    ext x
    exact interpolation_zero_iff m hs0 hs1 (by norm_num)
      (fun y hy => standard_target_normSq_le_three m hy) x
  regular := by
    intro s hs0 hs1 x hx
    have hx0 : StandardSaddle.levelMap m (1 / 2) x = 0 := hx
    have hsq : CompactBirth.normSq x < 4 :=
      lt_of_le_of_lt (standard_target_normSq_le_three m hx0) (by norm_num)
    rw [(interpolation_eventuallyEq_standard m hsq).fderiv_eq]
    exact (StandardSaddle.targetFLS m).regular x hx0


-- @@ L686-720 verbatim
/-- Every defining-map homotopy is a regular slab: by contract, each spatial
member of the family is already a submersion on the common zero fiber. -/
theorem homotopy_regularSlab
    {n : ℕ} {X₀ X₁ : FramedLevelSet n} (D : DefiningMapHomotopy X₀ X₁) :
    regularSlab D.toCobordism.G 0 1 := by
  rw [regularSlab]
  intro t ht hcritical
  obtain ⟨v, hvcrit, hvt⟩ := hcritical
  apply hvcrit.2
  let x : EuclideanSpace ℝ (Fin (n + 1)) := spacePart v
  have hvrepr : cobSpaceTime x t = v := by
    rw [← hvt]
    exact spaceTime_spacePart v
  have hvzero : D.H (normRamp t) x = 0 := by
    have h := hvcrit.1
    rw [← hvrepr] at h
    have hspace : cobSpaceTime x t = spaceTime x t := rfl
    rw [hspace] at h
    change D.cobMap (spaceTime x t) = 0 at h
    rwa [D.cobMap_spaceTime] at h
  have hxfib : x ∈ X₀.fiber := by
    have hmem : x ∈ {y | D.H (normRamp t) y = 0} := hvzero
    rwa [D.fiber_eq _ (normRamp_nonneg _) (normRamp_le_one _)] at hmem
  have hsurj : Function.Surjective
      (fderiv ℝ (D.H (normRamp t)) x) :=
    D.regular _ (normRamp_nonneg _) (normRamp_le_one _) x hxfib
  rw [← hvrepr]
  change Function.Surjective (spatialDeriv D.cobMap (cobSpaceTime x t))
  rw [← fderiv_sliceMap D.contDiff_cobMap t x]
  have hslice : sliceMap D.cobMap t = D.H (normRamp t) := by
    funext y
    change D.cobMap (cobSpaceTime y t) = D.H (normRamp t) y
    have hspace : cobSpaceTime y t = spaceTime y t := rfl
    rw [hspace, D.cobMap_spaceTime]
  rwa [hslice]


-- @@ L722-723 verbatim
def sourceTransportCobordism :=
  (sourceHomotopy m).signedCobordism (StandardSaddle.sourceSign m)


-- @@ L725-726 verbatim
def targetTransportCobordism :=
  (targetHomotopy m).signedCobordism (StandardSaddle.targetSign m)


-- @@ L728-732 verbatim
theorem sourceTransport_targetSign_eq :
    (StandardSaddle.sourceSign m).restrict (sourceHomotopy m).fiber_subset =
      sourceSign m := by
  apply FiberSign.eq_of_toFun_eq
  rfl


-- @@ L734-738 verbatim
theorem targetTransport_targetSign_eq :
    (StandardSaddle.targetSign m).restrict (targetHomotopy m).fiber_subset =
      targetSign m := by
  apply FiberSign.eq_of_toFun_eq
  rfl


-- @@ L740-750 verbatim
/-- The compact incoming two-oval state has the same (zero) positive framed
delta as the polynomial Cassini state. -/
theorem sourceSign_positiveDelta_eq_zero :
    (sourceSign m).positiveDelta = 0 := by
  have htransport :=
    (sourceTransportCobordism m).positiveDelta_eq_of_regularSlab
      (homotopy_regularSlab (sourceHomotopy m))
  rw [sourceTransport_targetSign_eq m] at htransport
  rw [← htransport]
  exact StandardSaddle.sourceSign_positiveDelta_eq_zero m
    (StandardSaddle.sourceFLS m).exists_tamedField.some


-- @@ L752-761 verbatim
/-- The compact outgoing oval also has zero positive framed delta. -/
theorem targetSign_positiveDelta_eq_zero :
    (targetSign m).positiveDelta = 0 := by
  have htransport :=
    (targetTransportCobordism m).positiveDelta_eq_of_regularSlab
      (homotopy_regularSlab (targetHomotopy m))
  rw [targetTransport_targetSign_eq m] at htransport
  rw [← htransport]
  exact StandardSaddle.targetSign_positiveDelta_eq_zero m
    (StandardSaddle.targetFLS m).exists_tamedField.some


-- @@ L763-765 verbatim
theorem compactSaddle_positiveDelta_eq :
    (sourceSign m).positiveDelta = (targetSign m).positiveDelta := by
  rw [sourceSign_positiveDelta_eq_zero m, targetSign_positiveDelta_eq_zero m]


-- @@ L767-771 verbatim
theorem sourceNegativeSign_neg_eq :
    (sourceNegativeSign m).neg = sourceSign m := by
  apply FiberSign.eq_of_toFun_eq
  funext x
  simp [sourceNegativeSign, sourceSign]


-- @@ L773-777 verbatim
theorem targetNegativeSign_neg_eq :
    (targetNegativeSign m).neg = targetSign m := by
  apply FiberSign.eq_of_toFun_eq
  funext x
  simp [targetNegativeSign, targetSign]


-- @@ L779-782 verbatim
theorem sourceNegativeSign_negativeDelta_eq_zero :
    (sourceNegativeSign m).negativeDelta = 0 := by
  rw [FiberSign.negativeDelta, sourceNegativeSign_neg_eq,
    sourceSign_positiveDelta_eq_zero]


-- @@ L784-787 verbatim
theorem targetNegativeSign_negativeDelta_eq_zero :
    (targetNegativeSign m).negativeDelta = 0 := by
  rw [FiberSign.negativeDelta, targetNegativeSign_neg_eq,
    targetSign_positiveDelta_eq_zero]


-- @@ L789-793 verbatim
theorem compactNegativeSaddle_negativeDelta_eq :
    (sourceNegativeSign m).negativeDelta =
      (targetNegativeSign m).negativeDelta := by
  rw [sourceNegativeSign_negativeDelta_eq_zero m,
    targetNegativeSign_negativeDelta_eq_zero m]


-- @@ L795-795 verbatim
end CompactSaddle

-- @@ L796-796 verbatim
end Submission
