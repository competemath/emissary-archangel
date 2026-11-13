import Mathlib
import Submission.MorseLedgerCobordism


-- @@ L4-18 verbatim
/-!
# A spatially flat representative of the standard birth

The juxtaposition API in `MorseLedgerCobordism` requires every local move to be
literally equal to one common nonzero vector outside a spatial ball.  The
polynomial standard-birth map is not flat at infinity.  This file performs a
radial, smooth compactification of that map.  The interpolation cannot create a
new zero: in the transition annulus either a transverse coordinate survives, or
the radial equation is strictly positive.  Consequently the compactified map
has exactly the old zero set and exactly the old differential along it.

This supplies the first concrete flat local move needed by
`ConfigurationReductionKit.deathPos`; no quotient, choice, or placeholder is
used.
-/


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
open Set Function Metric

-- @@ L23-23 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L25-25 verbatim
namespace Submission

-- @@ L26-26 verbatim
namespace CompactBirth


-- @@ L28-28 verbatim
variable (m : ℕ)


-- @@ L30-30 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 2))

-- @@ L31-31 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (m + 3))

-- @@ L32-32 verbatim
local notation "F" => EuclideanSpace ℝ (Fin (m + 1))


-- @@ L34-37 verbatim
/-- Squared Euclidean norm, written polynomially so smoothness at the origin is
immediate. -/
def normSq {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) : ℝ :=
  ∑ i, x i ^ 2


-- @@ L39-42 verbatim
lemma normSq_eq_norm_sq {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) :
    normSq x = ‖x‖ ^ 2 := by
  rw [norm_sq_eq_sum]
  rfl


-- @@ L44-47 verbatim
lemma contDiff_normSq {k : ℕ} :
    ContDiff ℝ ∞ (normSq : EuclideanSpace ℝ (Fin k) → ℝ) := by
  unfold normSq
  fun_prop


-- @@ L49-52 verbatim
/-- The cutoff is zero on the squared ball of radius `sqrt 2`, and one outside
the ball of radius `2`. -/
def cutoff {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) : ℝ :=
  Real.smoothTransition ((normSq x - 2) / 2)


-- @@ L54-57 verbatim
lemma contDiff_cutoff {k : ℕ} :
    ContDiff ℝ ∞ (cutoff : EuclideanSpace ℝ (Fin k) → ℝ) := by
  exact Real.smoothTransition.contDiff.comp
    (((contDiff_normSq).sub contDiff_const).div_const 2)


-- @@ L59-61 verbatim
lemma cutoff_nonneg {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) :
    0 ≤ cutoff x :=
  Real.smoothTransition.nonneg _


-- @@ L63-65 verbatim
lemma cutoff_le_one {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) :
    cutoff x ≤ 1 :=
  Real.smoothTransition.le_one _


-- @@ L67-70 verbatim
lemma cutoff_eq_zero {k : ℕ} {x : EuclideanSpace ℝ (Fin k)}
    (hx : normSq x ≤ 2) : cutoff x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  linarith


-- @@ L72-75 verbatim
lemma cutoff_eq_one {k : ℕ} {x : EuclideanSpace ℝ (Fin k)}
    (hx : 4 ≤ normSq x) : cutoff x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  linarith


-- @@ L77-79 verbatim
/-- Common nonzero background vector for all compactified birth pieces. -/
def background : F :=
  WithLp.toLp 2 (Fin.lastCases 1 (fun _ : Fin m => 0))


-- @@ L81-82 verbatim
@[simp] lemma background_apply_last : background m (Fin.last m) = 1 := by
  simp [background]


-- @@ L84-86 verbatim
@[simp] lemma background_apply_castSucc (j : Fin m) :
    background m j.castSucc = 0 := by
  simp [background]


-- @@ L88-91 verbatim
lemma background_ne_zero : background m ≠ 0 := by
  intro h
  have := congrArg (fun q : F => q (Fin.last m)) h
  simp at this


-- @@ L93-95 verbatim
/-- Compactification of a standard-birth level map. -/
def levelMap (a : ℝ) (x : E) : F :=
  (1 - cutoff x) • StandardBirth.circleMap m a x + cutoff x • background m


-- @@ L97-100 verbatim
lemma contDiff_levelMap (a : ℝ) : ContDiff ℝ ∞ (levelMap m a) := by
  exact ((contDiff_const.sub contDiff_cutoff).smul
    (StandardBirth.contDiff_circleMap m a)).add
    (contDiff_cutoff.smul contDiff_const)


-- @@ L102-104 verbatim
@[simp] lemma levelMap_apply_castSucc (a : ℝ) (x : E) (j : Fin m) :
    levelMap m a x j.castSucc = (1 - cutoff x) * x j.castSucc.castSucc := by
  simp [levelMap, StandardBirth.circleMap_apply_castSucc]


-- @@ L106-109 verbatim
@[simp] lemma levelMap_apply_last (a : ℝ) (x : E) :
    levelMap m a x (Fin.last m) =
      (1 - cutoff x) * (StandardBirth.radialSq m x - a) + cutoff x := by
  simp [levelMap, StandardBirth.circleMap_apply_last]


-- @@ L111-114 verbatim
/-- Compactification of the whole birth event. -/
def eventMap (v : E') : F :=
  (1 - cutoff (initCLM (m + 2) v)) • StandardBirth.eventMap m v +
    cutoff (initCLM (m + 2) v) • background m


-- @@ L116-121 verbatim
lemma contDiff_eventMap : ContDiff ℝ ∞ (eventMap m) := by
  have hcut : ContDiff ℝ ∞
      (fun v : E' => cutoff (initCLM (m + 2) v)) :=
    contDiff_cutoff.comp (initCLM (m + 2)).contDiff
  exact ((contDiff_const.sub hcut).smul
    (StandardBirth.contDiff_eventMap m)).add (hcut.smul contDiff_const)


-- @@ L123-127 verbatim
@[simp] lemma eventMap_apply_castSucc (v : E') (j : Fin m) :
    eventMap m v j.castSucc =
      (1 - cutoff (initCLM (m + 2) v)) * v j.castSucc.castSucc.castSucc := by
  simp [eventMap, StandardBirth.eventMap,
    StandardBirth.circleMap_apply_castSucc]


-- @@ L129-135 verbatim
@[simp] lemma eventMap_apply_last (v : E') :
    eventMap m v (Fin.last m) =
      (1 - cutoff (initCLM (m + 2) v)) *
          (StandardBirth.radialSq m (initCLM (m + 2) v) - birthHeight (vertC v)) +
        cutoff (initCLM (m + 2) v) := by
  simp [eventMap, StandardBirth.eventMap,
    StandardBirth.circleMap_apply_last]


-- @@ L137-139 verbatim
lemma eventMap_spaceTime (x : E) (t : ℝ) :
    eventMap m (spaceTime x t) = levelMap m (birthHeight t) x := by
  rw [eventMap, levelMap, initCLM_spaceTime, StandardBirth.eventMap_spaceTime]


-- @@ L141-155 verbatim
lemma birthHeight_le_one (t : ℝ) : birthHeight t ≤ 1 := by
  by_cases ht : t < 1 / 2
  · exact (birthHeight_neg_of_lt_half ht).le.trans (by norm_num)
  · by_cases hthree : 3 / 4 ≤ t
    · rw [birthHeight_of_threeQuarter_le hthree]
    · rw [birthHeight, if_neg ht, birthHeightRight]
      have hc0 := Real.smoothTransition.nonneg (8 * (t - 5 / 8))
      have hc1 := Real.smoothTransition.le_one (8 * (t - 5 / 8))
      change (1 - birthRightCutoff t) * (t - 1 / 2) +
        birthRightCutoff t ≤ 1
      change 0 ≤ birthRightCutoff t at hc0
      change birthRightCutoff t ≤ 1 at hc1
      have ht0 : 0 ≤ t - 1 / 2 := by linarith
      have ht1 : t - 1 / 2 ≤ 1 := by linarith
      nlinarith


-- @@ L157-162 verbatim
lemma eventMap_cutoff_ne_one {v : E'} (hv : eventMap m v = 0) :
    cutoff (initCLM (m + 2) v) ≠ 1 := by
  intro hc
  have hlast := congrArg (fun q : F => q (Fin.last m)) hv
  rw [eventMap_apply_last, hc] at hlast
  norm_num at hlast


-- @@ L164-172 verbatim
lemma transverse_eq_zero_of_eventMap_eq_zero {v : E'}
    (hv : eventMap m v = 0) (j : Fin m) :
    v j.castSucc.castSucc.castSucc = 0 := by
  have hcoord := congrArg (fun q : F => q j.castSucc) hv
  rw [eventMap_apply_castSucc] at hcoord
  simp only [PiLp.zero_apply] at hcoord
  have hc : cutoff (initCLM (m + 2) v) < 1 :=
    lt_of_le_of_ne (cutoff_le_one _) (eventMap_cutoff_ne_one m hv)
  exact (mul_eq_zero.mp hcoord).resolve_left (sub_ne_zero.mpr hc.ne')


-- @@ L174-184 verbatim
lemma normSq_init_eq_radialSq_of_eventMap_eq_zero {v : E'}
    (hv : eventMap m v = 0) :
    normSq (initCLM (m + 2) v) =
      StandardBirth.radialSq m (initCLM (m + 2) v) := by
  unfold normSq StandardBirth.radialSq
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [initCLM_apply]
  have hz : ∀ j : Fin m, v j.castSucc.castSucc.castSucc ^ 2 = 0 :=
    fun j => by rw [transverse_eq_zero_of_eventMap_eq_zero m hv j, zero_pow (by norm_num)]
  simp only [hz, Finset.sum_const_zero, zero_add]
  rfl


-- @@ L186-213 verbatim
/-- The compactification introduces no event-surface points. -/
theorem eventMap_zero_iff (v : E') :
    eventMap m v = 0 ↔ StandardBirth.eventMap m v = 0 := by
  constructor
  · intro hv
    have hc_lt : cutoff (initCLM (m + 2) v) < 1 :=
      lt_of_le_of_ne (cutoff_le_one _) (eventMap_cutoff_ne_one m hv)
    have hr := normSq_init_eq_radialSq_of_eventMap_eq_zero m hv
    have hlast := congrArg (fun q : F => q (Fin.last m)) hv
    rw [eventMap_apply_last] at hlast
    simp only [PiLp.zero_apply] at hlast
    have hslt : normSq (initCLM (m + 2) v) < 2 := by
      by_contra hnot
      have hsge : 2 ≤ normSq (initCLM (m + 2) v) := not_lt.mp hnot
      have hheight := birthHeight_le_one (vertC v)
      have hc0 := cutoff_nonneg (initCLM (m + 2) v)
      rw [hr] at hsge
      nlinarith
    have hc0 : cutoff (initCLM (m + 2) v) = 0 :=
      cutoff_eq_zero hslt.le
    simpa [eventMap, hc0] using hv
  · intro hv
    have hbound := StandardBirth.eventMap_spatial_bound_one m v hv
    have hs : normSq (initCLM (m + 2) v) ≤ 2 := by
      rw [normSq_eq_norm_sq]
      nlinarith [norm_nonneg (initCLM (m + 2) v)]
    have hc0 : cutoff (initCLM (m + 2) v) = 0 := cutoff_eq_zero hs
    simp [eventMap, hc0, hv]


-- @@ L215-221 verbatim
theorem levelMap_neg_one_zero_iff (x : E) :
    levelMap m (-1) x = 0 ↔ StandardBirth.circleMap m (-1) x = 0 := by
  have hheight : birthHeight 0 = -1 := birthHeight_of_le_quarter (by norm_num)
  rw [← hheight]
  rw [← eventMap_spaceTime m x 0]
  rw [eventMap_zero_iff]
  rw [StandardBirth.eventMap_spaceTime]


-- @@ L223-229 verbatim
theorem levelMap_one_zero_iff (x : E) :
    levelMap m 1 x = 0 ↔ StandardBirth.circleMap m 1 x = 0 := by
  have hheight : birthHeight 1 = 1 := birthHeight_of_threeQuarter_le (by norm_num)
  rw [← hheight]
  rw [← eventMap_spaceTime m x 1]
  rw [eventMap_zero_iff]
  rw [StandardBirth.eventMap_spaceTime]


-- @@ L231-238 verbatim
lemma levelMap_eventuallyEq_circleMap {a : ℝ} {x : E}
    (hx : normSq x < 2) :
    Filter.EventuallyEq (nhds x) (levelMap m a) (StandardBirth.circleMap m a) := by
  have hopen : IsOpen {y : E | normSq y < 2} :=
    isOpen_lt contDiff_normSq.continuous continuous_const
  exact Filter.eventuallyEq_of_mem (hopen.mem_nhds hx) fun y hy => by
    rw [levelMap, cutoff_eq_zero hy.le]
    simp


-- @@ L240-252 verbatim
lemma eventMap_eventuallyEq_standard {v : E'}
    (hv : StandardBirth.eventMap m v = 0) :
    Filter.EventuallyEq (nhds v) (eventMap m) (StandardBirth.eventMap m) := by
  have hbound := StandardBirth.eventMap_spatial_bound_one m v hv
  have hslt : normSq (initCLM (m + 2) v) < 2 := by
    rw [normSq_eq_norm_sq]
    nlinarith [norm_nonneg (initCLM (m + 2) v)]
  have hopen : IsOpen {w : E' | normSq (initCLM (m + 2) w) < 2} :=
    isOpen_lt (contDiff_normSq.continuous.comp (initCLM (m + 2)).continuous)
      continuous_const
  exact Filter.eventuallyEq_of_mem (hopen.mem_nhds hslt) fun w hw => by
    rw [eventMap, cutoff_eq_zero hw.le]
    simp


-- @@ L254-278 verbatim
/-- Flat incoming presentation.  Its fiber is still empty. -/
def sourceFLS : FramedLevelSet (m + 1) where
  g := levelMap m (-1)
  smooth := contDiff_levelMap m (-1)
  fiber_bounded := by
    have heq : {x : E | levelMap m (-1) x = 0} =
        {x : E | StandardBirth.circleMap m (-1) x = 0} := by
      ext x
      exact levelMap_neg_one_zero_iff m x
    rw [heq]
    exact (StandardBirth.sourceFLS m).fiber_bounded
  regular := by
    intro x hx
    have hx' : StandardBirth.circleMap m (-1) x = 0 :=
      (levelMap_neg_one_zero_iff m x).mp hx
    have hsq : normSq x < 2 := by
      have hfalse := (StandardBirth.sourceFLS m).regular x hx'
      exact False.elim (by
        have h := congrArg (fun q : F => q (Fin.last m)) hx'
        simp only [StandardBirth.circleMap_apply_last, PiLp.zero_apply,
          StandardBirth.radialSq] at h
        nlinarith [sq_nonneg (x (StandardBirth.radialFirst m)),
          sq_nonneg (x (StandardBirth.radialSecond m))])
    rw [(levelMap_eventuallyEq_circleMap m hsq).fderiv_eq]
    exact (StandardBirth.sourceFLS m).regular x hx'


-- @@ L280-305 verbatim
/-- Flat outgoing presentation of the born circle. -/
def targetFLS : FramedLevelSet (m + 1) where
  g := levelMap m 1
  smooth := contDiff_levelMap m 1
  fiber_bounded := by
    have heq : {x : E | levelMap m 1 x = 0} =
        {x : E | StandardBirth.circleMap m 1 x = 0} := by
      ext x
      exact levelMap_one_zero_iff m x
    rw [heq]
    exact (StandardBirth.targetFLS m).fiber_bounded
  regular := by
    intro x hx
    have hx' : StandardBirth.circleMap m 1 x = 0 :=
      (levelMap_one_zero_iff m x).mp hx
    have hv : StandardBirth.eventMap m (spaceTime x 1) = 0 := by
      rw [StandardBirth.eventMap_spaceTime,
        birthHeight_of_threeQuarter_le (by norm_num)]
      exact hx'
    have hbound := StandardBirth.eventMap_spatial_bound_one m (spaceTime x 1) hv
    rw [initCLM_spaceTime] at hbound
    have hsq : normSq x < 2 := by
      rw [normSq_eq_norm_sq]
      nlinarith [norm_nonneg x]
    rw [(levelMap_eventuallyEq_circleMap m hsq).fderiv_eq]
    exact (StandardBirth.targetFLS m).regular x hx'


-- @@ L307-328 verbatim
/-- The compactified birth is a genuine framed cobordism. -/
def cobordism : FramedLevelCobordism (m + 1) where
  X₀ := sourceFLS m
  X₁ := targetFLS m
  G := eventMap m
  smooth := contDiff_eventMap m
  spatial_bounded := by
    obtain ⟨R, hR⟩ := StandardBirth.eventMap_spatial_bounded m
    exact ⟨R, fun v hv => hR v ((eventMap_zero_iff m v).mp hv)⟩
  regular := by
    intro v hv
    have hv' := (eventMap_zero_iff m v).mp hv
    rw [(eventMap_eventuallyEq_standard m hv').fderiv_eq]
    exact StandardBirth.eventMap_regular m v hv'
  collar_zero := by
    intro x t ht
    rw [eventMap_spaceTime, birthHeight_of_le_quarter ht]
    rfl
  collar_one := by
    intro x t ht
    rw [eventMap_spaceTime, birthHeight_of_threeQuarter_le ht]
    rfl


-- @@ L330-341 verbatim
/-- The compactified birth is literally the common background outside the
spatial radius-two ball, uniformly in time. -/
theorem cobordism_spatialFlatOutside :
    (cobordism m).SpatialFlatOutside (background m) 0 2 := by
  intro v hv
  have hn : 2 ≤ ‖initCLM (m + 2) v‖ := by
    simpa [dist_zero_right] using hv
  have hs : 4 ≤ normSq (initCLM (m + 2) v) := by
    rw [normSq_eq_norm_sq]
    nlinarith [norm_nonneg (initCLM (m + 2) v)]
  have hc := cutoff_eq_one hs
  simp [cobordism, eventMap, hc]


-- @@ L343-346 verbatim
def sourceSign : FiberSign (sourceFLS m) where
  toFun := fun _ => 1
  continuous := continuous_const
  nonzero := by simp


-- @@ L348-351 verbatim
def targetSign : FiberSign (targetFLS m) where
  toFun := fun _ => 1
  continuous := continuous_const
  nonzero := by simp


-- @@ L353-363 verbatim
/-- A spatially flat, constant-positive signed birth. -/
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


-- @@ L365-368 verbatim
/-- The corresponding flat death, ready to be adjoined to a separated tail. -/
def signedDeathCobordism :
    SignedFramedLevelCobordism (targetSign m) (sourceSign m) :=
  (signedCobordism m).reverse


-- @@ L370-372 verbatim
theorem signedCobordism_spatialFlatOutside :
    (signedCobordism m).SpatialFlatOutside (background m) 0 2 :=
  cobordism_spatialFlatOutside m


-- @@ L374-379 verbatim
theorem signedDeathCobordism_spatialFlatOutside :
    (signedDeathCobordism m).SpatialFlatOutside (background m) 0 2 := by
  intro v hv
  change eventMap m (reparamMap (m + 1) (-1) 1 v) = background m
  apply cobordism_spatialFlatOutside m
  simpa [reparamMap, initCLM_spaceTime] using hv


-- @@ L381-398 verbatim
/-- The concrete positive-death reduction with an arbitrary unchanged flat
tail.  This is the geometric operation required by the `deathPos` field once
the standard configurations have been laid out in separated balls. -/
theorem nonempty_death_juxtapose_tail
    {X : FramedLevelSet (m + 1)} (S : FiberSign X)
    {p : EuclideanSpace ℝ (Fin (m + 2))} {R : ℝ}
    (hX : X.FlatOutside (background m) p R)
    (hsep : 2 + R < dist (0 : EuclideanSpace ℝ (Fin (m + 2))) p) :
    Nonempty (SignedFramedLevelCobordism
      ((targetSign m).juxtapose S (background_ne_zero m)
        (signedDeathCobordism_spatialFlatOutside m).flatOutside_source hX hsep)
      ((sourceSign m).juxtapose S (background_ne_zero m)
        (signedDeathCobordism_spatialFlatOutside m).flatOutside_target hX hsep)) := by
  exact SignedFramedLevelCobordism.nonempty_juxtapose_tail
    (signedDeathCobordism m) (background_ne_zero m)
    (signedDeathCobordism_spatialFlatOutside m) S hX hsep
    (signedDeathCobordism_spatialFlatOutside m).flatOutside_source
    (signedDeathCobordism_spatialFlatOutside m).flatOutside_target


-- @@ L400-400 verbatim
end CompactBirth

-- @@ L401-401 verbatim
end Submission
