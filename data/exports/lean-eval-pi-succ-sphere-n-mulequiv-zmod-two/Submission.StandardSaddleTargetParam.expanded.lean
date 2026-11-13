import Submission.StandardSaddleFrameClass
import Submission.ExplicitOrbitParam
import Submission.StandardBirthDelta


-- @@ L5-15 verbatim
/-!
# Explicit parametrization of the outgoing Cassini oval

The positive Cassini level is star-shaped about the saddle point.  Solving its
quadratic equation in the squared polar radius gives

`rho(theta) = cos (2 theta) + sqrt (cos (2 theta)^2 + 1/2)`.

This file installs that literal parametrization and proves that it lies in the
target fiber.  It is the outgoing-loop input for the saddle splice calculation.
-/


-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
set_option maxHeartbeats 1600000


-- @@ L21-21 verbatim
namespace Submission

-- @@ L22-22 verbatim
namespace StandardSaddle


-- @@ L24-24 verbatim
open Set Function Topology InnerProductSpace

-- @@ L25-25 verbatim
open scoped RealInnerProductSpace Topology Matrix unitInterval


-- @@ L27-27 verbatim
variable (m : ℕ)


-- @@ L29-29 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 3))


-- @@ L31-34 verbatim
/-- Squared polar radius of the unique positive-level Cassini oval. -/
def targetRadiusSq (theta : ℝ) : ℝ :=
  Real.cos (2 * theta) +
    Real.sqrt (Real.cos (2 * theta) ^ 2 + 1 / 2)


-- @@ L36-43 verbatim
theorem targetRadiusSq_pos (theta : ℝ) : 0 < targetRadiusSq theta := by
  let c := Real.cos (2 * theta)
  let s := Real.sqrt (c ^ 2 + 1 / 2)
  have hinside : 0 ≤ c ^ 2 + (1 / 2 : ℝ) := by positivity
  have hsSq : s ^ 2 = c ^ 2 + 1 / 2 := Real.sq_sqrt hinside
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  change 0 < c + s
  nlinarith


-- @@ L45-47 verbatim
/-- Positive polar radius. -/
def targetRadius (theta : ℝ) : ℝ :=
  Real.sqrt (targetRadiusSq theta)


-- @@ L49-50 verbatim
theorem targetRadius_pos (theta : ℝ) : 0 < targetRadius theta := by
  exact Real.sqrt_pos.2 (targetRadiusSq_pos theta)


-- @@ L52-54 verbatim
theorem targetRadius_sq (theta : ℝ) :
    targetRadius theta ^ 2 = targetRadiusSq theta := by
  exact Real.sq_sqrt (targetRadiusSq_pos theta).le


-- @@ L56-61 verbatim
/-- Once-around polar parametrization of the outgoing Cassini oval. -/
def targetPoint (theta : ℝ) : E :=
  (targetRadius theta * Real.cos theta) •
      EuclideanSpace.single (planeFirst m) 1 +
    (targetRadius theta * Real.sin theta) •
      EuclideanSpace.single (planeSecond m) 1


-- @@ L63-70 verbatim
@[simp] theorem targetPoint_apply_planeFirst (theta : ℝ) :
    targetPoint m theta (planeFirst m) =
      targetRadius theta * Real.cos theta := by
  have hAB : planeFirst m ≠ planeSecond m := by
    intro h
    have := congrArg Fin.val h
    simp [planeFirst, planeSecond] at this
  simp [targetPoint, hAB]


-- @@ L72-79 verbatim
@[simp] theorem targetPoint_apply_planeSecond (theta : ℝ) :
    targetPoint m theta (planeSecond m) =
      targetRadius theta * Real.sin theta := by
  have hBA : planeSecond m ≠ planeFirst m := by
    intro h
    have := congrArg Fin.val h
    simp [planeFirst, planeSecond] at this
  simp [targetPoint, hBA]


-- @@ L81-94 verbatim
@[simp] theorem targetPoint_apply_transverse (theta : ℝ)
    (j : Fin (m + 1)) :
    targetPoint m theta j.castSucc.castSucc = 0 := by
  have hjA : j.castSucc.castSucc ≠ planeFirst m := by
    intro h
    have := congrArg Fin.val h
    simp [planeFirst] at this
    omega
  have hjB : j.castSucc.castSucc ≠ planeSecond m := by
    intro h
    have := congrArg Fin.val h
    simp [planeSecond] at this
    omega
  simp [targetPoint, hjA, hjB]


-- @@ L96-106 verbatim
theorem radiusSq_targetPoint (theta : ℝ) :
    radiusSq m (targetPoint m theta) = targetRadiusSq theta := by
  rw [radiusSq, targetPoint_apply_planeFirst, targetPoint_apply_planeSecond]
  rw [mul_pow, mul_pow, targetRadius_sq]
  calc
    targetRadiusSq theta * Real.cos theta ^ 2 +
        targetRadiusSq theta * Real.sin theta ^ 2 =
      targetRadiusSq theta *
        (Real.cos theta ^ 2 + Real.sin theta ^ 2) := by ring
    _ = targetRadiusSq theta := by
      rw [Real.cos_sq_add_sin_sq, mul_one]


-- @@ L108-116 verbatim
theorem targetRadiusSq_equation (theta : ℝ) :
    targetRadiusSq theta ^ 2 -
        2 * targetRadiusSq theta * Real.cos (2 * theta) = 1 / 2 := by
  let c := Real.cos (2 * theta)
  let s := Real.sqrt (c ^ 2 + 1 / 2)
  have hinside : 0 ≤ c ^ 2 + (1 / 2 : ℝ) := by positivity
  have hsSq : s ^ 2 = c ^ 2 + 1 / 2 := Real.sq_sqrt hinside
  change (c + s) ^ 2 - 2 * (c + s) * c = 1 / 2
  nlinarith


-- @@ L118-120 verbatim
theorem cos_sq_sub_sin_sq (theta : ℝ) :
    Real.cos theta ^ 2 - Real.sin theta ^ 2 = Real.cos (2 * theta) := by
  exact (Real.cos_two_mul' theta).symm


-- @@ L122-137 verbatim
theorem cassiniQ_targetPoint (theta : ℝ) :
    cassiniQ m (targetPoint m theta) = 1 / 2 := by
  rw [cassiniQ_eq, radiusSq_targetPoint,
    targetPoint_apply_planeFirst, targetPoint_apply_planeSecond]
  rw [mul_pow, mul_pow, targetRadius_sq]
  have htrig := cos_sq_sub_sin_sq theta
  have heq := targetRadiusSq_equation theta
  calc
    targetRadiusSq theta ^ 2 -
          2 * (targetRadiusSq theta * Real.cos theta ^ 2) +
          2 * (targetRadiusSq theta * Real.sin theta ^ 2) =
        targetRadiusSq theta ^ 2 - 2 * targetRadiusSq theta *
          (Real.cos theta ^ 2 - Real.sin theta ^ 2) := by ring
    _ = targetRadiusSq theta ^ 2 -
        2 * targetRadiusSq theta * Real.cos (2 * theta) := by rw [htrig]
    _ = 1 / 2 := heq


-- @@ L139-147 verbatim
theorem targetPoint_mem_target_fiber (theta : ℝ) :
    targetPoint m theta ∈ (targetFLS m).fiber := by
  apply (WithLp.equiv 2 _).injective
  funext i
  induction i using Fin.lastCases with
  | last =>
      simp [targetFLS, levelMap, cassiniQ_targetPoint]
  | cast j =>
      simp [targetFLS, levelMap]


-- @@ L149-151 verbatim
theorem continuous_targetRadiusSq : Continuous targetRadiusSq := by
  unfold targetRadiusSq
  fun_prop


-- @@ L153-154 verbatim
theorem continuous_targetRadius : Continuous targetRadius := by
  exact Real.continuous_sqrt.comp continuous_targetRadiusSq


-- @@ L156-159 verbatim
theorem continuous_targetPoint : Continuous (targetPoint m) := by
  exact ((continuous_targetRadius.mul Real.continuous_cos).smul
      continuous_const).add
    ((continuous_targetRadius.mul Real.continuous_sin).smul continuous_const)


-- @@ L161-161 verbatim
/-! ## The positive Cassini oval is a simple closed orbit -/


-- @@ L163-187 verbatim
theorem targetPoint_eq_iff_mod {theta theta' : ℝ}
    (h : targetPoint m theta = targetPoint m theta') :
    ∃ z : ℤ, theta' = theta + (z : ℝ) * (2 * Real.pi) := by
  have hrho : targetRadiusSq theta = targetRadiusSq theta' := by
    have := congrArg (radiusSq m) h
    simpa [radiusSq_targetPoint] using this
  have hr : targetRadius theta = targetRadius theta' := by
    simp only [targetRadius]
    rw [hrho]
  have hr0 : targetRadius theta ≠ 0 := (targetRadius_pos theta).ne'
  have hcos : Real.cos theta = Real.cos theta' := by
    have hc := congrArg (fun x : E => x (planeFirst m)) h
    simp only [targetPoint_apply_planeFirst] at hc
    rw [← hr] at hc
    exact mul_left_cancel₀ hr0 hc
  have hsin : Real.sin theta = Real.sin theta' := by
    have hs := congrArg (fun x : E => x (planeSecond m)) h
    simp only [targetPoint_apply_planeSecond] at hs
    rw [← hr] at hs
    exact mul_left_cancel₀ hr0 hs
  have hone : Real.cos (theta' - theta) = 1 := by
    rw [Real.cos_sub, ← hcos, ← hsin]
    linear_combination Real.sin_sq_add_cos_sq theta
  obtain ⟨z, hz⟩ := (Real.cos_eq_one_iff _).mp hone
  exact ⟨z, by linarith⟩


-- @@ L189-196 verbatim
theorem targetPoint_two_pi :
    targetPoint m (2 * Real.pi) = targetPoint m 0 := by
  have hfour : Real.cos (2 * (2 * Real.pi)) = 1 := by
    rw [show 2 * (2 * Real.pi) = 2 * Real.pi + 2 * Real.pi by ring,
      Real.cos_add]
    simp
  unfold targetPoint targetRadius targetRadiusSq
  simp [Real.cos_two_pi, Real.sin_two_pi, hfour]


-- @@ L198-202 verbatim
/-- The once-around closed-interval parametrization of the outgoing oval. -/
def targetCurve : C(I, E) where
  toFun u := targetPoint m (2 * Real.pi * (u : ℝ))
  continuous_toFun := (continuous_targetPoint m).comp
    ((continuous_const.mul continuous_const).mul continuous_subtype_val)


-- @@ L204-205 verbatim
@[simp] theorem targetCurve_zero : targetCurve m 0 = targetPoint m 0 := by
  simp [targetCurve]


-- @@ L207-211 verbatim
theorem targetCurve_closed : targetCurve m 0 = targetCurve m 1 := by
  rw [targetCurve_zero]
  change targetPoint m 0 = targetPoint m (2 * Real.pi * (1 : ℝ))
  norm_num
  exact (targetPoint_two_pi m).symm


-- @@ L213-253 verbatim
theorem targetCurve_eq_cases {u v : I}
    (huv : targetCurve m u = targetCurve m v) :
    u = v ∨ (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) := by
  obtain ⟨z, hz⟩ := targetPoint_eq_iff_mod m huv
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


-- @@ L255-258 verbatim
theorem targetPoint_mem_orbit (V : TamedField (targetFLS m)) (theta : ℝ) :
    targetPoint m theta ∈ V.orbit (targetPoint m 0) := by
  exact V.continuousCurve_mem_orbit (targetPoint m) (continuous_targetPoint m)
    (targetPoint_mem_target_fiber m) theta


-- @@ L260-270 verbatim
/-- The outgoing Cassini oval as a generic simple closed intrinsic orbit
parametrization. -/
def targetSimpleClosedOrbitParam (V : TamedField (targetFLS m)) :
    SimpleClosedOrbitParam (targetFLS m) V where
  p := targetPoint m 0
  hp := targetPoint_mem_target_fiber m 0
  curve := targetCurve m
  curve_zero := targetCurve_zero m
  curve_closed := targetCurve_closed m
  curve_mem_orbit := fun u => targetPoint_mem_orbit m V _
  curve_eq_cases := targetCurve_eq_cases m


-- @@ L272-272 verbatim
/-! ## The target fiber has exactly this one orbit -/


-- @@ L274-297 verbatim
theorem radiusSq_pos_of_mem_target_fiber {x : E}
    (hx : x ∈ (targetFLS m).fiber) : 0 < radiusSq m x := by
  have hr0 : 0 ≤ radiusSq m x := by
    simp [radiusSq]
    positivity
  apply lt_of_le_of_ne hr0
  intro hr
  have hrz : radiusSq m x = 0 := hr.symm
  have hA : x (planeFirst m) = 0 := by
    have hs : x (planeFirst m) ^ 2 = 0 := by
      have := sq_nonneg (x (planeSecond m))
      simp [radiusSq] at hrz
      nlinarith
    exact sq_eq_zero_iff.mp hs
  have hB : x (planeSecond m) = 0 := by
    have hs : x (planeSecond m) ^ 2 = 0 := by
      have := sq_nonneg (x (planeFirst m))
      simp [radiusSq] at hrz
      nlinarith
    exact sq_eq_zero_iff.mp hs
  have hq := cassiniQ_eq_level_of_levelMap_eq_zero m hx
  rw [cassiniQ_eq] at hq
  rw [hrz, hA, hB] at hq
  norm_num at hq


-- @@ L299-350 verbatim
theorem targetRadiusSq_eq_of_polar_coordinates
    {x : E} {theta : ℝ} (hx : x ∈ (targetFLS m).fiber)
    (hcos : Real.cos theta =
      x (planeFirst m) / Real.sqrt (radiusSq m x))
    (hsin : Real.sin theta =
      x (planeSecond m) / Real.sqrt (radiusSq m x)) :
    radiusSq m x = targetRadiusSq theta := by
  let rho := radiusSq m x
  let c := Real.cos (2 * theta)
  let s := Real.sqrt (c ^ 2 + 1 / 2)
  have hrho : 0 < rho := radiusSq_pos_of_mem_target_fiber m hx
  have hsqrt : (Real.sqrt rho) ^ 2 = rho := Real.sq_sqrt hrho.le
  have hsqrt0 : Real.sqrt rho ≠ 0 := (Real.sqrt_pos.2 hrho).ne'
  have hxA : x (planeFirst m) = Real.sqrt rho * Real.cos theta := by
    change Real.cos theta = x (planeFirst m) / Real.sqrt rho at hcos
    rw [hcos]
    field_simp
  have hxB : x (planeSecond m) = Real.sqrt rho * Real.sin theta := by
    change Real.sin theta = x (planeSecond m) / Real.sqrt rho at hsin
    rw [hsin]
    field_simp
  have hq := cassiniQ_eq_level_of_levelMap_eq_zero m hx
  rw [cassiniQ_eq] at hq
  change rho ^ 2 - 2 * x (planeFirst m) ^ 2 +
      2 * x (planeSecond m) ^ 2 = 1 / 2 at hq
  rw [hxA, hxB, mul_pow, mul_pow, hsqrt] at hq
  have htrig := cos_sq_sub_sin_sq theta
  have hquad : rho ^ 2 - 2 * rho * c = 1 / 2 := by
    change rho ^ 2 - 2 * rho * Real.cos (2 * theta) = 1 / 2
    calc
      rho ^ 2 - 2 * rho * Real.cos (2 * theta) =
          rho ^ 2 - 2 * rho *
            (Real.cos theta ^ 2 - Real.sin theta ^ 2) := by rw [htrig]
      _ = 1 / 2 := by nlinarith
  have hsInside : 0 ≤ c ^ 2 + (1 / 2 : ℝ) := by positivity
  have hsSq : s ^ 2 = c ^ 2 + 1 / 2 := Real.sq_sqrt hsInside
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hdiffSq : (rho - c) ^ 2 = s ^ 2 := by nlinarith
  have hdiffPos : 0 < rho - c := by
    by_cases hc : 0 < c
    · have hprod : 0 < rho * (rho - 2 * c) := by nlinarith
      have : 0 < rho - 2 * c := by
        rcases mul_pos_iff.mp hprod with hp | hn
        · exact hp.2
        · exact False.elim ((not_lt_of_ge hrho.le) hn.1)
      nlinarith
    · have hc0 : c ≤ 0 := not_lt.mp hc
      linarith
  have hdiff : rho - c = s := by
    nlinarith
  change rho = c + s
  linarith


-- @@ L352-398 verbatim
theorem target_fiber_eq_range :
    (targetFLS m).fiber = Set.range (targetPoint m) := by
  ext x
  constructor
  · intro hx
    let rho := radiusSq m x
    have hrho : 0 < rho := radiusSq_pos_of_mem_target_fiber m hx
    have hsqrt : (Real.sqrt rho) ^ 2 = rho := Real.sq_sqrt hrho.le
    have hsqrt0 : Real.sqrt rho ≠ 0 := (Real.sqrt_pos.2 hrho).ne'
    have hunit :
        (x (planeFirst m) / Real.sqrt rho) ^ 2 +
          (x (planeSecond m) / Real.sqrt rho) ^ 2 = 1 := by
      calc
        (x (planeFirst m) / Real.sqrt rho) ^ 2 +
            (x (planeSecond m) / Real.sqrt rho) ^ 2 =
          (x (planeFirst m) ^ 2 + x (planeSecond m) ^ 2) /
            (Real.sqrt rho) ^ 2 := by ring
        _ = rho / rho := by rw [hsqrt]; rfl
        _ = 1 := div_self hrho.ne'
    obtain ⟨theta, hcos, hsin⟩ :=
      StandardBirth.exists_angle_of_sq_add_sq_eq_one hunit
    have hrhoTarget : rho = targetRadiusSq theta :=
      targetRadiusSq_eq_of_polar_coordinates m hx hcos hsin
    have hradius : Real.sqrt rho = targetRadius theta := by
      simp only [targetRadius]
      rw [hrhoTarget]
    refine ⟨theta, ?_⟩
    apply (WithLp.equiv 2 _).injective
    funext i
    induction i using Fin.lastCases with
    | last =>
        change targetPoint m theta (planeSecond m) = x (planeSecond m)
        rw [targetPoint_apply_planeSecond, ← hradius, hsin]
        field_simp
    | cast i =>
        induction i using Fin.lastCases with
        | last =>
            change targetPoint m theta (planeFirst m) = x (planeFirst m)
            rw [targetPoint_apply_planeFirst, ← hradius, hcos]
            field_simp
        | cast j =>
            have hxj := transverse_eq_zero_of_levelMap_eq_zero m hx j
            change targetPoint m theta j.castSucc.castSucc =
              x j.castSucc.castSucc
            rw [targetPoint_apply_transverse, hxj]
  · rintro ⟨theta, rfl⟩
    exact targetPoint_mem_target_fiber m theta


-- @@ L400-406 verbatim
theorem target_orbit_eq_fiber (V : TamedField (targetFLS m)) :
    V.orbit (targetPoint m 0) = (targetFLS m).fiber := by
  apply Set.Subset.antisymm
  · exact V.orbit_subset_fiber (targetPoint_mem_target_fiber m 0)
  · rw [target_fiber_eq_range m]
    rintro x ⟨theta, rfl⟩
    exact targetPoint_mem_orbit m V theta


-- @@ L408-411 verbatim
/-- The unique orbit index of the outgoing Cassini oval. -/
def targetOrbitIndex (V : TamedField (targetFLS m)) : V.OrbitIndex :=
  ⟨V.orbit (targetPoint m 0), V.mem_orbitFinset.mpr
    ⟨targetPoint m 0, targetPoint_mem_target_fiber m 0, rfl⟩⟩


-- @@ L413-415 verbatim
@[simp] theorem targetOrbitIndex_coe (V : TamedField (targetFLS m)) :
    ((targetOrbitIndex m V : V.OrbitIndex) : Set E) =
      V.orbit (targetPoint m 0) := rfl


-- @@ L417-423 verbatim
theorem orbitIndex_eq_targetOrbitIndex (V : TamedField (targetFLS m))
    (O : V.OrbitIndex) : O = targetOrbitIndex m V := by
  apply Subtype.ext
  change (O : Set E) = V.orbit (targetPoint m 0)
  rw [V.orbitPoint_orbit, V.orbit_eq_of_mem]
  rw [target_orbit_eq_fiber m V]
  exact V.orbitPoint_mem_fiber O


-- @@ L425-434 verbatim
theorem target_framedDelta_eq_orbitContribution
    (V : TamedField (targetFLS m)) :
    V.framedDelta = V.orbitContribution (targetOrbitIndex m V) := by
  classical
  letI : Unique V.OrbitIndex := {
    default := targetOrbitIndex m V
    uniq := orbitIndex_eq_targetOrbitIndex m V }
  simp [TamedField.framedDelta]
  exact congrArg V.orbitContribution
    (orbitIndex_eq_targetOrbitIndex m V default)


-- @@ L436-442 verbatim
/-- The explicit polar loop computes the intrinsic fundamental frame class. -/
theorem target_paramFrameClass_eq_fundamental
    (V : TamedField (targetFLS m)) :
    loopClassZ2 (targetSimpleClosedOrbitParam m V).paramFrameLoop
        (targetSimpleClosedOrbitParam m V).paramFrameLoop_closed =
      V.fundamentalFrameClass (targetPoint_mem_target_fiber m 0) :=
  (targetSimpleClosedOrbitParam m V).paramFrameClass_eq_fundamental


-- @@ L444-465 verbatim
/-- Exact reduction of the outgoing geometric delta to the explicit Cassini
Gram--Schmidt frame loop. -/
theorem target_framedDelta_eq_paramFrameClass_add_one
    (V : TamedField (targetFLS m)) :
    V.framedDelta =
      loopClassZ2 (targetSimpleClosedOrbitParam m V).paramFrameLoop
        (targetSimpleClosedOrbitParam m V).paramFrameLoop_closed + 1 := by
  rw [target_framedDelta_eq_orbitContribution]
  unfold TamedField.orbitContribution TamedField.orbitFrameClass
  have hpoint : V.orbitPoint (targetOrbitIndex m V) ∈
      V.orbit (targetPoint m 0) := by
    rw [← targetOrbitIndex_coe m V, V.orbitPoint_orbit]
    exact V.mem_orbit_self _
  have hbase :
      V.fundamentalFrameClass
          (V.orbitPoint_mem_fiber (targetOrbitIndex m V)) =
        V.fundamentalFrameClass (targetPoint_mem_target_fiber m 0) :=
    V.fundamentalFrameClass_eq_of_mem_orbit
      (targetPoint_mem_target_fiber m 0) hpoint
  change V.fundamentalFrameClass
      (V.orbitPoint_mem_fiber (targetOrbitIndex m V)) + 1 = _
  rw [hbase, ← target_paramFrameClass_eq_fundamental m V]


-- @@ L467-481 verbatim
theorem targetSign_positiveFramedDelta_eq_framedDelta
    (V : TamedField (targetFLS m)) :
    (targetSign m).positiveFramedDelta V = V.framedDelta := by
  classical
  unfold FiberSign.positiveFramedDelta TamedField.deltaOn TamedField.framedDelta
  apply Finset.sum_congr rfl
  intro O _
  have hselected : (O : Set E) ∈
      (targetSign m).positiveOrbitCollection V := by
    intro x hx
    refine ⟨?_, ?_⟩
    · rw [V.orbitPoint_orbit O] at hx
      exact V.orbit_subset_fiber (V.orbitPoint_mem_fiber O) hx
    · simp [targetSign]
  simp [hselected]


-- @@ L483-490 verbatim
theorem targetSign_positiveDelta_eq_paramFrameClass_add_one
    (V : TamedField (targetFLS m)) :
    (targetSign m).positiveDelta =
      loopClassZ2 (targetSimpleClosedOrbitParam m V).paramFrameLoop
        (targetSimpleClosedOrbitParam m V).paramFrameLoop_closed + 1 := by
  rw [(targetSign m).positiveDelta_eq V,
    targetSign_positiveFramedDelta_eq_framedDelta,
    target_framedDelta_eq_paramFrameClass_add_one]


-- @@ L492-508 verbatim
/-- Pointwise reduction of the intrinsic outgoing frame loop to the explicit
two-plane Cassini frame computed in `StandardSaddleFrameClass`. -/
theorem target_paramFrameLoop_apply
    (V : TamedField (targetFLS m)) (u : I) :
    ((targetSimpleClosedOrbitParam m V).paramFrameLoop u :
        Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ) =
      rowsMatrix (endpointUnitFrame m (1 / 2)
        (targetPoint m (2 * Real.pi * (u : ℝ)))) := by
  change frameLoop (targetFLS m)
      (targetSimpleClosedOrbitParam m V).realCurve (u : ℝ) = _
  unfold frameLoop
  rw [(targetSimpleClosedOrbitParam m V).realCurve_coe]
  change rowsMatrix (gramSchmidtNormed ℝ
      (frameAt (targetFLS m)
        (targetPoint m (2 * Real.pi * (u : ℝ))))) = _
  rw [gramSchmidtNormed_frameAt_target m
    (targetPoint_mem_target_fiber m _)]


-- @@ L510-510 verbatim
end StandardSaddle

-- @@ L511-511 verbatim
end Submission
