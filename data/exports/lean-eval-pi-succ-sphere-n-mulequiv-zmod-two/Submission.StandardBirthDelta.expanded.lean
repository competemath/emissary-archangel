import Submission.ExplicitOrbitParam
import Submission.MorseLedgerCobordism


-- @@ L4-12 verbatim
/-!
# The geometric delta of the standard definite Morse event

This file connects the literal birth cobordism from `MorseLedgerCobordism` to
the intrinsic orbit machinery of `Delta`.  It first identifies its outgoing
unit circle as a single flow orbit and packages the usual angular
parametrization as a `SimpleClosedOrbitParam`.  The remaining frame calculation
is thereby reduced to the explicit Gram--Schmidt loop along that circle.
-/


-- @@ L14-14 verbatim
noncomputable section


-- @@ L16-16 verbatim
set_option maxHeartbeats 1600000


-- @@ L18-18 verbatim
namespace Submission

-- @@ L19-19 verbatim
namespace StandardBirth


-- @@ L21-21 verbatim
open Set Function Topology

-- @@ L22-22 verbatim
open scoped RealInnerProductSpace Topology Matrix unitInterval


-- @@ L24-24 verbatim
variable (m : ℕ)


-- @@ L26-26 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 2))


-- @@ L28-32 verbatim
/-- The unit circle in the two radial coordinates of the standard birth
presentation. -/
def circlePoint (theta : ℝ) : E :=
  Real.cos theta • EuclideanSpace.single (radialFirst m) 1 +
    Real.sin theta • EuclideanSpace.single (radialSecond m) 1


-- @@ L34-40 verbatim
@[simp] theorem circlePoint_apply_radialFirst (theta : ℝ) :
    circlePoint m theta (radialFirst m) = Real.cos theta := by
  have hAB : radialFirst m ≠ radialSecond m := by
    intro h
    have := congrArg Fin.val h
    simp [radialFirst, radialSecond] at this
  simp [circlePoint, Pi.single_apply, hAB]


-- @@ L42-48 verbatim
@[simp] theorem circlePoint_apply_radialSecond (theta : ℝ) :
    circlePoint m theta (radialSecond m) = Real.sin theta := by
  have hBA : radialSecond m ≠ radialFirst m := by
    intro h
    have := congrArg Fin.val h
    simp [radialFirst, radialSecond] at this
  simp [circlePoint, Pi.single_apply, hBA]


-- @@ L50-64 verbatim
@[simp] theorem circlePoint_apply_transverse (theta : ℝ) (j : Fin m) :
    circlePoint m theta j.castSucc.castSucc = 0 := by
  have hjA : j.castSucc.castSucc ≠ radialFirst m :=
    by
      intro h
      have := congrArg Fin.val h
      simp [radialFirst] at this
      omega
  have hjB : j.castSucc.castSucc ≠ radialSecond m :=
    by
      intro h
      have := congrArg Fin.val h
      simp [radialSecond] at this
      omega
  simp [circlePoint, Pi.single_apply, hjA, hjB]


-- @@ L66-68 verbatim
theorem continuous_circlePoint : Continuous (circlePoint m) := by
  exact (Real.continuous_cos.smul continuous_const).add
    (Real.continuous_sin.smul continuous_const)


-- @@ L70-78 verbatim
theorem circlePoint_mem_target_fiber (theta : ℝ) :
    circlePoint m theta ∈ (targetFLS m).fiber := by
  apply (WithLp.equiv 2 _).injective
  funext i
  induction i using Fin.lastCases with
  | last =>
      simp [targetFLS, circleMap, radialSq, Real.cos_sq_add_sin_sq]
  | cast j =>
      simp [targetFLS, circleMap]


-- @@ L80-83 verbatim
theorem circlePoint_mem_orbit (V : TamedField (targetFLS m)) (theta : ℝ) :
    circlePoint m theta ∈ V.orbit (circlePoint m 0) := by
  exact V.continuousCurve_mem_orbit (circlePoint m) (continuous_circlePoint m)
    (circlePoint_mem_target_fiber m) theta


-- @@ L85-97 verbatim
/-- Equality of two angular points determines the angles modulo `2π`. -/
theorem circlePoint_eq_iff_mod {theta theta' : ℝ}
    (h : circlePoint m theta = circlePoint m theta') :
    ∃ z : ℤ, theta' = theta + (z : ℝ) * (2 * Real.pi) := by
  have hcos : Real.cos theta = Real.cos theta' := by
    simpa using congrArg (fun x : E => x (radialFirst m)) h
  have hsin : Real.sin theta = Real.sin theta' := by
    simpa using congrArg (fun x : E => x (radialSecond m)) h
  have hone : Real.cos (theta' - theta) = 1 := by
    rw [Real.cos_sub, ← hcos, ← hsin]
    linear_combination Real.sin_sq_add_cos_sq theta
  obtain ⟨z, hz⟩ := (Real.cos_eq_one_iff _).mp hone
  exact ⟨z, by linarith⟩


-- @@ L99-103 verbatim
/-- The once-around unit-interval parametrization. -/
def unitCircleCurve : C(I, E) where
  toFun u := circlePoint m (2 * Real.pi * (u : ℝ))
  continuous_toFun := (continuous_circlePoint m).comp
    ((continuous_const.mul continuous_const).mul continuous_subtype_val)


-- @@ L105-106 verbatim
@[simp] theorem unitCircleCurve_zero : unitCircleCurve m 0 = circlePoint m 0 := by
  simp [unitCircleCurve]


-- @@ L108-120 verbatim
theorem unitCircleCurve_closed : unitCircleCurve m 0 = unitCircleCurve m 1 := by
  apply (WithLp.equiv 2 _).injective
  funext i
  by_cases hiA : i = radialFirst m
  · subst i
    simp [unitCircleCurve]
  · by_cases hiB : i = radialSecond m
    · subst i
      simp [unitCircleCurve]
    · have hi : ∀ theta, circlePoint m theta i = 0 := by
        intro theta
        simp [circlePoint, Pi.single_apply, hiA, hiB]
      simp [unitCircleCurve, hi]


-- @@ L122-162 verbatim
theorem unitCircleCurve_eq_cases {u v : I}
    (huv : unitCircleCurve m u = unitCircleCurve m v) :
    u = v ∨ (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) := by
  obtain ⟨z, hz⟩ := circlePoint_eq_iff_mod m huv
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


-- @@ L164-173 verbatim
/-- The standard born circle as a generic simple closed orbit parameter. -/
def simpleClosedOrbitParam (V : TamedField (targetFLS m)) :
    SimpleClosedOrbitParam (targetFLS m) V where
  p := circlePoint m 0
  hp := circlePoint_mem_target_fiber m 0
  curve := unitCircleCurve m
  curve_zero := unitCircleCurve_zero m
  curve_closed := unitCircleCurve_closed m
  curve_mem_orbit := fun u => circlePoint_mem_orbit m V _
  curve_eq_cases := unitCircleCurve_eq_cases m


-- @@ L175-182 verbatim
/-- The explicit circle frame is now identified with the intrinsic frame class
without any reference to a chosen flow parametrization. -/
theorem unitCircle_paramFrameClass_eq_fundamental
    (V : TamedField (targetFLS m)) :
    loopClassZ2 (simpleClosedOrbitParam m V).paramFrameLoop
        (simpleClosedOrbitParam m V).paramFrameLoop_closed =
      V.fundamentalFrameClass (circlePoint_mem_target_fiber m 0) :=
  (simpleClosedOrbitParam m V).paramFrameClass_eq_fundamental


-- @@ L184-184 verbatim
/-! ## The target fiber has exactly one orbit -/


-- @@ L186-201 verbatim
theorem exists_angle_of_sq_add_sq_eq_one {a b : ℝ}
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


-- @@ L203-234 verbatim
theorem target_fiber_eq_range :
    (targetFLS m).fiber = Set.range (circlePoint m) := by
  ext x
  constructor
  · intro hx
    have hr : x (radialFirst m) ^ 2 + x (radialSecond m) ^ 2 = 1 := by
      have h := congrArg (fun q => q (Fin.last m)) hx
      simp [targetFLS, circleMap, radialSq] at h
      linarith
    obtain ⟨theta, hcos, hsin⟩ := exists_angle_of_sq_add_sq_eq_one hr
    refine ⟨theta, ?_⟩
    apply (WithLp.equiv 2 _).injective
    funext i
    induction i using Fin.lastCases with
    | last =>
        change circlePoint m theta (radialSecond m) = x (radialSecond m)
        rw [circlePoint_apply_radialSecond, hsin]
    | cast i =>
        induction i using Fin.lastCases with
        | last =>
            change circlePoint m theta (radialFirst m) = x (radialFirst m)
            rw [circlePoint_apply_radialFirst, hcos]
        | cast j =>
            have hj := congrArg (fun q => q j.castSucc) hx
            have hxj : x j.castSucc.castSucc = 0 := by
              simpa [targetFLS, circleMap] using hj
            change circlePoint m theta j.castSucc.castSucc =
              x j.castSucc.castSucc
            rw [hxj]
            exact circlePoint_apply_transverse m theta j
  · rintro ⟨theta, rfl⟩
    exact circlePoint_mem_target_fiber m theta


-- @@ L236-242 verbatim
theorem target_orbit_eq_fiber (V : TamedField (targetFLS m)) :
    V.orbit (circlePoint m 0) = (targetFLS m).fiber := by
  apply Set.Subset.antisymm
  · exact V.orbit_subset_fiber (circlePoint_mem_target_fiber m 0)
  · rw [target_fiber_eq_range m]
    rintro x ⟨theta, rfl⟩
    exact circlePoint_mem_orbit m V theta


-- @@ L244-247 verbatim
/-- The unique orbit index of the born circle. -/
def targetOrbitIndex (V : TamedField (targetFLS m)) : V.OrbitIndex :=
  ⟨V.orbit (circlePoint m 0), V.mem_orbitFinset.mpr
    ⟨circlePoint m 0, circlePoint_mem_target_fiber m 0, rfl⟩⟩


-- @@ L249-251 verbatim
@[simp] theorem targetOrbitIndex_coe (V : TamedField (targetFLS m)) :
    ((targetOrbitIndex m V : V.OrbitIndex) : Set E) =
      V.orbit (circlePoint m 0) := rfl


-- @@ L253-259 verbatim
theorem orbitIndex_eq_targetOrbitIndex (V : TamedField (targetFLS m))
    (O : V.OrbitIndex) : O = targetOrbitIndex m V := by
  apply Subtype.ext
  change (O : Set E) = V.orbit (circlePoint m 0)
  rw [V.orbitPoint_orbit O, V.orbit_eq_of_mem]
  rw [target_orbit_eq_fiber m V]
  exact V.orbitPoint_mem_fiber O


-- @@ L261-271 verbatim
/-- The total target delta is the contribution of its unique circle. -/
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


-- @@ L273-293 verbatim
/-- Exact reduction of the geometric birth calculation to the explicit
Gram--Schmidt frame loop along the unit circle. -/
theorem target_framedDelta_eq_paramFrameClass_add_one
    (V : TamedField (targetFLS m)) :
    V.framedDelta =
      loopClassZ2 (simpleClosedOrbitParam m V).paramFrameLoop
        (simpleClosedOrbitParam m V).paramFrameLoop_closed + 1 := by
  rw [target_framedDelta_eq_orbitContribution]
  unfold TamedField.orbitContribution TamedField.orbitFrameClass
  have hpoint : V.orbitPoint (targetOrbitIndex m V) ∈
      V.orbit (circlePoint m 0) := by
    rw [← targetOrbitIndex_coe m V, V.orbitPoint_orbit]
    exact V.mem_orbit_self _
  have hbase :
      V.fundamentalFrameClass (V.orbitPoint_mem_fiber (targetOrbitIndex m V)) =
        V.fundamentalFrameClass (circlePoint_mem_target_fiber m 0) :=
    V.fundamentalFrameClass_eq_of_mem_orbit
      (circlePoint_mem_target_fiber m 0) hpoint
  change V.fundamentalFrameClass
      (V.orbitPoint_mem_fiber (targetOrbitIndex m V)) + 1 = _
  rw [hbase, ← unitCircle_paramFrameClass_eq_fundamental m V]


-- @@ L295-309 verbatim
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


-- @@ L311-315 verbatim
theorem targetSign_positiveDelta_eq_framedDelta
    (V : TamedField (targetFLS m)) :
    (targetSign m).positiveDelta = V.framedDelta := by
  rw [(targetSign m).positiveDelta_eq V,
    targetSign_positiveFramedDelta_eq_framedDelta]


-- @@ L317-326 verbatim
/-- Once the remaining explicit frame loop is identified with the already
computed one-turn definite model, the literal born circle has delta zero. -/
theorem targetSign_positiveDelta_eq_zero_of_paramFrameClass
    (V : TamedField (targetFLS m))
    (hframe : loopClassZ2 (simpleClosedOrbitParam m V).paramFrameLoop
      (simpleClosedOrbitParam m V).paramFrameLoop_closed = 1) :
    (targetSign m).positiveDelta = 0 := by
  rw [targetSign_positiveDelta_eq_framedDelta m V,
    target_framedDelta_eq_paramFrameClass_add_one m V, hframe]
  decide


-- @@ L328-335 verbatim
theorem source_fiber_eq_empty : (sourceFLS m).fiber = ∅ := by
  ext x
  simp only [FramedLevelSet.fiber, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    iff_false]
  intro hx
  have h := congrArg (fun q => q (Fin.last m)) hx
  simp [sourceFLS, circleMap, radialSq] at h
  nlinarith [sq_nonneg (x (radialFirst m)), sq_nonneg (x (radialSecond m))]


-- @@ L337-339 verbatim
@[simp] theorem sourceSign_positiveDelta :
    (sourceSign m).positiveDelta = 0 :=
  FiberSign.positiveDelta_eq_zero_of_fiber_eq_empty _ (source_fiber_eq_empty m)


-- @@ L341-349 verbatim
/-- The literal birth preserves the signed delta once its explicit outgoing
frame loop is discharged. -/
theorem source_target_positiveDelta_eq_of_paramFrameClass
    (V : TamedField (targetFLS m))
    (hframe : loopClassZ2 (simpleClosedOrbitParam m V).paramFrameLoop
      (simpleClosedOrbitParam m V).paramFrameLoop_closed = 1) :
    (sourceSign m).positiveDelta = (targetSign m).positiveDelta := by
  rw [sourceSign_positiveDelta,
    targetSign_positiveDelta_eq_zero_of_paramFrameClass m V hframe]


-- @@ L351-351 verbatim
end StandardBirth

-- @@ L352-352 verbatim
end Submission
