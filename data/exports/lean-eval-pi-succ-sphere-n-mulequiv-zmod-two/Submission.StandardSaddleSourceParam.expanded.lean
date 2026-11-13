import Submission.StandardSaddleTargetParam


-- @@ L3-13 verbatim
/-!
# Explicit parametrizations of the two incoming Cassini ovals

At the source level the Cassini equation is

`|z^2 - 1|^2 = 1/2`.

Because `1 + (1/sqrt 2) exp(i theta)` stays in the open right half-plane, it
has a continuous square root with positive real part.  That root parametrizes
the right incoming oval and its negative parametrizes the left one.
-/


-- @@ L15-15 verbatim
noncomputable section


-- @@ L17-17 verbatim
set_option maxHeartbeats 1600000


-- @@ L19-19 verbatim
namespace Submission

-- @@ L20-20 verbatim
namespace StandardSaddle


-- @@ L22-22 verbatim
open Set Function Topology InnerProductSpace

-- @@ L23-23 verbatim
open scoped RealInnerProductSpace Topology Matrix unitInterval


-- @@ L25-25 verbatim
variable (m : ℕ)


-- @@ L27-27 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 3))


-- @@ L29-30 verbatim
/-- Radius of the circle `z^2 - 1` traverses in the complex plane. -/
def sourceScale : ℝ := Real.sqrt (1 / 2)


-- @@ L32-33 verbatim
theorem sourceScale_pos : 0 < sourceScale := by
  exact Real.sqrt_pos.2 (by norm_num)


-- @@ L35-36 verbatim
theorem sourceScale_sq : sourceScale ^ 2 = 1 / 2 := by
  exact Real.sq_sqrt (by norm_num)


-- @@ L38-41 verbatim
theorem sourceScale_lt_one : sourceScale < 1 := by
  have hs0 := sourceScale_pos
  have hs2 := sourceScale_sq
  nlinarith


-- @@ L43-44 verbatim
def sourceRadicandFirst (theta : ℝ) : ℝ :=
  1 + sourceScale * Real.cos theta


-- @@ L46-47 verbatim
def sourceRadicandSecond (theta : ℝ) : ℝ :=
  sourceScale * Real.sin theta


-- @@ L49-55 verbatim
theorem sourceRadicandFirst_pos (theta : ℝ) :
    0 < sourceRadicandFirst theta := by
  have hc := Real.neg_one_le_cos theta
  have hs0 := sourceScale_pos
  have hs1 := sourceScale_lt_one
  unfold sourceRadicandFirst
  nlinarith


-- @@ L57-60 verbatim
/-- Modulus of the radicand. -/
def sourceRadicandNorm (theta : ℝ) : ℝ :=
  Real.sqrt (sourceRadicandFirst theta ^ 2 +
    sourceRadicandSecond theta ^ 2)


-- @@ L62-66 verbatim
theorem sourceRadicandNorm_sq (theta : ℝ) :
    sourceRadicandNorm theta ^ 2 =
      sourceRadicandFirst theta ^ 2 +
        sourceRadicandSecond theta ^ 2 := by
  exact Real.sq_sqrt (by positivity)


-- @@ L68-72 verbatim
theorem sourceRadicandNorm_pos (theta : ℝ) :
    0 < sourceRadicandNorm theta := by
  apply Real.sqrt_pos.2
  have hA := sourceRadicandFirst_pos theta
  nlinarith [sq_nonneg (sourceRadicandSecond theta)]


-- @@ L74-76 verbatim
/-- Positive real coordinate of the preferred square root. -/
def sourceRootFirst (theta : ℝ) : ℝ :=
  Real.sqrt ((sourceRadicandNorm theta + sourceRadicandFirst theta) / 2)


-- @@ L78-82 verbatim
theorem sourceRootFirst_pos (theta : ℝ) : 0 < sourceRootFirst theta := by
  apply Real.sqrt_pos.2
  have hR := sourceRadicandNorm_pos theta
  have hA := sourceRadicandFirst_pos theta
  positivity


-- @@ L84-90 verbatim
theorem sourceRootFirst_sq (theta : ℝ) :
    sourceRootFirst theta ^ 2 =
      (sourceRadicandNorm theta + sourceRadicandFirst theta) / 2 := by
  apply Real.sq_sqrt
  have hR := sourceRadicandNorm_pos theta
  have hA := sourceRadicandFirst_pos theta
  positivity


-- @@ L92-95 verbatim
/-- Imaginary coordinate of the preferred square root.  The division is safe
because `sourceRootFirst` is everywhere positive. -/
def sourceRootSecond (theta : ℝ) : ℝ :=
  sourceRadicandSecond theta / (2 * sourceRootFirst theta)


-- @@ L97-101 verbatim
theorem two_mul_sourceRootFirst_mul_sourceRootSecond (theta : ℝ) :
    2 * sourceRootFirst theta * sourceRootSecond theta =
      sourceRadicandSecond theta := by
  rw [sourceRootSecond]
  field_simp [(sourceRootFirst_pos theta).ne']


-- @@ L103-121 verbatim
theorem sourceRoot_sq_sub_sq (theta : ℝ) :
    sourceRootFirst theta ^ 2 - sourceRootSecond theta ^ 2 =
      sourceRadicandFirst theta := by
  let A := sourceRadicandFirst theta
  let B := sourceRadicandSecond theta
  let R := sourceRadicandNorm theta
  let u := sourceRootFirst theta
  let v := sourceRootSecond theta
  have hR : R ^ 2 = A ^ 2 + B ^ 2 := sourceRadicandNorm_sq theta
  have hU : u ^ 2 = (R + A) / 2 := sourceRootFirst_sq theta
  have hu0 : u ≠ 0 := (sourceRootFirst_pos theta).ne'
  have hV : v = B / (2 * u) := rfl
  change u ^ 2 - v ^ 2 = A
  rw [hV]
  field_simp
  have hU2 : 2 * u ^ 2 = R + A := by nlinarith [hU]
  have hUsq := congrArg (fun z : ℝ => z ^ 2) hU2
  have hU2A := congrArg (fun z : ℝ => 2 * A * z) hU2
  nlinarith [hUsq, hU2A]


-- @@ L123-125 verbatim
theorem continuous_sourceRadicandFirst : Continuous sourceRadicandFirst := by
  unfold sourceRadicandFirst sourceScale
  fun_prop


-- @@ L127-129 verbatim
theorem continuous_sourceRadicandSecond : Continuous sourceRadicandSecond := by
  unfold sourceRadicandSecond sourceScale
  fun_prop


-- @@ L131-134 verbatim
theorem continuous_sourceRadicandNorm : Continuous sourceRadicandNorm := by
  exact Real.continuous_sqrt.comp
    ((continuous_sourceRadicandFirst.pow 2).add
      (continuous_sourceRadicandSecond.pow 2))


-- @@ L136-139 verbatim
theorem continuous_sourceRootFirst : Continuous sourceRootFirst := by
  exact Real.continuous_sqrt.comp
    ((continuous_sourceRadicandNorm.add
      continuous_sourceRadicandFirst).div_const 2)


-- @@ L141-145 verbatim
theorem continuous_sourceRootSecond : Continuous sourceRootSecond := by
  apply Continuous.div continuous_sourceRadicandSecond
    (continuous_const.mul continuous_sourceRootFirst)
  intro theta
  exact mul_ne_zero (by norm_num) (sourceRootFirst_pos theta).ne'


-- @@ L147-150 verbatim
/-- Right incoming oval. -/
def sourcePointRight (theta : ℝ) : E :=
  sourceRootFirst theta • EuclideanSpace.single (planeFirst m) 1 +
    sourceRootSecond theta • EuclideanSpace.single (planeSecond m) 1


-- @@ L152-153 verbatim
/-- Left incoming oval, obtained by the other square root. -/
def sourcePointLeft (theta : ℝ) : E := -sourcePointRight m theta


-- @@ L155-161 verbatim
@[simp] theorem sourcePointRight_apply_planeFirst (theta : ℝ) :
    sourcePointRight m theta (planeFirst m) = sourceRootFirst theta := by
  have hAB : planeFirst m ≠ planeSecond m := by
    intro h
    have := congrArg Fin.val h
    simp [planeFirst, planeSecond] at this
  simp [sourcePointRight, hAB]


-- @@ L163-169 verbatim
@[simp] theorem sourcePointRight_apply_planeSecond (theta : ℝ) :
    sourcePointRight m theta (planeSecond m) = sourceRootSecond theta := by
  have hBA : planeSecond m ≠ planeFirst m := by
    intro h
    have := congrArg Fin.val h
    simp [planeFirst, planeSecond] at this
  simp [sourcePointRight, hBA]


-- @@ L171-173 verbatim
@[simp] theorem sourcePointLeft_apply_planeFirst (theta : ℝ) :
    sourcePointLeft m theta (planeFirst m) = -sourceRootFirst theta := by
  simp [sourcePointLeft]


-- @@ L175-177 verbatim
@[simp] theorem sourcePointLeft_apply_planeSecond (theta : ℝ) :
    sourcePointLeft m theta (planeSecond m) = -sourceRootSecond theta := by
  simp [sourcePointLeft]


-- @@ L179-192 verbatim
@[simp] theorem sourcePointRight_apply_transverse (theta : ℝ)
    (j : Fin (m + 1)) :
    sourcePointRight m theta j.castSucc.castSucc = 0 := by
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
  simp [sourcePointRight, hjA, hjB]


-- @@ L194-200 verbatim
theorem cassiniQ_eq_complex_square (x : E) :
    cassiniQ m x =
      (x (planeFirst m) ^ 2 - x (planeSecond m) ^ 2 - 1) ^ 2 +
        (2 * x (planeFirst m) * x (planeSecond m)) ^ 2 - 1 := by
  rw [cassiniQ_eq]
  simp only [radiusSq]
  ring


-- @@ L202-215 verbatim
theorem cassiniQ_sourcePointRight (theta : ℝ) :
    cassiniQ m (sourcePointRight m theta) = -1 / 2 := by
  rw [cassiniQ_eq_complex_square, sourcePointRight_apply_planeFirst,
    sourcePointRight_apply_planeSecond, sourceRoot_sq_sub_sq,
    two_mul_sourceRootFirst_mul_sourceRootSecond]
  unfold sourceRadicandFirst sourceRadicandSecond
  rw [add_sub_cancel_left]
  have hs := sourceScale_sq
  calc
    (sourceScale * Real.cos theta) ^ 2 +
          (sourceScale * Real.sin theta) ^ 2 - 1 =
        sourceScale ^ 2 *
          (Real.cos theta ^ 2 + Real.sin theta ^ 2) - 1 := by ring
    _ = -1 / 2 := by rw [Real.cos_sq_add_sin_sq, mul_one, hs]; ring


-- @@ L217-219 verbatim
theorem cassiniQ_neg (x : E) : cassiniQ m (-x) = cassiniQ m x := by
  rw [cassiniQ_eq, cassiniQ_eq]
  simp [radiusSq]


-- @@ L221-223 verbatim
theorem cassiniQ_sourcePointLeft (theta : ℝ) :
    cassiniQ m (sourcePointLeft m theta) = -1 / 2 := by
  rw [sourcePointLeft, cassiniQ_neg, cassiniQ_sourcePointRight]


-- @@ L225-231 verbatim
theorem sourcePointRight_mem_source_fiber (theta : ℝ) :
    sourcePointRight m theta ∈ (sourceFLS m).fiber := by
  apply (WithLp.equiv 2 _).injective
  funext i
  induction i using Fin.lastCases with
  | last => simp [sourceFLS, levelMap, cassiniQ_sourcePointRight]
  | cast j => simp [sourceFLS, levelMap]


-- @@ L233-239 verbatim
theorem sourcePointLeft_mem_source_fiber (theta : ℝ) :
    sourcePointLeft m theta ∈ (sourceFLS m).fiber := by
  apply (WithLp.equiv 2 _).injective
  funext i
  induction i using Fin.lastCases with
  | last => simp [sourceFLS, levelMap, cassiniQ_sourcePointLeft]
  | cast j => simp [sourceFLS, levelMap, sourcePointLeft]


-- @@ L241-243 verbatim
theorem continuous_sourcePointRight : Continuous (sourcePointRight m) := by
  exact (continuous_sourceRootFirst.smul continuous_const).add
    (continuous_sourceRootSecond.smul continuous_const)


-- @@ L245-246 verbatim
theorem continuous_sourcePointLeft : Continuous (sourcePointLeft m) := by
  exact (continuous_sourcePointRight m).neg


-- @@ L248-248 verbatim
/-! ## Two simple closed incoming orbit parametrizations -/


-- @@ L250-275 verbatim
theorem sourcePointRight_eq_iff_mod {theta theta' : ℝ}
    (h : sourcePointRight m theta = sourcePointRight m theta') :
    ∃ z : ℤ, theta' = theta + (z : ℝ) * (2 * Real.pi) := by
  have hu : sourceRootFirst theta = sourceRootFirst theta' := by
    simpa using congrArg (fun x : E => x (planeFirst m)) h
  have hv : sourceRootSecond theta = sourceRootSecond theta' := by
    simpa using congrArg (fun x : E => x (planeSecond m)) h
  have hA : sourceRadicandFirst theta = sourceRadicandFirst theta' := by
    rw [← sourceRoot_sq_sub_sq theta, ← sourceRoot_sq_sub_sq theta', hu, hv]
  have hB : sourceRadicandSecond theta = sourceRadicandSecond theta' := by
    rw [← two_mul_sourceRootFirst_mul_sourceRootSecond theta,
      ← two_mul_sourceRootFirst_mul_sourceRootSecond theta', hu, hv]
  have hs0 : sourceScale ≠ 0 := sourceScale_pos.ne'
  have hcos : Real.cos theta = Real.cos theta' := by
    unfold sourceRadicandFirst at hA
    have : sourceScale * Real.cos theta = sourceScale * Real.cos theta' := by
      linarith
    exact mul_left_cancel₀ hs0 this
  have hsin : Real.sin theta = Real.sin theta' := by
    unfold sourceRadicandSecond at hB
    exact mul_left_cancel₀ hs0 hB
  have hone : Real.cos (theta' - theta) = 1 := by
    rw [Real.cos_sub, ← hcos, ← hsin]
    linear_combination Real.sin_sq_add_cos_sq theta
  obtain ⟨z, hz⟩ := (Real.cos_eq_one_iff _).mp hone
  exact ⟨z, by linarith⟩


-- @@ L277-281 verbatim
theorem sourcePointLeft_eq_iff_mod {theta theta' : ℝ}
    (h : sourcePointLeft m theta = sourcePointLeft m theta') :
    ∃ z : ℤ, theta' = theta + (z : ℝ) * (2 * Real.pi) := by
  apply sourcePointRight_eq_iff_mod m
  simpa [sourcePointLeft] using h


-- @@ L283-287 verbatim
theorem sourcePointRight_two_pi :
    sourcePointRight m (2 * Real.pi) = sourcePointRight m 0 := by
  unfold sourcePointRight sourceRootSecond sourceRootFirst sourceRadicandNorm
    sourceRadicandFirst sourceRadicandSecond
  simp [Real.cos_two_pi, Real.sin_two_pi]


-- @@ L289-291 verbatim
theorem sourcePointLeft_two_pi :
    sourcePointLeft m (2 * Real.pi) = sourcePointLeft m 0 := by
  rw [sourcePointLeft, sourcePointLeft, sourcePointRight_two_pi]


-- @@ L293-296 verbatim
def sourceCurveRight : C(I, E) where
  toFun u := sourcePointRight m (2 * Real.pi * (u : ℝ))
  continuous_toFun := (continuous_sourcePointRight m).comp
    ((continuous_const.mul continuous_const).mul continuous_subtype_val)


-- @@ L298-301 verbatim
def sourceCurveLeft : C(I, E) where
  toFun u := sourcePointLeft m (2 * Real.pi * (u : ℝ))
  continuous_toFun := (continuous_sourcePointLeft m).comp
    ((continuous_const.mul continuous_const).mul continuous_subtype_val)


-- @@ L303-304 verbatim
@[simp] theorem sourceCurveRight_zero :
    sourceCurveRight m 0 = sourcePointRight m 0 := by simp [sourceCurveRight]


-- @@ L306-307 verbatim
@[simp] theorem sourceCurveLeft_zero :
    sourceCurveLeft m 0 = sourcePointLeft m 0 := by simp [sourceCurveLeft]


-- @@ L309-313 verbatim
theorem sourceCurveRight_closed : sourceCurveRight m 0 = sourceCurveRight m 1 := by
  rw [sourceCurveRight_zero]
  change sourcePointRight m 0 = sourcePointRight m (2 * Real.pi * (1 : ℝ))
  norm_num
  exact (sourcePointRight_two_pi m).symm


-- @@ L315-319 verbatim
theorem sourceCurveLeft_closed : sourceCurveLeft m 0 = sourceCurveLeft m 1 := by
  rw [sourceCurveLeft_zero]
  change sourcePointLeft m 0 = sourcePointLeft m (2 * Real.pi * (1 : ℝ))
  norm_num
  exact (sourcePointLeft_two_pi m).symm


-- @@ L321-355 verbatim
private theorem interval_eq_cases_of_angle_mod {u v : I} {z : ℤ}
    (huvZ : (v : ℝ) = (u : ℝ) + (z : ℝ)) :
    u = v ∨ (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) := by
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


-- @@ L357-366 verbatim
theorem sourceCurveRight_eq_cases {u v : I}
    (huv : sourceCurveRight m u = sourceCurveRight m v) :
    u = v ∨ (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) := by
  obtain ⟨z, hz⟩ := sourcePointRight_eq_iff_mod m huv
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have huvZ : (v : ℝ) = (u : ℝ) + (z : ℝ) := by
    change 2 * Real.pi * (v : ℝ) =
      2 * Real.pi * (u : ℝ) + (z : ℝ) * (2 * Real.pi) at hz
    nlinarith
  exact interval_eq_cases_of_angle_mod huvZ


-- @@ L368-377 verbatim
theorem sourceCurveLeft_eq_cases {u v : I}
    (huv : sourceCurveLeft m u = sourceCurveLeft m v) :
    u = v ∨ (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) := by
  obtain ⟨z, hz⟩ := sourcePointLeft_eq_iff_mod m huv
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have huvZ : (v : ℝ) = (u : ℝ) + (z : ℝ) := by
    change 2 * Real.pi * (v : ℝ) =
      2 * Real.pi * (u : ℝ) + (z : ℝ) * (2 * Real.pi) at hz
    nlinarith
  exact interval_eq_cases_of_angle_mod huvZ


-- @@ L379-382 verbatim
theorem sourcePointRight_mem_orbit (V : TamedField (sourceFLS m)) (theta : ℝ) :
    sourcePointRight m theta ∈ V.orbit (sourcePointRight m 0) := by
  exact V.continuousCurve_mem_orbit (sourcePointRight m)
    (continuous_sourcePointRight m) (sourcePointRight_mem_source_fiber m) theta


-- @@ L384-387 verbatim
theorem sourcePointLeft_mem_orbit (V : TamedField (sourceFLS m)) (theta : ℝ) :
    sourcePointLeft m theta ∈ V.orbit (sourcePointLeft m 0) := by
  exact V.continuousCurve_mem_orbit (sourcePointLeft m)
    (continuous_sourcePointLeft m) (sourcePointLeft_mem_source_fiber m) theta


-- @@ L389-397 verbatim
def sourceRightSimpleClosedOrbitParam (V : TamedField (sourceFLS m)) :
    SimpleClosedOrbitParam (sourceFLS m) V where
  p := sourcePointRight m 0
  hp := sourcePointRight_mem_source_fiber m 0
  curve := sourceCurveRight m
  curve_zero := sourceCurveRight_zero m
  curve_closed := sourceCurveRight_closed m
  curve_mem_orbit := fun _ => sourcePointRight_mem_orbit m V _
  curve_eq_cases := sourceCurveRight_eq_cases m


-- @@ L399-407 verbatim
def sourceLeftSimpleClosedOrbitParam (V : TamedField (sourceFLS m)) :
    SimpleClosedOrbitParam (sourceFLS m) V where
  p := sourcePointLeft m 0
  hp := sourcePointLeft_mem_source_fiber m 0
  curve := sourceCurveLeft m
  curve_zero := sourceCurveLeft_zero m
  curve_closed := sourceCurveLeft_closed m
  curve_mem_orbit := fun _ => sourcePointLeft_mem_orbit m V _
  curve_eq_cases := sourceCurveLeft_eq_cases m


-- @@ L409-409 verbatim
/-! ## The source fiber is exactly the two incoming ovals -/


-- @@ L411-417 verbatim
theorem source_planeFirst_ne_zero_of_mem_fiber {x : E}
    (hx : x ∈ (sourceFLS m).fiber) : x (planeFirst m) ≠ 0 := by
  intro hzero
  have hq := cassiniQ_eq_level_of_levelMap_eq_zero m hx
  rw [cassiniQ_eq_complex_square, hzero] at hq
  norm_num at hq
  nlinarith [sq_nonneg (x (planeSecond m))]


-- @@ L419-530 verbatim
theorem source_fiber_eq_range_union :
    (sourceFLS m).fiber =
      Set.range (sourcePointRight m) ∪ Set.range (sourcePointLeft m) := by
  ext x
  constructor
  · intro hx
    let a := x (planeFirst m)
    let b := x (planeSecond m)
    have ha0 : a ≠ 0 := source_planeFirst_ne_zero_of_mem_fiber m hx
    have hc0 : sourceScale ≠ 0 := sourceScale_pos.ne'
    have hq := cassiniQ_eq_level_of_levelMap_eq_zero m hx
    rw [cassiniQ_eq_complex_square] at hq
    have hsum :
        (a ^ 2 - b ^ 2 - 1) ^ 2 + (2 * a * b) ^ 2 = 1 / 2 := by
      dsimp [a, b]
      nlinarith
    have hunit :
        ((a ^ 2 - b ^ 2 - 1) / sourceScale) ^ 2 +
            ((2 * a * b) / sourceScale) ^ 2 = 1 := by
      calc
        ((a ^ 2 - b ^ 2 - 1) / sourceScale) ^ 2 +
              ((2 * a * b) / sourceScale) ^ 2 =
            ((a ^ 2 - b ^ 2 - 1) ^ 2 + (2 * a * b) ^ 2) /
              sourceScale ^ 2 := by field_simp [hc0]
        _ = (1 / 2 : ℝ) / (1 / 2 : ℝ) := by
          rw [hsum, sourceScale_sq]
        _ = 1 := by norm_num
    obtain ⟨theta, hcos, hsin⟩ :=
      StandardBirth.exists_angle_of_sq_add_sq_eq_one hunit
    have hfirst : sourceRadicandFirst theta = a ^ 2 - b ^ 2 := by
      unfold sourceRadicandFirst
      rw [hcos]
      field_simp [hc0]
      ring
    have hsecond : sourceRadicandSecond theta = 2 * a * b := by
      unfold sourceRadicandSecond
      rw [hsin]
      field_simp [hc0]
    have hnormSq :
        sourceRadicandNorm theta ^ 2 = (a ^ 2 + b ^ 2) ^ 2 := by
      rw [sourceRadicandNorm_sq, hfirst, hsecond]
      ring
    have habNonneg : 0 ≤ a ^ 2 + b ^ 2 := by positivity
    have hnorm : sourceRadicandNorm theta = a ^ 2 + b ^ 2 := by
      have hn := (sourceRadicandNorm_pos theta).le
      nlinarith
    have hrootSq := sourceRootFirst_sq theta
    rw [hnorm, hfirst] at hrootSq
    rcases lt_or_gt_of_ne ha0 with haNeg | haPos
    · right
      have hroot : sourceRootFirst theta = -a := by
        have hr := sourceRootFirst_pos theta
        nlinarith
      have hrootSecond : sourceRootSecond theta = -b := by
        have hmul := two_mul_sourceRootFirst_mul_sourceRootSecond theta
        rw [hsecond, hroot] at hmul
        nlinarith
      have hright : sourcePointRight m theta = -x := by
        apply (WithLp.equiv 2 _).injective
        funext i
        induction i using Fin.lastCases with
        | last =>
            change sourcePointRight m theta (planeSecond m) =
              (-x) (planeSecond m)
            rw [sourcePointRight_apply_planeSecond, hrootSecond]
            rfl
        | cast i =>
            induction i using Fin.lastCases with
            | last =>
                change sourcePointRight m theta (planeFirst m) =
                  (-x) (planeFirst m)
                rw [sourcePointRight_apply_planeFirst, hroot]
                rfl
            | cast j =>
                have hxj := transverse_eq_zero_of_levelMap_eq_zero m hx j
                change sourcePointRight m theta j.castSucc.castSucc =
                  (-x) j.castSucc.castSucc
                simp [sourcePointRight_apply_transverse, hxj]
      refine ⟨theta, ?_⟩
      simp [sourcePointLeft, hright]
    · left
      have hroot : sourceRootFirst theta = a := by
        have hr := sourceRootFirst_pos theta
        nlinarith
      have hrootSecond : sourceRootSecond theta = b := by
        have hmul := two_mul_sourceRootFirst_mul_sourceRootSecond theta
        rw [hsecond, hroot] at hmul
        nlinarith
      refine ⟨theta, ?_⟩
      apply (WithLp.equiv 2 _).injective
      funext i
      induction i using Fin.lastCases with
      | last =>
          change sourcePointRight m theta (planeSecond m) =
            x (planeSecond m)
          rw [sourcePointRight_apply_planeSecond, hrootSecond]
      | cast i =>
          induction i using Fin.lastCases with
          | last =>
              change sourcePointRight m theta (planeFirst m) =
                x (planeFirst m)
              rw [sourcePointRight_apply_planeFirst, hroot]
          | cast j =>
              have hxj := transverse_eq_zero_of_levelMap_eq_zero m hx j
              change sourcePointRight m theta j.castSucc.castSucc =
                x j.castSucc.castSucc
              rw [sourcePointRight_apply_transverse, hxj]
  · rintro (hx | hx)
    · rcases hx with ⟨theta, rfl⟩
      exact sourcePointRight_mem_source_fiber m theta
    · rcases hx with ⟨theta, rfl⟩
      exact sourcePointLeft_mem_source_fiber m theta


-- @@ L532-532 verbatim
/-! ## The two intrinsic source orbits -/


-- @@ L534-541 verbatim
/-- Auxiliary sign separating the right and left Cassini ovals.  This is only
used for component counting; the saddle cobordism itself retains its constant
positive `sourceSign`. -/
def sourceOvalSign : FiberSign (sourceFLS m) where
  toFun := fun x => x (planeFirst m)
  continuous :=
    (EuclideanSpace.proj (planeFirst m) : E →L[ℝ] ℝ).continuous
  nonzero := fun _ hx => source_planeFirst_ne_zero_of_mem_fiber m hx


-- @@ L543-546 verbatim
@[simp] theorem sourceOvalSign_apply_right (theta : ℝ) :
    sourceOvalSign m (sourcePointRight m theta) = sourceRootFirst theta := by
  change sourcePointRight m theta (planeFirst m) = sourceRootFirst theta
  exact sourcePointRight_apply_planeFirst m theta


-- @@ L548-551 verbatim
@[simp] theorem sourceOvalSign_apply_left (theta : ℝ) :
    sourceOvalSign m (sourcePointLeft m theta) = -sourceRootFirst theta := by
  change sourcePointLeft m theta (planeFirst m) = -sourceRootFirst theta
  exact sourcePointLeft_apply_planeFirst m theta


-- @@ L553-569 verbatim
theorem source_right_orbit_subset_range
    (V : TamedField (sourceFLS m)) :
    V.orbit (sourcePointRight m 0) ⊆ Set.range (sourcePointRight m) := by
  intro x hx
  have hp := sourcePointRight_mem_source_fiber m 0
  have hxfiber := V.orbit_subset_fiber hp hx
  have hbase : 0 < sourceOvalSign m (sourcePointRight m 0) := by
    simpa using sourceRootFirst_pos 0
  have hxpos : 0 < sourceOvalSign m x :=
    ((sourceOvalSign m).pos_iff_of_mem_orbit V hp hx).mp hbase
  rw [source_fiber_eq_range_union m] at hxfiber
  rcases hxfiber with hright | hleft
  · exact hright
  · rcases hleft with ⟨theta, rfl⟩
    have hr := sourceRootFirst_pos theta
    simp only [sourceOvalSign_apply_left] at hxpos
    nlinarith


-- @@ L571-588 verbatim
theorem source_left_orbit_subset_range
    (V : TamedField (sourceFLS m)) :
    V.orbit (sourcePointLeft m 0) ⊆ Set.range (sourcePointLeft m) := by
  intro x hx
  have hp := sourcePointLeft_mem_source_fiber m 0
  have hsign := (sourceOvalSign m).pos_iff_of_mem_orbit V hp hx
  have hbaseNot : ¬ 0 < sourceOvalSign m (sourcePointLeft m 0) := by
    have hr := sourceRootFirst_pos 0
    simp only [sourceOvalSign_apply_left]
    nlinarith
  have hxfiber := V.orbit_subset_fiber hp hx
  rw [source_fiber_eq_range_union m] at hxfiber
  rcases hxfiber with hright | hleft
  · rcases hright with ⟨theta, rfl⟩
    have hrightPos : 0 < sourceOvalSign m (sourcePointRight m theta) := by
      simpa using sourceRootFirst_pos theta
    exact False.elim (hbaseNot (hsign.mpr hrightPos))
  · exact hleft


-- @@ L590-595 verbatim
theorem source_right_orbit_eq_range (V : TamedField (sourceFLS m)) :
    V.orbit (sourcePointRight m 0) = Set.range (sourcePointRight m) := by
  apply Set.Subset.antisymm
  · exact source_right_orbit_subset_range m V
  · rintro x ⟨theta, rfl⟩
    exact sourcePointRight_mem_orbit m V theta


-- @@ L597-602 verbatim
theorem source_left_orbit_eq_range (V : TamedField (sourceFLS m)) :
    V.orbit (sourcePointLeft m 0) = Set.range (sourcePointLeft m) := by
  apply Set.Subset.antisymm
  · exact source_left_orbit_subset_range m V
  · rintro x ⟨theta, rfl⟩
    exact sourcePointLeft_mem_orbit m V theta


-- @@ L604-614 verbatim
theorem source_ranges_disjoint :
    Disjoint (Set.range (sourcePointRight m))
      (Set.range (sourcePointLeft m)) := by
  rw [Set.disjoint_left]
  rintro x ⟨theta, rfl⟩ ⟨phi, hphi⟩
  have hcoord := congrArg (fun y : E => y (planeFirst m)) hphi
  simp only [sourcePointLeft_apply_planeFirst,
    sourcePointRight_apply_planeFirst] at hcoord
  have htheta := sourceRootFirst_pos theta
  have hphiPos := sourceRootFirst_pos phi
  nlinarith


-- @@ L616-619 verbatim
/-- The intrinsic orbit index of the right incoming oval. -/
def sourceRightOrbitIndex (V : TamedField (sourceFLS m)) : V.OrbitIndex :=
  ⟨V.orbit (sourcePointRight m 0), V.mem_orbitFinset.mpr
    ⟨sourcePointRight m 0, sourcePointRight_mem_source_fiber m 0, rfl⟩⟩


-- @@ L621-624 verbatim
/-- The intrinsic orbit index of the left incoming oval. -/
def sourceLeftOrbitIndex (V : TamedField (sourceFLS m)) : V.OrbitIndex :=
  ⟨V.orbit (sourcePointLeft m 0), V.mem_orbitFinset.mpr
    ⟨sourcePointLeft m 0, sourcePointLeft_mem_source_fiber m 0, rfl⟩⟩


-- @@ L626-628 verbatim
@[simp] theorem sourceRightOrbitIndex_coe (V : TamedField (sourceFLS m)) :
    ((sourceRightOrbitIndex m V : V.OrbitIndex) : Set E) =
      V.orbit (sourcePointRight m 0) := rfl


-- @@ L630-632 verbatim
@[simp] theorem sourceLeftOrbitIndex_coe (V : TamedField (sourceFLS m)) :
    ((sourceLeftOrbitIndex m V : V.OrbitIndex) : Set E) =
      V.orbit (sourcePointLeft m 0) := rfl


-- @@ L634-648 verbatim
theorem sourceRightOrbitIndex_ne_sourceLeftOrbitIndex
    (V : TamedField (sourceFLS m)) :
    sourceRightOrbitIndex m V ≠ sourceLeftOrbitIndex m V := by
  intro hindex
  have hsets := congrArg (fun O : V.OrbitIndex => (O : Set E)) hindex
  change V.orbit (sourcePointRight m 0) =
    V.orbit (sourcePointLeft m 0) at hsets
  rw [source_right_orbit_eq_range m V,
    source_left_orbit_eq_range m V] at hsets
  have hright : sourcePointRight m 0 ∈ Set.range (sourcePointRight m) :=
    ⟨0, rfl⟩
  have hleft : sourcePointRight m 0 ∈ Set.range (sourcePointLeft m) := by
    rw [← hsets]
    exact hright
  exact Set.disjoint_left.mp (source_ranges_disjoint m) hright hleft


-- @@ L650-665 verbatim
theorem orbitIndex_eq_sourceRight_or_sourceLeft
    (V : TamedField (sourceFLS m)) (O : V.OrbitIndex) :
    O = sourceRightOrbitIndex m V ∨ O = sourceLeftOrbitIndex m V := by
  have hp := V.orbitPoint_mem_fiber O
  rw [source_fiber_eq_range_union m] at hp
  rcases hp with ⟨theta, htheta⟩ | ⟨theta, htheta⟩
  · left
    apply Subtype.ext
    change (O : Set E) = V.orbit (sourcePointRight m 0)
    rw [V.orbitPoint_orbit O, ← htheta]
    exact V.orbit_eq_of_mem (sourcePointRight_mem_orbit m V theta)
  · right
    apply Subtype.ext
    change (O : Set E) = V.orbit (sourcePointLeft m 0)
    rw [V.orbitPoint_orbit O, ← htheta]
    exact V.orbit_eq_of_mem (sourcePointLeft_mem_orbit m V theta)


-- @@ L667-667 verbatim
/-! ## Reduction of the source delta to the two explicit frame loops -/


-- @@ L669-683 verbatim
theorem source_framedDelta_eq_orbitContributions
    (V : TamedField (sourceFLS m)) :
    V.framedDelta =
      V.orbitContribution (sourceRightOrbitIndex m V) +
        V.orbitContribution (sourceLeftOrbitIndex m V) := by
  classical
  unfold TamedField.framedDelta
  have huniv : (Finset.univ : Finset V.OrbitIndex) =
      {sourceRightOrbitIndex m V, sourceLeftOrbitIndex m V} := by
    ext O
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_iff]
    exact orbitIndex_eq_sourceRight_or_sourceLeft m V O
  rw [huniv]
  simp [sourceRightOrbitIndex_ne_sourceLeftOrbitIndex m V]


-- @@ L685-690 verbatim
theorem sourceRight_paramFrameClass_eq_fundamental
    (V : TamedField (sourceFLS m)) :
    loopClassZ2 (sourceRightSimpleClosedOrbitParam m V).paramFrameLoop
        (sourceRightSimpleClosedOrbitParam m V).paramFrameLoop_closed =
      V.fundamentalFrameClass (sourcePointRight_mem_source_fiber m 0) :=
  (sourceRightSimpleClosedOrbitParam m V).paramFrameClass_eq_fundamental


-- @@ L692-697 verbatim
theorem sourceLeft_paramFrameClass_eq_fundamental
    (V : TamedField (sourceFLS m)) :
    loopClassZ2 (sourceLeftSimpleClosedOrbitParam m V).paramFrameLoop
        (sourceLeftSimpleClosedOrbitParam m V).paramFrameLoop_closed =
      V.fundamentalFrameClass (sourcePointLeft_mem_source_fiber m 0) :=
  (sourceLeftSimpleClosedOrbitParam m V).paramFrameClass_eq_fundamental


-- @@ L699-717 verbatim
theorem sourceRight_orbitContribution_eq_paramFrameClass_add_one
    (V : TamedField (sourceFLS m)) :
    V.orbitContribution (sourceRightOrbitIndex m V) =
      loopClassZ2 (sourceRightSimpleClosedOrbitParam m V).paramFrameLoop
        (sourceRightSimpleClosedOrbitParam m V).paramFrameLoop_closed + 1 := by
  unfold TamedField.orbitContribution TamedField.orbitFrameClass
  have hpoint : V.orbitPoint (sourceRightOrbitIndex m V) ∈
      V.orbit (sourcePointRight m 0) := by
    rw [← sourceRightOrbitIndex_coe m V, V.orbitPoint_orbit]
    exact V.mem_orbit_self _
  have hbase :
      V.fundamentalFrameClass
          (V.orbitPoint_mem_fiber (sourceRightOrbitIndex m V)) =
        V.fundamentalFrameClass (sourcePointRight_mem_source_fiber m 0) :=
    V.fundamentalFrameClass_eq_of_mem_orbit
      (sourcePointRight_mem_source_fiber m 0) hpoint
  change V.fundamentalFrameClass
      (V.orbitPoint_mem_fiber (sourceRightOrbitIndex m V)) + 1 = _
  rw [hbase, ← sourceRight_paramFrameClass_eq_fundamental m V]


-- @@ L719-737 verbatim
theorem sourceLeft_orbitContribution_eq_paramFrameClass_add_one
    (V : TamedField (sourceFLS m)) :
    V.orbitContribution (sourceLeftOrbitIndex m V) =
      loopClassZ2 (sourceLeftSimpleClosedOrbitParam m V).paramFrameLoop
        (sourceLeftSimpleClosedOrbitParam m V).paramFrameLoop_closed + 1 := by
  unfold TamedField.orbitContribution TamedField.orbitFrameClass
  have hpoint : V.orbitPoint (sourceLeftOrbitIndex m V) ∈
      V.orbit (sourcePointLeft m 0) := by
    rw [← sourceLeftOrbitIndex_coe m V, V.orbitPoint_orbit]
    exact V.mem_orbit_self _
  have hbase :
      V.fundamentalFrameClass
          (V.orbitPoint_mem_fiber (sourceLeftOrbitIndex m V)) =
        V.fundamentalFrameClass (sourcePointLeft_mem_source_fiber m 0) :=
    V.fundamentalFrameClass_eq_of_mem_orbit
      (sourcePointLeft_mem_source_fiber m 0) hpoint
  change V.fundamentalFrameClass
      (V.orbitPoint_mem_fiber (sourceLeftOrbitIndex m V)) + 1 = _
  rw [hbase, ← sourceLeft_paramFrameClass_eq_fundamental m V]


-- @@ L739-760 verbatim
theorem source_framedDelta_eq_paramFrameClass_sum
    (V : TamedField (sourceFLS m)) :
    V.framedDelta =
      loopClassZ2 (sourceRightSimpleClosedOrbitParam m V).paramFrameLoop
          (sourceRightSimpleClosedOrbitParam m V).paramFrameLoop_closed +
        loopClassZ2 (sourceLeftSimpleClosedOrbitParam m V).paramFrameLoop
          (sourceLeftSimpleClosedOrbitParam m V).paramFrameLoop_closed := by
  rw [source_framedDelta_eq_orbitContributions,
    sourceRight_orbitContribution_eq_paramFrameClass_add_one,
    sourceLeft_orbitContribution_eq_paramFrameClass_add_one]
  let betaRight : ZMod 2 :=
    loopClassZ2 (sourceRightSimpleClosedOrbitParam m V).paramFrameLoop
      (sourceRightSimpleClosedOrbitParam m V).paramFrameLoop_closed
  let betaLeft : ZMod 2 :=
    loopClassZ2 (sourceLeftSimpleClosedOrbitParam m V).paramFrameLoop
      (sourceLeftSimpleClosedOrbitParam m V).paramFrameLoop_closed
  change (betaRight + 1) + (betaLeft + 1) = betaRight + betaLeft
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  calc
    (betaRight + 1) + (betaLeft + 1) =
        betaRight + betaLeft + (1 + 1) := by abel
    _ = betaRight + betaLeft := by rw [h11, add_zero]


-- @@ L762-776 verbatim
theorem sourceSign_positiveFramedDelta_eq_framedDelta
    (V : TamedField (sourceFLS m)) :
    (sourceSign m).positiveFramedDelta V = V.framedDelta := by
  classical
  unfold FiberSign.positiveFramedDelta TamedField.deltaOn TamedField.framedDelta
  apply Finset.sum_congr rfl
  intro O _
  have hselected : (O : Set E) ∈
      (sourceSign m).positiveOrbitCollection V := by
    intro x hx
    refine ⟨?_, ?_⟩
    · rw [V.orbitPoint_orbit O] at hx
      exact V.orbit_subset_fiber (V.orbitPoint_mem_fiber O) hx
    · simp [sourceSign]
  simp [hselected]


-- @@ L778-787 verbatim
theorem sourceSign_positiveDelta_eq_paramFrameClass_sum
    (V : TamedField (sourceFLS m)) :
    (sourceSign m).positiveDelta =
      loopClassZ2 (sourceRightSimpleClosedOrbitParam m V).paramFrameLoop
          (sourceRightSimpleClosedOrbitParam m V).paramFrameLoop_closed +
        loopClassZ2 (sourceLeftSimpleClosedOrbitParam m V).paramFrameLoop
          (sourceLeftSimpleClosedOrbitParam m V).paramFrameLoop_closed := by
  rw [(sourceSign m).positiveDelta_eq V,
    sourceSign_positiveFramedDelta_eq_framedDelta,
    source_framedDelta_eq_paramFrameClass_sum]


-- @@ L789-805 verbatim
/-- Pointwise reduction of the intrinsic right incoming frame loop to the
explicit source Cassini Gram--Schmidt frame. -/
theorem sourceRight_paramFrameLoop_apply
    (V : TamedField (sourceFLS m)) (u : I) :
    ((sourceRightSimpleClosedOrbitParam m V).paramFrameLoop u :
        Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ) =
      rowsMatrix (endpointUnitFrame m (-1 / 2)
        (sourcePointRight m (2 * Real.pi * (u : ℝ)))) := by
  change frameLoop (sourceFLS m)
      (sourceRightSimpleClosedOrbitParam m V).realCurve (u : ℝ) = _
  unfold frameLoop
  rw [(sourceRightSimpleClosedOrbitParam m V).realCurve_coe]
  change rowsMatrix (gramSchmidtNormed ℝ
      (frameAt (sourceFLS m)
        (sourcePointRight m (2 * Real.pi * (u : ℝ))))) = _
  rw [gramSchmidtNormed_frameAt_source m
    (sourcePointRight_mem_source_fiber m _)]


-- @@ L807-822 verbatim
/-- Pointwise reduction of the intrinsic left incoming frame loop. -/
theorem sourceLeft_paramFrameLoop_apply
    (V : TamedField (sourceFLS m)) (u : I) :
    ((sourceLeftSimpleClosedOrbitParam m V).paramFrameLoop u :
        Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ) =
      rowsMatrix (endpointUnitFrame m (-1 / 2)
        (sourcePointLeft m (2 * Real.pi * (u : ℝ)))) := by
  change frameLoop (sourceFLS m)
      (sourceLeftSimpleClosedOrbitParam m V).realCurve (u : ℝ) = _
  unfold frameLoop
  rw [(sourceLeftSimpleClosedOrbitParam m V).realCurve_coe]
  change rowsMatrix (gramSchmidtNormed ℝ
      (frameAt (sourceFLS m)
        (sourcePointLeft m (2 * Real.pi * (u : ℝ))))) = _
  rw [gramSchmidtNormed_frameAt_source m
    (sourcePointLeft_mem_source_fiber m _)]


-- @@ L824-824 verbatim
end StandardSaddle

-- @@ L825-825 verbatim
end Submission
