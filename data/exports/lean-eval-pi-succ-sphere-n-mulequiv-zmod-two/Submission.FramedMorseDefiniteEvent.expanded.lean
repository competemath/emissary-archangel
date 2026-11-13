import Mathlib
import Submission.FramedMorseEventExcision
import Submission.ExplicitOrbitParam


-- @@ L5-19 verbatim
/-!
# Installed definite Morse circles

The saddle event has four boundary ends.  A definite event is simpler: on its
nonempty side the local zero set is one complete circle.  This file transports
that literal circle through the installed Morse chart and proves the concrete
facts needed by framed excision:

* every point lies in the actual installed zero fiber;
* the circle lies in the expected regular slice;
* the whole parametrized circle belongs to one actual flow-orbit component;
* both the minimum and maximum time orientations are covered.

No local-model comparison or delta equality is assumed here.
-/


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
open Set Function Metric

-- @@ L24-24 verbatim
open scoped RealInnerProductSpace ContDiff Topology unitInterval


-- @@ L26-26 verbatim
namespace Submission


-- @@ L28-28 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)


-- @@ L30-30 verbatim
/-! ## The definite circle in Morse parameter space -/


-- @@ L32-34 verbatim
/-- Radius-`a` circle in the two-dimensional Morse parameter plane. -/
def definiteCircleParam (a theta : ℝ) : E₂ :=
  pairToMorseParam (a * Real.cos theta, a * Real.sin theta)


-- @@ L36-38 verbatim
@[simp] theorem definiteCircleParam_apply_zero (a theta : ℝ) :
    definiteCircleParam a theta 0 = a * Real.cos theta := by
  simp [definiteCircleParam]


-- @@ L40-42 verbatim
@[simp] theorem definiteCircleParam_apply_one (a theta : ℝ) :
    definiteCircleParam a theta 1 = a * Real.sin theta := by
  simp [definiteCircleParam]


-- @@ L44-51 verbatim
theorem norm_definiteCircleParam_sq (a theta : ℝ) :
    ‖definiteCircleParam a theta‖ ^ 2 = a ^ 2 := by
  rw [definiteCircleParam, norm_pairToMorseParam_sq]
  change (a * Real.cos theta) ^ 2 + (a * Real.sin theta) ^ 2 = a ^ 2
  calc
    (a * Real.cos theta) ^ 2 + (a * Real.sin theta) ^ 2 =
        a ^ 2 * (Real.sin theta ^ 2 + Real.cos theta ^ 2) := by ring
    _ = a ^ 2 := by rw [Real.sin_sq_add_cos_sq, mul_one]


-- @@ L53-56 verbatim
theorem norm_definiteCircleParam {a theta : ℝ} (ha : 0 ≤ a) :
    ‖definiteCircleParam a theta‖ = a := by
  have hsq := norm_definiteCircleParam_sq a theta
  nlinarith [norm_nonneg (definiteCircleParam a theta)]


-- @@ L58-65 verbatim
theorem definiteCircleParam_ne_zero {a theta : ℝ} (ha : a ≠ 0) :
    definiteCircleParam a theta ≠ 0 := by
  intro hzero
  have hsq := norm_definiteCircleParam_sq a theta
  rw [hzero, norm_zero] at hsq
  have ha2 : a ^ 2 = 0 := by nlinarith
  have haa : a * a = 0 := by simpa [pow_two] using ha2
  exact ha (mul_self_eq_zero.mp haa)


-- @@ L67-69 verbatim
/-- Counterclockwise angular tangent to the radius-`a` parameter circle. -/
def definiteCircleTangentParam (a theta : ℝ) : E₂ :=
  pairToMorseParam (-(a * Real.sin theta), a * Real.cos theta)


-- @@ L71-73 verbatim
@[simp] theorem definiteCircleTangentParam_apply_zero (a theta : ℝ) :
    definiteCircleTangentParam a theta 0 = -(a * Real.sin theta) := by
  simp [definiteCircleTangentParam]


-- @@ L75-77 verbatim
@[simp] theorem definiteCircleTangentParam_apply_one (a theta : ℝ) :
    definiteCircleTangentParam a theta 1 = a * Real.cos theta := by
  simp [definiteCircleTangentParam]


-- @@ L79-86 verbatim
/-- The minimum model uses the counterclockwise angular tangent. -/
theorem morseLevelTangent_minimum_definiteCircleParam (a theta : ℝ) :
    morseLevelTangent .minimum (definiteCircleParam a theta) =
      definiteCircleTangentParam a theta := by
  ext i
  fin_cases i <;>
    simp [morseLevelTangent, definiteCircleParam,
      definiteCircleTangentParam, pairToMorseParam]


-- @@ L88-95 verbatim
/-- The maximum model carries the opposite angular orientation. -/
theorem morseLevelTangent_maximum_definiteCircleParam (a theta : ℝ) :
    morseLevelTangent .maximum (definiteCircleParam a theta) =
      -definiteCircleTangentParam a theta := by
  ext i
  fin_cases i <;>
    simp [morseLevelTangent, definiteCircleParam,
      definiteCircleTangentParam, pairToMorseParam]


-- @@ L97-106 verbatim
theorem morseQuadratic_minimum_definiteCircleParam (a theta : ℝ) :
    morseQuadratic .minimum
        (definiteCircleParam a theta 0, definiteCircleParam a theta 1) =
      a ^ 2 := by
  simp only [morseQuadratic, definiteCircleParam_apply_zero,
    definiteCircleParam_apply_one]
  calc
    (a * Real.cos theta) ^ 2 + (a * Real.sin theta) ^ 2 =
        a ^ 2 * (Real.sin theta ^ 2 + Real.cos theta ^ 2) := by ring
    _ = a ^ 2 := by rw [Real.sin_sq_add_cos_sq, mul_one]


-- @@ L108-120 verbatim
theorem morseQuadratic_maximum_definiteCircleParam (a theta : ℝ) :
    morseQuadratic .maximum
        (definiteCircleParam a theta 0, definiteCircleParam a theta 1) =
      -(a ^ 2) := by
  simp only [morseQuadratic, definiteCircleParam_apply_zero,
    definiteCircleParam_apply_one]
  rw [show -(a * Real.cos theta) ^ 2 - (a * Real.sin theta) ^ 2 =
      -((a * Real.cos theta) ^ 2 + (a * Real.sin theta) ^ 2) by ring]
  rw [show (a * Real.cos theta) ^ 2 + (a * Real.sin theta) ^ 2 = a ^ 2 by
    calc
      (a * Real.cos theta) ^ 2 + (a * Real.sin theta) ^ 2 =
          a ^ 2 * (Real.sin theta ^ 2 + Real.cos theta ^ 2) := by ring
      _ = a ^ 2 := by rw [Real.sin_sq_add_cos_sq, mul_one]]


-- @@ L122-127 verbatim
/-- Once-around parametrization of the definite parameter circle. -/
def definiteCircleParamCurve (a : ℝ) : C(I, E₂) where
  toFun u := definiteCircleParam a (2 * Real.pi * (u : ℝ))
  continuous_toFun := by
    unfold definiteCircleParam pairToMorseParam
    fun_prop


-- @@ L129-131 verbatim
@[simp] theorem definiteCircleParamCurve_zero (a : ℝ) :
    definiteCircleParamCurve a 0 = definiteCircleParam a 0 := by
  simp [definiteCircleParamCurve]


-- @@ L133-138 verbatim
theorem definiteCircleParamCurve_closed (a : ℝ) :
    definiteCircleParamCurve a 0 = definiteCircleParamCurve a 1 := by
  ext i
  fin_cases i <;>
    simp [definiteCircleParamCurve, definiteCircleParam,
      Real.cos_two_pi, Real.sin_two_pi]


-- @@ L140-155 verbatim
/-- Equality on a nonzero parameter circle is equality of angles modulo one
full turn. -/
theorem definiteCircleParam_eq_iff_mod {a theta theta' : ℝ} (ha : a ≠ 0)
    (h : definiteCircleParam a theta = definiteCircleParam a theta') :
    ∃ z : ℤ, theta' = theta + (z : ℝ) * (2 * Real.pi) := by
  have hcos : Real.cos theta = Real.cos theta' := by
    apply mul_left_cancel₀ ha
    simpa using congrArg (fun x : E₂ => x 0) h
  have hsin : Real.sin theta = Real.sin theta' := by
    apply mul_left_cancel₀ ha
    simpa using congrArg (fun x : E₂ => x 1) h
  have hone : Real.cos (theta' - theta) = 1 := by
    rw [Real.cos_sub, ← hcos, ← hsin]
    linear_combination Real.sin_sq_add_cos_sq theta
  obtain ⟨z, hz⟩ := (Real.cos_eq_one_iff _).mp hone
  exact ⟨z, by linarith⟩


-- @@ L157-201 verbatim
/-- The once-around definite circle is injective except for its identified
endpoints. -/
theorem definiteCircleParamCurve_eq_cases {a : ℝ} (ha : a ≠ 0) {u v : I}
    (huv : definiteCircleParamCurve a u = definiteCircleParamCurve a v) :
    u = v ∨ (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) := by
  change definiteCircleParam a (2 * Real.pi * (u : ℝ)) =
    definiteCircleParam a (2 * Real.pi * (v : ℝ)) at huv
  obtain ⟨z, hz⟩ := definiteCircleParam_eq_iff_mod ha huv
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


-- @@ L203-203 verbatim
/-! ## An orbit index canonically attached to a simple closed parameter -/


-- @@ L205-205 verbatim
namespace SimpleClosedOrbitParam


-- @@ L207-207 verbatim
variable {n : ℕ} {X : FramedLevelSet n} {V : TamedField X}


-- @@ L209-211 verbatim
/-- The intrinsic component traversed by a simple closed orbit parameter. -/
def orbitIndex (P : SimpleClosedOrbitParam X V) : V.OrbitIndex :=
  ⟨V.orbit P.p, V.mem_orbitFinset.mpr ⟨P.p, P.hp, rfl⟩⟩


-- @@ L213-217 verbatim
theorem orbitPoint_mem_param_orbit (P : SimpleClosedOrbitParam X V) :
    V.orbitPoint P.orbitIndex ∈ V.orbit P.p := by
  change V.orbitPoint P.orbitIndex ∈ (P.orbitIndex : Set _)
  rw [V.orbitPoint_orbit]
  exact V.mem_orbit_self _


-- @@ L219-233 verbatim
/-- Reading the frame along a simple closed parameter computes the actual
`orbitFrameClass` of the component it traverses. -/
theorem orbitFrameClass_eq_paramFrameClass
    (P : SimpleClosedOrbitParam X V) :
    V.orbitFrameClass P.orbitIndex =
      loopClassZ2 P.paramFrameLoop P.paramFrameLoop_closed := by
  calc
    V.orbitFrameClass P.orbitIndex =
        V.fundamentalFrameClass
          (V.orbitPoint_mem_fiber P.orbitIndex) := rfl
    _ = V.fundamentalFrameClass P.hp :=
      V.fundamentalFrameClass_eq_of_mem_orbit P.hp
        P.orbitPoint_mem_param_orbit
    _ = loopClassZ2 P.paramFrameLoop P.paramFrameLoop_closed :=
      P.paramFrameClass_eq_fundamental.symm


-- @@ L235-235 verbatim
end SimpleClosedOrbitParam


-- @@ L237-237 verbatim
/-! ## Transport through an installed definite event -/


-- @@ L239-239 verbatim
namespace ExactFiniteMorseJetInstallation


-- @@ L241-241 verbatim
variable {n : ℕ}

-- @@ L242-242 verbatim
variable {C : FramedLevelCobordism n} {ι : Type*} [Fintype ι]

-- @@ L243-243 verbatim
variable {B : FiniteIFTSurfaceCover C ι}

-- @@ L244-244 verbatim
variable {G : GenericFiniteIFTSurfaceAtlas B.toSurfaceChartFamily}


-- @@ L246-246 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L247-247 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L249-253 verbatim
/-- The installed image of the definite parameter circle. -/
def criticalDefiniteCircle (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (a theta : ℝ) : E' :=
  R.criticalSurfaceParam p hp (definiteCircleParam a theta)


-- @@ L255-264 verbatim
theorem criticalDefiniteCircle_fiber
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    {a theta : ℝ} (ha : 0 ≤ a)
    (hrad : a < (R.criticalModelShrink p hp).radius) :
    (R.amplitude.toVerticalAmplitude.pullback C).G
      (R.criticalDefiniteCircle p hp a theta) = 0 := by
  apply R.criticalSurfaceParam_fiber p hp
  rw [norm_definiteCircleParam ha]
  exact hrad


-- @@ L266-277 verbatim
theorem criticalDefiniteCircle_regular
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    {a theta : ℝ} (ha : 0 < a)
    (hrad : a < (R.criticalModelShrink p hp).radius) :
    Surjective
      (spatialDeriv (R.amplitude.toVerticalAmplitude.pullback C).G
        (R.criticalDefiniteCircle p hp a theta)) := by
  apply R.criticalSurfaceParam_spatialDeriv_surjective_of_ne_zero p hp
  · rw [norm_definiteCircleParam ha.le]
    exact hrad
  · exact definiteCircleParam_ne_zero ha.ne'


-- @@ L279-312 verbatim
/-- One radius works simultaneously around an installed minimum: at every
point of every smaller definite circle, the transported counterclockwise
model tangent is a nonzero scalar multiple of the actual oriented slice
tangent.  This is the pointwise framing input for the birth loop. -/
theorem exists_radius_for_actual_minimum_circle_tangent_comparison
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum) :
    ∃ r > 0, r ≤ (R.criticalModelShrink p hp).radius ∧
      ∀ (a theta : ℝ), 0 < a → a < r →
        ∃ c : ℝ, c ≠ 0 ∧
          c • tauField
              (sliceMap (R.amplitude.toVerticalAmplitude.pullback C).G
                (tcoord (R.criticalDefiniteCircle p hp a theta)))
              (spacePart (R.criticalDefiniteCircle p hp a theta)) =
            spacePart (fderiv ℝ (R.criticalSurfaceParam p hp)
              (definiteCircleParam a theta)
              (definiteCircleTangentParam a theta)) := by
  obtain ⟨r, hr, hrle, hcompare⟩ :=
    R.exists_radius_for_actual_morse_tangent_comparison p hp
  refine ⟨r, hr, hrle, ?_⟩
  intro a theta ha har
  have hu : ‖definiteCircleParam a theta‖ < r := by
    rw [norm_definiteCircleParam ha.le]
    exact har
  have hquad : morseQuadratic (G.localMorseNormalForm p hp).index
      ((definiteCircleParam a theta) 0,
        (definiteCircleParam a theta) 1) ≠ 0 := by
    rw [hindex, morseQuadratic_minimum_definiteCircleParam]
    exact pow_ne_zero 2 ha.ne'
  obtain ⟨c, hc, hctau⟩ := hcompare _ hu hquad
  refine ⟨c, hc, ?_⟩
  simpa [criticalDefiniteCircle, hindex,
    morseLevelTangent_minimum_definiteCircleParam] using hctau


-- @@ L314-345 verbatim
/-- The corresponding uniform comparison at an installed maximum.  Its
canonical Morse tangent is clockwise, hence the explicit minus sign. -/
theorem exists_radius_for_actual_maximum_circle_tangent_comparison
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum) :
    ∃ r > 0, r ≤ (R.criticalModelShrink p hp).radius ∧
      ∀ (a theta : ℝ), 0 < a → a < r →
        ∃ c : ℝ, c ≠ 0 ∧
          c • tauField
              (sliceMap (R.amplitude.toVerticalAmplitude.pullback C).G
                (tcoord (R.criticalDefiniteCircle p hp a theta)))
              (spacePart (R.criticalDefiniteCircle p hp a theta)) =
            spacePart (fderiv ℝ (R.criticalSurfaceParam p hp)
              (definiteCircleParam a theta)
              (-definiteCircleTangentParam a theta)) := by
  obtain ⟨r, hr, hrle, hcompare⟩ :=
    R.exists_radius_for_actual_morse_tangent_comparison p hp
  refine ⟨r, hr, hrle, ?_⟩
  intro a theta ha har
  have hu : ‖definiteCircleParam a theta‖ < r := by
    rw [norm_definiteCircleParam ha.le]
    exact har
  have hquad : morseQuadratic (G.localMorseNormalForm p hp).index
      ((definiteCircleParam a theta) 0,
        (definiteCircleParam a theta) 1) ≠ 0 := by
    rw [hindex, morseQuadratic_maximum_definiteCircleParam]
    exact neg_ne_zero.mpr (pow_ne_zero 2 ha.ne')
  obtain ⟨c, hc, hctau⟩ := hcompare _ hu hquad
  refine ⟨c, hc, ?_⟩
  simpa [criticalDefiniteCircle, hindex,
    morseLevelTangent_maximum_definiteCircleParam] using hctau


-- @@ L347-360 verbatim
/-- At a minimum, the born circle is on the slice just above the event. -/
theorem criticalMinimumCircle_time
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum)
    {a theta : ℝ} (ha : 0 ≤ a)
    (hrad : a < (R.criticalModelShrink p hp).radius) :
    tcoord (R.criticalDefiniteCircle p hp a theta) =
      G.localSeparatedTime p p.2 + a ^ 2 := by
  rw [criticalDefiniteCircle,
    R.criticalSurfaceParam_time p hp _ (by
      rw [norm_definiteCircleParam ha]
      exact hrad), hindex,
    morseQuadratic_minimum_definiteCircleParam]


-- @@ L362-376 verbatim
/-- At a maximum, the dying circle is on the slice just below the event. -/
theorem criticalMaximumCircle_time
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum)
    {a theta : ℝ} (ha : 0 ≤ a)
    (hrad : a < (R.criticalModelShrink p hp).radius) :
    tcoord (R.criticalDefiniteCircle p hp a theta) =
      G.localSeparatedTime p p.2 - a ^ 2 := by
  rw [criticalDefiniteCircle,
    R.criticalSurfaceParam_time p hp _ (by
      rw [norm_definiteCircleParam ha]
      exact hrad), hindex,
    morseQuadratic_maximum_definiteCircleParam]
  ring


-- @@ L378-392 verbatim
/-- The complete installed definite circle as a continuous loop. -/
def criticalDefiniteCircleCurve
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (a : ℝ) (ha : 0 < a)
    (hrad : a < (R.criticalModelShrink p hp).radius) : C(I, E') where
  toFun u := R.criticalSurfaceParam p hp (definiteCircleParamCurve a u)
  continuous_toFun := by
    rw [continuous_iff_continuousAt]
    intro u
    apply (R.criticalSurfaceParam_differentiableAt p hp _ ?_).continuousAt.comp'
      (definiteCircleParamCurve a).continuous.continuousAt
    change ‖definiteCircleParam a (2 * Real.pi * (u : ℝ))‖ < _
    rw [norm_definiteCircleParam ha.le]
    exact hrad


-- @@ L394-402 verbatim
/-- Spatial projection of the installed definite circle. -/
def criticalDefiniteSpatialCircle
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (a : ℝ) (ha : 0 < a)
    (hrad : a < (R.criticalModelShrink p hp).radius) : C(I, E₁) where
  toFun u := spacePart (R.criticalDefiniteCircleCurve p hp a ha hrad u)
  continuous_toFun := continuous_spacePart.comp
    (R.criticalDefiniteCircleCurve p hp a ha hrad).continuous


-- @@ L404-413 verbatim
theorem criticalDefiniteCircleCurve_closed
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (a : ℝ) (ha : 0 < a)
    (hrad : a < (R.criticalModelShrink p hp).radius) :
    R.criticalDefiniteCircleCurve p hp a ha hrad 0 =
      R.criticalDefiniteCircleCurve p hp a ha hrad 1 := by
  change R.criticalSurfaceParam p hp (definiteCircleParamCurve a 0) =
    R.criticalSurfaceParam p hp (definiteCircleParamCurve a 1)
  rw [definiteCircleParamCurve_closed]


-- @@ L415-461 verbatim
/-- Injectivity of the installed surface chart upgrades to simple closedness
of a minimum circle after spatial projection: equal spatial points have equal
time automatically, so the ambient chart can be cancelled. -/
theorem criticalMinimumSpatialCircle_eq_cases
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum)
    {r a : ℝ} (ha : 0 < a)
    (hrad : a < (R.criticalModelShrink p hp).radius) (har : a < r)
    (hinj : Set.InjOn (R.criticalSurfaceParam p hp) (Metric.ball 0 r))
    {u v : I}
    (huv : R.criticalDefiniteSpatialCircle p hp a ha hrad u =
      R.criticalDefiniteSpatialCircle p hp a ha hrad v) :
    u = v ∨ (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) := by
  let thetaU : ℝ := 2 * Real.pi * (u : ℝ)
  let thetaV : ℝ := 2 * Real.pi * (v : ℝ)
  change spacePart (R.criticalDefiniteCircle p hp a thetaU) =
    spacePart (R.criticalDefiniteCircle p hp a thetaV) at huv
  have htimeU := R.criticalMinimumCircle_time p hp hindex
    (theta := thetaU) ha.le hrad
  have htimeV := R.criticalMinimumCircle_time p hp hindex
    (theta := thetaV) ha.le hrad
  have hamb : R.criticalDefiniteCircle p hp a thetaU =
      R.criticalDefiniteCircle p hp a thetaV := by
    calc
      R.criticalDefiniteCircle p hp a thetaU =
          cobSpaceTime
            (spacePart (R.criticalDefiniteCircle p hp a thetaU))
            (tcoord (R.criticalDefiniteCircle p hp a thetaU)) :=
        (spaceTime_spacePart _).symm
      _ = cobSpaceTime
            (spacePart (R.criticalDefiniteCircle p hp a thetaV))
            (tcoord (R.criticalDefiniteCircle p hp a thetaV)) := by
        rw [huv, htimeU, htimeV]
      _ = R.criticalDefiniteCircle p hp a thetaV :=
        spaceTime_spacePart _
  have hmemU : definiteCircleParam a thetaU ∈ Metric.ball (0 : E₂) r := by
    rw [Metric.mem_ball, dist_zero_right, norm_definiteCircleParam ha.le]
    exact har
  have hmemV : definiteCircleParam a thetaV ∈ Metric.ball (0 : E₂) r := by
    rw [Metric.mem_ball, dist_zero_right, norm_definiteCircleParam ha.le]
    exact har
  have hparam : definiteCircleParam a thetaU =
      definiteCircleParam a thetaV := by
    exact hinj hmemU hmemV hamb
  apply definiteCircleParamCurve_eq_cases ha.ne'
  exact hparam


-- @@ L463-507 verbatim
/-- The same simple-closedness statement for a maximum circle. -/
theorem criticalMaximumSpatialCircle_eq_cases
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum)
    {r a : ℝ} (ha : 0 < a)
    (hrad : a < (R.criticalModelShrink p hp).radius) (har : a < r)
    (hinj : Set.InjOn (R.criticalSurfaceParam p hp) (Metric.ball 0 r))
    {u v : I}
    (huv : R.criticalDefiniteSpatialCircle p hp a ha hrad u =
      R.criticalDefiniteSpatialCircle p hp a ha hrad v) :
    u = v ∨ (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) := by
  let thetaU : ℝ := 2 * Real.pi * (u : ℝ)
  let thetaV : ℝ := 2 * Real.pi * (v : ℝ)
  change spacePart (R.criticalDefiniteCircle p hp a thetaU) =
    spacePart (R.criticalDefiniteCircle p hp a thetaV) at huv
  have htimeU := R.criticalMaximumCircle_time p hp hindex
    (theta := thetaU) ha.le hrad
  have htimeV := R.criticalMaximumCircle_time p hp hindex
    (theta := thetaV) ha.le hrad
  have hamb : R.criticalDefiniteCircle p hp a thetaU =
      R.criticalDefiniteCircle p hp a thetaV := by
    calc
      R.criticalDefiniteCircle p hp a thetaU =
          cobSpaceTime
            (spacePart (R.criticalDefiniteCircle p hp a thetaU))
            (tcoord (R.criticalDefiniteCircle p hp a thetaU)) :=
        (spaceTime_spacePart _).symm
      _ = cobSpaceTime
            (spacePart (R.criticalDefiniteCircle p hp a thetaV))
            (tcoord (R.criticalDefiniteCircle p hp a thetaV)) := by
        rw [huv, htimeU, htimeV]
      _ = R.criticalDefiniteCircle p hp a thetaV :=
        spaceTime_spacePart _
  have hmemU : definiteCircleParam a thetaU ∈ Metric.ball (0 : E₂) r := by
    rw [Metric.mem_ball, dist_zero_right, norm_definiteCircleParam ha.le]
    exact har
  have hmemV : definiteCircleParam a thetaV ∈ Metric.ball (0 : E₂) r := by
    rw [Metric.mem_ball, dist_zero_right, norm_definiteCircleParam ha.le]
    exact har
  have hparam : definiteCircleParam a thetaU =
      definiteCircleParam a thetaV := by
    exact hinj hmemU hmemV hamb
  apply definiteCircleParamCurve_eq_cases ha.ne'
  exact hparam


-- @@ L509-518 verbatim
/-- The actual regular slice on the nonempty side of a minimum. -/
def criticalMinimumPositiveSlice
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (_hp : p ∈ G.criticalPoints) (a : ℝ)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (G.localSeparatedTime p p.2 + a ^ 2)) : FramedLevelSet n :=
  SlabTamedField.sliceFLSAt
    (R.amplitude.toVerticalAmplitude.pullback C).toLevelCobordismData
    (G.localSeparatedTime p p.2 + a ^ 2) hreg


-- @@ L520-529 verbatim
/-- The actual regular slice on the nonempty side of a maximum. -/
def criticalMaximumNegativeSlice
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (_hp : p ∈ G.criticalPoints) (a : ℝ)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (G.localSeparatedTime p p.2 - a ^ 2)) : FramedLevelSet n :=
  SlabTamedField.sliceFLSAt
    (R.amplitude.toVerticalAmplitude.pullback C).toLevelCobordismData
    (G.localSeparatedTime p p.2 - a ^ 2) hreg


-- @@ L531-556 verbatim
theorem criticalMinimumSpatialCircle_mem_fiber
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum)
    (a : ℝ) (ha : 0 < a)
    (hrad : a < (R.criticalModelShrink p hp).radius)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (G.localSeparatedTime p p.2 + a ^ 2)) (u : I) :
    R.criticalDefiniteSpatialCircle p hp a ha hrad u ∈
      (R.criticalMinimumPositiveSlice p hp a hreg).fiber := by
  rw [criticalMinimumPositiveSlice, SlabTamedField.sliceFLSAt_fiber]
  change (R.amplitude.toVerticalAmplitude.pullback C).G
    (cobSpaceTime
      (spacePart (R.criticalDefiniteCircleCurve p hp a ha hrad u))
      (G.localSeparatedTime p p.2 + a ^ 2)) = 0
  change (R.amplitude.toVerticalAmplitude.pullback C).G
    (cobSpaceTime
      (spacePart (R.criticalDefiniteCircle p hp a
        (2 * Real.pi * (u : ℝ))))
      (G.localSeparatedTime p p.2 + a ^ 2)) = 0
  rw [← R.criticalMinimumCircle_time p hp hindex
      (theta := 2 * Real.pi * (u : ℝ)) ha.le hrad,
    spaceTime_spacePart]
  exact R.criticalDefiniteCircle_fiber p hp
    (theta := 2 * Real.pi * (u : ℝ)) ha.le hrad


-- @@ L558-583 verbatim
theorem criticalMaximumSpatialCircle_mem_fiber
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum)
    (a : ℝ) (ha : 0 < a)
    (hrad : a < (R.criticalModelShrink p hp).radius)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (G.localSeparatedTime p p.2 - a ^ 2)) (u : I) :
    R.criticalDefiniteSpatialCircle p hp a ha hrad u ∈
      (R.criticalMaximumNegativeSlice p hp a hreg).fiber := by
  rw [criticalMaximumNegativeSlice, SlabTamedField.sliceFLSAt_fiber]
  change (R.amplitude.toVerticalAmplitude.pullback C).G
    (cobSpaceTime
      (spacePart (R.criticalDefiniteCircleCurve p hp a ha hrad u))
      (G.localSeparatedTime p p.2 - a ^ 2)) = 0
  change (R.amplitude.toVerticalAmplitude.pullback C).G
    (cobSpaceTime
      (spacePart (R.criticalDefiniteCircle p hp a
        (2 * Real.pi * (u : ℝ))))
      (G.localSeparatedTime p p.2 - a ^ 2)) = 0
  rw [← R.criticalMaximumCircle_time p hp hindex
      (theta := 2 * Real.pi * (u : ℝ)) ha.le hrad,
    spaceTime_spacePart]
  exact R.criticalDefiniteCircle_fiber p hp
    (theta := 2 * Real.pi * (u : ℝ)) ha.le hrad


-- @@ L585-601 verbatim
/-- The full born circle is contained in one actual orbit component. -/
theorem criticalMinimumSpatialCircle_mem_same_orbit
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum)
    (a : ℝ) (ha : 0 < a)
    (hrad : a < (R.criticalModelShrink p hp).radius)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (G.localSeparatedTime p p.2 + a ^ 2))
    (V : TamedField (R.criticalMinimumPositiveSlice p hp a hreg)) (u : I) :
    R.criticalDefiniteSpatialCircle p hp a ha hrad u ∈
      V.orbit (R.criticalDefiniteSpatialCircle p hp a ha hrad 0) := by
  apply V.continuousMap_mem_orbit
    (R.criticalDefiniteSpatialCircle p hp a ha hrad)
  intro v
  exact R.criticalMinimumSpatialCircle_mem_fiber p hp hindex a ha hrad hreg v


-- @@ L603-619 verbatim
/-- The full pre-death circle is contained in one actual orbit component. -/
theorem criticalMaximumSpatialCircle_mem_same_orbit
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum)
    (a : ℝ) (ha : 0 < a)
    (hrad : a < (R.criticalModelShrink p hp).radius)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (G.localSeparatedTime p p.2 - a ^ 2))
    (V : TamedField (R.criticalMaximumNegativeSlice p hp a hreg)) (u : I) :
    R.criticalDefiniteSpatialCircle p hp a ha hrad u ∈
      V.orbit (R.criticalDefiniteSpatialCircle p hp a ha hrad 0) := by
  apply V.continuousMap_mem_orbit
    (R.criticalDefiniteSpatialCircle p hp a ha hrad)
  intro v
  exact R.criticalMaximumSpatialCircle_mem_fiber p hp hindex a ha hrad hreg v


-- @@ L621-621 verbatim
/-! ## Installed definite circles as genuine once-around orbit parameters -/


-- @@ L623-661 verbatim
/-- After one uniform radius shrink, every installed minimum circle is a
`SimpleClosedOrbitParam` for every tamed field on its actual regular slice.
Thus its directly read frame loop computes the intrinsic orbit frame class. -/
theorem exists_radius_for_criticalMinimumSimpleClosedOrbitParam
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum) :
    ∃ r > 0, r ≤ (R.criticalModelShrink p hp).radius ∧
      ∀ (a : ℝ) (ha : 0 < a) (har : a < r)
        (hreg : sliceRegular
          (R.amplitude.toVerticalAmplitude.pullback C).G
          (G.localSeparatedTime p p.2 + a ^ 2))
        (V : TamedField (R.criticalMinimumPositiveSlice p hp a hreg)),
        Nonempty (SimpleClosedOrbitParam
          (R.criticalMinimumPositiveSlice p hp a hreg) V) := by
  obtain ⟨r, hr, hrle, hinj⟩ :=
    R.exists_criticalSurfaceParam_injOn_radius p hp
  refine ⟨r, hr, hrle, ?_⟩
  intro a ha har hreg V
  let hrad : a < (R.criticalModelShrink p hp).radius := har.trans_le hrle
  let P : SimpleClosedOrbitParam
      (R.criticalMinimumPositiveSlice p hp a hreg) V := {
    p := R.criticalDefiniteSpatialCircle p hp a ha hrad 0
    hp := R.criticalMinimumSpatialCircle_mem_fiber p hp hindex
      a ha hrad hreg 0
    curve := R.criticalDefiniteSpatialCircle p hp a ha hrad
    curve_zero := rfl
    curve_closed := by
      exact congrArg spacePart
        (R.criticalDefiniteCircleCurve_closed p hp a ha hrad)
    curve_mem_orbit := fun u =>
      R.criticalMinimumSpatialCircle_mem_same_orbit p hp hindex
        a ha hrad hreg V u
    curve_eq_cases := by
      intro u v huv
      exact R.criticalMinimumSpatialCircle_eq_cases p hp hindex
        ha hrad har hinj huv
  }
  exact ⟨P⟩


-- @@ L663-699 verbatim
/-- The identical once-around package on the pre-death side of a maximum. -/
theorem exists_radius_for_criticalMaximumSimpleClosedOrbitParam
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum) :
    ∃ r > 0, r ≤ (R.criticalModelShrink p hp).radius ∧
      ∀ (a : ℝ) (ha : 0 < a) (har : a < r)
        (hreg : sliceRegular
          (R.amplitude.toVerticalAmplitude.pullback C).G
          (G.localSeparatedTime p p.2 - a ^ 2))
        (V : TamedField (R.criticalMaximumNegativeSlice p hp a hreg)),
        Nonempty (SimpleClosedOrbitParam
          (R.criticalMaximumNegativeSlice p hp a hreg) V) := by
  obtain ⟨r, hr, hrle, hinj⟩ :=
    R.exists_criticalSurfaceParam_injOn_radius p hp
  refine ⟨r, hr, hrle, ?_⟩
  intro a ha har hreg V
  let hrad : a < (R.criticalModelShrink p hp).radius := har.trans_le hrle
  let P : SimpleClosedOrbitParam
      (R.criticalMaximumNegativeSlice p hp a hreg) V := {
    p := R.criticalDefiniteSpatialCircle p hp a ha hrad 0
    hp := R.criticalMaximumSpatialCircle_mem_fiber p hp hindex
      a ha hrad hreg 0
    curve := R.criticalDefiniteSpatialCircle p hp a ha hrad
    curve_zero := rfl
    curve_closed := by
      exact congrArg spacePart
        (R.criticalDefiniteCircleCurve_closed p hp a ha hrad)
    curve_mem_orbit := fun u =>
      R.criticalMaximumSpatialCircle_mem_same_orbit p hp hindex
        a ha hrad hreg V u
    curve_eq_cases := by
      intro u v huv
      exact R.criticalMaximumSpatialCircle_eq_cases p hp hindex
        ha hrad har hinj huv
  }
  exact ⟨P⟩


-- @@ L701-701 verbatim
end ExactFiniteMorseJetInstallation


-- @@ L703-703 verbatim
end Submission
