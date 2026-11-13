import Mathlib
import Submission.FramedMorseDefiniteNormalRow
import Submission.FramedMorseDefiniteEvent


-- @@ L5-12 verbatim
/-!
# Uniform sign control on installed definite circles

A positive installed Morse center has a whole sufficiently small family of
definite parameter circles on the positive sheet.  This is the sign input
needed by `InstalledDefinitePositiveOrbit`; the result is uniform in the polar
angle and applies identically to minima and maxima.
-/


-- @@ L14-14 verbatim
set_option autoImplicit false


-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-18 verbatim
namespace Submission


-- @@ L20-20 verbatim
open Set Filter Metric

-- @@ L21-21 verbatim
open scoped Topology RealInnerProductSpace


-- @@ L23-23 verbatim
variable {n : ℕ}

-- @@ L24-24 verbatim
variable {X₀ X₁ : FramedLevelSet n}

-- @@ L25-25 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}

-- @@ L26-26 verbatim
variable {C : SignedFramedLevelCobordism S₀ S₁}

-- @@ L27-27 verbatim
variable {ι : Type*} [Fintype ι]

-- @@ L28-28 verbatim
variable {B : FiniteIFTSurfaceCover C.cobordism ι}

-- @@ L29-29 verbatim
variable {G : GenericFiniteIFTSurfaceAtlas B.toSurfaceChartFamily}


-- @@ L31-31 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)


-- @@ L33-33 verbatim
namespace SignedFramedLevelCobordism


-- @@ L35-43 verbatim
/-- Restricting the sign to a regular slice does not change positivity at an
ambient point whose time coordinate is that slice value. -/
theorem pos_sliceSign_spacePart_iff
    (D : SignedFramedLevelCobordism S₀ S₁)
    {v : EuclideanSpace ℝ (Fin (n + 2))} {t : ℝ}
    (ht : sliceRegular D.cobordism.G t) (hvt : tcoord v = t) :
    0 < D v ↔ 0 < D.sliceSign t ht (spacePart v) := by
  change 0 < D v ↔ 0 < D (cobSpaceTime (spacePart v) t)
  rw [← hvt, spaceTime_spacePart]


-- @@ L45-45 verbatim
end SignedFramedLevelCobordism


-- @@ L47-47 verbatim
namespace ExactFiniteMorseJetInstallation


-- @@ L49-49 verbatim
/-! ## Explicit positive-side orbit parameters -/


-- @@ L51-83 verbatim
/-- The actual born circle, exposed as a named once-around parameter after an
injectivity shrink.  Unlike the older existential theorem, this definition
retains the exact base point needed for sign control. -/
def criticalMinimumSimpleClosedOrbitParamAt
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum)
    (r : ℝ) (hrle : r ≤ (R.criticalModelShrink p hp).radius)
    (hinj : Set.InjOn (R.criticalSurfaceParam p hp) (ball (0 : E₂) r))
    (a : ℝ) (ha : 0 < a) (har : a < r)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C.cobordism).G
      (G.localSeparatedTime p p.2 + a ^ 2))
    (V : TamedField (R.criticalMinimumPositiveSlice p hp a hreg)) :
    SimpleClosedOrbitParam (R.criticalMinimumPositiveSlice p hp a hreg) V := by
  let hrad : a < (R.criticalModelShrink p hp).radius := har.trans_le hrle
  exact {
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


-- @@ L85-98 verbatim
@[simp] theorem criticalMinimumSimpleClosedOrbitParamAt_p
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum)
    (r : ℝ) (hrle : r ≤ (R.criticalModelShrink p hp).radius)
    (hinj : Set.InjOn (R.criticalSurfaceParam p hp) (ball (0 : E₂) r))
    (a : ℝ) (ha : 0 < a) (har : a < r)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C.cobordism).G
      (G.localSeparatedTime p p.2 + a ^ 2))
    (V : TamedField (R.criticalMinimumPositiveSlice p hp a hreg)) :
    (R.criticalMinimumSimpleClosedOrbitParamAt p hp hindex r hrle hinj
      a ha har hreg V).p =
      R.criticalDefiniteSpatialCircle p hp a ha (har.trans_le hrle) 0 := rfl


-- @@ L100-130 verbatim
/-- The corresponding named pre-death circle at a maximum. -/
def criticalMaximumSimpleClosedOrbitParamAt
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum)
    (r : ℝ) (hrle : r ≤ (R.criticalModelShrink p hp).radius)
    (hinj : Set.InjOn (R.criticalSurfaceParam p hp) (ball (0 : E₂) r))
    (a : ℝ) (ha : 0 < a) (har : a < r)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C.cobordism).G
      (G.localSeparatedTime p p.2 - a ^ 2))
    (V : TamedField (R.criticalMaximumNegativeSlice p hp a hreg)) :
    SimpleClosedOrbitParam (R.criticalMaximumNegativeSlice p hp a hreg) V := by
  let hrad : a < (R.criticalModelShrink p hp).radius := har.trans_le hrle
  exact {
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


-- @@ L132-145 verbatim
@[simp] theorem criticalMaximumSimpleClosedOrbitParamAt_p
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum)
    (r : ℝ) (hrle : r ≤ (R.criticalModelShrink p hp).radius)
    (hinj : Set.InjOn (R.criticalSurfaceParam p hp) (ball (0 : E₂) r))
    (a : ℝ) (ha : 0 < a) (har : a < r)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C.cobordism).G
      (G.localSeparatedTime p p.2 - a ^ 2))
    (V : TamedField (R.criticalMaximumNegativeSlice p hp a hreg)) :
    (R.criticalMaximumSimpleClosedOrbitParamAt p hp hindex r hrle hinj
      a ha har hreg V).p =
      R.criticalDefiniteSpatialCircle p hp a ha (har.trans_le hrle) 0 := rfl


-- @@ L147-178 verbatim
/-- Positivity at the actual installed center persists on every sufficiently
small definite circle, uniformly in its angular parameter. -/
theorem exists_radius_criticalDefiniteCircle_positive
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hcenter : 0 <
      (R.amplitude.toVerticalAmplitude.pullbackSigned C)
        (R.criticalCenter p)) :
    ∃ r > 0, r ≤ (R.criticalModelShrink p hp).radius ∧
      ∀ (a theta : ℝ), 0 ≤ a → a < r →
        0 < (R.amplitude.toVerticalAmplitude.pullbackSigned C)
          (R.criticalDefiniteCircle p hp a theta) := by
  let L := R.amplitude.toVerticalAmplitude.pullbackSigned C
  let f : E₂ → ℝ := fun u => L (R.criticalSurfaceParam p hp u)
  have hf : ContinuousAt f 0 :=
    L.continuous.continuousAt.comp
      (R.criticalSurfaceParam_contDiffAt_zero p hp).continuousAt
  have hfzero : 0 < f 0 := by
    simpa [f, L] using hcenter
  have hpositive : {u : E₂ | 0 < f u} ∈ nhds 0 :=
    hf (Ioi_mem_nhds hfzero)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpositive
  let r := min ε (R.criticalModelShrink p hp).radius
  have hr : 0 < r := lt_min hε (R.criticalModelShrink p hp).radius_pos
  refine ⟨r, hr, min_le_right _ _, ?_⟩
  intro a theta ha har
  have haε : a < ε := har.trans_le (min_le_left _ _)
  have hu : definiteCircleParam a theta ∈ ball (0 : E₂) ε := by
    rw [mem_ball, dist_zero_right, norm_definiteCircleParam ha]
    exact haε
  have hfu : 0 < f (definiteCircleParam a theta) := hball hu
  simpa [f, L, criticalDefiniteCircle] using hfu


-- @@ L180-232 verbatim
/-- At a positive minimum center, every sufficiently small post-event slice
contains an explicitly based positive once-around orbit parameter. -/
theorem exists_radius_for_criticalMinimumPositiveSimpleClosedOrbitParam
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .minimum)
    (hcenter : 0 <
      (R.amplitude.toVerticalAmplitude.pullbackSigned C)
        (R.criticalCenter p)) :
    ∃ r > 0, r ≤ (R.criticalModelShrink p hp).radius ∧
      ∀ (a : ℝ) (ha : 0 < a) (har : a < r)
        (hreg : sliceRegular
          (R.amplitude.toVerticalAmplitude.pullback C.cobordism).G
          (G.localSeparatedTime p p.2 + a ^ 2))
        (V : TamedField (R.criticalMinimumPositiveSlice p hp a hreg)),
        Nonempty {P : SimpleClosedOrbitParam
          (R.criticalMinimumPositiveSlice p hp a hreg) V //
          0 < (R.amplitude.toVerticalAmplitude.pullbackSigned C).sliceSign
            (G.localSeparatedTime p p.2 + a ^ 2) hreg P.p} := by
  obtain ⟨rInj, hrInj, hrInjle, hinj⟩ :=
    R.exists_criticalSurfaceParam_injOn_radius p hp
  obtain ⟨rSign, hrSign, _hrSignle, hsign⟩ :=
    R.exists_radius_criticalDefiniteCircle_positive p hp hcenter
  let r := min rInj rSign
  have hr : 0 < r := lt_min hrInj hrSign
  have hrle : r ≤ (R.criticalModelShrink p hp).radius :=
    (min_le_left rInj rSign).trans hrInjle
  refine ⟨r, hr, hrle, ?_⟩
  intro a ha har hreg V
  have harInj : a < rInj := har.trans_le (min_le_left rInj rSign)
  have harSign : a < rSign := har.trans_le (min_le_right rInj rSign)
  have hrad : a < (R.criticalModelShrink p hp).radius :=
    harInj.trans_le hrInjle
  let P := R.criticalMinimumSimpleClosedOrbitParamAt p hp hindex
    rInj hrInjle hinj a ha harInj hreg V
  have hambient : 0 <
      (R.amplitude.toVerticalAmplitude.pullbackSigned C)
        (R.criticalDefiniteCircle p hp a 0) :=
    hsign a 0 ha.le harSign
  have htime : tcoord (R.criticalDefiniteCircle p hp a 0) =
      G.localSeparatedTime p p.2 + a ^ 2 :=
    R.criticalMinimumCircle_time p hp hindex ha.le hrad
  have hslice : 0 <
      (R.amplitude.toVerticalAmplitude.pullbackSigned C).sliceSign
        (G.localSeparatedTime p p.2 + a ^ 2) hreg
        (spacePart (R.criticalDefiniteCircle p hp a 0)) :=
    (SignedFramedLevelCobordism.pos_sliceSign_spacePart_iff
      (R.amplitude.toVerticalAmplitude.pullbackSigned C) hreg htime).mp hambient
  refine ⟨⟨P, ?_⟩⟩
  simpa [P, criticalMinimumSimpleClosedOrbitParamAt,
    criticalDefiniteSpatialCircle, criticalDefiniteCircleCurve,
    criticalDefiniteCircle,
    definiteCircleParamCurve] using hslice


-- @@ L234-286 verbatim
/-- At a positive maximum center, every sufficiently small pre-event slice
contains the corresponding explicitly based positive once-around parameter. -/
theorem exists_radius_for_criticalMaximumPositiveSimpleClosedOrbitParam
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .maximum)
    (hcenter : 0 <
      (R.amplitude.toVerticalAmplitude.pullbackSigned C)
        (R.criticalCenter p)) :
    ∃ r > 0, r ≤ (R.criticalModelShrink p hp).radius ∧
      ∀ (a : ℝ) (ha : 0 < a) (har : a < r)
        (hreg : sliceRegular
          (R.amplitude.toVerticalAmplitude.pullback C.cobordism).G
          (G.localSeparatedTime p p.2 - a ^ 2))
        (V : TamedField (R.criticalMaximumNegativeSlice p hp a hreg)),
        Nonempty {P : SimpleClosedOrbitParam
          (R.criticalMaximumNegativeSlice p hp a hreg) V //
          0 < (R.amplitude.toVerticalAmplitude.pullbackSigned C).sliceSign
            (G.localSeparatedTime p p.2 - a ^ 2) hreg P.p} := by
  obtain ⟨rInj, hrInj, hrInjle, hinj⟩ :=
    R.exists_criticalSurfaceParam_injOn_radius p hp
  obtain ⟨rSign, hrSign, _hrSignle, hsign⟩ :=
    R.exists_radius_criticalDefiniteCircle_positive p hp hcenter
  let r := min rInj rSign
  have hr : 0 < r := lt_min hrInj hrSign
  have hrle : r ≤ (R.criticalModelShrink p hp).radius :=
    (min_le_left rInj rSign).trans hrInjle
  refine ⟨r, hr, hrle, ?_⟩
  intro a ha har hreg V
  have harInj : a < rInj := har.trans_le (min_le_left rInj rSign)
  have harSign : a < rSign := har.trans_le (min_le_right rInj rSign)
  have hrad : a < (R.criticalModelShrink p hp).radius :=
    harInj.trans_le hrInjle
  let P := R.criticalMaximumSimpleClosedOrbitParamAt p hp hindex
    rInj hrInjle hinj a ha harInj hreg V
  have hambient : 0 <
      (R.amplitude.toVerticalAmplitude.pullbackSigned C)
        (R.criticalDefiniteCircle p hp a 0) :=
    hsign a 0 ha.le harSign
  have htime : tcoord (R.criticalDefiniteCircle p hp a 0) =
      G.localSeparatedTime p p.2 - a ^ 2 :=
    R.criticalMaximumCircle_time p hp hindex ha.le hrad
  have hslice : 0 <
      (R.amplitude.toVerticalAmplitude.pullbackSigned C).sliceSign
        (G.localSeparatedTime p p.2 - a ^ 2) hreg
        (spacePart (R.criticalDefiniteCircle p hp a 0)) :=
    (SignedFramedLevelCobordism.pos_sliceSign_spacePart_iff
      (R.amplitude.toVerticalAmplitude.pullbackSigned C) hreg htime).mp hambient
  refine ⟨⟨P, ?_⟩⟩
  simpa [P, criticalMaximumSimpleClosedOrbitParamAt,
    criticalDefiniteSpatialCircle, criticalDefiniteCircleCurve,
    criticalDefiniteCircle,
    definiteCircleParamCurve] using hslice


-- @@ L288-288 verbatim
end ExactFiniteMorseJetInstallation

-- @@ L289-289 verbatim
end Submission
