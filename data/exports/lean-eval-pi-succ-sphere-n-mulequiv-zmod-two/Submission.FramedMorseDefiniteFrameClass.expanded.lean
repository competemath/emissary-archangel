import Mathlib
import Submission.FramedMorseDefiniteEvent
import Submission.SOPositiveFrameHomotopy


-- @@ L5-13 verbatim
/-!
# Radius invariance of an installed definite Morse frame

The nonempty side of an installed minimum or maximum is parametrized by
concentric circles in the exact Morse surface chart.  This file constructs the
literal annulus between any two positive radii and proves that the canonical
regular-zero frame loops on its boundary have the same stable class.  Hence the
local class calculation may be performed at an arbitrarily small radius.
-/


-- @@ L15-15 verbatim
noncomputable section


-- @@ L17-17 verbatim
open Set Function Metric

-- @@ L18-18 verbatim
open scoped RealInnerProductSpace unitInterval


-- @@ L20-20 verbatim
namespace Submission


-- @@ L22-22 verbatim
set_option autoImplicit false


-- @@ L24-24 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)


-- @@ L26-28 verbatim
/-- Convex interpolation between two radii. -/
def definiteRadiusInterpolation (a b : ℝ) (s : I) : ℝ :=
  (1 - (s : ℝ)) * a + (s : ℝ) * b


-- @@ L30-32 verbatim
@[simp] theorem definiteRadiusInterpolation_zero (a b : ℝ) :
    definiteRadiusInterpolation a b 0 = a := by
  simp [definiteRadiusInterpolation]


-- @@ L34-36 verbatim
@[simp] theorem definiteRadiusInterpolation_one (a b : ℝ) :
    definiteRadiusInterpolation a b 1 = b := by
  simp [definiteRadiusInterpolation]


-- @@ L38-41 verbatim
theorem continuous_definiteRadiusInterpolation (a b : ℝ) :
    Continuous (definiteRadiusInterpolation a b) := by
  unfold definiteRadiusInterpolation
  fun_prop


-- @@ L43-53 verbatim
theorem definiteRadiusInterpolation_pos {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (s : I) :
    0 < definiteRadiusInterpolation a b s := by
  have hs0 : 0 ≤ (s : ℝ) := s.property.1
  have hs1 : (s : ℝ) ≤ 1 := s.property.2
  unfold definiteRadiusInterpolation
  by_cases hs : (s : ℝ) = 0
  · simp [hs, ha]
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg (sub_nonneg.mpr hs1) ha.le)
    (mul_pos (lt_of_le_of_ne hs0 (Ne.symm hs)) hb)


-- @@ L55-72 verbatim
theorem definiteRadiusInterpolation_lt {a b r : ℝ}
    (har : a < r) (hbr : b < r) (s : I) :
    definiteRadiusInterpolation a b s < r := by
  have hs0 : 0 ≤ (s : ℝ) := s.property.1
  have hs1 : (s : ℝ) ≤ 1 := s.property.2
  by_cases hsone : (s : ℝ) = 1
  · simp [definiteRadiusInterpolation, hsone, hbr]
  have hslt : (s : ℝ) < 1 := lt_of_le_of_ne hs1 hsone
  have hleft : (1 - (s : ℝ)) * a < (1 - (s : ℝ)) * r :=
    mul_lt_mul_of_pos_left har (sub_pos.mpr hslt)
  have hright : (s : ℝ) * b ≤ (s : ℝ) * r :=
    mul_le_mul_of_nonneg_left hbr.le hs0
  unfold definiteRadiusInterpolation
  calc
    (1 - (s : ℝ)) * a + (s : ℝ) * b <
        (1 - (s : ℝ)) * r + (s : ℝ) * r :=
      add_lt_add_of_lt_of_le hleft hright
    _ = r := by ring


-- @@ L74-74 verbatim
namespace ExactFiniteMorseJetInstallation


-- @@ L76-76 verbatim
variable {n : ℕ}

-- @@ L77-77 verbatim
variable {C : FramedLevelCobordism n} {ι : Type*} [Fintype ι]

-- @@ L78-78 verbatim
variable {B : FiniteIFTSurfaceCover C ι}

-- @@ L79-79 verbatim
variable {G : GenericFiniteIFTSurfaceAtlas B.toSurfaceChartFamily}


-- @@ L81-81 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L83-125 verbatim
/-- The literal annulus homotopy between two installed definite circles. -/
def criticalDefiniteCircleRadiusHomotopy
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hradA : a < (R.criticalModelShrink p hp).radius)
    (hradB : b < (R.criticalModelShrink p hp).radius) :
    ContinuousMap.Homotopy
      (R.criticalDefiniteCircleCurve p hp a ha hradA)
      (R.criticalDefiniteCircleCurve p hp b hb hradB) where
  toFun q := R.criticalDefiniteCircle p hp
    (definiteRadiusInterpolation a b q.1)
    (2 * Real.pi * (q.2 : ℝ))
  continuous_toFun := by
    let u : I × I → E₂ := fun q => definiteCircleParam
      (definiteRadiusInterpolation a b q.1)
      (2 * Real.pi * (q.2 : ℝ))
    have hu : Continuous u := by
      unfold u definiteCircleParam pairToMorseParam
        definiteRadiusInterpolation
      fun_prop
    rw [continuous_iff_continuousAt]
    intro q
    apply (R.criticalSurfaceParam_differentiableAt p hp (u q) ?_).continuousAt.comp'
      hu.continuousAt
    change ‖definiteCircleParam
      (definiteRadiusInterpolation a b q.1)
      (2 * Real.pi * (q.2 : ℝ))‖ < _
    rw [norm_definiteCircleParam
      (definiteRadiusInterpolation_pos ha hb q.1).le]
    exact definiteRadiusInterpolation_lt hradA hradB q.1
  map_zero_left u := by
    change R.criticalDefiniteCircle p hp
      (definiteRadiusInterpolation a b 0)
      (2 * Real.pi * (u : ℝ)) =
        R.criticalSurfaceParam p hp (definiteCircleParamCurve a u)
    simp [definiteCircleParamCurve, criticalDefiniteCircle]
  map_one_left u := by
    change R.criticalDefiniteCircle p hp
      (definiteRadiusInterpolation a b 1)
      (2 * Real.pi * (u : ℝ)) =
        R.criticalSurfaceParam p hp (definiteCircleParamCurve b u)
    simp [definiteCircleParamCurve, criticalDefiniteCircle]


-- @@ L127-141 verbatim
/-- Every point of the radius annulus is a spatially regular zero. -/
theorem criticalDefiniteCircleRadiusHomotopy_regular
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hradA : a < (R.criticalModelShrink p hp).radius)
    (hradB : b < (R.criticalModelShrink p hp).radius)
    (q : I × I) :
    Surjective
      (spatialDeriv (R.amplitude.toVerticalAmplitude.pullback C).G
        (R.criticalDefiniteCircleRadiusHomotopy p hp a b ha hb
          hradA hradB q)) := by
  exact R.criticalDefiniteCircle_regular p hp
    (definiteRadiusInterpolation_pos ha hb q.1)
    (definiteRadiusInterpolation_lt hradA hradB q.1)


-- @@ L143-170 verbatim
/-- Every intermediate circle closes after one turn. -/
theorem criticalDefiniteCircleRadiusHomotopy_closed
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hradA : a < (R.criticalModelShrink p hp).radius)
    (hradB : b < (R.criticalModelShrink p hp).radius)
    (s : I) :
    R.criticalDefiniteCircleRadiusHomotopy p hp a b ha hb
        hradA hradB (s, 0) =
      R.criticalDefiniteCircleRadiusHomotopy p hp a b ha hb
        hradA hradB (s, 1) := by
  change (R.criticalDefiniteCircleRadiusHomotopy p hp a b ha hb
      hradA hradB).toFun (s, 0) =
    (R.criticalDefiniteCircleRadiusHomotopy p hp a b ha hb
      hradA hradB).toFun (s, 1)
  simp only [criticalDefiniteCircleRadiusHomotopy]
  norm_num
  change R.criticalDefiniteCircle p hp
      (definiteRadiusInterpolation a b s) 0 =
    R.criticalDefiniteCircle p hp
      (definiteRadiusInterpolation a b s) (2 * Real.pi)
  unfold criticalDefiniteCircle
  congr 1
  ext i
  fin_cases i <;>
    simp [definiteCircleParam, pairToMorseParam,
      Real.cos_two_pi, Real.sin_two_pi]


-- @@ L172-211 verbatim
/-- The regular-zero frame class of an installed definite circle is independent
of the chosen positive radius inside the exact Morse chart. -/
theorem loopClassZ2_criticalDefiniteCircle_radius_congr
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hradA : a < (R.criticalModelShrink p hp).radius)
    (hradB : b < (R.criticalModelShrink p hp).radius) :
    let zA := R.criticalDefiniteCircleCurve p hp a ha hradA
    let zB := R.criticalDefiniteCircleCurve p hp b hb hradB
    let hregA : ∀ u, Surjective
        (spatialDeriv (R.amplitude.toVerticalAmplitude.pullback C).G
          (zA u)) := fun u => by
      exact R.criticalDefiniteCircle_regular p hp ha hradA
    let hregB : ∀ u, Surjective
        (spatialDeriv (R.amplitude.toVerticalAmplitude.pullback C).G
          (zB u)) := fun u => by
      exact R.criticalDefiniteCircle_regular p hp hb hradB
    loopClassZ2
        (regularZeroFrame
          (R.amplitude.toVerticalAmplitude.pullback C).smooth zA hregA)
        (regularZeroFrame_closed
          (R.amplitude.toVerticalAmplitude.pullback C).smooth zA hregA
          (R.criticalDefiniteCircleCurve_closed p hp a ha hradA)) =
      loopClassZ2
        (regularZeroFrame
          (R.amplitude.toVerticalAmplitude.pullback C).smooth zB hregB)
        (regularZeroFrame_closed
          (R.amplitude.toVerticalAmplitude.pullback C).smooth zB hregB
          (R.criticalDefiniteCircleCurve_closed p hp b hb hradB)) := by
  dsimp only
  exact loopClassZ2_regularZeroFrame_congr
    (R.amplitude.toVerticalAmplitude.pullback C).smooth
    (R.criticalDefiniteCircleRadiusHomotopy p hp a b ha hb hradA hradB)
    (R.criticalDefiniteCircleRadiusHomotopy_regular p hp a b ha hb
      hradA hradB)
    (R.criticalDefiniteCircleCurve_closed p hp a ha hradA)
    (R.criticalDefiniteCircleCurve_closed p hp b hb hradB)
    (R.criticalDefiniteCircleRadiusHomotopy_closed p hp a b ha hb
      hradA hradB)


-- @@ L213-213 verbatim
end ExactFiniteMorseJetInstallation


-- @@ L215-215 verbatim
end Submission
