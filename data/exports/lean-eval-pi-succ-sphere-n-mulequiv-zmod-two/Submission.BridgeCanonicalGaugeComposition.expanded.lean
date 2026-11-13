import Mathlib
import Submission.BridgeCompactBackgroundGauge
import Submission.SOStableCanonicalCircleNormalization


-- @@ L5-16 verbatim
/-!
# Simultaneous bridge-background and canonical-slot frame gauges

The bridge-background gauge is spatially constant and changes the native
background to the compact Morse background.  The canonical finite gauge is a
product of special-orthogonal gauges supported near the finitely many
canonical circles.  This file composes the two paths at the same time.

The result is one actual `DefiningMapHomotopy`.  Its endpoint still has the
compact background literally (not merely up to an equivalence), because the
finite factor is exactly the identity outside an explicit finite radius.
-/


-- @@ L18-18 verbatim
set_option autoImplicit false


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
open Set Function Metric

-- @@ L23-23 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L25-25 verbatim
namespace Submission

-- @@ L26-26 verbatim
namespace BridgeCanonicalGaugeComposition


-- @@ L28-28 verbatim
open SmoothCartesianSOLoop


-- @@ L30-30 verbatim
variable {m : ℕ}


-- @@ L32-32 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 3))

-- @@ L33-33 verbatim
local notation "F" => EuclideanSpace ℝ (Fin (m + 2))


-- @@ L35-35 verbatim
/-! ## A concrete radius containing every supported canonical tube -/


-- @@ L37-37 verbatim
variable {X₀ : FramedLevelSet (m + 2)}

-- @@ L38-38 verbatim
variable (V₀ : TamedField X₀)


-- @@ L40-45 verbatim
/-- A deliberately generous explicit radius containing all translated outer
tubes.  A tube point is less than two units from its center, and every center
norm is bounded by the finite sum below. -/
def supportRadius : ℝ :=
  2 + ∑ O : V₀.OrbitIndex,
    ‖CanonicalRoundOrbit.center V₀ (by omega) O‖


-- @@ L47-49 verbatim
theorem supportRadius_nonneg : 0 ≤ supportRadius V₀ := by
  dsimp [supportRadius]
  positivity


-- @@ L51-58 verbatim
/-- The radius-`1/3` tube around the unit circle lies in the open ball of
radius two about the origin. -/
theorem norm_lt_two_of_mem_outerTube {v : E}
    (hv : v ∈ tubeRegion (m := m) (1 / 3)) : ‖v‖ < 2 := by
  have hd : tubeDistSq v < (1 / 3 : ℝ) ^ 2 := hv
  have hr := rad_le_norm v
  rw [tubeDistSq] at hd
  nlinarith [sq_nonneg (‖v‖ - 1), norm_nonneg v]


-- @@ L60-86 verbatim
/-- Outside `supportRadius`, a point misses the translated outer tube of
every canonical slot. -/
theorem sub_center_not_mem_outerTube_of_supportRadius_le_norm
    {x : E} (hx : supportRadius V₀ ≤ ‖x‖)
    (O : V₀.OrbitIndex) :
    x - CanonicalRoundOrbit.center V₀ (by omega) O ∉
      tubeRegion (m := m) (1 / 3) := by
  intro hmem
  have hoff :
      ‖x - CanonicalRoundOrbit.center V₀ (by omega) O‖ < 2 :=
    norm_lt_two_of_mem_outerTube hmem
  have hcenter :
      ‖CanonicalRoundOrbit.center V₀ (by omega) O‖ ≤
        ∑ P : V₀.OrbitIndex,
          ‖CanonicalRoundOrbit.center V₀ (by omega) P‖ := by
    exact Finset.single_le_sum (fun P _ => norm_nonneg
      (CanonicalRoundOrbit.center V₀ (by omega) P))
      (Finset.mem_univ O)
  have htriangle :
      ‖x‖ ≤ ‖x - CanonicalRoundOrbit.center V₀ (by omega) O‖ +
        ‖CanonicalRoundOrbit.center V₀ (by omega) O‖ := by
    simpa only [sub_add_cancel] using
      norm_add_le (x - CanonicalRoundOrbit.center V₀ (by omega) O)
        (CanonicalRoundOrbit.center V₀ (by omega) O)
  have hlt : ‖x‖ < supportRadius V₀ :=
    lt_of_le_of_lt htriangle (add_lt_add_of_lt_of_le hoff hcenter)
  exact (not_lt_of_ge hx) hlt


-- @@ L88-88 verbatim
/-! ## The finite factor is exactly trivial at spatial infinity -/


-- @@ L90-90 verbatim
variable (L₀ : V₀.OrbitIndex → SmoothCartesianSOLoop (m + 2))

-- @@ L91-91 verbatim
variable (N₀ : ∀ O : V₀.OrbitIndex, (L₀ O).NullGaugeData)


-- @@ L93-103 verbatim
theorem listSpatialGauge_eq_one_of_supportRadius_le_norm
    (tail : List V₀.OrbitIndex) {x : E}
    (hx : supportRadius V₀ ≤ ‖x‖) :
    CanonicalFiniteGauge.listSpatialGauge V₀ L₀ N₀ tail 1 x = 1 := by
  induction tail with
  | nil => rfl
  | cons O tail ih =>
      rw [CanonicalFiniteGauge.listSpatialGauge,
        (N₀ O).centeredSpatialGauge_eq_one_off_outer,
        ih, one_mul]
      exact sub_center_not_mem_outerTube_of_supportRadius_le_norm V₀ hx O


-- @@ L105-109 verbatim
theorem spatialGauge_eq_one_of_supportRadius_le_norm
    {x : E} (hx : supportRadius V₀ ≤ ‖x‖) :
    CanonicalFiniteGauge.spatialGauge V₀ L₀ N₀ 1 x = 1 := by
  exact listSpatialGauge_eq_one_of_supportRadius_le_norm V₀ L₀ N₀
    (CanonicalFiniteGauge.orbitList V₀) hx


-- @@ L111-111 verbatim
/-! ## Simultaneous composition with the global background gauge -/


-- @@ L113-124 verbatim
/-- First apply the global positive-scale/rotation gauge, then the finite
supported special-orthogonal gauge. -/
def combinedGauge
    (V₀ : TamedField X₀)
    (L₀ : V₀.OrbitIndex → SmoothCartesianSOLoop (m + 2))
    (N₀ : ∀ O : V₀.OrbitIndex, (L₀ O).NullGaugeData)
    {a b : F}
    (D : BridgeCompactBackgroundGauge.Data (n := m + 2) a b)
    (s : ℝ) (x : E) : F →L[ℝ] F :=
  (SOFrameGauge.toCLM
      (CanonicalFiniteGauge.spatialGauge V₀ L₀ N₀ s x)).comp
    (BridgeCompactBackgroundGauge.Data.gauge D s x)


-- @@ L126-135 verbatim
theorem combinedGauge_smooth {a b : F}
    (D : BridgeCompactBackgroundGauge.Data (n := m + 2) a b) :
    ContDiff ℝ ∞ (fun p : ℝ × E =>
      combinedGauge V₀ L₀ N₀ D p.1 p.2) := by
  have hfinite : ContDiff ℝ ∞ (fun p : ℝ × E =>
      SOFrameGauge.toCLM
        (CanonicalFiniteGauge.spatialGauge V₀ L₀ N₀ p.1 p.2)) :=
    SOFrameGauge.contDiff_toCLM
      (CanonicalFiniteGauge.spatialGauge_smooth V₀ L₀ N₀)
  exact hfinite.clm_comp D.gauge_smooth


-- @@ L137-140 verbatim
@[simp] theorem combinedGauge_zero {a b : F}
    (D : BridgeCompactBackgroundGauge.Data (n := m + 2) a b) (x : E) :
    combinedGauge V₀ L₀ N₀ D 0 x = ContinuousLinearMap.id ℝ F := by
  simp [combinedGauge, D.gauge_zero]


-- @@ L142-148 verbatim
theorem combinedGauge_bijective {a b : F}
    (D : BridgeCompactBackgroundGauge.Data (n := m + 2) a b)
    (s : ℝ) (x : E) :
    Bijective (combinedGauge V₀ L₀ N₀ D s x) := by
  exact (SOFrameGauge.toCLM_bijective
      (CanonicalFiniteGauge.spatialGauge V₀ L₀ N₀ s x)).comp
    (D.gauge_bijective s x)


-- @@ L150-163 verbatim
/-- The two gauge paths give one genuine common-fiber homotopy, rather than
two interface-level promises. -/
def homotopy {a b : F}
    (D : BridgeCompactBackgroundGauge.Data (n := m + 2) a b)
    (X : FramedLevelSet (m + 2)) :
    DefiningMapHomotopy X
      (X.gaugeTransform (combinedGauge V₀ L₀ N₀ D 1)
        (contDiff_gauge_slice
          (combinedGauge_smooth V₀ L₀ N₀ D) 1)
        (fun x => combinedGauge_bijective V₀ L₀ N₀ D 1 x)) :=
  DefiningMapHomotopy.ofGauge X (combinedGauge V₀ L₀ N₀ D)
    (combinedGauge_smooth V₀ L₀ N₀ D)
    (combinedGauge_zero V₀ L₀ N₀ D)
    (fun s _hs x => combinedGauge_bijective V₀ L₀ N₀ D s x)


-- @@ L165-175 verbatim
/-- At spatial infinity the composite endpoint sends the old background
literally to the requested new background. -/
theorem combinedGauge_one_apply_source_of_supportRadius_le_norm
    {a b : F}
    (D : BridgeCompactBackgroundGauge.Data (n := m + 2) a b)
    {x : E} (hx : supportRadius V₀ ≤ ‖x‖) :
    combinedGauge V₀ L₀ N₀ D 1 x a = b := by
  rw [combinedGauge, ContinuousLinearMap.comp_apply,
    spatialGauge_eq_one_of_supportRadius_le_norm V₀ L₀ N₀ hx,
    SOFrameGauge.toCLM_one, ContinuousLinearMap.id_apply,
    D.gauge_one_apply_source]


-- @@ L177-177 verbatim
/-! ## Exact flat endpoint package -/


-- @@ L179-182 verbatim
/-- A radius simultaneously containing the input non-flat region and every
canonical supported gauge tube. -/
def flatRadius {a : F} (A : FlatSignedConfiguration (m + 2) a) : ℝ :=
  max (‖A.center‖ + A.radius) (supportRadius V₀)


-- @@ L184-188 verbatim
theorem flatRadius_nonneg {a : F}
    (A : FlatSignedConfiguration (m + 2) a) :
    0 ≤ flatRadius V₀ A := by
  apply le_max_of_le_right
  exact supportRadius_nonneg V₀


-- @@ L190-216 verbatim
/-- The endpoint of the simultaneous homotopy is a literal flat
configuration with background `c₂`. -/
def targetFlat {a b : F}
    (D : BridgeCompactBackgroundGauge.Data (n := m + 2) a b)
    (A : FlatSignedConfiguration (m + 2) a) :
    FlatSignedConfiguration (m + 2) b where
  X := (homotopy V₀ L₀ N₀ D A.X).toCobordism.X₁
  sign := A.sign.restrict
    (homotopy V₀ L₀ N₀ D A.X).fiber_subset
  center := 0
  radius := flatRadius V₀ A
  radius_nonneg := flatRadius_nonneg V₀ A
  flatOutside := by
    intro x hx
    rw [dist_zero_right] at hx
    have hinputBound : ‖A.center‖ + A.radius ≤ ‖x‖ :=
      (le_max_left _ _).trans hx
    have hsupport : supportRadius V₀ ≤ ‖x‖ :=
      (le_max_right _ _).trans hx
    have htriangle := dist_triangle x A.center 0
    rw [dist_zero_right, dist_zero_right] at htriangle
    have hinput : A.radius ≤ dist x A.center := by
      linarith
    change combinedGauge V₀ L₀ N₀ D 1 x (A.X.g x) = b
    rw [A.flatOutside x hinput]
    exact combinedGauge_one_apply_source_of_supportRadius_le_norm
      V₀ L₀ N₀ D hsupport


-- @@ L218-225 verbatim
/-- The whole simultaneous change, including the compact background and all
canonical slot gauges, is an actual signed framed cobordism. -/
def signedCobordism {a b : F}
    (D : BridgeCompactBackgroundGauge.Data (n := m + 2) a b)
    (A : FlatSignedConfiguration (m + 2) a) :
    SignedFramedLevelCobordism A.sign
      (targetFlat V₀ L₀ N₀ D A).sign :=
  (homotopy V₀ L₀ N₀ D A.X).signedCobordism A.sign


-- @@ L227-227 verbatim
end BridgeCanonicalGaugeComposition

-- @@ L228-228 verbatim
end Submission
