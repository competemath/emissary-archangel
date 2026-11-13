import Mathlib
import Submission.ExplicitOrbitParam


-- @@ L4-14 verbatim
/-!
# Intrinsic once-around parametrizations of fiber orbits

Every orbit component of a tamed framed level set has a positive fundamental
period.  Running the intrinsic flow from the chosen orbit point for exactly
that period gives a canonical once-around parametrization.  This file packages
it as `SimpleClosedOrbitParam`, including the endpoint-only repetition proof.

The construction supplies the concrete circle used by componentwise bridge
normalization; no external parametrization choice is needed.
-/


-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-18 verbatim
namespace Submission


-- @@ L20-20 verbatim
open Set Function Topology

-- @@ L21-21 verbatim
open scoped RealInnerProductSpace Topology unitInterval


-- @@ L23-23 verbatim
set_option autoImplicit false


-- @@ L25-25 verbatim
variable {n : ℕ} {X : FramedLevelSet n}


-- @@ L27-27 verbatim
namespace TamedField


-- @@ L29-29 verbatim
variable (V : TamedField X)


-- @@ L31-31 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L33-38 verbatim
/-- The intrinsic flow through the chosen point of `O`, run for one positive
fundamental period over the unit interval. -/
def intrinsicOrbitCurve (O : V.OrbitIndex) : C(I, E) where
  toFun u := V.flow (V.orbitPoint O) ((u : ℝ) * V.orbitPeriod O)
  continuous_toFun := (V.continuous_flow (V.orbitPoint O)).comp
    (continuous_subtype_val.mul continuous_const)


-- @@ L40-42 verbatim
@[simp] theorem intrinsicOrbitCurve_zero (O : V.OrbitIndex) :
    V.intrinsicOrbitCurve O 0 = V.orbitPoint O := by
  simp [intrinsicOrbitCurve]


-- @@ L44-49 verbatim
/-- The intrinsic curve closes after its one fundamental period. -/
theorem intrinsicOrbitCurve_closed (O : V.OrbitIndex) :
    V.intrinsicOrbitCurve O 0 = V.intrinsicOrbitCurve O 1 := by
  change V.flow (V.orbitPoint O) (0 * V.orbitPeriod O) =
    V.flow (V.orbitPoint O) (1 * V.orbitPeriod O)
  simpa using (V.flow_periodic_orbitPeriod O 0).symm


-- @@ L51-53 verbatim
theorem intrinsicOrbitCurve_mem_orbit (O : V.OrbitIndex) (u : I) :
    V.intrinsicOrbitCurve O u ∈ V.orbit (V.orbitPoint O) := by
  exact V.flow_mem_orbit _ _


-- @@ L55-116 verbatim
/-- On a single positive fundamental period the intrinsic flow has no
repetitions except the identified endpoints. -/
theorem intrinsicOrbitCurve_eq_cases (O : V.OrbitIndex) {u v : I}
    (huv : V.intrinsicOrbitCurve O u = V.intrinsicOrbitCurve O v) :
    u = v ∨ (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) := by
  have hmem := (V.flow_eq_iff_sub_mem_zmultiples
    (V.orbitPoint_mem_fiber O)
    ((u : ℝ) * V.orbitPeriod O)
    ((v : ℝ) * V.orbitPeriod O)).mp huv
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  have hTpos : 0 < V.orbitPeriod O := V.orbitPeriod_pos O
  have huvInt : (u : ℝ) - (v : ℝ) = (k : ℝ) := by
    have hk' : (k : ℝ) * V.orbitPeriod O =
        (u : ℝ) * V.orbitPeriod O - (v : ℝ) * V.orbitPeriod O := by
      simpa [zsmul_eq_mul, orbitPeriod] using hk
    nlinarith
  rcases lt_trichotomy (u : ℝ) (v : ℝ) with huvlt | huveq | huvgt
  · right; left
    have hknegR : (k : ℝ) < 0 := by rw [← huvInt]; linarith
    have hkneg : k < 0 := by exact_mod_cast hknegR
    have hkge : (-1 : ℤ) ≤ k := by
      have hkgeR : (-1 : ℝ) ≤ (k : ℝ) := by
        rw [← huvInt]
        linarith [u.2.1, v.2.2]
      exact_mod_cast hkgeR
    have hkval : k = -1 := by omega
    constructor
    · apply Subtype.ext
      change (u : ℝ) = 0
      have hd : (u : ℝ) - (v : ℝ) = -1 := by
        rw [huvInt, hkval]
        norm_num
      nlinarith [u.2.1, v.2.2]
    · apply Subtype.ext
      change (v : ℝ) = 1
      have hd : (u : ℝ) - (v : ℝ) = -1 := by
        rw [huvInt, hkval]
        norm_num
      nlinarith [u.2.1, v.2.2]
  · exact Or.inl (Subtype.ext huveq)
  · right; right
    have hkposR : (0 : ℝ) < (k : ℝ) := by rw [← huvInt]; linarith
    have hkpos : 0 < k := by exact_mod_cast hkposR
    have hkle : k ≤ 1 := by
      have hkleR : (k : ℝ) ≤ 1 := by
        rw [← huvInt]
        linarith [u.2.2, v.2.1]
      exact_mod_cast hkleR
    have hkval : k = 1 := by omega
    constructor
    · apply Subtype.ext
      change (u : ℝ) = 1
      have hd : (u : ℝ) - (v : ℝ) = 1 := by
        rw [huvInt, hkval]
        norm_num
      nlinarith [u.2.2, v.2.1]
    · apply Subtype.ext
      change (v : ℝ) = 0
      have hd : (u : ℝ) - (v : ℝ) = 1 := by
        rw [huvInt, hkval]
        norm_num
      nlinarith [u.2.2, v.2.1]


-- @@ L118-128 verbatim
/-- Canonical once-around simple closed parametrization of an arbitrary orbit
component. -/
def intrinsicSimpleClosedOrbitParam (O : V.OrbitIndex) :
    SimpleClosedOrbitParam X V where
  p := V.orbitPoint O
  hp := V.orbitPoint_mem_fiber O
  curve := V.intrinsicOrbitCurve O
  curve_zero := V.intrinsicOrbitCurve_zero O
  curve_closed := V.intrinsicOrbitCurve_closed O
  curve_mem_orbit := V.intrinsicOrbitCurve_mem_orbit O
  curve_eq_cases := V.intrinsicOrbitCurve_eq_cases O


-- @@ L130-136 verbatim
/-- Its parameter frame loop computes the intrinsic class of the selected
orbit, with no orientation correction. -/
theorem intrinsicParamFrameClass (O : V.OrbitIndex) :
    loopClassZ2 (V.intrinsicSimpleClosedOrbitParam O).paramFrameLoop
        (V.intrinsicSimpleClosedOrbitParam O).paramFrameLoop_closed =
      V.orbitFrameClass O := by
  exact (V.intrinsicSimpleClosedOrbitParam O).paramFrameClass_eq_fundamental


-- @@ L138-138 verbatim
end TamedField


-- @@ L140-140 verbatim
end Submission
