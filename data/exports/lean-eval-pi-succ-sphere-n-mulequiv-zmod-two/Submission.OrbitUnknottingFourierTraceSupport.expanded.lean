import Mathlib
import Submission.OrbitUnknottingFourierRelativeTrack


-- @@ L4-13 verbatim
/-!
# A support neighborhood for a relative Fourier trace

A relative embedded-circle track avoids every other source and canonical
target at each time.  This file upgrades that pointwise statement to a
uniform support statement.  The joint track is continuous on time times the
quotient circle, hence its trace over the compact time interval is compact.
The compact trace and the closed obstacle configuration therefore have
disjoint closed metric thickenings.
-/


-- @@ L15-15 verbatim
set_option autoImplicit false


-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
open Set Function

-- @@ L20-20 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L22-22 verbatim
namespace Submission

-- @@ L23-23 verbatim
namespace TamedField

-- @@ L24-24 verbatim
namespace FourierTraceSupport


-- @@ L26-26 verbatim
variable {n : ℕ} {X : FramedLevelSet n} (V : TamedField X)


-- @@ L28-28 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L29-29 verbatim
local notation "C" => AddCircle (1 : ℝ)


-- @@ L31-31 verbatim
variable {V} (h2 : 2 ≤ n) (O : V.OrbitIndex)


-- @@ L33-33 verbatim
open FourierRelativeTrack


-- @@ L35-35 verbatim
namespace RelativeEmbeddedCircleTrack


-- @@ L37-37 verbatim
variable (R : RelativeEmbeddedCircleTrack (V := V) h2 O)


-- @@ L39-62 verbatim
/-- The descended circle track is jointly continuous in time and circle
phase.  We first descend each scalar coordinate through the quotient in the
second factor.  The final `toLp` step identifies the product-topology
coordinate function with the normed `EuclideanSpace`; spelling out this step
avoids relying on definitional equality of the two topology instances. -/
theorem continuous_jointCircle :
    Continuous (fun q : ℝ × C => R.track.circle q.1 q.2) := by
  have hraw : Continuous (fun q : ℝ × C => fun i : Fin (n + 1) =>
      R.track.circle q.1 q.2 i) := by
    apply continuous_pi
    intro i
    apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
    have hi : Continuous (fun q : ℝ × ℝ => R.track.lift q.1 q.2 i) :=
      (EuclideanSpace.proj i).continuous.comp R.track.smooth_lift.continuous
    apply hi.congr
    intro q
    change R.track.lift q.1 q.2 i =
      R.track.circle q.1 (q.2 : C) i
    rw [R.track.circle_coe]
  have htop :=
    (PiLp.continuous_toLp (2 : ENNReal) (fun _ : Fin (n + 1) => ℝ)).comp hraw
  apply htop.congr
  intro q
  exact WithLp.toLp_ofLp (2 : ENNReal) (R.track.circle q.1 q.2)


-- @@ L64-68 verbatim
/-- The full spatial trace of the moving circle over the closed unit time
interval. -/
def trace : Set E :=
  Set.range (fun q : Set.Icc (0 : ℝ) 1 × C =>
    R.track.circle q.1.1 q.2)


-- @@ L70-74 verbatim
theorem continuous_traceParam :
    Continuous (fun q : Set.Icc (0 : ℝ) 1 × C =>
      R.track.circle q.1.1 q.2) := by
  exact (continuous_jointCircle (V := V) (h2 := h2) (O := O) R).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)


-- @@ L76-79 verbatim
/-- The trace is compact, uniformly in both the time and circle variables. -/
theorem isCompact_trace : IsCompact (trace (V := V) h2 O R) := by
  exact isCompact_range
    (continuous_traceParam (V := V) (h2 := h2) (O := O) R)


-- @@ L81-102 verbatim
/-- The entire trace, including both endpoint circles, misses every source
and target belonging to another component. -/
theorem trace_disjoint_obstacleSet :
    Disjoint (trace (V := V) h2 O R)
      (OrbitUnknottingSupport.obstacleSet V h2 O) := by
  rw [Set.disjoint_left]
  intro x hxTrace hxObstacle
  obtain ⟨q, rfl⟩ := hxTrace
  obtain ⟨P, hPerase, hxSource | hxTarget⟩ :=
    Set.mem_iUnion₂.mp hxObstacle
  · have hPO : P ≠ O := by
      exact (Finset.mem_erase.mp hPerase).1
    exact Set.disjoint_left.mp
      (FourierRelativeTrack.RelativeEmbeddedCircleTrack.range_disjoint_source
        (V := V) (h2 := h2) (O := O) R q.1.property P hPO)
      ⟨q.2, rfl⟩ hxSource
  · have hPO : P ≠ O := by
      exact (Finset.mem_erase.mp hPerase).1
    exact Set.disjoint_left.mp
      (FourierRelativeTrack.RelativeEmbeddedCircleTrack.range_disjoint_target
        (V := V) (h2 := h2) (O := O) R q.1.property P hPO)
      ⟨q.2, rfl⟩ hxTarget


-- @@ L104-124 verbatim
/-- A positive open thickening of the whole Fourier trace has closure
disjoint from every relative obstacle.  This is the uniform support region
needed by the subsequent finite ambient-extension construction. -/
theorem exists_trace_thickening :
    ∃ δ : ℝ, 0 < δ ∧
      trace (V := V) h2 O R ⊆
        Metric.thickening δ (trace (V := V) h2 O R) ∧
      IsOpen (Metric.thickening δ (trace (V := V) h2 O R)) ∧
      Disjoint (closure (Metric.thickening δ (trace (V := V) h2 O R)))
        (OrbitUnknottingSupport.obstacleSet V h2 O) := by
  have htrace := isCompact_trace (V := V) (h2 := h2) (O := O) R
  have hobstacle := OrbitUnknottingSupport.isCompact_obstacleSet V h2 O
  have hdisjoint :=
    trace_disjoint_obstacleSet (V := V) (h2 := h2) (O := O) R
  obtain ⟨δ, hδ, hclosed⟩ :=
    hdisjoint.exists_cthickenings htrace hobstacle.isClosed
  refine ⟨δ, hδ, Metric.self_subset_thickening hδ _,
    Metric.isOpen_thickening, ?_⟩
  exact hclosed.mono
    (Metric.closure_thickening_subset_cthickening δ _)
    (Metric.self_subset_cthickening _)


-- @@ L126-126 verbatim
end RelativeEmbeddedCircleTrack


-- @@ L128-128 verbatim
end FourierTraceSupport

-- @@ L129-129 verbatim
end TamedField

-- @@ L130-130 verbatim
end Submission
