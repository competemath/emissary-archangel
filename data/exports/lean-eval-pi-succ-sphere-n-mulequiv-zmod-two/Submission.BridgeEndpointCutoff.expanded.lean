import Mathlib
import Submission.BridgeSignedCollapse
import Submission.SignedPTEndpoint


-- @@ L5-10 verbatim
/-!
# The canonical bridge collapse as an endpoint `PTCutoff`

This is the small interface between the canonical bridge construction and the
cutoff-independent signed endpoint collapse API.
-/


-- @@ L12-12 verbatim
noncomputable section


-- @@ L14-14 verbatim
open Set Function Metric Topology.Homotopy

-- @@ L15-15 verbatim
open scoped Topology RealInnerProductSpace ContDiff unitInterval


-- @@ L17-17 verbatim
namespace Submission


-- @@ L19-19 verbatim
variable {n : ℕ}

-- @@ L20-21 verbatim
variable {z : HomotopyGroup (Fin (n + 1))
    (UnitSphere (EuclideanSpace ℝ (Fin (n + 1)))) (southPole n)}


-- @@ L23-23 verbatim
namespace BridgeData


-- @@ L25-25 verbatim
variable (B : BridgeData n z)


-- @@ L27-27 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L29-50 verbatim
/-- The canonical northern bridge cutoff, packaged as the endpoint selector for the
canonical bridge fiber sign. -/
def northEndpointPTCutoff : FiberSign.PTCutoff B.fiberSign where
  toFun := B.northCutoff
  smooth := B.contDiff_northCutoff
  range := fun x => ⟨B.northCutoff_nonneg x, B.northCutoff_le_one x⟩
  positive_one := by
    rintro x ⟨hxFiber, hxPos⟩
    apply B.northCutoff_of_northFiber
    apply (B.mem_north_iff hxFiber).mpr
    simpa [fiberSign_apply, northSource] using hxPos
  negative_zero := by
    rintro x ⟨hxFiber, hxNeg⟩
    have hdich := hxFiber
    rw [B.fiber_eq] at hdich
    rcases hdich with hnorth | hsouth
    · have hpos := (B.mem_north_iff hxFiber).mp hnorth
      have : 0 < B.fiberSign x := by
        simpa [fiberSign_apply, northSource] using hpos
      linarith
    · exact B.northCutoff_of_southFiber hsouth
  compact_support := B.hasCompactSupport_northCutoff


-- @@ L52-54 verbatim
@[simp]
lemma northEndpointPTCutoff_apply (x : E) :
    B.northEndpointPTCutoff x = B.northCutoff x := rfl


-- @@ L56-60 verbatim
/-- At the raw-vector level the generic signed endpoint construction specializes
definitionally to the canonical bridge signed collapse. -/
lemma northEndpointPTCutoff_raw (x : E) :
    FiberSign.PTCutoff.raw B.fiberSign B.northEndpointPTCutoff x =
      B.signedCollapseRaw x := rfl


-- @@ L62-71 verbatim
/-- The normalized generic endpoint sphere map is the canonical bridge signed
collapse pointwise. -/
lemma northEndpointPTCutoff_sphereMap (x : E) :
    FiberSign.PTCutoff.sphereMap B.fiberSign B.northEndpointPTCutoff x =
      B.signedCollapseCM x := by
  apply Subtype.ext
  change ‖FiberSign.PTCutoff.raw B.fiberSign B.northEndpointPTCutoff x‖⁻¹ •
      FiberSign.PTCutoff.raw B.fiberSign B.northEndpointPTCutoff x =
    ‖B.signedCollapseRaw x‖⁻¹ • B.signedCollapseRaw x
  rw [B.northEndpointPTCutoff_raw]


-- @@ L73-83 verbatim
/-- Cubical loop obtained from the generic endpoint `sphereMap`. -/
def northEndpointPTCutoffLoop :
    Ω^ (Fin (n + 1)) (UnitSphere E) (southPole n) :=
  ⟨(FiberSign.PTCutoff.sphereMap B.fiberSign B.northEndpointPTCutoff).comp
      ⟨cubeToBridgeDomain, continuous_cubeToBridgeDomain⟩,
    by
      intro t ht
      change FiberSign.PTCutoff.sphereMap B.fiberSign B.northEndpointPTCutoff
        (cubeToBridgeDomain t) = southPole n
      rw [B.northEndpointPTCutoff_sphereMap]
      exact B.signedCollapse_cube_boundary ht⟩


-- @@ L85-89 verbatim
@[simp]
lemma northEndpointPTCutoffLoop_apply (t : I^(Fin (n + 1))) :
    B.northEndpointPTCutoffLoop t =
      FiberSign.PTCutoff.sphereMap B.fiberSign B.northEndpointPTCutoff
        (cubeToBridgeDomain t) := rfl


-- @@ L91-97 verbatim
theorem northEndpointPTCutoffLoop_eq_signedCollapseLoop :
    B.northEndpointPTCutoffLoop = B.signedCollapseLoop := by
  apply GenLoop.ext
  intro t
  rw [B.northEndpointPTCutoffLoop_apply, B.signedCollapseLoop_apply,
    B.northEndpointPTCutoff_sphereMap]
  rfl


-- @@ L99-105 verbatim
/-- The generic endpoint loop produced by the canonical bridge cutoff represents
the bridge's original homotopy class. -/
theorem northEndpointPTCutoffLoop_class_eq :
    (⟦B.northEndpointPTCutoffLoop⟧ : HomotopyGroup (Fin (n + 1))
      (UnitSphere E) (southPole n)) = z := by
  rw [B.northEndpointPTCutoffLoop_eq_signedCollapseLoop]
  exact B.signedCollapseLoop_class_eq


-- @@ L107-107 verbatim
end BridgeData


-- @@ L109-109 verbatim
end Submission
