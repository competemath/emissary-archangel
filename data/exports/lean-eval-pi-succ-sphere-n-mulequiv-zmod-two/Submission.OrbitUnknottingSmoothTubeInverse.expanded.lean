import Mathlib
import Submission.OrbitUnknottingGlobalTube


-- @@ L4-17 verbatim
/-!
# Smooth inverse germs for the orbit tube

The globally embedded quotient tube is the topological input needed to keep
different orbit moves disjoint.  To write an ambient move in tube coordinates
we also need a smooth inverse near the zero section.  This file records the
inverse-function-theorem inverse explicitly and proves its value and derivative
at every point of the lifted zero section.

These statements are local in the real phase coordinate.  They are compatible
with the period-one quotient constructed in `OrbitUnknottingUniformTube` and
provide the local straightening germs used by a supported tube-coordinate
ambient isotopy.
-/


-- @@ L19-19 verbatim
set_option autoImplicit false

-- @@ L20-20 verbatim
set_option maxHeartbeats 800000


-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
open Set Function

-- @@ L25-25 verbatim
open scoped Topology ContDiff


-- @@ L27-27 verbatim
namespace Submission

-- @@ L28-28 verbatim
namespace TamedField


-- @@ L30-30 verbatim
variable {n : ℕ} {X : FramedLevelSet n} (V : TamedField X)


-- @@ L32-32 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L33-33 verbatim
local notation "N" => EuclideanSpace ℝ (Fin n)


-- @@ L35-39 verbatim
/-- The inverse-function-theorem inverse of the framed orbit tube at phase
`u`, regarded as a total function with the usual arbitrary values outside the
local target. -/
def orbitTubeLocalInverse (O : V.OrbitIndex) (u : ℝ) : E → ℝ × N :=
  (V.orbitTubeLocalHomeomorph O u).symm


-- @@ L41-49 verbatim
/-- The center point of the orbit belongs to the target of its local tube
chart. -/
theorem orbitTube_center_mem_localTarget (O : V.OrbitIndex) (u : ℝ) :
    V.intrinsicOrbitLift O u ∈
      (V.orbitTubeLocalHomeomorph O u).target := by
  rw [← V.orbitTubeLift_zero O u]
  rw [← V.orbitTubeLocalHomeomorph_coe O u]
  exact (V.orbitTubeLocalHomeomorph O u).map_source
    (V.orbitTube_center_mem_localSource O u)


-- @@ L51-61 verbatim
/-- The local tube inverse sends the orbit center back to its phase and zero
normal coordinate. -/
@[simp] theorem orbitTubeLocalInverse_center (O : V.OrbitIndex) (u : ℝ) :
    V.orbitTubeLocalInverse O u (V.intrinsicOrbitLift O u) =
      (u, (0 : N)) := by
  rw [← V.orbitTubeLift_zero O u]
  change (V.orbitTubeLocalHomeomorph O u).symm
      (V.orbitTubeLift O (u, (0 : N))) = (u, (0 : N))
  rw [← V.orbitTubeLocalHomeomorph_coe O u]
  exact (V.orbitTubeLocalHomeomorph O u).left_inv
    (V.orbitTube_center_mem_localSource O u)


-- @@ L63-86 verbatim
/-- The inverse tube coordinate is smooth at every point of the orbit zero
section. -/
theorem contDiffAt_orbitTubeLocalInverse_center
    (O : V.OrbitIndex) (u : ℝ) :
    ContDiffAt ℝ ∞ (V.orbitTubeLocalInverse O u)
      (V.intrinsicOrbitLift O u) := by
  let e := V.orbitTubeLocalHomeomorph O u
  have htarget : V.intrinsicOrbitLift O u ∈ e.target := by
    simpa [e] using V.orbitTube_center_mem_localTarget O u
  have hinverse : e.symm (V.intrinsicOrbitLift O u) =
      (u, (0 : N)) := by
    simpa [e, orbitTubeLocalInverse] using
      V.orbitTubeLocalInverse_center O u
  have hderiv : HasFDerivAt e
      (V.orbitTubeDerivEquiv O u : (ℝ × N) →L[ℝ] E)
      (e.symm (V.intrinsicOrbitLift O u)) := by
    rw [hinverse]
    simpa [e] using V.hasFDerivAt_orbitTubeLift_zero O u
  have hsmooth : ContDiffAt ℝ ∞ e
      (e.symm (V.intrinsicOrbitLift O u)) := by
    rw [hinverse]
    simpa [e] using (V.contDiff_orbitTubeLift O).contDiffAt
  change ContDiffAt ℝ ∞ e.symm (V.intrinsicOrbitLift O u)
  exact e.contDiffAt_symm htarget hderiv hsmooth


-- @@ L88-110 verbatim
/-- The derivative of the inverse tube coordinate at the zero section is the
inverse of the explicit tangent-normal frame equivalence. -/
theorem hasFDerivAt_orbitTubeLocalInverse_center
    (O : V.OrbitIndex) (u : ℝ) :
    HasFDerivAt (V.orbitTubeLocalInverse O u)
      ((V.orbitTubeDerivEquiv O u).symm : E →L[ℝ] (ℝ × N))
      (V.intrinsicOrbitLift O u) := by
  let e := V.orbitTubeLocalHomeomorph O u
  have htarget : V.intrinsicOrbitLift O u ∈ e.target := by
    simpa [e] using V.orbitTube_center_mem_localTarget O u
  have hinverse : e.symm (V.intrinsicOrbitLift O u) =
      (u, (0 : N)) := by
    simpa [e, orbitTubeLocalInverse] using
      V.orbitTubeLocalInverse_center O u
  have hderiv : HasFDerivAt e
      (V.orbitTubeDerivEquiv O u : (ℝ × N) →L[ℝ] E)
      (e.symm (V.intrinsicOrbitLift O u)) := by
    rw [hinverse]
    simpa [e] using V.hasFDerivAt_orbitTubeLift_zero O u
  change HasFDerivAt e.symm
    ((V.orbitTubeDerivEquiv O u).symm : E →L[ℝ] (ℝ × N))
    (V.intrinsicOrbitLift O u)
  exact e.hasFDerivAt_symm htarget hderiv


-- @@ L112-119 verbatim
/-- Consequently the Frechet derivative of the local inverse is available in
closed form at every point of the orbit. -/
@[simp] theorem fderiv_orbitTubeLocalInverse_center
    (O : V.OrbitIndex) (u : ℝ) :
    fderiv ℝ (V.orbitTubeLocalInverse O u)
      (V.intrinsicOrbitLift O u) =
      ((V.orbitTubeDerivEquiv O u).symm : E →L[ℝ] (ℝ × N)) := by
  exact (V.hasFDerivAt_orbitTubeLocalInverse_center O u).fderiv


-- @@ L121-121 verbatim
end TamedField

-- @@ L122-122 verbatim
end Submission
