import Mathlib
import Submission.LocalIFTSurfaceChart
import Submission.FiniteIFTSurfaceCover


-- @@ L5-12 verbatim
/-!
# Existence of finite IFT surface covers

`LocalIFTSurfaceChart` constructs a compact-core chart neighborhood at every
regular zero of a framed cobordism.  Every zero of a `FramedLevelCobordism` is
regular by definition, so these pointwise neighborhoods feed directly into the
compact finite-subcover theorem of `FiniteIFTSurfaceCover`.
-/


-- @@ L14-14 verbatim
noncomputable section


-- @@ L16-16 verbatim
open Set Function Metric

-- @@ L17-17 verbatim
open scoped RealInnerProductSpace ContDiff Topology


-- @@ L19-19 verbatim
namespace Submission


-- @@ L21-21 verbatim
variable {n : ℕ}


-- @@ L23-23 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L25-25 verbatim
namespace LocalIFTSurfaceChart


-- @@ L27-46 verbatim
/-- Convert the explicit local IFT neighborhood at a slab-fiber point into the
generic compact patch interface used by finite subcover extraction. -/
def compactPatchAt (C : FramedLevelCobordism n) {v : E'}
    (hv : v ∈ C.fiber) : CompactIFTSurfacePatchAt C v := by
  let N := localChartNeighborhood C hv.1
  exact {
    chart := N.chart
    chart_center := N.chart_center
    chart_domain_open := by
      exact LocalIFTSurfaceChart.isOpen_chartDomain C (C.regular v hv.1)
    ambient := N.ambient
    ambient_open := N.ambient_open
    center_mem_ambient := N.center_mem_ambient
    core := N.core
    compact_core := N.compact_core
    core_subset_domain := N.core_subset_domain
    fiber_inter_ambient_subset := by
      intro x hx
      exact N.fiber_ambient_subset_param_core ⟨hx.1.1, hx.2⟩
  }


-- @@ L48-51 verbatim
/-- Every point of the compact slab fiber has a compact-core IFT patch. -/
theorem nonempty_compactPatchAt (C : FramedLevelCobordism n) {v : E'}
    (hv : v ∈ C.fiber) : Nonempty (CompactIFTSurfacePatchAt C v) :=
  ⟨compactPatchAt C hv⟩


-- @@ L53-53 verbatim
end LocalIFTSurfaceChart


-- @@ L55-61 verbatim
/-- Every framed level cobordism admits a finite IFT surface cover of its whole
compact time-slab fiber. -/
theorem exists_finiteIFTSurfaceCover (C : FramedLevelCobordism n) :
    ∃ s : Finset C.fiber, Nonempty (FiniteIFTSurfaceCover C (↥s)) := by
  apply exists_finiteIFTSurfaceCover_of_pointwise C
  intro v hv
  exact LocalIFTSurfaceChart.nonempty_compactPatchAt C hv


-- @@ L63-63 verbatim
end Submission
