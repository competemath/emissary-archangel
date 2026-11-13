import Mathlib
import Submission.MorseGenericity2D


-- @@ L4-16 verbatim
/-!
# Finite IFT covers of a compact cobordism slab

This file isolates the compactness step between the pointwise implicit-function
theorem and the finite-chart Sard construction.  A `CompactIFTSurfacePatchAt`
is one genuine IFT chart together with a smaller compact parameter core whose
image covers the part of the slab fiber in an ambient open neighborhood of its
center.  Compactness of the slab fiber then extracts finitely many such patches.

No genericity or perturbation is used here.  The output is both the existing
`FiniteIFTSurfaceChartFamily` consumed by `MorseGenericity2D` and the additional
ambient cover statement needed by the later no-new-critical-points argument.
-/


-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-20 verbatim
open Set Function Metric

-- @@ L21-21 verbatim
open scoped RealInnerProductSpace ContDiff Topology


-- @@ L23-23 verbatim
namespace Submission


-- @@ L25-25 verbatim
variable {n : ℕ}


-- @@ L27-27 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

-- @@ L28-28 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L30-30 verbatim
namespace FramedLevelCobordism


-- @@ L32-36 verbatim
/-- The zero fiber restricted to the compact time slab is closed. -/
theorem isClosed_slabFiber (C : FramedLevelCobordism n) : IsClosed C.fiber := by
  rw [FramedLevelCobordism.fiber]
  exact (isClosed_singleton.preimage C.smooth.continuous).inter
    (isClosed_Icc.preimage contDiff_vertC.continuous)


-- @@ L38-41 verbatim
/-- Spatial boundedness and the bounded time coordinate make the slab fiber
compact. -/
theorem isCompact_slabFiber (C : FramedLevelCobordism n) : IsCompact C.fiber :=
  Metric.isCompact_of_isClosed_isBounded C.isClosed_slabFiber C.isBounded_fiber


-- @@ L43-43 verbatim
end FramedLevelCobordism


-- @@ L45-64 verbatim
/-- A point-centered IFT patch with a compact parameter core covering the
nearby part of the actual slab fiber. -/
structure CompactIFTSurfacePatchAt (C : FramedLevelCobordism n) (v : E') where
  /-- The globally represented, locally valid IFT chart. -/
  chart : IFTSurfaceChart C
  /-- Its distinguished center is the prescribed fiber point. -/
  chart_center : chart.center = v
  /-- Production IFT charts retain their genuine open parameter domain. -/
  chart_domain_open : IsOpen chart.domain
  /-- An ambient neighborhood on which the chart covers the fiber. -/
  ambient : Set E'
  ambient_open : IsOpen ambient
  center_mem_ambient : v ∈ ambient
  /-- A compact parameter core lying inside the chart's valid domain. -/
  core : Set E₂
  compact_core : IsCompact core
  core_subset_domain : core ⊆ chart.domain
  /-- Every slab-fiber point in the ambient neighborhood is represented by a
  parameter in the compact core. -/
  fiber_inter_ambient_subset : C.fiber ∩ ambient ⊆ chart.param '' core


-- @@ L66-74 verbatim
/-- A finite IFT family that also remembers the ambient neighborhoods covered
by its compact parameter cores. -/
structure FiniteIFTSurfaceCover (C : FramedLevelCobordism n)
    (ι : Type*) [Fintype ι] extends FiniteIFTSurfaceChartFamily C ι where
  domain_open : ∀ i, IsOpen (chart i).domain
  ambient : ι → Set E'
  ambient_open : ∀ i, IsOpen (ambient i)
  fiber_subset_ambient : C.fiber ⊆ ⋃ i, ambient i
  fiber_patch : ∀ i, C.fiber ∩ ambient i ⊆ (chart i).param '' core i


-- @@ L76-76 verbatim
namespace FiniteIFTSurfaceCover


-- @@ L78-78 verbatim
variable {C : FramedLevelCobordism n} {ι : Type*} [Fintype ι]


-- @@ L80-84 verbatim
/-- Forgetting the ambient coverage leaves exactly the finite family expected
by the finite-chart Sard theorem. -/
def toSurfaceChartFamily (B : FiniteIFTSurfaceCover C ι) :
    FiniteIFTSurfaceChartFamily C ι :=
  B.toFiniteIFTSurfaceChartFamily


-- @@ L86-93 verbatim
/-- Every point of the compact slab fiber is represented in the compact core
of one of the finitely many selected charts. -/
theorem exists_chart_parameter (B : FiniteIFTSurfaceCover C ι) {v : E'}
    (hv : v ∈ C.fiber) :
    ∃ i : ι, ∃ u : E₂, u ∈ B.core i ∧ (B.chart i).param u = v := by
  obtain ⟨i, hvi⟩ := Set.mem_iUnion.mp (B.fiber_subset_ambient hv)
  obtain ⟨u, hu, huv⟩ := B.fiber_patch i ⟨hv, hvi⟩
  exact ⟨i, u, hu, huv⟩


-- @@ L95-95 verbatim
end FiniteIFTSurfaceCover


-- @@ L97-127 verbatim
/-- Pointwise compact IFT patches admit a finite subcover of the cobordism
slab fiber.  The finite index type is the subtype of the selected `Finset` of
fiber points, so no arbitrary finite enumeration is introduced. -/
theorem exists_finiteIFTSurfaceCover_of_pointwise
    (C : FramedLevelCobordism n)
    (hlocal : ∀ v, v ∈ C.fiber → Nonempty (CompactIFTSurfacePatchAt C v)) :
    ∃ s : Finset C.fiber, Nonempty (FiniteIFTSurfaceCover C (↥s)) := by
  classical
  let patch : ∀ q : C.fiber, CompactIFTSurfacePatchAt C q.1 :=
    fun q => Classical.choice (hlocal q.1 q.2)
  have hcover : C.fiber ⊆ ⋃ q : C.fiber, (patch q).ambient := by
    intro v hv
    exact Set.mem_iUnion.mpr
      ⟨⟨v, hv⟩, (patch ⟨v, hv⟩).center_mem_ambient⟩
  obtain ⟨s, hs⟩ := C.isCompact_slabFiber.elim_finite_subcover
    (fun q : C.fiber => (patch q).ambient)
    (fun q => (patch q).ambient_open) hcover
  refine ⟨s, ⟨{
    chart := fun i => (patch i.1).chart
    core := fun i => (patch i.1).core
    compact_core := fun i => (patch i.1).compact_core
    core_subset_domain := fun i => (patch i.1).core_subset_domain
    domain_open := fun i => (patch i.1).chart_domain_open
    ambient := fun i => (patch i.1).ambient
    ambient_open := fun i => (patch i.1).ambient_open
    fiber_subset_ambient := ?_
    fiber_patch := fun i => (patch i.1).fiber_inter_ambient_subset
  }⟩⟩
  intro v hv
  obtain ⟨q, hqs, hvq⟩ := Set.mem_iUnion₂.mp (hs hv)
  exact Set.mem_iUnion.mpr ⟨⟨q, hqs⟩, hvq⟩


-- @@ L129-129 verbatim
end Submission
