import Mathlib
import Submission.FiniteIFTSurfaceCover
import Submission.VerticalSlabTransport


-- @@ L5-13 verbatim
/-!
# Covering a vertically perturbed fiber by the original finite IFT atlas

The finite IFT cover is selected on the original compact slab fiber.  A small
vertical amplitude pulls the cobordism back through a global diffeomorphism.
The slab-fiber equivalence from `VerticalSlabTransport` therefore turns every
point of the perturbed fiber, and in particular every middle-slab critical
point, into a compact-core parameter of one of the original IFT charts.
-/


-- @@ L15-15 verbatim
noncomputable section


-- @@ L17-17 verbatim
open Set Function Metric

-- @@ L18-18 verbatim
open scoped RealInnerProductSpace ContDiff Topology


-- @@ L20-20 verbatim
namespace Submission


-- @@ L22-22 verbatim
variable {n : ℕ}


-- @@ L24-24 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

-- @@ L25-25 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L27-27 verbatim
namespace FiniteIFTSurfaceCover


-- @@ L29-29 verbatim
variable {C : FramedLevelCobordism n} {ι : Type*} [Fintype ι]


-- @@ L31-43 verbatim
/-- Every point of the pulled-back slab fiber is the inverse-diffeomorphic
image of a compact-core parameter in the original finite IFT cover. -/
theorem exists_pullback_chart_parameter (B : FiniteIFTSurfaceCover C ι)
    (a : SmallVerticalAmplitude (n := n)) {v : E'}
    (hv : v ∈ (a.toVerticalAmplitude.pullback C).fiber) :
    ∃ i : ι, ∃ u : E₂, u ∈ B.core i ∧
      a.diffeomorph.symm ((B.chart i).param u) = v := by
  have hw : verticalShift a v ∈ C.fiber := a.verticalShift_mem_fiber hv
  obtain ⟨i, u, hu, huv⟩ := B.exists_chart_parameter hw
  refine ⟨i, u, hu, ?_⟩
  rw [huv]
  change a.diffeomorph.symm (a.diffeomorph v) = v
  exact a.diffeomorph.symm_apply_apply v


-- @@ L45-56 verbatim
/-- Specialization to the compact global critical locus of the pulled-back
cobordism.  This discharges the topological coverage half of the later
`SignedMorseGeometry.coreCritical_cover` field; only the local Morse-coordinate
recentring remains there. -/
theorem exists_pullback_chart_parameter_of_coreCritical
    (B : FiniteIFTSurfaceCover C ι)
    (a : SmallVerticalAmplitude (n := n)) {v : E'}
    (hv : v ∈ coreCriticalPoints (a.toVerticalAmplitude.pullback C)) :
    ∃ i : ι, ∃ u : E₂, u ∈ B.core i ∧
      a.diffeomorph.symm ((B.chart i).param u) = v := by
  exact B.exists_pullback_chart_parameter a
    (coreCriticalPoints_subset_fiber _ hv)


-- @@ L58-69 verbatim
/-- Set-theoretic form: the full pulled-back slab fiber is covered by inverse
images of the finitely many compact chart cores. -/
theorem pullback_fiber_subset_iUnion_core_image
    (B : FiniteIFTSurfaceCover C ι)
    (a : SmallVerticalAmplitude (n := n)) :
    (a.toVerticalAmplitude.pullback C).fiber ⊆
      ⋃ i : ι, a.diffeomorph.symm '' (B.chart i).param '' B.core i := by
  intro v hv
  obtain ⟨i, u, hu, huv⟩ := B.exists_pullback_chart_parameter a hv
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  exact ⟨(B.chart i).param u, ⟨u, hu, rfl⟩, huv⟩


-- @@ L71-71 verbatim
end FiniteIFTSurfaceCover


-- @@ L73-73 verbatim
end Submission
