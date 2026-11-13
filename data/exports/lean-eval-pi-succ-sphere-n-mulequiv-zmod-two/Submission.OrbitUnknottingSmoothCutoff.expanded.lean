import Mathlib
import Submission.OrbitUnknottingSupportNeighborhood


-- @@ L4-15 verbatim
/-!
# A smooth cutoff for one supported orbit move

The support neighborhood constructed in
`OrbitUnknottingSupportNeighborhood` can be realized as the support of a
smooth scalar cutoff.  The cutoff is identically one on the active source and
target circles, and is identically zero on a neighborhood of every other
source and target circle.

This is the analytic localization needed before extending a local orbit
motion to a compactly supported ambient vector field.
-/


-- @@ L17-17 verbatim
set_option autoImplicit false


-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
open Set Function Filter

-- @@ L22-22 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L24-24 verbatim
namespace Submission

-- @@ L25-25 verbatim
namespace OrbitUnknottingSupport


-- @@ L27-27 verbatim
variable {n : ℕ} {X : FramedLevelSet n} (V : TamedField X) (h2 : 2 ≤ n)


-- @@ L29-29 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L31-43 verbatim
/-- Smooth localization data for the move of one orbit.  The topological
support is separated from the complete finite obstacle configuration. -/
structure SmoothCutoffData (O : V.OrbitIndex) where
  radius : ℝ
  radius_pos : 0 < radius
  cutoff : E → ℝ
  contDiff_cutoff : ContDiff ℝ ∞ cutoff
  range_cutoff : Set.range cutoff ⊆ Set.Icc 0 1
  support_cutoff : Function.support cutoff =
    Metric.thickening radius (activeSet V h2 O)
  one_iff_active : ∀ x : E, x ∈ activeSet V h2 O ↔ cutoff x = 1
  tsupport_disjoint_obstacle :
    Disjoint (tsupport cutoff) (obstacleSet V h2 O)


-- @@ L45-66 verbatim
/-- A smooth `[0,1]`-valued cutoff, equal to one precisely on the active
source-and-target pair, whose topological support avoids all other pairs. -/
theorem exists_smoothCutoffData (O : V.OrbitIndex) :
    Nonempty (SmoothCutoffData V h2 O) := by
  obtain ⟨δ, hδ, hcore, hopen, hclosure⟩ :=
    exists_support_thickening V h2 O
  obtain ⟨χ, hχsmooth, hχrange, hχsupport, hχone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff
      (modelWithCornersSelf ℝ E) (n := ⊤) hopen
      (isCompact_activeSet V h2 O).isClosed hcore
  refine ⟨{
    radius := δ
    radius_pos := hδ
    cutoff := χ
    contDiff_cutoff := contMDiff_iff_contDiff.mp hχsmooth
    range_cutoff := hχrange
    support_cutoff := hχsupport
    one_iff_active := hχone
    tsupport_disjoint_obstacle := ?_
  }⟩
  rw [tsupport, hχsupport]
  exact hclosure


-- @@ L68-68 verbatim
namespace SmoothCutoffData


-- @@ L70-70 verbatim
variable {h2 : 2 ≤ n} {O : V.OrbitIndex}


-- @@ L72-74 verbatim
@[simp] theorem cutoff_eq_one_iff (C : SmoothCutoffData V h2 O) (x : E) :
    C.cutoff x = 1 ↔ x ∈ activeSet V h2 O :=
  (C.one_iff_active x).symm


-- @@ L76-78 verbatim
theorem cutoff_nonneg (C : SmoothCutoffData V h2 O) (x : E) :
    0 ≤ C.cutoff x :=
  C.range_cutoff ⟨x, rfl⟩ |>.1


-- @@ L80-82 verbatim
theorem cutoff_le_one (C : SmoothCutoffData V h2 O) (x : E) :
    C.cutoff x ≤ 1 :=
  C.range_cutoff ⟨x, rfl⟩ |>.2


-- @@ L84-90 verbatim
/-- The cutoff is compactly supported. -/
theorem isCompact_tsupport (C : SmoothCutoffData V h2 O) :
    IsCompact (tsupport C.cutoff) := by
  rw [tsupport, C.support_cutoff]
  exact (isCompact_activeSet V h2 O).cthickening.of_isClosed_subset
    isClosed_closure
    (Metric.closure_thickening_subset_cthickening C.radius _)


-- @@ L92-95 verbatim
theorem cutoff_eq_one_on_source (C : SmoothCutoffData V h2 O)
    {x : E} (hx : x ∈ (O : Set E)) :
    C.cutoff x = 1 :=
  (C.one_iff_active x).mp (Or.inl hx)


-- @@ L97-100 verbatim
theorem cutoff_eq_one_on_target (C : SmoothCutoffData V h2 O)
    {x : E} (hx : x ∈ CanonicalRoundOrbit.target V h2 O) :
    C.cutoff x = 1 :=
  (C.one_iff_active x).mp (Or.inr hx)


-- @@ L102-110 verbatim
/-- At every obstacle point the cutoff agrees with zero on a whole
neighborhood, not merely at that point. -/
theorem eventuallyEq_zero_of_mem_obstacle
    (C : SmoothCutoffData V h2 O) {x : E}
    (hx : x ∈ obstacleSet V h2 O) :
    C.cutoff =ᶠ[𝓝 x] 0 := by
  rw [← notMem_tsupport_iff_eventuallyEq]
  exact fun hxSupport =>
    Set.disjoint_left.mp C.tsupport_disjoint_obstacle hxSupport hx


-- @@ L112-119 verbatim
/-- Componentwise form of the neighborhood-zero conclusion for every other
source orbit. -/
theorem eventuallyEq_zero_on_other_source
    (C : SmoothCutoffData V h2 O) (P : V.OrbitIndex) (hPO : P ≠ O)
    {x : E} (hx : x ∈ (P : Set E)) :
    C.cutoff =ᶠ[𝓝 x] 0 :=
  eventuallyEq_zero_of_mem_obstacle (V := V) C
    (source_subset_obstacleSet V h2 O P hPO hx)


-- @@ L121-128 verbatim
/-- Componentwise form of the neighborhood-zero conclusion for every other
canonical target circle. -/
theorem eventuallyEq_zero_on_other_target
    (C : SmoothCutoffData V h2 O) (P : V.OrbitIndex) (hPO : P ≠ O)
    {x : E} (hx : x ∈ CanonicalRoundOrbit.target V h2 P) :
    C.cutoff =ᶠ[𝓝 x] 0 :=
  eventuallyEq_zero_of_mem_obstacle (V := V) C
    (target_subset_obstacleSet V h2 O P hPO hx)


-- @@ L130-130 verbatim
end SmoothCutoffData


-- @@ L132-132 verbatim
end OrbitUnknottingSupport

-- @@ L133-133 verbatim
end Submission
