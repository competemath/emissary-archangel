import Mathlib
import Submission.CanonicalRoundOrbitUnknotting
import Submission.OrbitUnknottingFourierEmbeddingTrack
import Submission.OrbitUnknottingSupportNeighborhood


-- @@ L6-20 verbatim
/-!
# Assembly of relative orbit moves

The analytic isotopy-extension argument is naturally local to one orbit.  Its
use by the normalization pipeline is global: one move is required for every
component, and different moves must fix each other's source and assigned
target circles.  This file isolates that purely formal assembly step.

For one orbit, `RelativeCanonicalOrbitMove` records only the endpoint on the
period-one intrinsic lift and fixedness on the already-defined finite obstacle
set.  Those two statements imply the set-level endpoint and mutual-relative
contracts of `SupportedCanonicalRoundUnknotting`.  Thus the remaining
geometric construction may work one orbit at a time without repeating any
finite-component bookkeeping.
-/


-- @@ L22-22 verbatim
set_option autoImplicit false


-- @@ L24-24 verbatim
noncomputable section


-- @@ L26-26 verbatim
open Set Function

-- @@ L27-27 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L29-29 verbatim
namespace Submission

-- @@ L30-30 verbatim
namespace TamedField


-- @@ L32-32 verbatim
variable {n : ℕ} {X : FramedLevelSet n} (V : TamedField X)


-- @@ L34-34 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L36-43 verbatim
/-- A complete relative ambient realization for one selected orbit. -/
structure RelativeCanonicalOrbitMove (h2 : 2 ≤ n) (O : V.OrbitIndex) where
  move : SmoothAmbientIsotopy n
  endpoint_lift : ∀ u : ℝ,
    move.forward 1 (V.intrinsicOrbitLift O u) =
      FourierEmbeddingTrack.targetLift (V := V) h2 O u
  fixed_obstacle : move.FixedOn
    (OrbitUnknottingSupport.obstacleSet V h2 O)


-- @@ L45-45 verbatim
variable {V} {h2 : 2 ≤ n} {O : V.OrbitIndex}


-- @@ L47-47 verbatim
namespace RelativeCanonicalOrbitMove


-- @@ L49-49 verbatim
variable (M : V.RelativeCanonicalOrbitMove h2 O)


-- @@ L51-69 verbatim
/-- Pointwise endpoint control on real lifts gives the required image equality
between the source orbit and its canonical quotient-circle target. -/
theorem endpoint_image :
    M.move.forward 1 '' (O : Set E) =
      CanonicalRoundOrbit.target V h2 O := by
  rw [← V.range_intrinsicOrbitEmbedding O]
  ext y
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective a
    rw [V.intrinsicOrbitEmbedding_coe, M.endpoint_lift,
      FourierEmbeddingTrack.targetLift_eq_circlePoint]
    exact ⟨(u : AddCircle (1 : ℝ)), rfl⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective a
    refine ⟨V.intrinsicOrbitEmbedding O (u : AddCircle (1 : ℝ)),
      ⟨(u : AddCircle (1 : ℝ)), rfl⟩, ?_⟩
    rw [V.intrinsicOrbitEmbedding_coe, M.endpoint_lift,
      FourierEmbeddingTrack.targetLift_eq_circlePoint]


-- @@ L71-83 verbatim
/-- The obstacle fixedness contract simultaneously fixes any chosen other
source orbit and its assigned target. -/
theorem fixedOn_other_source_union_target
    (P : V.OrbitIndex) (hPO : P ≠ O) :
    M.move.FixedOn
      ((P : Set E) ∪ CanonicalRoundOrbit.target V h2 P) := by
  apply M.fixed_obstacle.mono
  intro x hx
  rcases hx with hx | hx
  · exact OrbitUnknottingSupport.source_subset_obstacleSet
      V h2 O P hPO hx
  · exact OrbitUnknottingSupport.target_subset_obstacleSet
      V h2 O P hPO hx


-- @@ L85-85 verbatim
end RelativeCanonicalOrbitMove


-- @@ L87-101 verbatim
/-- Choose one completed local realization for every orbit and assemble the
global componentwise unknotting input consumed by the finite ambient schedule.
No compatibility choice remains: obstacle fixedness proves it automatically. -/
def supportedCanonicalRoundUnknottingOfRelativeMoves
    (V : TamedField X) (h2 : 2 ≤ n)
    (realize : ∀ O : V.OrbitIndex,
      Nonempty (V.RelativeCanonicalOrbitMove h2 O)) :
    SmoothAmbientIsotopy.SupportedCanonicalRoundUnknotting
      (X := X) (V := V) h2 where
  move O := (realize O).some.move
  endpoint_image O := (realize O).some.endpoint_image
  mutuallyRelative O P hOP := by
    exact ⟨
      (realize O).some.fixedOn_other_source_union_target P hOP.symm,
      (realize P).some.fixedOn_other_source_union_target O hOP⟩


-- @@ L103-103 verbatim
end TamedField

-- @@ L104-104 verbatim
end Submission

