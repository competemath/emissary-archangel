import Mathlib
import Submission.IntrinsicOrbitParam
import Submission.CanonicalRoundOrbitUnknotting


-- @@ L5-28 verbatim
/-!
# A support neighborhood for one orbit unknotting move

Fix one orbit `O`.  Its local ambient move must carry `O` to its assigned
canonical round target while fixing every other source orbit and every other
target.  This file constructs the first genuine geometric ingredient for that
move: an open support neighborhood of

`O ∪ canonicalTarget(O)`

whose closure avoids all other sources and targets.

The proof uses only geometry already available in the repository:

* every tamed-flow orbit is a compact embedded circle (with the canonical
  `intrinsicSimpleClosedOrbitParam`);
* the canonical round targets are compact and lie outside a ball containing
  the entire source fiber;
* distinct source orbits and distinct canonical targets are disjoint; and
* compact/closed disjoint subsets of a metric space have disjoint closed
  thickenings.

No ambient isotopy or isotopy-extension principle is assumed here.
-/


-- @@ L30-30 verbatim
set_option autoImplicit false


-- @@ L32-32 verbatim
noncomputable section


-- @@ L34-34 verbatim
open Set Function

-- @@ L35-35 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L37-37 verbatim
namespace Submission

-- @@ L38-38 verbatim
namespace OrbitUnknottingSupport


-- @@ L40-40 verbatim
variable {n : ℕ} {X : FramedLevelSet n} (V : TamedField X) (h2 : 2 ≤ n)


-- @@ L42-42 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L44-46 verbatim
/-- The compact core which the local move is allowed to change. -/
def activeSet (O : V.OrbitIndex) : Set E :=
  (O : Set E) ∪ CanonicalRoundOrbit.target V h2 O


-- @@ L48-51 verbatim
/-- Every source and target belonging to another orbit component. -/
def obstacleSet (O : V.OrbitIndex) : Set E :=
  ⋃ P ∈ (Finset.univ : Finset V.OrbitIndex).erase O,
    (P : Set E) ∪ CanonicalRoundOrbit.target V h2 P


-- @@ L53-56 verbatim
/-- The intrinsic once-around parametrization attached to the active source
circle.  This records the embedded-circle input to the later local move. -/
def intrinsicParam (O : V.OrbitIndex) : SimpleClosedOrbitParam X V :=
  V.intrinsicSimpleClosedOrbitParam O


-- @@ L58-62 verbatim
/-- An orbit-index source set is compact. -/
theorem isCompact_source (O : V.OrbitIndex) :
    IsCompact (O : Set E) := by
  rw [V.orbitPoint_orbit O]
  exact V.isCompact_orbit (V.orbitPoint_mem_fiber O)


-- @@ L64-66 verbatim
theorem isCompact_activeSet (O : V.OrbitIndex) :
    IsCompact (activeSet V h2 O) :=
  (isCompact_source V O).union (CanonicalRoundOrbit.isCompact_target V h2 O)


-- @@ L68-73 verbatim
theorem isCompact_obstacleSet (O : V.OrbitIndex) :
    IsCompact (obstacleSet V h2 O) := by
  apply ((Finset.univ : Finset V.OrbitIndex).erase O).isCompact_biUnion
  intro P hP
  exact (isCompact_source V P).union
    (CanonicalRoundOrbit.isCompact_target V h2 P)


-- @@ L75-80 verbatim
/-- A different source orbit is part of the obstacle set. -/
theorem source_subset_obstacleSet (O P : V.OrbitIndex) (hPO : P ≠ O) :
    (P : Set E) ⊆ obstacleSet V h2 O := by
  intro x hx
  exact Set.mem_iUnion₂.mpr
    ⟨P, by simp [hPO], Or.inl hx⟩


-- @@ L82-87 verbatim
/-- A different canonical target is part of the obstacle set. -/
theorem target_subset_obstacleSet (O P : V.OrbitIndex) (hPO : P ≠ O) :
    CanonicalRoundOrbit.target V h2 P ⊆ obstacleSet V h2 O := by
  intro x hx
  exact Set.mem_iUnion₂.mpr
    ⟨P, by simp [hPO], Or.inr hx⟩


-- @@ L89-120 verbatim
/-- The active source-and-target pair is disjoint from every other
source-and-target pair. -/
theorem activeSet_disjoint_obstacleSet (O : V.OrbitIndex) :
    Disjoint (activeSet V h2 O) (obstacleSet V h2 O) := by
  rw [Set.disjoint_left]
  intro x hxActive hxObstacle
  rcases hxActive with hxO | hxTargetO
  · have hxFiber : x ∈ X.fiber :=
      SmoothAmbientIsotopy.OrbitMoveFamily.orbit_subset_fiber O hxO
    obtain ⟨P, hPerase, hxP | hxTargetP⟩ :=
      Set.mem_iUnion₂.mp hxObstacle
    · have hPO : P ≠ O := by simpa using (Finset.mem_erase.mp hPerase).1
      have hsets : (O : Set E) ≠ (P : Set E) := by
        intro h
        exact hPO (Subtype.ext h).symm
      exact Set.disjoint_left.mp
        (V.orbitFinset_pairwise_disjoint O O.property P P.property hsets)
        hxO hxP
    · exact Set.disjoint_left.mp
        (CanonicalRoundOrbit.target_disjoint_fiber V h2 P)
        hxTargetP hxFiber
  · obtain ⟨P, hPerase, hxP | hxTargetP⟩ :=
      Set.mem_iUnion₂.mp hxObstacle
    · have hxFiber : x ∈ X.fiber :=
        SmoothAmbientIsotopy.OrbitMoveFamily.orbit_subset_fiber P hxP
      exact Set.disjoint_left.mp
        (CanonicalRoundOrbit.target_disjoint_fiber V h2 O)
        hxTargetO hxFiber
    · have hPO : P ≠ O := by simpa using (Finset.mem_erase.mp hPerase).1
      exact Set.disjoint_left.mp
        (CanonicalRoundOrbit.target_disjoint V h2 hPO.symm)
        hxTargetO hxTargetP


-- @@ L122-139 verbatim
/-- There is a positive-radius open support neighborhood of the active pair
whose closure misses the whole finite obstacle configuration. -/
theorem exists_support_thickening (O : V.OrbitIndex) :
    ∃ δ : ℝ, 0 < δ ∧
      activeSet V h2 O ⊆ Metric.thickening δ (activeSet V h2 O) ∧
      IsOpen (Metric.thickening δ (activeSet V h2 O)) ∧
      Disjoint (closure (Metric.thickening δ (activeSet V h2 O)))
        (obstacleSet V h2 O) := by
  have hactive := isCompact_activeSet V h2 O
  have hobstacle := isCompact_obstacleSet V h2 O
  have hdisjoint := activeSet_disjoint_obstacleSet V h2 O
  obtain ⟨δ, hδ, hclosed⟩ :=
    hdisjoint.exists_cthickenings hactive hobstacle.isClosed
  refine ⟨δ, hδ, Metric.self_subset_thickening hδ _,
    Metric.isOpen_thickening, ?_⟩
  exact hclosed.mono
    (Metric.closure_thickening_subset_cthickening δ _)
    (Metric.self_subset_cthickening _)


-- @@ L141-157 verbatim
/-- Componentwise form: the chosen support closure misses each other source
and each other target separately. -/
theorem exists_support_thickening_componentwise (O : V.OrbitIndex) :
    ∃ δ : ℝ, 0 < δ ∧
      activeSet V h2 O ⊆ Metric.thickening δ (activeSet V h2 O) ∧
      IsOpen (Metric.thickening δ (activeSet V h2 O)) ∧
      ∀ P : V.OrbitIndex, P ≠ O →
        Disjoint (closure (Metric.thickening δ (activeSet V h2 O)))
            (P : Set E) ∧
          Disjoint (closure (Metric.thickening δ (activeSet V h2 O)))
            (CanonicalRoundOrbit.target V h2 P) := by
  obtain ⟨δ, hδ, hcore, hopen, hdisjoint⟩ :=
    exists_support_thickening V h2 O
  refine ⟨δ, hδ, hcore, hopen, ?_⟩
  intro P hPO
  exact ⟨hdisjoint.mono_right (source_subset_obstacleSet V h2 O P hPO),
    hdisjoint.mono_right (target_subset_obstacleSet V h2 O P hPO)⟩


-- @@ L159-159 verbatim
end OrbitUnknottingSupport

-- @@ L160-160 verbatim
end Submission
