import Submission.ProductionMorseSaddleSupply
import Submission.ProductionMorseSaddleExteriorClassification


-- @@ L4-17 verbatim
/-!
# Exterior source families at production saddles

The full-radius saddle classification identifies every orbit meeting the local
cover with one of the two distinguished branch orbits.  This file packages the
immediate consequence needed by the critical-flow construction: every orbit
in either reduced merge/split source family lies in the chronological exterior
orbit collection, and its ambientized points lie in the whole exterior slab
core.

For a split the two negative branch indices are globally equal.  That equality
is the only topology input needed to turn deletion of one representative into
avoidance of both local branches.
-/


-- @@ L19-19 verbatim
set_option autoImplicit false

-- @@ L20-20 verbatim
set_option maxHeartbeats 2400000


-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
open Set Function


-- @@ L26-26 verbatim
namespace Submission


-- @@ L28-28 verbatim
variable {n : ℕ}


-- @@ L30-30 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L31-31 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L33-33 verbatim
variable {X₀ X₁ : FramedLevelSet n}

-- @@ L34-34 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}

-- @@ L35-35 verbatim
variable {SC : SignedFramedLevelCobordism S₀ S₁}


-- @@ L37-37 verbatim
namespace ValueSeparatedSignedMorsePackage


-- @@ L39-59 verbatim
/-- Every orbit retained by the merge source family avoids both local
negative-side saddle branches and hence the entire event-cover ball. -/
theorem chronologicalSaddleMergeSourceOrbit_mem_exterior
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (O : (D.chronologicalBeforeField t ht).OrbitIndex)
    (hO : (O : Set E₁) ∈
      D.chronologicalSaddleMergeExteriorSourceFamily t ht hindex) :
    (O : Set E₁) ∈ D.chronologicalExteriorOrbitCollection t ht
      (D.chronologicalBeforeTime t ht) := by
  have hneNegative : (O : Set E₁) ≠
      ((D.chronologicalSaddleNegativeOrbit t ht hindex .negative :
        (D.chronologicalBeforeField t ht).OrbitIndex) : Set E₁) := by
    simpa only [Set.mem_singleton_iff] using hO.1.2
  have hnePositive : (O : Set E₁) ≠
      ((D.chronologicalSaddleNegativeOrbit t ht hindex .positive :
        (D.chronologicalBeforeField t ht).OrbitIndex) : Set E₁) := by
    simpa only [Set.mem_singleton_iff] using hO.2
  exact D.chronologicalSaddleBeforeOrbit_mem_exterior_of_ne_branches
    t ht hindex O hnePositive hneNegative


-- @@ L61-93 verbatim
/-- On the split side the two negative local branches are one global orbit.
Deleting its chosen negative representative therefore excludes both local
branches from the retained source family. -/
theorem chronologicalSaddleSplitSourceOrbit_mem_exterior
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (hbranches :
      D.chronologicalSaddleNegativeOrbit t ht hindex .negative =
        D.chronologicalSaddleNegativeOrbit t ht hindex .positive)
    (O : (D.chronologicalBeforeField t ht).OrbitIndex)
    (hO : (O : Set E₁) ∈
      D.chronologicalSaddleSplitExteriorSourceFamily t ht hindex) :
    (O : Set E₁) ∈ D.chronologicalExteriorOrbitCollection t ht
      (D.chronologicalBeforeTime t ht) := by
  have hneNegative : (O : Set E₁) ≠
      ((D.chronologicalSaddleNegativeOrbit t ht hindex .negative :
        (D.chronologicalBeforeField t ht).OrbitIndex) : Set E₁) := by
    simpa only [Set.mem_singleton_iff] using hO.2
  have hbranchSets :
      ((D.chronologicalSaddleNegativeOrbit t ht hindex .negative :
        (D.chronologicalBeforeField t ht).OrbitIndex) : Set E₁) =
      ((D.chronologicalSaddleNegativeOrbit t ht hindex .positive :
        (D.chronologicalBeforeField t ht).OrbitIndex) : Set E₁) :=
    congrArg (fun Q : (D.chronologicalBeforeField t ht).OrbitIndex =>
      (Q : Set E₁)) hbranches
  have hnePositive : (O : Set E₁) ≠
      ((D.chronologicalSaddleNegativeOrbit t ht hindex .positive :
        (D.chronologicalBeforeField t ht).OrbitIndex) : Set E₁) := by
    intro h
    exact hneNegative (h.trans hbranchSets.symm)
  exact D.chronologicalSaddleBeforeOrbit_mem_exterior_of_ne_branches
    t ht hindex O hnePositive hneNegative


-- @@ L95-122 verbatim
/-- Exact-before-field specialization of ambientization into the whole
exterior slab.  Keeping the field definition fixed avoids dependent
elaboration through an arbitrary propositionally equal slice field. -/
theorem chronologicalSaddleBeforeOrbitPoint_mem_exteriorSlabCore
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (O : (D.chronologicalBeforeField t ht).OrbitIndex)
    {x : E₁} (hx : x ∈ (O : Set E₁))
    (hexterior : (O : Set E₁) ∈
      D.chronologicalExteriorOrbitCollection t ht
        (D.chronologicalBeforeTime t ht)) :
    cobSpaceTime x (D.chronologicalBeforeTime t ht) ∈
      D.chronologicalExteriorSlabCore t ht := by
  rw [chronologicalExteriorSlabCore]
  refine ⟨⟨?_, ?_⟩, hexterior x hx⟩
  · have hxFiber : x ∈ (D.chronologicalBeforeSlice t ht).fiber := by
      apply (D.chronologicalBeforeField t ht).orbit_subset_fiber
        ((D.chronologicalBeforeField t ht).orbitPoint_mem_fiber O)
      rwa [← (D.chronologicalBeforeField t ht).orbitPoint_orbit O]
    rw [chronologicalBeforeSlice,
      SlabTamedField.sliceFLSAt_fiber] at hxFiber
    exact hxFiber
  · change tcoord (cobSpaceTime x (D.chronologicalBeforeTime t ht)) ∈ Set.Icc
      (D.position.eventBracket t ht).before
      (D.position.eventBracket t ht).after
    rw [tcoord_spaceTime]
    have hb := D.chronologicalBeforeTime_mem_bracket t ht
    exact ⟨hb.1.le, hb.2.le⟩


-- @@ L124-138 verbatim
/-- Ambient points on every merge-source orbit lie in the compactly
controlled exterior event slab. -/
theorem chronologicalSaddleMergeSourcePoint_mem_exteriorSlabCore
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (O : {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
      (D.chronologicalSaddleMergeExteriorSourceFamily t ht hindex)})
    {x : E₁} (hx : x ∈ (O.1 : Set E₁)) :
    cobSpaceTime x (D.chronologicalBeforeTime t ht) ∈
      D.chronologicalExteriorSlabCore t ht := by
  apply D.chronologicalSaddleBeforeOrbitPoint_mem_exteriorSlabCore
    t ht O.1 hx
  apply D.chronologicalSaddleMergeSourceOrbit_mem_exterior t ht hindex O.1
  exact ((D.chronologicalBeforeField t ht).mem_selectedOrbitFinset O.1).mp O.2


-- @@ L140-158 verbatim
/-- Split analogue, using the global equality of the two incoming local
branch indices. -/
theorem chronologicalSaddleSplitSourcePoint_mem_exteriorSlabCore
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (hbranches :
      D.chronologicalSaddleNegativeOrbit t ht hindex .negative =
        D.chronologicalSaddleNegativeOrbit t ht hindex .positive)
    (O : {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
      (D.chronologicalSaddleSplitExteriorSourceFamily t ht hindex)})
    {x : E₁} (hx : x ∈ (O.1 : Set E₁)) :
    cobSpaceTime x (D.chronologicalBeforeTime t ht) ∈
      D.chronologicalExteriorSlabCore t ht := by
  apply D.chronologicalSaddleBeforeOrbitPoint_mem_exteriorSlabCore
    t ht O.1 hx
  apply D.chronologicalSaddleSplitSourceOrbit_mem_exterior
    t ht hindex hbranches O.1
  exact ((D.chronologicalBeforeField t ht).mem_selectedOrbitFinset O.1).mp O.2


-- @@ L160-160 verbatim
end ValueSeparatedSignedMorsePackage


-- @@ L162-162 verbatim
end Submission
