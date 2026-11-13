import Submission.ProductionMorseSaddleLocalExcision


-- @@ L3-15 verbatim
/-!
# Exterior classification at production saddle slices

The full-radius local saddle theorem says that the portion of either nearby
regular slice inside the complete event-cover ball lies in the union of the
two distinguished branch orbits.  This file specializes that theorem to the
chronological production slices.

Consequently, any orbit different from both distinguished branch orbits is
entirely outside the open cover ball.  This is the direct saddle analogue of
the definite-event exterior classifications used by the canonical exterior
flow construction.
-/


-- @@ L17-17 verbatim
set_option autoImplicit false

-- @@ L18-18 verbatim
set_option maxHeartbeats 2400000


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
open Set Function Metric

-- @@ L23-23 verbatim
open scoped RealInnerProductSpace Topology unitInterval


-- @@ L25-25 verbatim
namespace Submission


-- @@ L27-27 verbatim
variable {n : ℕ}


-- @@ L29-29 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L31-31 verbatim
variable {X₀ X₁ : FramedLevelSet n}

-- @@ L32-32 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}

-- @@ L33-33 verbatim
variable {SC : SignedFramedLevelCobordism S₀ S₁}


-- @@ L35-35 verbatim
namespace ValueSeparatedSignedMorsePackage


-- @@ L37-65 verbatim
/-- Every covered point on the chronological positive saddle slice belongs
to one of its two distinguished positive-branch orbits. -/
theorem chronologicalSaddleAfterCoveredSliceFiber_subset_union_orbits
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle) :
    (D.position.eventModel t ht).coveredSliceFiber
        (D.chronologicalAfterTime t ht) ⊆
      ((D.chronologicalSaddlePositiveOrbit t ht hindex .positive :
        (D.chronologicalAfterField t ht).OrbitIndex) : Set E₁) ∪
      ((D.chronologicalSaddlePositiveOrbit t ht hindex .negative :
        (D.chronologicalAfterField t ht).OrbitIndex) : Set E₁) := by
  let T := D.chronologicalEventEmbeddedShrink t ht
  let rho := D.chronologicalSaddleBoundaryRadius t ht
  let a := D.chronologicalWindowRadius t ht
  have H := T.saddlePositive_coveredSliceFiber_subset_union_orbits_full
    (D.chronologicalEventFullRadiusSmooth t ht) hindex rho a
    (D.chronologicalSaddleBoundaryRadius_pos t ht)
    (D.chronologicalWindowRadius_pos t ht)
    (D.chronologicalWindowRadius_sq_lt_saddleBoundaryRadius_sq t ht)
    ((D.chronologicalSaddleBoundaryRadius_lt_embedded t ht).trans_le
      T.radius_le)
    (D.chronologicalAfterTime_regular t ht)
    (D.chronologicalAfterField t ht)
  simpa only [chronologicalAfterTime, chronologicalAfterSlice,
    StandardMorseEventAt.EmbeddedShrink.saddlePositiveSlice,
    chronologicalSaddlePositiveOrbit,
    StandardMorseEventAt.EmbeddedShrink.saddlePositiveBranchOrbitIndex_coe]
    using H


-- @@ L67-95 verbatim
/-- Every covered point on the chronological negative saddle slice belongs
to one of its two distinguished negative-branch orbits. -/
theorem chronologicalSaddleBeforeCoveredSliceFiber_subset_union_orbits
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle) :
    (D.position.eventModel t ht).coveredSliceFiber
        (D.chronologicalBeforeTime t ht) ⊆
      ((D.chronologicalSaddleNegativeOrbit t ht hindex .positive :
        (D.chronologicalBeforeField t ht).OrbitIndex) : Set E₁) ∪
      ((D.chronologicalSaddleNegativeOrbit t ht hindex .negative :
        (D.chronologicalBeforeField t ht).OrbitIndex) : Set E₁) := by
  let T := D.chronologicalEventEmbeddedShrink t ht
  let rho := D.chronologicalSaddleBoundaryRadius t ht
  let a := D.chronologicalWindowRadius t ht
  have H := T.saddleNegative_coveredSliceFiber_subset_union_orbits_full
    (D.chronologicalEventFullRadiusSmooth t ht) hindex rho a
    (D.chronologicalSaddleBoundaryRadius_pos t ht)
    (D.chronologicalWindowRadius_pos t ht)
    (D.chronologicalWindowRadius_sq_lt_saddleBoundaryRadius_sq t ht)
    ((D.chronologicalSaddleBoundaryRadius_lt_embedded t ht).trans_le
      T.radius_le)
    (D.chronologicalBeforeTime_regular t ht)
    (D.chronologicalBeforeField t ht)
  simpa only [chronologicalBeforeTime, chronologicalBeforeSlice,
    StandardMorseEventAt.EmbeddedShrink.saddleNegativeSlice,
    chronologicalSaddleNegativeOrbit,
    StandardMorseEventAt.EmbeddedShrink.saddleNegativeBranchOrbitIndex_coe]
    using H


-- @@ L97-152 verbatim
/-- An orbit on the chronological negative slice which is different from
both local saddle branch orbits lies entirely outside the event-cover ball. -/
theorem chronologicalSaddleBeforeOrbit_mem_exterior_of_ne_branches
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (O : (D.chronologicalBeforeField t ht).OrbitIndex)
    (hnePositive : (O : Set E₁) ≠
      ((D.chronologicalSaddleNegativeOrbit t ht hindex .positive :
        (D.chronologicalBeforeField t ht).OrbitIndex) : Set E₁))
    (hneNegative : (O : Set E₁) ≠
      ((D.chronologicalSaddleNegativeOrbit t ht hindex .negative :
        (D.chronologicalBeforeField t ht).OrbitIndex) : Set E₁)) :
    (O : Set E₁) ∈ D.chronologicalExteriorOrbitCollection t ht
      (D.chronologicalBeforeTime t ht) := by
  intro x hxO
  by_contra houtside
  have hxFiber : x ∈ (D.chronologicalBeforeSlice t ht).fiber := by
    apply (D.chronologicalBeforeField t ht).orbit_subset_fiber
      ((D.chronologicalBeforeField t ht).orbitPoint_mem_fiber O)
    rwa [← (D.chronologicalBeforeField t ht).orbitPoint_orbit O]
  have hxzero : D.signedOutput.cobordism.G
      (cobSpaceTime x (D.chronologicalBeforeTime t ht)) = 0 := by
    rw [chronologicalBeforeSlice,
      SlabTamedField.sliceFLSAt_fiber] at hxFiber
    exact hxFiber
  have hxCovered : x ∈ (D.position.eventModel t ht).coveredSliceFiber
      (D.chronologicalBeforeTime t ht) :=
    ⟨lt_of_not_ge houtside, hxzero⟩
  have hxLocal :=
    D.chronologicalSaddleBeforeCoveredSliceFiber_subset_union_orbits
      t ht hindex hxCovered
  have hxO' : x ∈ (D.chronologicalBeforeField t ht).orbit
      ((D.chronologicalBeforeField t ht).orbitPoint O) := by
    rwa [← (D.chronologicalBeforeField t ht).orbitPoint_orbit O]
  rcases hxLocal with hxPositive | hxNegative
  · apply hnePositive
    calc
      (O : Set E₁) = (D.chronologicalBeforeField t ht).orbit
          ((D.chronologicalBeforeField t ht).orbitPoint O) :=
        (D.chronologicalBeforeField t ht).orbitPoint_orbit O
      _ = (D.chronologicalBeforeField t ht).orbit x :=
        ((D.chronologicalBeforeField t ht).orbit_eq_of_mem hxO').symm
      _ = ((D.chronologicalSaddleNegativeOrbit t ht hindex .positive :
          (D.chronologicalBeforeField t ht).OrbitIndex) : Set E₁) :=
        (D.chronologicalBeforeField t ht).orbit_eq_of_mem hxPositive
  · apply hneNegative
    calc
      (O : Set E₁) = (D.chronologicalBeforeField t ht).orbit
          ((D.chronologicalBeforeField t ht).orbitPoint O) :=
        (D.chronologicalBeforeField t ht).orbitPoint_orbit O
      _ = (D.chronologicalBeforeField t ht).orbit x :=
        ((D.chronologicalBeforeField t ht).orbit_eq_of_mem hxO').symm
      _ = ((D.chronologicalSaddleNegativeOrbit t ht hindex .negative :
          (D.chronologicalBeforeField t ht).OrbitIndex) : Set E₁) :=
        (D.chronologicalBeforeField t ht).orbit_eq_of_mem hxNegative


-- @@ L154-209 verbatim
/-- An orbit on the chronological positive slice which is different from
both local saddle branch orbits lies entirely outside the event-cover ball. -/
theorem chronologicalSaddleAfterOrbit_mem_exterior_of_ne_branches
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (O : (D.chronologicalAfterField t ht).OrbitIndex)
    (hnePositive : (O : Set E₁) ≠
      ((D.chronologicalSaddlePositiveOrbit t ht hindex .positive :
        (D.chronologicalAfterField t ht).OrbitIndex) : Set E₁))
    (hneNegative : (O : Set E₁) ≠
      ((D.chronologicalSaddlePositiveOrbit t ht hindex .negative :
        (D.chronologicalAfterField t ht).OrbitIndex) : Set E₁)) :
    (O : Set E₁) ∈ D.chronologicalExteriorOrbitCollection t ht
      (D.chronologicalAfterTime t ht) := by
  intro x hxO
  by_contra houtside
  have hxFiber : x ∈ (D.chronologicalAfterSlice t ht).fiber := by
    apply (D.chronologicalAfterField t ht).orbit_subset_fiber
      ((D.chronologicalAfterField t ht).orbitPoint_mem_fiber O)
    rwa [← (D.chronologicalAfterField t ht).orbitPoint_orbit O]
  have hxzero : D.signedOutput.cobordism.G
      (cobSpaceTime x (D.chronologicalAfterTime t ht)) = 0 := by
    rw [chronologicalAfterSlice,
      SlabTamedField.sliceFLSAt_fiber] at hxFiber
    exact hxFiber
  have hxCovered : x ∈ (D.position.eventModel t ht).coveredSliceFiber
      (D.chronologicalAfterTime t ht) :=
    ⟨lt_of_not_ge houtside, hxzero⟩
  have hxLocal :=
    D.chronologicalSaddleAfterCoveredSliceFiber_subset_union_orbits
      t ht hindex hxCovered
  have hxO' : x ∈ (D.chronologicalAfterField t ht).orbit
      ((D.chronologicalAfterField t ht).orbitPoint O) := by
    rwa [← (D.chronologicalAfterField t ht).orbitPoint_orbit O]
  rcases hxLocal with hxPositive | hxNegative
  · apply hnePositive
    calc
      (O : Set E₁) = (D.chronologicalAfterField t ht).orbit
          ((D.chronologicalAfterField t ht).orbitPoint O) :=
        (D.chronologicalAfterField t ht).orbitPoint_orbit O
      _ = (D.chronologicalAfterField t ht).orbit x :=
        ((D.chronologicalAfterField t ht).orbit_eq_of_mem hxO').symm
      _ = ((D.chronologicalSaddlePositiveOrbit t ht hindex .positive :
          (D.chronologicalAfterField t ht).OrbitIndex) : Set E₁) :=
        (D.chronologicalAfterField t ht).orbit_eq_of_mem hxPositive
  · apply hneNegative
    calc
      (O : Set E₁) = (D.chronologicalAfterField t ht).orbit
          ((D.chronologicalAfterField t ht).orbitPoint O) :=
        (D.chronologicalAfterField t ht).orbitPoint_orbit O
      _ = (D.chronologicalAfterField t ht).orbit x :=
        ((D.chronologicalAfterField t ht).orbit_eq_of_mem hxO').symm
      _ = ((D.chronologicalSaddlePositiveOrbit t ht hindex .negative :
          (D.chronologicalAfterField t ht).OrbitIndex) : Set E₁) :=
        (D.chronologicalAfterField t ht).orbit_eq_of_mem hxNegative


-- @@ L211-211 verbatim
end ValueSeparatedSignedMorsePackage


-- @@ L213-213 verbatim
end Submission
