import Submission.ProductionMorseDefiniteCanonicalPairingAdapter


-- @@ L3-17 verbatim
/-!
# Reverse-flow audit for definite component balance

This audit records the reverse-flow facts that are already supported by the
whole exterior-slab API.  It intentionally stops before constructing a
`CanonicalCriticalExteriorFlowCore` with negative time step: that structure
computes its endpoint slices as `t - ε` and `t + ε`, whereas the production
fields are indexed by `chronologicalAfterTime` and `chronologicalBeforeTime`.
For negative `ε` those slices are propositionally, but not definitionally,
equal.  A valid reverse core therefore needs explicit transport equivalences
for the two tamed fields and their selected-orbit subtypes.

No reverse component map or cardinality equality is asserted here until that
transport layer is supplied and checked by Lean.
-/


-- @@ L19-19 verbatim
set_option autoImplicit false

-- @@ L20-20 verbatim
set_option maxHeartbeats 2400000


-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
open Set Function

-- @@ L25-25 verbatim
open scoped RealInnerProductSpace Topology unitInterval


-- @@ L27-27 verbatim
namespace Submission


-- @@ L29-29 verbatim
variable {a : ℕ}

-- @@ L30-30 verbatim
variable {X₀ X₁ : FramedLevelSet (a + 2)}

-- @@ L31-31 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}

-- @@ L32-32 verbatim
variable {SC : SignedFramedLevelCobordism S₀ S₁}


-- @@ L34-34 verbatim
local notation "Eₐ" => EuclideanSpace ℝ (Fin (a + 3))


-- @@ L36-36 verbatim
namespace ValueSeparatedSignedMorsePackage


-- @@ L38-63 verbatim
/-- Ambientizing an orbit point at either inner chronological slice puts it
in the whole exterior slab whenever its orbit is outside the local cover. -/
theorem chronologicalOrbitPoint_mem_exteriorSlabCore
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (s : ℝ)
    (hs : s ∈ Set.Icc (D.position.eventBracket t ht).before
      (D.position.eventBracket t ht).after)
    (hreg : sliceRegular D.signedOutput.cobordism.G s)
    (V : TamedField (SlabTamedField.sliceFLSAt
      D.signedOutput.cobordism.toLevelCobordismData s
      hreg))
    (O : V.OrbitIndex) {x : Eₐ} (hx : x ∈ (O : Set Eₐ))
    (hexterior : (O : Set Eₐ) ∈
      D.chronologicalExteriorOrbitCollection t ht s) :
    cobSpaceTime x s ∈ D.chronologicalExteriorSlabCore t ht := by
  rw [chronologicalExteriorSlabCore]
  refine ⟨⟨?_, ?_⟩, hexterior x hx⟩
  · have hxFiber : x ∈
        (SlabTamedField.sliceFLSAt
          D.signedOutput.cobordism.toLevelCobordismData s
          hreg).fiber := by
      apply V.orbit_subset_fiber (V.orbitPoint_mem_fiber O)
      rwa [← V.orbitPoint_orbit O]
    rwa [SlabTamedField.sliceFLSAt_fiber] at hxFiber
  · simpa using hs


-- @@ L65-125 verbatim
/-- Any safe shift from a point of the whole exterior slab to the critical
time lands in the compact critical exterior.  The shift may have either sign. -/
theorem chronologicalDefiniteExteriorShift_mem
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .minimum ∨
      (D.position.eventModel t ht).index = .maximum)
    {p : EuclideanSpace ℝ (Fin ((a + 2) + 2))} {s : ℝ}
    (hp : p ∈ D.chronologicalExteriorSlabCore t ht)
    (hsafe : |s| ≤
      (D.chronologicalExteriorSlabTimeField t ht).safeTime)
    (htime : tcoord p + s =
      tcoord (D.position.eventCenter t ht)) :
    (D.chronologicalExteriorSlabTimeField t ht).base.flow p s ∈
      criticalSliceExteriorCore
        D.signedOutput.cobordism.toLevelCobordismData
        (D.position.eventCenter t ht)
        (tcoord (D.position.eventCenter t ht))
        (D.position.eventModel t ht).fiberCoverRadius := by
  let R := D.chronologicalExteriorSlabTimeField t ht
  have hshort : |s| < 2 * R.safeTime := by
    have hpos := R.safeTime_pos
    linarith
  have hp' := hp
  rw [chronologicalExteriorSlabCore] at hp'
  have hpfiber : p ∈
      D.signedOutput.cobordism.toLevelCobordismData.fiber := hp'.1.1
  have hyfiber : R.base.flow p s ∈
      D.signedOutput.cobordism.toLevelCobordismData.fiber :=
    R.flow_mem_fiber hpfiber s
  have hytime : tcoord (R.base.flow p s) =
      tcoord (D.position.eventCenter t ht) := by
    rw [R.tcoord_flow hp hsafe]
    exact htime
  have hyspatial : Function.Surjective
      (spatialDeriv D.signedOutput.cobordism.G (R.base.flow p s)) :=
    R.flow_spatialDeriv_surjective hp hshort
  rw [mem_criticalSliceExteriorCore]
  refine ⟨hyfiber, hytime, ?_⟩
  by_contra hdist
  have hlt : dist (R.base.flow p s) (D.position.eventCenter t ht) <
      (D.position.eventModel t ht).fiberCoverRadius :=
    lt_of_not_ge hdist
  have hyrepr : cobSpaceTime
      (spacePart (R.base.flow p s))
      (tcoord (D.position.eventCenter t ht)) = R.base.flow p s := by
    rw [← hytime, spaceTime_spacePart]
  have hcovered : spacePart (R.base.flow p s) ∈
      (D.position.eventModel t ht).coveredSliceFiber
        (tcoord (D.position.eventCenter t ht)) := by
    constructor
    · rwa [hyrepr]
    · rwa [hyrepr]
  have hycenter : R.base.flow p s = D.position.eventCenter t ht := by
    exact hyrepr.symm.trans
      ((D.position.eventModel t ht).definite_coveredSliceFiber_at_critical_eq_center
        hindex hcovered)
  have hcenterCritical :=
    (D.position.eventModel t ht).center_mem_timeCritical
  rw [hycenter] at hyspatial
  exact hcenterCritical.2 hyspatial


-- @@ L127-134 verbatim
/-- The chosen chronological half-window is safe in the reverse direction. -/
theorem chronologicalWindowRadius_sq_reverse_safe
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    |-(D.chronologicalWindowRadius t ht ^ 2)| ≤
      (D.chronologicalExteriorSlabTimeField t ht).safeTime := by
  simpa [chronologicalCriticalExteriorTimeField] using
    D.chronologicalWindowRadius_sq_le_safeTime t ht


-- @@ L136-136 verbatim
end ValueSeparatedSignedMorsePackage


-- @@ L138-138 verbatim
end Submission
