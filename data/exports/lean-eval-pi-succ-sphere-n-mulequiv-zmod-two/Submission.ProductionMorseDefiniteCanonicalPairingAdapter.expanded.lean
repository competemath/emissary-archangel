import Submission.ProductionMorseSaddleFrameClassAdapter


-- @@ L3-22 verbatim
/-!
# Cardinality adapters for production definite Morse pairings

`ProductionMorseDefiniteCanonicalPairing` proves that the short exterior flow
forces an injective map of orbit components.  This file turns that fact into a
production-facing adapter with three independent global inputs:

* the chosen chronological half-window fits the compact exterior field's safe
  time;
* that flow sends the complete selected source union into the compact critical
  exterior (a parameter-free `MapsTo` assertion);
* the two finite exterior families have the same cardinality, and at a minimum
  the forced image avoids the born local component.

The `MapsTo` assertion supplies every pointwise midpoint obligation.  Finite
cardinality plus the already-proved injectivity supplies surjectivity, so no
component equivalence or pointwise choice of preimages is part of the kit.
The final section plugs the reduced definite kits and the reduced saddle kits
directly into `ProductionMorseEventGeometryKit`.
-/


-- @@ L24-24 verbatim
set_option autoImplicit false

-- @@ L25-25 verbatim
set_option maxHeartbeats 2400000


-- @@ L27-27 verbatim
noncomputable section


-- @@ L29-29 verbatim
open Set Function

-- @@ L30-30 verbatim
open scoped RealInnerProductSpace Topology unitInterval


-- @@ L32-32 verbatim
namespace Submission


-- @@ L34-34 verbatim
/-! ## Parameter-free selected source unions -/


-- @@ L36-36 verbatim
namespace TamedField


-- @@ L38-38 verbatim
variable {n : ℕ}


-- @@ L40-40 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L41-41 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L43-52 verbatim
/-- Ambientize the union of a finite selected family of intrinsic orbit
components on one regular slice.  This set does not depend on a chosen
once-around parameter. -/
def selectedAmbientOrbitUnion
    {C : LevelCobordismData n} {t : ℝ}
    {hreg : sliceRegular C.G t}
    (V : TamedField (SlabTamedField.sliceFLSAt C t hreg))
    (A : Set (Set E)) : Set E' :=
  {v | ∃ O : {O // O ∈ V.selectedOrbitFinset A},
    ∃ x ∈ (O.1 : Set E), v = cobSpaceTime x t}


-- @@ L54-66 verbatim
/-- Every point of the intrinsic once-around parameter belongs to the
parameter-free selected ambient union. -/
theorem intrinsicExteriorAmbientLoop_mem_selectedAmbientOrbitUnion
    {C : LevelCobordismData n} {t : ℝ}
    {hreg : sliceRegular C.G t}
    (V : TamedField (SlabTamedField.sliceFLSAt C t hreg))
    (A : Set (Set E))
    (O : {O // O ∈ V.selectedOrbitFinset A}) (q : I) :
    (V.intrinsicSimpleClosedOrbitParam O.1).exteriorAmbientLoop q ∈
      V.selectedAmbientOrbitUnion A := by
  refine ⟨O, (V.intrinsicSimpleClosedOrbitParam O.1).curve q, ?_, rfl⟩
  rw [V.orbitPoint_orbit O.1]
  exact (V.intrinsicSimpleClosedOrbitParam O.1).curve_mem_orbit q


-- @@ L68-68 verbatim
end TamedField


-- @@ L70-70 verbatim
/-! ## Production source unions and compact-flow control -/


-- @@ L72-72 verbatim
variable {a : ℕ}

-- @@ L73-73 verbatim
variable {X₀ X₁ : FramedLevelSet (a + 2)}

-- @@ L74-74 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}

-- @@ L75-75 verbatim
variable {SC : SignedFramedLevelCobordism S₀ S₁}


-- @@ L77-77 verbatim
local notation "Eₐ" => EuclideanSpace ℝ (Fin (a + 3))


-- @@ L79-79 verbatim
namespace ValueSeparatedSignedMorsePackage


-- @@ L81-87 verbatim
/-- The complete incoming positive exterior of a minimum, ambientized on the
inner chronological slice. -/
abbrev chronologicalMinimumExteriorAmbientSource
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :=
  (D.chronologicalBeforeField t ht).selectedAmbientOrbitUnion
    (D.chronologicalMinimumExteriorSourceFamily t ht)


-- @@ L89-98 verbatim
/-- The incoming positive exterior of a maximum after deleting the dying
local component, ambientized on the inner chronological slice. -/
abbrev chronologicalMaximumExteriorAmbientSource
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum) :=
  (D.chronologicalMaximumLocalField t ht).selectedAmbientOrbitUnion
    (D.chronologicalMaximumExteriorSourceFamily t ht hpositive hindex)


-- @@ L100-118 verbatim
/-- Independent analytic/global control for a production minimum.

`source_mapsTo_core` is one geometric inclusion for the whole selected union;
it replaces the earlier nested quantification over orbit parameters. -/
structure ChronologicalMinimumExteriorFlowControl
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum) : Type where
  source_mapsTo_core : MapsTo
    (fun v => (D.chronologicalCriticalExteriorTimeField t ht).base.flow v
      (D.chronologicalWindowRadius t ht ^ 2))
    (D.chronologicalMinimumExteriorAmbientSource t ht)
    (criticalSliceExteriorCore
      D.signedOutput.cobordism.toLevelCobordismData
      (D.position.eventCenter t ht)
      (tcoord (D.position.eventCenter t ht))
      (D.position.eventModel t ht).fiberCoverRadius)


-- @@ L120-136 verbatim
/-- The analogous compact-flow control for a production maximum. -/
structure ChronologicalMaximumExteriorFlowControl
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum) : Type where
  source_mapsTo_core : MapsTo
    (fun v => (D.chronologicalCriticalExteriorTimeField t ht).base.flow v
      (D.chronologicalWindowRadius t ht ^ 2))
    (D.chronologicalMaximumExteriorAmbientSource
      t ht hpositive hindex)
    (criticalSliceExteriorCore
      D.signedOutput.cobordism.toLevelCobordismData
      (D.position.eventCenter t ht)
      (tcoord (D.position.eventCenter t ht))
      (D.position.eventModel t ht).fiberCoverRadius)


-- @@ L138-214 verbatim
/-- A point of the incoming exterior slab flows to the critical exterior
automatically at either definite event.  The whole-slab compact field keeps
the flow spatially regular; if its midpoint entered the cover ball, the exact
definite quadratic model would force it to be the critical center, a
contradiction. -/
theorem chronologicalDefiniteExteriorMidpoint_mem
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .minimum ∨
      (D.position.eventModel t ht).index = .maximum)
    {p : EuclideanSpace ℝ (Fin ((a + 2) + 2))}
    (hp : p ∈ D.chronologicalExteriorSlabCore t ht)
    (hptime : tcoord p = D.chronologicalBeforeTime t ht) :
    (D.chronologicalCriticalExteriorTimeField t ht).base.flow p
        (D.chronologicalWindowRadius t ht ^ 2) ∈
      criticalSliceExteriorCore
        D.signedOutput.cobordism.toLevelCobordismData
        (D.position.eventCenter t ht)
        (tcoord (D.position.eventCenter t ht))
        (D.position.eventModel t ht).fiberCoverRadius := by
  let R := D.chronologicalExteriorSlabTimeField t ht
  let s := D.chronologicalWindowRadius t ht ^ 2
  change R.base.flow p s ∈ criticalSliceExteriorCore
    D.signedOutput.cobordism.toLevelCobordismData
    (D.position.eventCenter t ht)
    (tcoord (D.position.eventCenter t ht))
    (D.position.eventModel t ht).fiberCoverRadius
  have hsafe : |s| ≤ R.safeTime := by
    simpa [R, s, chronologicalCriticalExteriorTimeField] using
      D.chronologicalWindowRadius_sq_le_safeTime t ht
  have hshort : |s| < 2 * R.safeTime := by
    have hpos := R.safeTime_pos
    linarith
  have hp' := hp
  rw [chronologicalExteriorSlabCore] at hp'
  have hpfiber : p ∈ D.signedOutput.cobordism.toLevelCobordismData.fiber :=
    hp'.1.1
  have hyfiber : R.base.flow p s ∈
      D.signedOutput.cobordism.toLevelCobordismData.fiber :=
    R.flow_mem_fiber hpfiber s
  have hytime : tcoord (R.base.flow p s) =
      tcoord (D.position.eventCenter t ht) := by
    calc
      tcoord (R.base.flow p s) = tcoord p + s := R.tcoord_flow hp hsafe
      _ = tcoord (D.position.eventCenter t ht) := by
        rw [hptime]
        simp only [chronologicalBeforeTime]
        dsimp [s]
        ring
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
    · rw [hyrepr]
      exact hlt
    · rw [hyrepr]
      exact hyfiber
  have hycenter : R.base.flow p s = D.position.eventCenter t ht := by
    exact hyrepr.symm.trans
      ((D.position.eventModel t ht).definite_coveredSliceFiber_at_critical_eq_center
        hindex hcovered)
  have hcenterCritical := (D.position.eventModel t ht).center_mem_timeCritical
  rw [hycenter] at hyspatial
  exact hcenterCritical.2 hyspatial


-- @@ L216-241 verbatim
/-- Ambientizing a point of any incoming orbit which is outside the local
cover ball places it in the whole exterior event slab. -/
theorem chronologicalBeforeOrbitPoint_mem_exteriorSlabCore
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (V : TamedField (D.chronologicalBeforeSlice t ht))
    (O : V.OrbitIndex) {x : Eₐ} (hx : x ∈ (O : Set Eₐ))
    (hexterior : (O : Set Eₐ) ∈
      D.chronologicalExteriorOrbitCollection t ht
        (D.chronologicalBeforeTime t ht)) :
    cobSpaceTime x (D.chronologicalBeforeTime t ht) ∈
      D.chronologicalExteriorSlabCore t ht := by
  rw [chronologicalExteriorSlabCore]
  refine ⟨⟨?_, ?_⟩, hexterior x hx⟩
  · have hxFiber : x ∈ (D.chronologicalBeforeSlice t ht).fiber := by
      apply V.orbit_subset_fiber (V.orbitPoint_mem_fiber O)
      rwa [← V.orbitPoint_orbit O]
    rw [chronologicalBeforeSlice,
      SlabTamedField.sliceFLSAt_fiber] at hxFiber
    exact hxFiber
  · change tcoord (cobSpaceTime x (D.chronologicalBeforeTime t ht)) ∈ Icc
      (D.position.eventBracket t ht).before
      (D.position.eventBracket t ht).after
    rw [tcoord_spaceTime]
    have hb := D.chronologicalBeforeTime_mem_bracket t ht
    exact ⟨hb.1.le, hb.2.le⟩


-- @@ L243-243 verbatim
namespace ChronologicalMinimumExteriorFlowControl


-- @@ L245-245 verbatim
variable {D : ValueSeparatedSignedMorsePackage SC}

-- @@ L246-246 verbatim
variable {t : ℝ} {ht : t ∈ D.position.eventTimes}

-- @@ L247-248 verbatim
variable {hpositive : D.position.eventCenter t ht ∈
  (D.signedOutput.labelMorsePosition D.position).positiveCenters}

-- @@ L249-249 verbatim
variable {hindex : (D.position.eventModel t ht).index = .minimum}


-- @@ L251-264 verbatim
/-- The minimum exterior flow control is forced by local excision and the
whole-slab time field; it carries no independent geometric input. -/
def canonical : ChronologicalMinimumExteriorFlowControl
    D t ht hpositive hindex where
  source_mapsTo_core := by
    intro v hv
    rcases hv with ⟨O, x, hx, rfl⟩
    apply D.chronologicalDefiniteExteriorMidpoint_mem t ht
      (Or.inl hindex)
    · apply D.chronologicalBeforeOrbitPoint_mem_exteriorSlabCore
        t ht (D.chronologicalBeforeField t ht) O.1 hx
      exact D.chronologicalMinimumBeforeOrbit_mem_exterior
        t ht hindex O.1
    · simp


-- @@ L266-272 verbatim
/-- Safety is automatic because the chronological window is chosen inside
the canonical exterior field's uniform safe time. -/
def safe
    (_F : ChronologicalMinimumExteriorFlowControl
      D t ht hpositive hindex) :
    D.ChronologicalExteriorSafe t ht :=
  D.chronologicalWindowRadius_sq_le_safeTime t ht


-- @@ L274-284 verbatim
/-- Global `MapsTo` control discharges the complete pointwise midpoint
contract used by the canonical core. -/
def midpointCapture
    (F : ChronologicalMinimumExteriorFlowControl
      D t ht hpositive hindex) :
    D.ChronologicalMinimumExteriorMidpointCapture t ht := by
  intro O q
  exact F.source_mapsTo_core
    (TamedField.intrinsicExteriorAmbientLoop_mem_selectedAmbientOrbitUnion
      (D.chronologicalBeforeField t ht)
      (D.chronologicalMinimumExteriorSourceFamily t ht) O q)


-- @@ L286-286 verbatim
end ChronologicalMinimumExteriorFlowControl


-- @@ L288-288 verbatim
namespace ChronologicalMaximumExteriorFlowControl


-- @@ L290-290 verbatim
variable {D : ValueSeparatedSignedMorsePackage SC}

-- @@ L291-291 verbatim
variable {t : ℝ} {ht : t ∈ D.position.eventTimes}

-- @@ L292-293 verbatim
variable {hpositive : D.position.eventCenter t ht ∈
  (D.signedOutput.labelMorsePosition D.position).positiveCenters}

-- @@ L294-294 verbatim
variable {hindex : (D.position.eventModel t ht).index = .maximum}


-- @@ L296-311 verbatim
/-- The maximum source family excludes the dying local circle, so local
excision again constructs the complete exterior flow control automatically. -/
def canonical : ChronologicalMaximumExteriorFlowControl
    D t ht hpositive hindex where
  source_mapsTo_core := by
    intro v hv
    rcases hv with ⟨O, x, hx, rfl⟩
    apply D.chronologicalDefiniteExteriorMidpoint_mem t ht
      (Or.inr hindex)
    · apply D.chronologicalBeforeOrbitPoint_mem_exteriorSlabCore
        t ht (D.chronologicalMaximumLocalField t ht) O.1 hx
      apply D.chronologicalMaximumBeforeOrbit_mem_exterior_of_ne_local
        t ht hpositive hindex O.1
      exact ((D.chronologicalMaximumLocalField t ht).mem_selectedOrbitFinset
        O.1).mp O.2 |>.2
    · simp


-- @@ L313-319 verbatim
/-- Maximum-event flow safety is supplied by the same adaptive chronological
window. -/
def safe
    (_F : ChronologicalMaximumExteriorFlowControl
      D t ht hpositive hindex) :
    D.ChronologicalExteriorSafe t ht :=
  D.chronologicalWindowRadius_sq_le_safeTime t ht


-- @@ L321-332 verbatim
/-- Maximum version of the parameter-free midpoint adapter. -/
def midpointCapture
    (F : ChronologicalMaximumExteriorFlowControl
      D t ht hpositive hindex) :
    D.ChronologicalMaximumExteriorMidpointCapture
      t ht hpositive hindex := by
  intro O q
  exact F.source_mapsTo_core
    (TamedField.intrinsicExteriorAmbientLoop_mem_selectedAmbientOrbitUnion
      (D.chronologicalMaximumLocalField t ht)
      (D.chronologicalMaximumExteriorSourceFamily
        t ht hpositive hindex) O q)


-- @@ L334-334 verbatim
end ChronologicalMaximumExteriorFlowControl


-- @@ L336-336 verbatim
/-! ## Minimal finite-component contracts -/


-- @@ L338-368 verbatim
/-- The two genuinely global component statements left at a minimum.

Avoidance of the born component is independent of counting.  Equality of the
two finite exterior cardinalities is strictly weaker than supplying an
equivalence or a pointwise preimage function. -/
structure ChronologicalMinimumExteriorComponentBalance
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum) : Type where
  target_ne_local : ∀
      O : {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
        (D.chronologicalMinimumExteriorSourceFamily t ht)},
    (((D.chronologicalMinimumExteriorFlowCore
        t ht
          (ChronologicalMinimumExteriorFlowControl.canonical
            (D := D) (t := t) (ht := ht)
            (hpositive := hpositive) (hindex := hindex)).safe
          (ChronologicalMinimumExteriorFlowControl.canonical
            (D := D) (t := t) (ht := ht)
            (hpositive := hpositive) (hindex := hindex)).midpointCapture).targetOrbit O :
          (D.chronologicalMinimumLocalField t ht).OrbitIndex) : Set Eₐ) ≠
      (((D.chronologicalMinimumLocalOrbit t ht hpositive hindex).1 :
        (D.chronologicalMinimumLocalField t ht).OrbitIndex) : Set Eₐ)
  card_eq :
    ((D.chronologicalBeforeField t ht).selectedOrbitFinset
      (D.chronologicalMinimumExteriorSourceFamily t ht)).card =
    ((D.chronologicalMinimumLocalField t ht).selectedOrbitFinset
      (D.chronologicalMinimumExteriorTargetFamily
        t ht hpositive hindex)).card


-- @@ L370-383 verbatim
/-- At a maximum positivity and target membership are automatic, so finite
cardinality balance is the sole component-level contract. -/
structure ChronologicalMaximumExteriorComponentBalance
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum) : Type where
  card_eq :
    ((D.chronologicalMaximumLocalField t ht).selectedOrbitFinset
      (D.chronologicalMaximumExteriorSourceFamily
        t ht hpositive hindex)).card =
    ((D.chronologicalAfterField t ht).selectedOrbitFinset
      (D.chronologicalMaximumExteriorTargetFamily t ht)).card


-- @@ L385-394 verbatim
/-- Complete reduced minimum input.  Exterior flow control is canonical, so
only the independent finite-component balance remains. -/
structure ChronologicalMinimumExteriorCardinalityKit
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum) : Type where
  components : D.ChronologicalMinimumExteriorComponentBalance
    t ht hpositive hindex


-- @@ L396-404 verbatim
/-- Complete reduced maximum input. -/
structure ChronologicalMaximumExteriorCardinalityKit
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum) : Type where
  components : D.ChronologicalMaximumExteriorComponentBalance
    t ht hpositive hindex


-- @@ L406-406 verbatim
/-! ## Cardinality forces surjectivity -/


-- @@ L408-408 verbatim
namespace ChronologicalMinimumExteriorCardinalityKit


-- @@ L410-410 verbatim
variable {D : ValueSeparatedSignedMorsePackage SC}

-- @@ L411-411 verbatim
variable {t : ℝ} {ht : t ∈ D.position.eventTimes}

-- @@ L412-413 verbatim
variable {hpositive : D.position.eventCenter t ht ∈
  (D.signedOutput.labelMorsePosition D.position).positiveCenters}

-- @@ L414-414 verbatim
variable {hindex : (D.position.eventModel t ht).index = .minimum}


-- @@ L416-420 verbatim
/-- The canonical exterior flow underlying every reduced minimum kit. -/
def flow (_K : ChronologicalMinimumExteriorCardinalityKit
    D t ht hpositive hindex) :
    D.ChronologicalMinimumExteriorFlowControl t ht hpositive hindex :=
  ChronologicalMinimumExteriorFlowControl.canonical


-- @@ L422-437 verbatim
def targetMem
    (K : ChronologicalMinimumExteriorCardinalityKit
      D t ht hpositive hindex)
    (O : {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
      (D.chronologicalMinimumExteriorSourceFamily t ht)}) :
    (D.chronologicalMinimumExteriorFlowCore
      t ht K.flow.safe K.flow.midpointCapture).targetOrbit O ∈
        (D.chronologicalMinimumLocalField t ht).selectedOrbitFinset
          (D.chronologicalMinimumExteriorTargetFamily
            t ht hpositive hindex) := by
  apply ((D.chronologicalMinimumLocalField t ht).mem_selectedOrbitFinset _).mpr
  constructor
  · exact ((D.chronologicalMinimumLocalField t ht).mem_selectedOrbitFinset _).mp
      (D.chronologicalMinimumTargetOrbit_mem_positive
        t ht K.flow.safe K.flow.midpointCapture O)
  · simpa using K.components.target_ne_local O


-- @@ L439-447 verbatim
def targetMap
    (K : ChronologicalMinimumExteriorCardinalityKit
      D t ht hpositive hindex) :
    {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
      (D.chronologicalMinimumExteriorSourceFamily t ht)} →
    {Q // Q ∈ (D.chronologicalMinimumLocalField t ht).selectedOrbitFinset
      (D.chronologicalMinimumExteriorTargetFamily t ht hpositive hindex)} :=
  fun O => ⟨(D.chronologicalMinimumExteriorFlowCore
    t ht K.flow.safe K.flow.midpointCapture).targetOrbit O, K.targetMem O⟩


-- @@ L449-455 verbatim
theorem targetMap_injective
    (K : ChronologicalMinimumExteriorCardinalityKit
      D t ht hpositive hindex) : Function.Injective K.targetMap := by
  intro O P hOP
  apply (D.chronologicalMinimumExteriorFlowCore
    t ht K.flow.safe K.flow.midpointCapture).targetOrbit_injective
  exact congrArg Subtype.val hOP


-- @@ L457-468 verbatim
theorem targetMap_surjective
    (K : ChronologicalMinimumExteriorCardinalityKit
      D t ht hpositive hindex) : Function.Surjective K.targetMap := by
  have hcard : Fintype.card
      {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
        (D.chronologicalMinimumExteriorSourceFamily t ht)} =
      Fintype.card
      {Q // Q ∈ (D.chronologicalMinimumLocalField t ht).selectedOrbitFinset
        (D.chronologicalMinimumExteriorTargetFamily t ht hpositive hindex)} := by
    simpa only [Fintype.card_coe] using K.components.card_eq
  exact ((Fintype.bijective_iff_injective_and_card K.targetMap).mpr
    ⟨K.targetMap_injective, hcard⟩).surjective


-- @@ L470-478 verbatim
def toTargetCompletion
    (K : ChronologicalMinimumExteriorCardinalityKit
      D t ht hpositive hindex) :
    D.ChronologicalMinimumTargetCompletion t ht hpositive hindex
      K.flow.safe K.flow.midpointCapture where
  target_ne_local := K.components.target_ne_local
  target_surjective Q := by
    obtain ⟨O, hO⟩ := K.targetMap_surjective Q
    exact ⟨O, congrArg Subtype.val hO⟩


-- @@ L480-486 verbatim
/-- Direct construction of the exact minimum field consumed by
`ProductionMorseEventGeometryKit`. -/
def toFlowInducedPairing
    (K : ChronologicalMinimumExteriorCardinalityKit
      D t ht hpositive hindex) :
    D.ChronologicalMinimumFlowInducedPairing t ht hpositive hindex :=
  ⟨K.flow.safe, K.flow.midpointCapture, K.toTargetCompletion⟩


-- @@ L488-493 verbatim
def toPositiveLedgerMove
    (K : ChronologicalMinimumExteriorCardinalityKit
      D t ht hpositive hindex) :
    PositiveEventLedgerMoveData D.signedOutput D.position t ht :=
  D.minimumPositiveLedgerMove_of_flowInducedPairing
    t ht hpositive hindex K.toFlowInducedPairing


-- @@ L495-495 verbatim
end ChronologicalMinimumExteriorCardinalityKit


-- @@ L497-497 verbatim
namespace ChronologicalMaximumExteriorCardinalityKit


-- @@ L499-499 verbatim
variable {D : ValueSeparatedSignedMorsePackage SC}

-- @@ L500-500 verbatim
variable {t : ℝ} {ht : t ∈ D.position.eventTimes}

-- @@ L501-502 verbatim
variable {hpositive : D.position.eventCenter t ht ∈
  (D.signedOutput.labelMorsePosition D.position).positiveCenters}

-- @@ L503-503 verbatim
variable {hindex : (D.position.eventModel t ht).index = .maximum}


-- @@ L505-509 verbatim
/-- The canonical exterior flow underlying every reduced maximum kit. -/
def flow (_K : ChronologicalMaximumExteriorCardinalityKit
    D t ht hpositive hindex) :
    D.ChronologicalMaximumExteriorFlowControl t ht hpositive hindex :=
  ChronologicalMaximumExteriorFlowControl.canonical


-- @@ L511-521 verbatim
def targetMap
    (K : ChronologicalMaximumExteriorCardinalityKit
      D t ht hpositive hindex) :
    {O // O ∈ (D.chronologicalMaximumLocalField t ht).selectedOrbitFinset
      (D.chronologicalMaximumExteriorSourceFamily t ht hpositive hindex)} →
    {Q // Q ∈ (D.chronologicalAfterField t ht).selectedOrbitFinset
      (D.chronologicalMaximumExteriorTargetFamily t ht)} :=
  fun O => ⟨(D.chronologicalMaximumExteriorFlowCore
      t ht hpositive hindex K.flow.safe K.flow.midpointCapture).targetOrbit O,
    D.chronologicalMaximumTargetOrbit_mem_positive
      t ht hpositive hindex K.flow.safe K.flow.midpointCapture O⟩


-- @@ L523-530 verbatim
theorem targetMap_injective
    (K : ChronologicalMaximumExteriorCardinalityKit
      D t ht hpositive hindex) : Function.Injective K.targetMap := by
  intro O P hOP
  apply (D.chronologicalMaximumExteriorFlowCore
    t ht hpositive hindex K.flow.safe
      K.flow.midpointCapture).targetOrbit_injective
  exact congrArg Subtype.val hOP


-- @@ L532-544 verbatim
theorem targetMap_surjective
    (K : ChronologicalMaximumExteriorCardinalityKit
      D t ht hpositive hindex) : Function.Surjective K.targetMap := by
  have hcard : Fintype.card
      {O // O ∈ (D.chronologicalMaximumLocalField t ht).selectedOrbitFinset
        (D.chronologicalMaximumExteriorSourceFamily
          t ht hpositive hindex)} =
      Fintype.card
      {Q // Q ∈ (D.chronologicalAfterField t ht).selectedOrbitFinset
        (D.chronologicalMaximumExteriorTargetFamily t ht)} := by
    simpa only [Fintype.card_coe] using K.components.card_eq
  exact ((Fintype.bijective_iff_injective_and_card K.targetMap).mpr
    ⟨K.targetMap_injective, hcard⟩).surjective


-- @@ L546-553 verbatim
def toTargetCompletion
    (K : ChronologicalMaximumExteriorCardinalityKit
      D t ht hpositive hindex) :
    D.ChronologicalMaximumTargetCompletion t ht hpositive hindex
      K.flow.safe K.flow.midpointCapture where
  target_surjective Q := by
    obtain ⟨O, hO⟩ := K.targetMap_surjective Q
    exact ⟨O, congrArg Subtype.val hO⟩


-- @@ L555-561 verbatim
/-- Direct construction of the exact maximum field consumed by the final
production event kit. -/
def toFlowInducedPairing
    (K : ChronologicalMaximumExteriorCardinalityKit
      D t ht hpositive hindex) :
    D.ChronologicalMaximumFlowInducedPairing t ht hpositive hindex :=
  ⟨K.flow.safe, K.flow.midpointCapture, K.toTargetCompletion⟩


-- @@ L563-568 verbatim
def toPositiveLedgerMove
    (K : ChronologicalMaximumExteriorCardinalityKit
      D t ht hpositive hindex) :
    PositiveEventLedgerMoveData D.signedOutput D.position t ht :=
  D.maximumPositiveLedgerMove_of_flowInducedPairing
    t ht hpositive hindex K.toFlowInducedPairing


-- @@ L570-570 verbatim
end ChronologicalMaximumExteriorCardinalityKit


-- @@ L572-572 verbatim
end ValueSeparatedSignedMorsePackage


-- @@ L574-574 verbatim
/-! ## Direct adapter to the final production geometry kit -/


-- @@ L576-588 verbatim
/-- Dimension-uniform family of reduced minimum kits. -/
abbrev ProductionMorseMinimumExteriorCardinalityKits (a : ℕ) :=
  ∀ {X Y : FramedLevelSet (a + 2)}
    {S : FiberSign X} {T : FiberSign Y}
    (C : SignedFramedLevelCobordism S T)
    (D : ValueSeparatedSignedMorsePackage C)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum),
      Nonempty
        (D.ChronologicalMinimumExteriorCardinalityKit
          t ht hpositive hindex)


-- @@ L590-602 verbatim
/-- Dimension-uniform family of reduced maximum kits. -/
abbrev ProductionMorseMaximumExteriorCardinalityKits (a : ℕ) :=
  ∀ {X Y : FramedLevelSet (a + 2)}
    {S : FiberSign X} {T : FiberSign Y}
    (C : SignedFramedLevelCobordism S T)
    (D : ValueSeparatedSignedMorsePackage C)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum),
      Nonempty
        (D.ChronologicalMaximumExteriorCardinalityKit
          t ht hpositive hindex)


-- @@ L604-619 verbatim
theorem minimumGeometry_of_exteriorCardinalityKits {a : ℕ}
    (K : ProductionMorseMinimumExteriorCardinalityKits a) :
    ∀ {X Y : FramedLevelSet (a + 2)}
      {S : FiberSign X} {T : FiberSign Y}
      (C : SignedFramedLevelCobordism S T)
      (D : ValueSeparatedSignedMorsePackage C)
      (t : ℝ) (ht : t ∈ D.position.eventTimes)
      (hpositive : D.position.eventCenter t ht ∈
        (D.signedOutput.labelMorsePosition D.position).positiveCenters)
      (hindex : (D.position.eventModel t ht).index = .minimum),
        Nonempty
          (D.ChronologicalMinimumFlowInducedPairing
            t ht hpositive hindex) := by
  intro X Y S T C D t ht hpositive hindex
  obtain ⟨K⟩ := K C D t ht hpositive hindex
  exact ⟨K.toFlowInducedPairing⟩


-- @@ L621-636 verbatim
theorem maximumGeometry_of_exteriorCardinalityKits {a : ℕ}
    (K : ProductionMorseMaximumExteriorCardinalityKits a) :
    ∀ {X Y : FramedLevelSet (a + 2)}
      {S : FiberSign X} {T : FiberSign Y}
      (C : SignedFramedLevelCobordism S T)
      (D : ValueSeparatedSignedMorsePackage C)
      (t : ℝ) (ht : t ∈ D.position.eventTimes)
      (hpositive : D.position.eventCenter t ht ∈
        (D.signedOutput.labelMorsePosition D.position).positiveCenters)
      (hindex : (D.position.eventModel t ht).index = .maximum),
        Nonempty
          (D.ChronologicalMaximumFlowInducedPairing
            t ht hpositive hindex) := by
  intro X Y S T C D t ht hpositive hindex
  obtain ⟨K⟩ := K C D t ht hpositive hindex
  exact ⟨K.toFlowInducedPairing⟩


-- @@ L638-647 verbatim
/-- Direct constructor for the final production event kit from the reduced
minimum/maximum cardinality kits and the reduced saddle frame-class kits. -/
def productionMorseEventGeometryKit_of_reducedKits {a : ℕ}
    (Kmin : ProductionMorseMinimumExteriorCardinalityKits a)
    (Ksaddle : ProductionMorseSaddleFrameClassKits a)
    (Kmax : ProductionMorseMaximumExteriorCardinalityKits a) :
    ProductionMorseEventGeometryKit a where
  minimum := minimumGeometry_of_exteriorCardinalityKits Kmin
  saddle := saddleGeometry_of_frameClassKits Ksaddle
  maximum := maximumGeometry_of_exteriorCardinalityKits Kmax


-- @@ L649-656 verbatim
/-- The same reduced kits directly supply the signed cobordism invariant. -/
def signedCobordismDeltaInvariant_of_reducedMorseKits {a : ℕ}
    (Kmin : ProductionMorseMinimumExteriorCardinalityKits a)
    (Ksaddle : ProductionMorseSaddleFrameClassKits a)
    (Kmax : ProductionMorseMaximumExteriorCardinalityKits a) :
    SignedCobordismDeltaInvariant (a + 2) :=
  (productionMorseEventGeometryKit_of_reducedKits
    Kmin Ksaddle Kmax).toSignedCobordismDeltaInvariant


-- @@ L658-658 verbatim
end Submission
