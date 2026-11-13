import Submission.ProductionMorseDefiniteCompleteLedger
import Submission.IntrinsicOrbitParam


-- @@ L4-20 verbatim
/-!
# Canonical exterior capture for production definite Morse events

The former `CriticalExteriorFlowCapture` contract stored two arbitrary
once-around parameters, a critical-slice loop, and four compatibility
equalities for every exterior component.  None of those choices is geometric:
the negative orbit has a canonical intrinsic parameter, its time-`ε` image is
the only possible critical-slice lift, and its positive boundary itself is a
simple closed parameter.

This file carries out those constructions.  The remaining contract is only
the genuine component-pairing assertion: the canonical midpoint lies in the
compact critical exterior and its second half-flow lands in the prescribed
target component.  Together with the uniform safe-time inequality and the
bijection of selected components, this produces the full capture structure and
hence the complete definite-event ledger callback.
-/


-- @@ L22-22 verbatim
set_option autoImplicit false

-- @@ L23-23 verbatim
set_option maxHeartbeats 1200000


-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
open Set Function Metric

-- @@ L28-28 verbatim
open scoped RealInnerProductSpace Topology unitInterval


-- @@ L30-30 verbatim
namespace Submission


-- @@ L32-32 verbatim
variable {n : ℕ}


-- @@ L34-34 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L35-35 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L37-37 verbatim
/-! ## The reduced, canonical pairing contract -/


-- @@ L39-75 verbatim
/--
The irreducible geometric input for a short critical-exterior transport.

For a selected negative component we use its intrinsic once-around parameter.
Flowing that loop by `ε` gives a *canonical* candidate on the critical slice.
The only pointwise hypotheses say that this candidate really lies in the
chosen compact exterior and that its positive endpoint belongs to the selected
component assigned by `orbitEquiv`.
-/
structure CanonicalCriticalExteriorFlowPairing
    (C : LevelCobordismData n)
    (criticalCenter : EuclideanSpace ℝ (Fin (n + 2))) (t r ε : ℝ)
    (R : CompactTimeTamedField C
      (criticalSliceExteriorCore C criticalCenter t r))
    (hneg : sliceRegular C.G (t - ε))
    (hpos : sliceRegular C.G (t + ε))
    (Vneg : TamedField (SlabTamedField.sliceFLSAt C (t - ε) hneg))
    (Vpos : TamedField (SlabTamedField.sliceFLSAt C (t + ε) hpos))
    (A B : Set (Set (EuclideanSpace ℝ (Fin (n + 1))))) where
  safe : |ε| ≤ R.safeTime
  orbitEquiv :
    {O // O ∈ Vneg.selectedOrbitFinset A} ≃
      {O // O ∈ Vpos.selectedOrbitFinset B}
  midpoint_mem : ∀
      (O : {O // O ∈ Vneg.selectedOrbitFinset A}) (q : I),
    R.base.flow
        ((Vneg.intrinsicSimpleClosedOrbitParam O.1).exteriorAmbientLoop q) ε ∈
      criticalSliceExteriorCore C criticalCenter t r
  positive_base_mem : ∀
      (O : {O // O ∈ Vneg.selectedOrbitFinset A}),
    spacePart
        (R.base.flow
          (R.base.flow
            ((Vneg.intrinsicSimpleClosedOrbitParam O.1).exteriorAmbientLoop 0)
            ε)
          ε) ∈
      ((orbitEquiv O).1 : Set (EuclideanSpace ℝ (Fin (n + 1))))


-- @@ L77-77 verbatim
namespace CanonicalCriticalExteriorFlowPairing


-- @@ L79-79 verbatim
variable {C : LevelCobordismData n}

-- @@ L80-80 verbatim
variable {criticalCenter : EuclideanSpace ℝ (Fin (n + 2))} {t r ε : ℝ}

-- @@ L81-82 verbatim
variable {R : CompactTimeTamedField C
  (criticalSliceExteriorCore C criticalCenter t r)}

-- @@ L83-83 verbatim
variable {hneg : sliceRegular C.G (t - ε)}

-- @@ L84-84 verbatim
variable {hpos : sliceRegular C.G (t + ε)}

-- @@ L85-86 verbatim
variable {Vneg : TamedField
  (SlabTamedField.sliceFLSAt C (t - ε) hneg)}

-- @@ L87-88 verbatim
variable {Vpos : TamedField
  (SlabTamedField.sliceFLSAt C (t + ε) hpos)}

-- @@ L89-89 verbatim
variable {A B : Set (Set (EuclideanSpace ℝ (Fin (n + 1))))}


-- @@ L91-91 verbatim
include criticalCenter A B


-- @@ L93-101 verbatim
/-- The canonical source parameter; no parameter choice is part of the
reduced contract. -/
def negativeParam
    (H : CanonicalCriticalExteriorFlowPairing C criticalCenter t r ε R
      hneg hpos Vneg Vpos A B)
    (O : {O // O ∈ Vneg.selectedOrbitFinset A}) :
    SimpleClosedOrbitParam
      (SlabTamedField.sliceFLSAt C (t - ε) hneg) Vneg :=
  Vneg.intrinsicSimpleClosedOrbitParam O.1


-- @@ L103-113 verbatim
/-- The unique candidate critical-slice loop obtained by half-flowing the
canonical negative parameter. -/
def coreLoop
    (H : CanonicalCriticalExteriorFlowPairing C criticalCenter t r ε R
      hneg hpos Vneg Vpos A B)
    (O : {O // O ∈ Vneg.selectedOrbitFinset A}) :
    C(I, EuclideanSpace ℝ (Fin (n + 2))) where
  toFun q := R.base.flow (H.negativeParam O |>.exteriorAmbientLoop q) ε
  continuous_toFun := R.base.continuous_flow_uncurry.comp
    (((H.negativeParam O).exteriorAmbientLoop.continuous).prodMk
      continuous_const)


-- @@ L115-120 verbatim
theorem coreLoop_mem
    (H : CanonicalCriticalExteriorFlowPairing C criticalCenter t r ε R
      hneg hpos Vneg Vpos A B)
    (O : {O // O ∈ Vneg.selectedOrbitFinset A}) (q : I) :
    H.coreLoop O q ∈ criticalSliceExteriorCore C criticalCenter t r := by
  exact H.midpoint_mem O q


-- @@ L122-128 verbatim
theorem coreLoop_fiber
    (H : CanonicalCriticalExteriorFlowPairing C criticalCenter t r ε R
      hneg hpos Vneg Vpos A B)
    (O : {O // O ∈ Vneg.selectedOrbitFinset A}) (q : I) :
    C.G (H.coreLoop O q) = 0 :=
  (mem_criticalSliceExteriorCore C criticalCenter (H.coreLoop O q) t r).mp
    (H.coreLoop_mem O q) |>.1


-- @@ L130-136 verbatim
theorem coreLoop_time
    (H : CanonicalCriticalExteriorFlowPairing C criticalCenter t r ε R
      hneg hpos Vneg Vpos A B)
    (O : {O // O ∈ Vneg.selectedOrbitFinset A}) (q : I) :
    tcoord (H.coreLoop O q) = t :=
  (mem_criticalSliceExteriorCore C criticalCenter (H.coreLoop O q) t r).mp
    (H.coreLoop_mem O q) |>.2.1


-- @@ L138-148 verbatim
/-- Spatial curve on the positive slice obtained from the second half of the
same canonical flow cylinder. -/
def positiveCurve
    (H : CanonicalCriticalExteriorFlowPairing C criticalCenter t r ε R
      hneg hpos Vneg Vpos A B)
    (O : {O // O ∈ Vneg.selectedOrbitFinset A}) :
    C(I, EuclideanSpace ℝ (Fin (n + 1))) where
  toFun q := spacePart (R.base.flow (H.coreLoop O q) ε)
  continuous_toFun := continuous_spacePart.comp <|
    R.base.continuous_flow_uncurry.comp
      ((H.coreLoop O).continuous.prodMk continuous_const)


-- @@ L150-155 verbatim
theorem positiveEndpoint_time
    (H : CanonicalCriticalExteriorFlowPairing C criticalCenter t r ε R
      hneg hpos Vneg Vpos A B)
    (O : {O // O ∈ Vneg.selectedOrbitFinset A}) (q : I) :
    tcoord (R.base.flow (H.coreLoop O q) ε) = t + ε := by
  rw [R.tcoord_flow (H.coreLoop_mem O q) H.safe, H.coreLoop_time O q]


-- @@ L157-167 verbatim
theorem positiveCurve_mem_fiber
    (H : CanonicalCriticalExteriorFlowPairing C criticalCenter t r ε R
      hneg hpos Vneg Vpos A B)
    (O : {O // O ∈ Vneg.selectedOrbitFinset A}) (q : I) :
    H.positiveCurve O q ∈
      (SlabTamedField.sliceFLSAt C (t + ε) hpos).fiber := by
  rw [SlabTamedField.sliceFLSAt_fiber]
  change C.G (cobSpaceTime
    (spacePart (R.base.flow (H.coreLoop O q) ε)) (t + ε)) = 0
  rw [← H.positiveEndpoint_time O q, spaceTime_spacePart]
  exact R.flow_mem_fiber (H.coreLoop_fiber O q) ε


-- @@ L169-180 verbatim
theorem positiveCurve_closed
    (H : CanonicalCriticalExteriorFlowPairing C criticalCenter t r ε R
      hneg hpos Vneg Vpos A B)
    (O : {O // O ∈ Vneg.selectedOrbitFinset A}) :
    H.positiveCurve O 0 = H.positiveCurve O 1 := by
  change spacePart
      (R.base.flow
        (R.base.flow ((H.negativeParam O).exteriorAmbientLoop 0) ε) ε) =
    spacePart
      (R.base.flow
        (R.base.flow ((H.negativeParam O).exteriorAmbientLoop 1) ε) ε)
  rw [(H.negativeParam O).exteriorAmbientLoop_closed]


-- @@ L182-188 verbatim
theorem positiveCurve_mem_orbit
    (H : CanonicalCriticalExteriorFlowPairing C criticalCenter t r ε R
      hneg hpos Vneg Vpos A B)
    (O : {O // O ∈ Vneg.selectedOrbitFinset A}) (q : I) :
    H.positiveCurve O q ∈ Vpos.orbit (H.positiveCurve O 0) := by
  exact Vpos.continuousMap_mem_orbit (H.positiveCurve O)
    (H.positiveCurve_mem_fiber O) q


-- @@ L190-224 verbatim
theorem positiveCurve_eq_cases
    (H : CanonicalCriticalExteriorFlowPairing C criticalCenter t r ε R
      hneg hpos Vneg Vpos A B)
    (O : {O // O ∈ Vneg.selectedOrbitFinset A}) {u v : I}
    (huv : H.positiveCurve O u = H.positiveCurve O v) :
    u = v ∨ (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) := by
  have hambient :
      R.base.flow (H.coreLoop O u) ε =
        R.base.flow (H.coreLoop O v) ε := by
    calc
      R.base.flow (H.coreLoop O u) ε =
          cobSpaceTime (H.positiveCurve O u) (t + ε) := by
        rw [← H.positiveEndpoint_time O u]
        change R.base.flow (H.coreLoop O u) ε =
          cobSpaceTime (spacePart (R.base.flow (H.coreLoop O u) ε))
            (tcoord (R.base.flow (H.coreLoop O u) ε))
        exact (spaceTime_spacePart _).symm
      _ = cobSpaceTime (H.positiveCurve O v) (t + ε) := by rw [huv]
      _ = R.base.flow (H.coreLoop O v) ε := by
        rw [← H.positiveEndpoint_time O v]
        change cobSpaceTime
            (spacePart (R.base.flow (H.coreLoop O v) ε))
            (tcoord (R.base.flow (H.coreLoop O v) ε)) =
          R.base.flow (H.coreLoop O v) ε
        exact spaceTime_spacePart _
  have hcore : H.coreLoop O u = H.coreLoop O v :=
    R.flow_apply_injective ε hambient
  have hnegativeAmbient :
      (H.negativeParam O).exteriorAmbientLoop u =
        (H.negativeParam O).exteriorAmbientLoop v := by
    apply R.flow_apply_injective ε
    exact hcore
  apply (H.negativeParam O).curve_eq_cases
  simpa [SimpleClosedOrbitParam.exteriorAmbientLoop] using
    congrArg spacePart hnegativeAmbient


-- @@ L226-240 verbatim
/-- The positive boundary is automatically a genuine once-around parameter;
its phase is whatever the exterior flow produces. -/
def positiveParam
    (H : CanonicalCriticalExteriorFlowPairing C criticalCenter t r ε R
      hneg hpos Vneg Vpos A B)
    (O : {O // O ∈ Vneg.selectedOrbitFinset A}) :
    SimpleClosedOrbitParam
      (SlabTamedField.sliceFLSAt C (t + ε) hpos) Vpos where
  p := H.positiveCurve O 0
  hp := H.positiveCurve_mem_fiber O 0
  curve := H.positiveCurve O
  curve_zero := rfl
  curve_closed := H.positiveCurve_closed O
  curve_mem_orbit := H.positiveCurve_mem_orbit O
  curve_eq_cases := H.positiveCurve_eq_cases O


-- @@ L242-248 verbatim
theorem negativeParam_orbitIndex
    (H : CanonicalCriticalExteriorFlowPairing C criticalCenter t r ε R
      hneg hpos Vneg Vpos A B)
    (O : {O // O ∈ Vneg.selectedOrbitFinset A}) :
    (H.negativeParam O).orbitIndex = O.1 := by
  apply Subtype.ext
  exact (Vneg.orbitPoint_orbit O.1).symm


-- @@ L250-270 verbatim
theorem positiveParam_orbitIndex
    (H : CanonicalCriticalExteriorFlowPairing C criticalCenter t r ε R
      hneg hpos Vneg Vpos A B)
    (O : {O // O ∈ Vneg.selectedOrbitFinset A}) :
    (H.positiveParam O).orbitIndex = (H.orbitEquiv O).1 := by
  apply Subtype.ext
  change Vpos.orbit (H.positiveCurve O 0) =
    ((H.orbitEquiv O).1 : Set (EuclideanSpace ℝ (Fin (n + 1))))
  calc
    Vpos.orbit (H.positiveCurve O 0) =
        Vpos.orbit (Vpos.orbitPoint (H.orbitEquiv O).1) := by
      apply Vpos.orbit_eq_of_mem
      have hb : H.positiveCurve O 0 ∈
          ((H.orbitEquiv O).1 :
            Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
        exact H.positive_base_mem O
      rw [Vpos.orbitPoint_orbit (H.orbitEquiv O).1] at hb
      exact hb
    _ = ((H.orbitEquiv O).1 :
        Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
      (Vpos.orbitPoint_orbit (H.orbitEquiv O).1).symm


-- @@ L272-282 verbatim
theorem negative_boundary
    (H : CanonicalCriticalExteriorFlowPairing C criticalCenter t r ε R
      hneg hpos Vneg Vpos A B)
    (O : {O // O ∈ Vneg.selectedOrbitFinset A}) (q : I) :
    R.base.flow (H.coreLoop O q) (-ε) =
      (H.negativeParam O).exteriorAmbientLoop q := by
  change R.base.flow
      (R.base.flow ((H.negativeParam O).exteriorAmbientLoop q) ε) (-ε) =
    (H.negativeParam O).exteriorAmbientLoop q
  simpa using congrFun (R.base.flow_shift
    ((H.negativeParam O).exteriorAmbientLoop q) ε) (-ε)


-- @@ L284-296 verbatim
theorem positive_boundary
    (H : CanonicalCriticalExteriorFlowPairing C criticalCenter t r ε R
      hneg hpos Vneg Vpos A B)
    (O : {O // O ∈ Vneg.selectedOrbitFinset A}) (q : I) :
    R.base.flow (H.coreLoop O q) ε =
      (H.positiveParam O).exteriorAmbientLoop q := by
  change R.base.flow (H.coreLoop O q) ε =
    cobSpaceTime (H.positiveCurve O q) (t + ε)
  rw [← H.positiveEndpoint_time O q]
  change R.base.flow (H.coreLoop O q) ε =
    cobSpaceTime (spacePart (R.base.flow (H.coreLoop O q) ε))
      (tcoord (R.base.flow (H.coreLoop O q) ε))
  exact (spaceTime_spacePart _).symm


-- @@ L298-314 verbatim
/-- The reduced pairing data canonically supplies every field of the original
critical exterior capture. -/
def toCriticalExteriorFlowCapture
    (H : CanonicalCriticalExteriorFlowPairing C criticalCenter t r ε R
      hneg hpos Vneg Vpos A B) :
    CriticalExteriorFlowCapture C criticalCenter t r ε R
      hneg hpos Vneg Vpos A B where
  safe := H.safe
  orbitEquiv := H.orbitEquiv
  coreLoop := H.coreLoop
  core_mem := H.coreLoop_mem
  negativeParam := H.negativeParam
  positiveParam := H.positiveParam
  negative_orbit := H.negativeParam_orbitIndex
  positive_orbit := H.positiveParam_orbitIndex
  negative_boundary := H.negative_boundary
  positive_boundary := H.positive_boundary


-- @@ L316-316 verbatim
end CanonicalCriticalExteriorFlowPairing


-- @@ L318-318 verbatim
/-! ## Production specializations and ledger callbacks -/


-- @@ L320-320 verbatim
variable {a : ℕ}

-- @@ L321-321 verbatim
variable {X₀ X₁ : FramedLevelSet (a + 2)}

-- @@ L322-322 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}

-- @@ L323-323 verbatim
variable {SC : SignedFramedLevelCobordism S₀ S₁}


-- @@ L325-325 verbatim
local notation "Eₐ" => EuclideanSpace ℝ (Fin (a + 3))


-- @@ L327-327 verbatim
namespace ValueSeparatedSignedMorsePackage


-- @@ L329-354 verbatim
/-- Reduced canonical pairing contract specialized to a production minimum. -/
abbrev ChronologicalMinimumExteriorCanonicalPairing
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum) :=
  CanonicalCriticalExteriorFlowPairing
    D.signedOutput.cobordism.toLevelCobordismData
    (D.position.eventCenter t ht)
    (tcoord (D.position.eventCenter t ht))
    (D.position.eventModel t ht).fiberCoverRadius
    (D.chronologicalWindowRadius t ht ^ 2)
    (D.chronologicalCriticalExteriorTimeField t ht)
    (D.chronologicalBeforeTime_regular t ht)
    (D.chronologicalAfterTime_regular t ht)
    (D.chronologicalBeforeField t ht)
    (D.chronologicalMinimumLocalField t ht)
    ((D.signedOutput.sliceSign (D.chronologicalBeforeTime t ht)
      (D.chronologicalBeforeTime_regular t ht)).positiveOrbitCollection
        (D.chronologicalBeforeField t ht))
    (((D.signedOutput.sliceSign (D.chronologicalAfterTime t ht)
      (D.chronologicalAfterTime_regular t ht)).positiveOrbitCollection
        (D.chronologicalMinimumLocalField t ht)) \
      {(((D.chronologicalMinimumLocalOrbit t ht hpositive hindex).1 :
        (D.chronologicalMinimumLocalField t ht).OrbitIndex) : Set Eₐ)})


-- @@ L356-381 verbatim
/-- Reduced canonical pairing contract specialized to a production maximum. -/
abbrev ChronologicalMaximumExteriorCanonicalPairing
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum) :=
  CanonicalCriticalExteriorFlowPairing
    D.signedOutput.cobordism.toLevelCobordismData
    (D.position.eventCenter t ht)
    (tcoord (D.position.eventCenter t ht))
    (D.position.eventModel t ht).fiberCoverRadius
    (D.chronologicalWindowRadius t ht ^ 2)
    (D.chronologicalCriticalExteriorTimeField t ht)
    (D.chronologicalBeforeTime_regular t ht)
    (D.chronologicalAfterTime_regular t ht)
    (D.chronologicalMaximumLocalField t ht)
    (D.chronologicalAfterField t ht)
    (((D.signedOutput.sliceSign (D.chronologicalBeforeTime t ht)
      (D.chronologicalBeforeTime_regular t ht)).positiveOrbitCollection
        (D.chronologicalMaximumLocalField t ht)) \
      {(((D.chronologicalMaximumLocalOrbit t ht hpositive hindex).1 :
        (D.chronologicalMaximumLocalField t ht).OrbitIndex) : Set Eₐ)})
    ((D.signedOutput.sliceSign (D.chronologicalAfterTime t ht)
      (D.chronologicalAfterTime_regular t ht)).positiveOrbitCollection
        (D.chronologicalAfterField t ht))


-- @@ L383-394 verbatim
/-- A canonical production minimum pairing constructs the former full capture
record without any extra parameter or loop choices. -/
def minimumExteriorFlowCapture_of_canonicalPairing
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum)
    (H : D.ChronologicalMinimumExteriorCanonicalPairing
      t ht hpositive hindex) :
    D.ChronologicalMinimumExteriorFlowCapture t ht hpositive hindex :=
  H.toCriticalExteriorFlowCapture


-- @@ L396-406 verbatim
/-- Maximum analogue of `minimumExteriorFlowCapture_of_canonicalPairing`. -/
def maximumExteriorFlowCapture_of_canonicalPairing
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum)
    (H : D.ChronologicalMaximumExteriorCanonicalPairing
      t ht hpositive hindex) :
    D.ChronologicalMaximumExteriorFlowCapture t ht hpositive hindex :=
  H.toCriticalExteriorFlowCapture


-- @@ L408-421 verbatim
/-- Complete positive minimum ledger callback from only the reduced canonical
pairing contract. -/
def minimumPositiveLedgerMove_of_canonicalPairing
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum)
    (H : D.ChronologicalMinimumExteriorCanonicalPairing
      t ht hpositive hindex) :
    PositiveEventLedgerMoveData D.signedOutput D.position t ht :=
  D.minimumPositiveLedgerMove t ht hpositive hindex
    (D.minimumExteriorFlowCapture_of_canonicalPairing
      t ht hpositive hindex H)


-- @@ L423-436 verbatim
/-- Complete positive maximum ledger callback from only the reduced canonical
pairing contract. -/
def maximumPositiveLedgerMove_of_canonicalPairing
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum)
    (H : D.ChronologicalMaximumExteriorCanonicalPairing
      t ht hpositive hindex) :
    PositiveEventLedgerMoveData D.signedOutput D.position t ht :=
  D.maximumPositiveLedgerMove t ht hpositive hindex
    (D.maximumExteriorFlowCapture_of_canonicalPairing
      t ht hpositive hindex H)


-- @@ L438-438 verbatim
end ValueSeparatedSignedMorsePackage


-- @@ L440-440 verbatim
end Submission
