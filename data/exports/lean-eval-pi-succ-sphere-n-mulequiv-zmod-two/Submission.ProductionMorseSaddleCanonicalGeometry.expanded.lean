import Submission.ProductionMorseDefiniteExteriorCapture
import Submission.SaddleFrameSpliceCompleteness


-- @@ L4-19 verbatim
/-!
# Canonical exterior data for production saddle events

The saddle ledger adapter originally retained a full
`CriticalExteriorFlowCapture`.  As for definite events, its loop parameters
and both boundary identities are canonical once the component pairing is
known: start with each intrinsic negative parameter and flow it to the
critical slice.  This file replaces that choice-heavy field by the reduced
`CanonicalCriticalExteriorFlowPairing` contract and then recovers the exact
merge/split geometry consumed by the production ledger.

The remaining fields now describe only genuine saddle topology: which side
has two components, the canonical exterior component pairing, and the single
stable frame-class splice identity.  Stable `SO` completeness constructs the
three exterior-relative frame homotopies from that identity.
-/


-- @@ L21-21 verbatim
set_option autoImplicit false


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
namespace Submission


-- @@ L27-27 verbatim
variable {n : ℕ}

-- @@ L28-28 verbatim
variable {X₀ X₁ : FramedLevelSet n}

-- @@ L29-29 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}

-- @@ L30-30 verbatim
variable {SC : SignedFramedLevelCobordism S₀ S₁}


-- @@ L32-32 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L34-34 verbatim
namespace ValueSeparatedSignedMorsePackage


-- @@ L36-64 verbatim
/-- Canonical tail pairing for the chronological merge orientation. -/
abbrev ChronologicalSaddleMergeExteriorCanonicalPairing
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .saddle) :=
  CanonicalCriticalExteriorFlowPairing
    D.signedOutput.cobordism.toLevelCobordismData
    (D.position.eventCenter t ht)
    (tcoord (D.position.eventCenter t ht))
    ((D.position.eventModel t ht).fiberCoverRadius / 2)
    (D.chronologicalWindowRadius t ht ^ 2)
    (D.chronologicalSaddleCriticalExteriorTimeField t ht)
    (D.chronologicalBeforeTime_regular t ht)
    (D.chronologicalAfterTime_regular t ht)
    (D.chronologicalBeforeField t ht)
    (D.chronologicalAfterField t ht)
    ((D.chronologicalSaddleNegativeCollection t ht \
      {(((D.chronologicalSaddleNegativeSelectedOrbit
        t ht hpositive hindex .negative).1 :
          (D.chronologicalBeforeField t ht).OrbitIndex) : Set E₁)}) \
      {(((D.chronologicalSaddleNegativeSelectedOrbit
        t ht hpositive hindex .positive).1 :
          (D.chronologicalBeforeField t ht).OrbitIndex) : Set E₁)})
    (D.chronologicalSaddlePositiveCollection t ht \
      {(((D.chronologicalSaddlePositiveSelectedOrbit
        t ht hpositive hindex .negative).1 :
          (D.chronologicalAfterField t ht).OrbitIndex) : Set E₁)})


-- @@ L66-94 verbatim
/-- Canonical tail pairing for the chronological split orientation. -/
abbrev ChronologicalSaddleSplitExteriorCanonicalPairing
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .saddle) :=
  CanonicalCriticalExteriorFlowPairing
    D.signedOutput.cobordism.toLevelCobordismData
    (D.position.eventCenter t ht)
    (tcoord (D.position.eventCenter t ht))
    ((D.position.eventModel t ht).fiberCoverRadius / 2)
    (D.chronologicalWindowRadius t ht ^ 2)
    (D.chronologicalSaddleCriticalExteriorTimeField t ht)
    (D.chronologicalBeforeTime_regular t ht)
    (D.chronologicalAfterTime_regular t ht)
    (D.chronologicalBeforeField t ht)
    (D.chronologicalAfterField t ht)
    (D.chronologicalSaddleNegativeCollection t ht \
      {(((D.chronologicalSaddleNegativeSelectedOrbit
        t ht hpositive hindex .negative).1 :
          (D.chronologicalBeforeField t ht).OrbitIndex) : Set E₁)})
    ((D.chronologicalSaddlePositiveCollection t ht \
      {(((D.chronologicalSaddlePositiveSelectedOrbit
        t ht hpositive hindex .negative).1 :
          (D.chronologicalAfterField t ht).OrbitIndex) : Set E₁)}) \
      {(((D.chronologicalSaddlePositiveSelectedOrbit
        t ht hpositive hindex .positive).1 :
          (D.chronologicalAfterField t ht).OrbitIndex) : Set E₁)})


-- @@ L96-120 verbatim
/-- Choice-free exterior version of the chronological merge geometry. -/
structure ChronologicalSaddleMergeCanonicalGeometry
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .saddle) where
  incoming_ne :
    D.chronologicalSaddleNegativeSelectedOrbit
        t ht hpositive hindex .negative ≠
      D.chronologicalSaddleNegativeSelectedOrbit
        t ht hpositive hindex .positive
  outgoing_eq :
    D.chronologicalSaddlePositiveOrbit t ht hindex .negative =
      D.chronologicalSaddlePositiveOrbit t ht hindex .positive
  exteriorPairing :
    D.ChronologicalSaddleMergeExteriorCanonicalPairing
      t ht hpositive hindex
  frame_splice :
    (D.chronologicalAfterField t ht).orbitFrameClass
        (D.chronologicalSaddlePositiveOrbit t ht hindex .negative) =
      (D.chronologicalBeforeField t ht).orbitFrameClass
          (D.chronologicalSaddleNegativeOrbit t ht hindex .negative) +
        (D.chronologicalBeforeField t ht).orbitFrameClass
          (D.chronologicalSaddleNegativeOrbit t ht hindex .positive) + 1


-- @@ L122-146 verbatim
/-- Choice-free exterior version of the chronological split geometry. -/
structure ChronologicalSaddleSplitCanonicalGeometry
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .saddle) where
  incoming_ne :
    D.chronologicalSaddlePositiveSelectedOrbit
        t ht hpositive hindex .negative ≠
      D.chronologicalSaddlePositiveSelectedOrbit
        t ht hpositive hindex .positive
  outgoing_eq :
    D.chronologicalSaddleNegativeOrbit t ht hindex .negative =
      D.chronologicalSaddleNegativeOrbit t ht hindex .positive
  exteriorPairing :
    D.ChronologicalSaddleSplitExteriorCanonicalPairing
      t ht hpositive hindex
  frame_splice :
    (D.chronologicalBeforeField t ht).orbitFrameClass
        (D.chronologicalSaddleNegativeOrbit t ht hindex .negative) =
      (D.chronologicalAfterField t ht).orbitFrameClass
          (D.chronologicalSaddlePositiveOrbit t ht hindex .negative) +
        (D.chronologicalAfterField t ht).orbitFrameClass
          (D.chronologicalSaddlePositiveOrbit t ht hindex .positive) + 1


-- @@ L148-148 verbatim
namespace ChronologicalSaddleMergeCanonicalGeometry


-- @@ L150-150 verbatim
variable {D : ValueSeparatedSignedMorsePackage SC}

-- @@ L151-151 verbatim
variable {t : ℝ} {ht : t ∈ D.position.eventTimes}

-- @@ L152-153 verbatim
variable {hpositive : D.position.eventCenter t ht ∈
  (D.signedOutput.labelMorsePosition D.position).positiveCenters}

-- @@ L154-154 verbatim
variable {hindex : (D.position.eventModel t ht).index = .saddle}


-- @@ L156-167 verbatim
/-- Recover the full merge geometry; all loop data are generated by the
canonical pairing constructor. -/
def toGeometry
    (G : ChronologicalSaddleMergeCanonicalGeometry
      D t ht hpositive hindex)
    (hn : 2 ≤ n) :
    D.ChronologicalSaddleMergeGeometry t ht hpositive hindex where
  incoming_ne := G.incoming_ne
  outgoing_eq := G.outgoing_eq
  exteriorCapture := G.exteriorPairing.toCriticalExteriorFlowCapture
  frame := SaddleRelativeFrameSpliceData.ofOrbitFrameClassSplice
    hn G.frame_splice


-- @@ L169-169 verbatim
end ChronologicalSaddleMergeCanonicalGeometry


-- @@ L171-171 verbatim
namespace ChronologicalSaddleSplitCanonicalGeometry


-- @@ L173-173 verbatim
variable {D : ValueSeparatedSignedMorsePackage SC}

-- @@ L174-174 verbatim
variable {t : ℝ} {ht : t ∈ D.position.eventTimes}

-- @@ L175-176 verbatim
variable {hpositive : D.position.eventCenter t ht ∈
  (D.signedOutput.labelMorsePosition D.position).positiveCenters}

-- @@ L177-177 verbatim
variable {hindex : (D.position.eventModel t ht).index = .saddle}


-- @@ L179-189 verbatim
/-- Recover the full split geometry from its canonical pairing. -/
def toGeometry
    (G : ChronologicalSaddleSplitCanonicalGeometry
      D t ht hpositive hindex)
    (hn : 2 ≤ n) :
    D.ChronologicalSaddleSplitGeometry t ht hpositive hindex where
  incoming_ne := G.incoming_ne
  outgoing_eq := G.outgoing_eq
  exteriorCapture := G.exteriorPairing.toCriticalExteriorFlowCapture
  frame := SaddleRelativeFrameSpliceData.ofOrbitFrameClassSplice
    hn G.frame_splice


-- @@ L191-191 verbatim
end ChronologicalSaddleSplitCanonicalGeometry


-- @@ L193-211 verbatim
/-- Canonical saddle geometry directly supplies the production callback. -/
theorem nonempty_saddlePositiveLedgerMove_of_canonicalGeometry
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (hn : 2 ≤ n)
    (G : D.ChronologicalSaddleMergeCanonicalGeometry
          t ht hpositive hindex ⊕
        D.ChronologicalSaddleSplitCanonicalGeometry
          t ht hpositive hindex) :
    Nonempty (PositiveEventLedgerMoveData
      D.signedOutput D.position t ht) :=
  D.nonempty_saddlePositiveLedgerMove_of_geometry
    t ht hpositive hindex hn <|
      G.map
        (fun H => H.toGeometry hn)
        (fun H => H.toGeometry hn)


-- @@ L213-213 verbatim
end ValueSeparatedSignedMorsePackage


-- @@ L215-215 verbatim
end Submission
