import Submission.ProductionMorseChronologicalWindow
import Submission.ProductionMorseRegularWindowTransport
import Submission.ProductionMorseSaddleSignControl
import Submission.InstalledDefinitePositiveOrbit
import Submission.MorseLedgerPermutation


-- @@ L7-16 verbatim
/-!
# Local definite orbits for production ledger moves

This file constructs the distinguished positive circle on the smaller regular
chronological slice of a value-separated production minimum or maximum.  A
selected-component transport from that slice to the corresponding literal
event-bracket endpoint then identifies the distinguished endpoint orbit.  The
only event-crossing input left explicit is transport of the exterior
complement across the positive critical event.
-/


-- @@ L18-18 verbatim
set_option autoImplicit false

-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
open Set

-- @@ L22-22 verbatim
open scoped unitInterval


-- @@ L24-24 verbatim
namespace Submission


-- @@ L26-26 verbatim
variable {n : ℕ}

-- @@ L27-27 verbatim
variable {X₀ X₁ : FramedLevelSet n}

-- @@ L28-28 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}

-- @@ L29-29 verbatim
variable {C : SignedFramedLevelCobordism S₀ S₁}


-- @@ L31-31 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L32-32 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)


-- @@ L34-34 verbatim
namespace StandardMorseEventAt.EmbeddedShrink


-- @@ L36-58 verbatim
/-- The base point of the standard minimum circle is positive on its actual
regular slice whenever the event center is positive. -/
theorem minimumSimpleClosedOrbitParam_positive_of_center
    {center : EuclideanSpace ℝ (Fin (n + 2))}
    {M : StandardMorseEventAt C.cobordism center}
    (T : M.EmbeddedShrink) (hcenter : 0 < C center)
    (hindex : M.index = .minimum)
    (a : ℝ) (ha : 0 < a) (har : a < T.radius)
    (hreg : sliceRegular C.cobordism.G (tcoord center + a ^ 2))
    (V : TamedField (T.minimumPositiveSlice a hreg)) :
    0 < (C.sliceSign (tcoord center + a ^ 2) hreg)
      (T.minimumSimpleClosedOrbitParam hindex a ha har hreg V).p := by
  simp only [minimumSimpleClosedOrbitParam, definiteSpatialCircle,
    definiteCircleCurve, SignedFramedLevelCobordism.sliceSign]
  change 0 < C (cobSpaceTime
    (spacePart (M.definiteCircle a (2 * Real.pi * ((0 : I) : ℝ))))
      (tcoord center + a ^ 2))
  norm_num
  rw [← M.minimumCircle_time hindex ha.le (har.trans_le T.radius_le),
    spaceTime_spacePart]
  apply T.localPoint_positive_of_center hcenter
  rw [norm_definiteCircleParam ha.le]
  exact har


-- @@ L60-82 verbatim
/-- The base point of the standard maximum circle is positive on its actual
regular pre-death slice whenever the event center is positive. -/
theorem maximumSimpleClosedOrbitParam_positive_of_center
    {center : EuclideanSpace ℝ (Fin (n + 2))}
    {M : StandardMorseEventAt C.cobordism center}
    (T : M.EmbeddedShrink) (hcenter : 0 < C center)
    (hindex : M.index = .maximum)
    (a : ℝ) (ha : 0 < a) (har : a < T.radius)
    (hreg : sliceRegular C.cobordism.G (tcoord center - a ^ 2))
    (V : TamedField (T.maximumNegativeSlice a hreg)) :
    0 < (C.sliceSign (tcoord center - a ^ 2) hreg)
      (T.maximumSimpleClosedOrbitParam hindex a ha har hreg V).p := by
  simp only [maximumSimpleClosedOrbitParam, definiteSpatialCircle,
    definiteCircleCurve, SignedFramedLevelCobordism.sliceSign]
  change 0 < C (cobSpaceTime
    (spacePart (M.definiteCircle a (2 * Real.pi * ((0 : I) : ℝ))))
      (tcoord center - a ^ 2))
  norm_num
  rw [← M.maximumCircle_time hindex ha.le (har.trans_le T.radius_le),
    spaceTime_spacePart]
  apply T.localPoint_positive_of_center hcenter
  rw [norm_definiteCircleParam ha.le]
  exact har


-- @@ L84-84 verbatim
end StandardMorseEventAt.EmbeddedShrink


-- @@ L86-86 verbatim
namespace ValueSeparatedSignedMorsePackage


-- @@ L88-94 verbatim
/-- A fixed tamed field on the smaller regular slice carrying a born minimum
circle. -/
def chronologicalMinimumLocalField
    (D : ValueSeparatedSignedMorsePackage C)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    TamedField (D.chronologicalAfterSlice t ht) :=
  (D.chronologicalAfterSlice t ht).exists_tamedField.some


-- @@ L96-102 verbatim
/-- A fixed tamed field on the smaller regular slice carrying a pre-death
maximum circle. -/
def chronologicalMaximumLocalField
    (D : ValueSeparatedSignedMorsePackage C)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    TamedField (D.chronologicalBeforeSlice t ht) :=
  (D.chronologicalBeforeSlice t ht).exists_tamedField.some


-- @@ L104-117 verbatim
/-- The actual once-around born circle on the production minimum's smaller
regular chronological slice. -/
def chronologicalMinimumLocalParam
    (D : ValueSeparatedSignedMorsePackage C)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .minimum) :
    SimpleClosedOrbitParam (D.chronologicalAfterSlice t ht)
      (D.chronologicalMinimumLocalField t ht) := by
  exact (D.chronologicalEventEmbeddedShrink t ht).minimumSimpleClosedOrbitParam
    hindex (D.chronologicalWindowRadius t ht)
    (D.chronologicalWindowRadius_pos t ht)
    (D.chronologicalWindowRadius_lt_embedded t ht)
    (D.chronologicalAfterTime_regular t ht)
    (D.chronologicalMinimumLocalField t ht)


-- @@ L119-132 verbatim
/-- The actual once-around pre-death circle on the production maximum's
smaller regular chronological slice. -/
def chronologicalMaximumLocalParam
    (D : ValueSeparatedSignedMorsePackage C)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .maximum) :
    SimpleClosedOrbitParam (D.chronologicalBeforeSlice t ht)
      (D.chronologicalMaximumLocalField t ht) := by
  exact (D.chronologicalEventEmbeddedShrink t ht).maximumSimpleClosedOrbitParam
    hindex (D.chronologicalWindowRadius t ht)
    (D.chronologicalWindowRadius_pos t ht)
    (D.chronologicalWindowRadius_lt_embedded t ht)
    (D.chronologicalBeforeTime_regular t ht)
    (D.chronologicalMaximumLocalField t ht)


-- @@ L134-141 verbatim
theorem chronologicalEventCenter_positive
    (D : ValueSeparatedSignedMorsePackage C)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters) :
    0 < D.signedOutput (D.position.eventCenter t ht) :=
  ((D.signedOutput.labelMorsePosition D.position).mem_positiveCenters_iff.mp
    hpositive).2


-- @@ L143-159 verbatim
theorem chronologicalMinimumLocalParam_positive
    (D : ValueSeparatedSignedMorsePackage C)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum) :
    0 < (D.signedOutput.sliceSign (D.chronologicalAfterTime t ht)
      (D.chronologicalAfterTime_regular t ht))
        (D.chronologicalMinimumLocalParam t ht hindex).p := by
  exact StandardMorseEventAt.EmbeddedShrink.minimumSimpleClosedOrbitParam_positive_of_center
      (D.chronologicalEventEmbeddedShrink t ht)
      (D.chronologicalEventCenter_positive t ht hpositive) hindex
      (D.chronologicalWindowRadius t ht)
      (D.chronologicalWindowRadius_pos t ht)
      (D.chronologicalWindowRadius_lt_embedded t ht)
      (D.chronologicalAfterTime_regular t ht)
      (D.chronologicalMinimumLocalField t ht)


-- @@ L161-177 verbatim
theorem chronologicalMaximumLocalParam_positive
    (D : ValueSeparatedSignedMorsePackage C)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum) :
    0 < (D.signedOutput.sliceSign (D.chronologicalBeforeTime t ht)
      (D.chronologicalBeforeTime_regular t ht))
        (D.chronologicalMaximumLocalParam t ht hindex).p := by
  exact StandardMorseEventAt.EmbeddedShrink.maximumSimpleClosedOrbitParam_positive_of_center
      (D.chronologicalEventEmbeddedShrink t ht)
      (D.chronologicalEventCenter_positive t ht hpositive) hindex
      (D.chronologicalWindowRadius t ht)
      (D.chronologicalWindowRadius_pos t ht)
      (D.chronologicalWindowRadius_lt_embedded t ht)
      (D.chronologicalBeforeTime_regular t ht)
      (D.chronologicalMaximumLocalField t ht)


-- @@ L179-193 verbatim
/-- The distinguished born component selected by the actual minimum circle. -/
def chronologicalMinimumLocalOrbit
    (D : ValueSeparatedSignedMorsePackage C)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum) :
    (D.chronologicalMinimumLocalField t ht).SelectedOrbitIndex
      ((D.signedOutput.sliceSign (D.chronologicalAfterTime t ht)
        (D.chronologicalAfterTime_regular t ht)).positiveOrbitCollection
          (D.chronologicalMinimumLocalField t ht)) :=
  (D.chronologicalMinimumLocalParam t ht hindex).selectedPositiveOrbitIndex
    (D.signedOutput.sliceSign (D.chronologicalAfterTime t ht)
      (D.chronologicalAfterTime_regular t ht))
    (D.chronologicalMinimumLocalParam_positive t ht hpositive hindex)


-- @@ L195-209 verbatim
/-- The distinguished dying component selected by the actual maximum circle. -/
def chronologicalMaximumLocalOrbit
    (D : ValueSeparatedSignedMorsePackage C)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum) :
    (D.chronologicalMaximumLocalField t ht).SelectedOrbitIndex
      ((D.signedOutput.sliceSign (D.chronologicalBeforeTime t ht)
        (D.chronologicalBeforeTime_regular t ht)).positiveOrbitCollection
          (D.chronologicalMaximumLocalField t ht)) :=
  (D.chronologicalMaximumLocalParam t ht hindex).selectedPositiveOrbitIndex
    (D.signedOutput.sliceSign (D.chronologicalBeforeTime t ht)
      (D.chronologicalBeforeTime_regular t ht))
    (D.chronologicalMaximumLocalParam_positive t ht hpositive hindex)


-- @@ L211-230 verbatim
theorem chronologicalMinimumLocalOrbit_class_one
    (D : ValueSeparatedSignedMorsePackage C)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum)
    (hclass : loopClassZ2
      (D.chronologicalMinimumLocalParam t ht hindex).paramFrameLoop
      (D.chronologicalMinimumLocalParam t ht hindex).paramFrameLoop_closed = 1) :
    (D.chronologicalMinimumLocalField t ht).orbitFrameClass
      (D.chronologicalMinimumLocalOrbit t ht hpositive hindex).1 = 1 := by
  calc
    (D.chronologicalMinimumLocalField t ht).orbitFrameClass
        (D.chronologicalMinimumLocalOrbit t ht hpositive hindex).1 =
        loopClassZ2
          (D.chronologicalMinimumLocalParam t ht hindex).paramFrameLoop
          (D.chronologicalMinimumLocalParam t ht hindex).paramFrameLoop_closed :=
      SimpleClosedOrbitParam.orbitFrameClass_selectedPositiveOrbitIndex
        (D.chronologicalMinimumLocalParam t ht hindex) _ _
    _ = 1 := hclass


-- @@ L232-251 verbatim
theorem chronologicalMaximumLocalOrbit_class_one
    (D : ValueSeparatedSignedMorsePackage C)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum)
    (hclass : loopClassZ2
      (D.chronologicalMaximumLocalParam t ht hindex).paramFrameLoop
      (D.chronologicalMaximumLocalParam t ht hindex).paramFrameLoop_closed = 1) :
    (D.chronologicalMaximumLocalField t ht).orbitFrameClass
      (D.chronologicalMaximumLocalOrbit t ht hpositive hindex).1 = 1 := by
  calc
    (D.chronologicalMaximumLocalField t ht).orbitFrameClass
        (D.chronologicalMaximumLocalOrbit t ht hpositive hindex).1 =
        loopClassZ2
          (D.chronologicalMaximumLocalParam t ht hindex).paramFrameLoop
          (D.chronologicalMaximumLocalParam t ht hindex).paramFrameLoop_closed :=
      SimpleClosedOrbitParam.orbitFrameClass_selectedPositiveOrbitIndex
        (D.chronologicalMaximumLocalParam t ht hindex) _ _
    _ = 1 := hclass


-- @@ L253-253 verbatim
/-! ## Transport of the distinguished local orbit to the bracket endpoint -/


-- @@ L255-270 verbatim
/-- Complete positive-component transport from the minimum's inner slice to
the literal outgoing event-bracket slice. -/
def chronologicalMinimumWindowTransport
    (D : ValueSeparatedSignedMorsePackage C)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    (D.chronologicalMinimumLocalField t ht).SelectedDeltaTransport
      (D.position.eventAfterField t ht)
      ((D.signedOutput.sliceSign (D.chronologicalAfterTime t ht)
        (D.chronologicalAfterTime_regular t ht)).positiveOrbitCollection
          (D.chronologicalMinimumLocalField t ht))
      ((D.signedOutput.sliceSign (D.position.eventBracket t ht).after
        (D.position.eventBracket t ht).after_regular).positiveOrbitCollection
          (D.position.eventAfterField t ht)) :=
  D.afterWindowPositiveTransport t ht
    (D.chronologicalMinimumLocalField t ht)
    (D.position.eventAfterField t ht)


-- @@ L272-288 verbatim
/-- Complete positive-component transport from the maximum's inner slice back
to the literal incoming event-bracket slice. -/
def chronologicalMaximumWindowTransport
    (D : ValueSeparatedSignedMorsePackage C)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    (D.chronologicalMaximumLocalField t ht).SelectedDeltaTransport
      (D.position.eventBeforeField t ht)
      ((D.signedOutput.sliceSign (D.chronologicalBeforeTime t ht)
        (D.chronologicalBeforeTime_regular t ht)).positiveOrbitCollection
          (D.chronologicalMaximumLocalField t ht))
      ((D.signedOutput.sliceSign (D.position.eventBracket t ht).before
        (D.position.eventBracket t ht).before_regular).positiveOrbitCollection
          (D.position.eventBeforeField t ht)) :=
  TamedField.SelectedDeltaTransport.symm
    (D.beforeWindowPositiveTransport t ht
      (D.position.eventBeforeField t ht)
      (D.chronologicalMaximumLocalField t ht))


-- @@ L290-305 verbatim
/-- The born production circle, transported to the outgoing bracket slice. -/
def chronologicalMinimumBracketOrbit
    (D : ValueSeparatedSignedMorsePackage C)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum) :
    (D.position.eventAfterField t ht).SelectedOrbitIndex
      ((D.signedOutput.sliceSign (D.position.eventBracket t ht).after
        (D.position.eventBracket t ht).after_regular).positiveOrbitCollection
          (D.position.eventAfterField t ht)) :=
  TamedField.SelectedDeltaTransport.selectedOrbitIndexEquiv
    (D.chronologicalMinimumLocalField t ht)
    (D.position.eventAfterField t ht)
    (D.chronologicalMinimumWindowTransport t ht)
    (D.chronologicalMinimumLocalOrbit t ht hpositive hindex)


-- @@ L307-322 verbatim
/-- The dying production circle, transported to the incoming bracket slice. -/
def chronologicalMaximumBracketOrbit
    (D : ValueSeparatedSignedMorsePackage C)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum) :
    (D.position.eventBeforeField t ht).SelectedOrbitIndex
      ((D.signedOutput.sliceSign (D.position.eventBracket t ht).before
        (D.position.eventBracket t ht).before_regular).positiveOrbitCollection
          (D.position.eventBeforeField t ht)) :=
  TamedField.SelectedDeltaTransport.selectedOrbitIndexEquiv
    (D.chronologicalMaximumLocalField t ht)
    (D.position.eventBeforeField t ht)
    (D.chronologicalMaximumWindowTransport t ht)
    (D.chronologicalMaximumLocalOrbit t ht hpositive hindex)


-- @@ L324-342 verbatim
theorem chronologicalMinimumBracketOrbit_class_one
    (D : ValueSeparatedSignedMorsePackage C)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum)
    (hclass : loopClassZ2
      (D.chronologicalMinimumLocalParam t ht hindex).paramFrameLoop
      (D.chronologicalMinimumLocalParam t ht hindex).paramFrameLoop_closed = 1) :
    (D.position.eventAfterField t ht).orbitFrameClass
      (D.chronologicalMinimumBracketOrbit t ht hpositive hindex).1 = 1 := by
  have htransport :=
    TamedField.SelectedDeltaTransport.orbitFrameClass_eq
      (D.chronologicalMinimumLocalField t ht)
      (D.position.eventAfterField t ht)
      (D.chronologicalMinimumWindowTransport t ht)
      (D.chronologicalMinimumLocalOrbit t ht hpositive hindex)
  exact htransport.symm.trans
    (D.chronologicalMinimumLocalOrbit_class_one t ht hpositive hindex hclass)


-- @@ L344-362 verbatim
theorem chronologicalMaximumBracketOrbit_class_one
    (D : ValueSeparatedSignedMorsePackage C)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum)
    (hclass : loopClassZ2
      (D.chronologicalMaximumLocalParam t ht hindex).paramFrameLoop
      (D.chronologicalMaximumLocalParam t ht hindex).paramFrameLoop_closed = 1) :
    (D.position.eventBeforeField t ht).orbitFrameClass
      (D.chronologicalMaximumBracketOrbit t ht hpositive hindex).1 = 1 := by
  have htransport :=
    TamedField.SelectedDeltaTransport.orbitFrameClass_eq
      (D.chronologicalMaximumLocalField t ht)
      (D.position.eventBeforeField t ht)
      (D.chronologicalMaximumWindowTransport t ht)
      (D.chronologicalMaximumLocalOrbit t ht hpositive hindex)
  exact htransport.symm.trans
    (D.chronologicalMaximumLocalOrbit_class_one t ht hpositive hindex hclass)


-- @@ L364-368 verbatim
/-! ## Actual production callbacks

The explicit exterior transport below is the remaining geometric event-crossing
input.  All local orbit, positivity, endpoint transport, and distinguished
class-one data are now constructed from the production package. -/


-- @@ L370-399 verbatim
/-- A production minimum with transport of the literal exterior complement
supplies the complete positive ledger move. -/
def minimumPositiveLedgerMove_of_exteriorTransport
    (D : ValueSeparatedSignedMorsePackage C)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum)
    (hclass : loopClassZ2
      (D.chronologicalMinimumLocalParam t ht hindex).paramFrameLoop
      (D.chronologicalMinimumLocalParam t ht hindex).paramFrameLoop_closed = 1)
    (exteriorTransport :
      (D.position.eventBeforeField t ht).SelectedDeltaTransport
        (D.position.eventAfterField t ht)
        ((D.signedOutput.sliceSign (D.position.eventBracket t ht).before
          (D.position.eventBracket t ht).before_regular).positiveOrbitCollection
            (D.position.eventBeforeField t ht))
        (((D.signedOutput.sliceSign (D.position.eventBracket t ht).after
          (D.position.eventBracket t ht).after_regular).positiveOrbitCollection
            (D.position.eventAfterField t ht)) \
          {(((D.chronologicalMinimumBracketOrbit t ht hpositive hindex).1 :
            (D.position.eventAfterField t ht).OrbitIndex) : Set E₁)})) :
    PositiveEventLedgerMoveData D.signedOutput D.position t ht :=
  PositiveEventLedgerMoveData.minimum_of_distinguished_complement_transport
    hindex (D.position.eventBeforeField t ht)
    (D.position.eventAfterField t ht)
    (D.chronologicalMinimumBracketOrbit t ht hpositive hindex)
    exteriorTransport
    (D.chronologicalMinimumBracketOrbit_class_one
      t ht hpositive hindex hclass)


-- @@ L401-430 verbatim
/-- A production maximum with the reverse transport of the literal exterior
complement supplies the complete positive ledger move. -/
def maximumPositiveLedgerMove_of_exteriorTransport
    (D : ValueSeparatedSignedMorsePackage C)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum)
    (hclass : loopClassZ2
      (D.chronologicalMaximumLocalParam t ht hindex).paramFrameLoop
      (D.chronologicalMaximumLocalParam t ht hindex).paramFrameLoop_closed = 1)
    (exteriorTransport :
      (D.position.eventAfterField t ht).SelectedDeltaTransport
        (D.position.eventBeforeField t ht)
        ((D.signedOutput.sliceSign (D.position.eventBracket t ht).after
          (D.position.eventBracket t ht).after_regular).positiveOrbitCollection
            (D.position.eventAfterField t ht))
        (((D.signedOutput.sliceSign (D.position.eventBracket t ht).before
          (D.position.eventBracket t ht).before_regular).positiveOrbitCollection
            (D.position.eventBeforeField t ht)) \
          {(((D.chronologicalMaximumBracketOrbit t ht hpositive hindex).1 :
            (D.position.eventBeforeField t ht).OrbitIndex) : Set E₁)})) :
    PositiveEventLedgerMoveData D.signedOutput D.position t ht :=
  PositiveEventLedgerMoveData.maximum_of_distinguished_complement_transport
    hindex (D.position.eventBeforeField t ht)
    (D.position.eventAfterField t ht)
    (D.chronologicalMaximumBracketOrbit t ht hpositive hindex)
    exteriorTransport
    (D.chronologicalMaximumBracketOrbit_class_one
      t ht hpositive hindex hclass)


-- @@ L432-455 verbatim
theorem nonempty_minimumPositiveLedgerMove_of_exteriorTransport
    (D : ValueSeparatedSignedMorsePackage C)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum)
    (hclass : loopClassZ2
      (D.chronologicalMinimumLocalParam t ht hindex).paramFrameLoop
      (D.chronologicalMinimumLocalParam t ht hindex).paramFrameLoop_closed = 1)
    (exteriorTransport :
      (D.position.eventBeforeField t ht).SelectedDeltaTransport
        (D.position.eventAfterField t ht)
        ((D.signedOutput.sliceSign (D.position.eventBracket t ht).before
          (D.position.eventBracket t ht).before_regular).positiveOrbitCollection
            (D.position.eventBeforeField t ht))
        (((D.signedOutput.sliceSign (D.position.eventBracket t ht).after
          (D.position.eventBracket t ht).after_regular).positiveOrbitCollection
            (D.position.eventAfterField t ht)) \
          {(((D.chronologicalMinimumBracketOrbit t ht hpositive hindex).1 :
            (D.position.eventAfterField t ht).OrbitIndex) : Set E₁)})) :
    Nonempty (PositiveEventLedgerMoveData
      D.signedOutput D.position t ht) :=
  ⟨D.minimumPositiveLedgerMove_of_exteriorTransport
    t ht hpositive hindex hclass exteriorTransport⟩


-- @@ L457-480 verbatim
theorem nonempty_maximumPositiveLedgerMove_of_exteriorTransport
    (D : ValueSeparatedSignedMorsePackage C)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum)
    (hclass : loopClassZ2
      (D.chronologicalMaximumLocalParam t ht hindex).paramFrameLoop
      (D.chronologicalMaximumLocalParam t ht hindex).paramFrameLoop_closed = 1)
    (exteriorTransport :
      (D.position.eventAfterField t ht).SelectedDeltaTransport
        (D.position.eventBeforeField t ht)
        ((D.signedOutput.sliceSign (D.position.eventBracket t ht).after
          (D.position.eventBracket t ht).after_regular).positiveOrbitCollection
            (D.position.eventAfterField t ht))
        (((D.signedOutput.sliceSign (D.position.eventBracket t ht).before
          (D.position.eventBracket t ht).before_regular).positiveOrbitCollection
            (D.position.eventBeforeField t ht)) \
          {(((D.chronologicalMaximumBracketOrbit t ht hpositive hindex).1 :
            (D.position.eventBeforeField t ht).OrbitIndex) : Set E₁)})) :
    Nonempty (PositiveEventLedgerMoveData
      D.signedOutput D.position t ht) :=
  ⟨D.maximumPositiveLedgerMove_of_exteriorTransport
    t ht hpositive hindex hclass exteriorTransport⟩


-- @@ L482-482 verbatim
end ValueSeparatedSignedMorsePackage

-- @@ L483-483 verbatim
end Submission
