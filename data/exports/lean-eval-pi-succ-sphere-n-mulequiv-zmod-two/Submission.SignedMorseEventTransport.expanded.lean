import Mathlib
import Submission.MorseEventBracketExistence
import Submission.MorseLedgerPermutation
import Submission.SignedMorseBridge


-- @@ L6-28 verbatim
/-!
# Sign-aware component transport at Morse events

The positive invariant only sees critical events on the positive sheet.  The
previous component-excision interface nevertheless compared *every* event with
the positively signed literal birth/saddle model.  At a negative-sheet event
this is the wrong obligation: a sign-constant event neighbourhood contains no
positive local component, whereas the positive literal model can contain one
or two components.

This file splits the event resolution using the existing
`LabeledMorsePosition` partition.

* At a positive event the corrected minimal interface records the actual
  birth/death/saddle move on component frame ledgers, retaining an arbitrary
  common exterior tail.
* At a negative event the local model is absent.  The only relevant datum is a
  transport of the complete positive component family across the bracket.

Both data directly produce an `EventDeltaCrossing`.  The earlier componentwise
positive-event interface is retained below for compatibility, but is not
needed by the tail-aware endpoint theorem.
-/


-- @@ L30-30 verbatim
noncomputable section


-- @@ L32-32 verbatim
namespace Submission


-- @@ L34-34 verbatim
open Set


-- @@ L36-36 verbatim
variable {n : ℕ}

-- @@ L37-37 verbatim
variable {X₀ X₁ : FramedLevelSet n}

-- @@ L38-38 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}


-- @@ L40-40 verbatim
/-! ## Negative-sheet events -/


-- @@ L42-64 verbatim
/-- At a negative-sheet Morse event, the positive invariant has no local
birth/saddle piece.  Its complete positive component family is exterior to the
event neighbourhood, so one selected component transport is the entire
geometric input needed at the bracket.

The tamed fields are left arbitrary.  They are auxiliary choices and an
event-adapted construction should not have to identify them with a canonical
`Classical.choice`. -/
structure NegativeEventPositiveExteriorTransportData
    (C : SignedFramedLevelCobordism S₀ S₁)
    (P : MorsePosition C.cobordism)
    (t : ℝ) (ht : t ∈ P.eventTimes) where
  beforeField : TamedField
    (SlabTamedField.sliceFLSAt C.cobordism.toLevelCobordismData
      (P.eventBracket t ht).before (P.eventBracket t ht).before_regular)
  afterField : TamedField
    (SlabTamedField.sliceFLSAt C.cobordism.toLevelCobordismData
      (P.eventBracket t ht).after (P.eventBracket t ht).after_regular)
  exteriorTransport : beforeField.SelectedDeltaTransport afterField
    ((C.sliceSign (P.eventBracket t ht).before
      (P.eventBracket t ht).before_regular).positiveOrbitCollection beforeField)
    ((C.sliceSign (P.eventBracket t ht).after
      (P.eventBracket t ht).after_regular).positiveOrbitCollection afterField)


-- @@ L66-66 verbatim
namespace NegativeEventPositiveExteriorTransportData


-- @@ L68-68 verbatim
variable {C : SignedFramedLevelCobordism S₀ S₁}

-- @@ L69-69 verbatim
variable {P : MorsePosition C.cobordism}

-- @@ L70-70 verbatim
variable {t : ℝ} {ht : t ∈ P.eventTimes}


-- @@ L72-94 verbatim
/-- Transport of all positive components across a negative event proves the
actual complete-slice delta equality. -/
theorem slice_positiveDelta_eq
    (D : NegativeEventPositiveExteriorTransportData C P t ht) :
    (C.sliceSign (P.eventBracket t ht).before
        (P.eventBracket t ht).before_regular).positiveDelta =
      (C.sliceSign (P.eventBracket t ht).after
        (P.eventBracket t ht).after_regular).positiveDelta := by
  let Sbefore := C.sliceSign (P.eventBracket t ht).before
    (P.eventBracket t ht).before_regular
  let Safter := C.sliceSign (P.eventBracket t ht).after
    (P.eventBracket t ht).after_regular
  calc
    Sbefore.positiveDelta = Sbefore.positiveFramedDelta D.beforeField :=
      Sbefore.positiveDelta_eq D.beforeField
    _ = Safter.positiveFramedDelta D.afterField := by
      change D.beforeField.deltaOn
          (Sbefore.positiveOrbitCollection D.beforeField) =
        D.afterField.deltaOn
          (Safter.positiveOrbitCollection D.afterField)
      exact D.exteriorTransport.deltaOn_eq
    _ = Safter.positiveDelta :=
      (Safter.positiveDelta_eq D.afterField).symm


-- @@ L96-108 verbatim
/-- The canonical chronological bracket and the preceding complete-slice
equality give the induction-ready crossing. -/
def toEventDeltaCrossing
    (D : NegativeEventPositiveExteriorTransportData C P t ht) :
    EventDeltaCrossing C (P.eventCenter t ht) where
  before := (P.eventBracket t ht).before
  after := (P.eventBracket t ht).after
  before_lt := (P.eventBracket t ht).before_lt
  lt_after := (P.eventBracket t ht).lt_after
  before_regular := (P.eventBracket t ht).before_regular
  after_regular := (P.eventBracket t ht).after_regular
  isolates := (P.eventBracket t ht).isolates
  delta_eq := D.slice_positiveDelta_eq


-- @@ L110-110 verbatim
end NegativeEventPositiveExteriorTransportData


-- @@ L112-112 verbatim
/-! ## Tail-aware positive-sheet event moves -/


-- @@ L114-143 verbatim
/-- One actual Morse move on component frame ledgers, with the chronological
direction fixed by the Morse index.  The `Perm` fields account only for the
arbitrary enumeration of geometric orbit components.

Unlike transport to a fixed literal model, the saddle constructors retain the
incoming frame classes `β₁`, `β₂` and the common exterior `tail`.  Thus they
state the genuine splice relation `βhat = β₁ + β₂ + 1` without requiring the
individual complete circles to have the frame classes of a standard model. -/
inductive IndexedMorseLedgerMove :
    MorseIndexTwo → MorseLedger → MorseLedger → Prop
  | minimum (tail : MorseLedger) {before after : MorseLedger}
      (before_perm : before.Perm tail)
      (after_perm : after.Perm (1 :: tail)) :
      IndexedMorseLedgerMove .minimum before after
  | maximum (tail : MorseLedger) {before after : MorseLedger}
      (before_perm : before.Perm (1 :: tail))
      (after_perm : after.Perm tail) :
      IndexedMorseLedgerMove .maximum before after
  | saddleMerge (β₁ β₂ βhat : ZMod 2) (tail : MorseLedger)
      {before after : MorseLedger}
      (splice : βhat = β₁ + β₂ + 1)
      (before_perm : before.Perm (β₁ :: β₂ :: tail))
      (after_perm : after.Perm (βhat :: tail)) :
      IndexedMorseLedgerMove .saddle before after
  | saddleSplit (β₁ β₂ βhat : ZMod 2) (tail : MorseLedger)
      {before after : MorseLedger}
      (splice : βhat = β₁ + β₂ + 1)
      (before_perm : before.Perm (βhat :: tail))
      (after_perm : after.Perm (β₁ :: β₂ :: tail)) :
      IndexedMorseLedgerMove .saddle before after


-- @@ L145-145 verbatim
namespace IndexedMorseLedgerMove


-- @@ L147-147 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L149-161 verbatim
/-- Component geometry expressed as an `Option`-extension directly supplies
the index-aware minimum move required by `PositiveEventLedgerMoveData`. -/
theorem minimum_of_option_equiv
    {X Y : FramedLevelSet n} (V : TamedField X) (W : TamedField Y)
    (A B : Set (Set E))
    (e : Option (V.SelectedOrbitIndex A) ≃ W.SelectedOrbitIndex B)
    (hnone : W.orbitFrameClass (e none).1 = 1)
    (hsome : ∀ O : V.SelectedOrbitIndex A,
      V.orbitFrameClass O.1 = W.orbitFrameClass (e (some O)).1) :
    IndexedMorseLedgerMove .minimum
      (V.selectedFrameLedger A) (W.selectedFrameLedger B) := by
  exact .minimum (V.selectedFrameLedger A) (.refl _)
    (V.selectedFrameLedger_perm_cons_of_option_equiv W A B e hnone hsome)


-- @@ L163-176 verbatim
/-- The identical component correspondence, read in the reverse chronological
direction, supplies a maximum move. -/
theorem maximum_of_option_equiv
    {X Y : FramedLevelSet n} (V : TamedField X) (W : TamedField Y)
    (A B : Set (Set E))
    (e : Option (V.SelectedOrbitIndex A) ≃ W.SelectedOrbitIndex B)
    (hnone : W.orbitFrameClass (e none).1 = 1)
    (hsome : ∀ O : V.SelectedOrbitIndex A,
      V.orbitFrameClass O.1 = W.orbitFrameClass (e (some O)).1) :
    IndexedMorseLedgerMove .maximum
      (W.selectedFrameLedger B) (V.selectedFrameLedger A) := by
  exact .maximum (V.selectedFrameLedger A)
    (V.selectedFrameLedger_perm_cons_of_option_equiv W A B e hnone hsome)
    (.refl _)


-- @@ L178-194 verbatim
/-- Distinguished-new-component geometry is the form produced by local
definite-event excision: old components match the complement of the born
circle. -/
theorem minimum_of_distinguished_equiv
    {X Y : FramedLevelSet n} (V : TamedField X) (W : TamedField Y)
    (A B : Set (Set E))
    (new : W.SelectedOrbitIndex B)
    (e : V.SelectedOrbitIndex A ≃
      {O : W.SelectedOrbitIndex B // O ≠ new})
    (hnew : W.orbitFrameClass new.1 = 1)
    (hclass : ∀ O : V.SelectedOrbitIndex A,
      V.orbitFrameClass O.1 = W.orbitFrameClass (e O).1.1) :
    IndexedMorseLedgerMove .minimum
      (V.selectedFrameLedger A) (W.selectedFrameLedger B) := by
  exact .minimum (V.selectedFrameLedger A) (.refl _)
    (V.selectedFrameLedger_perm_cons_of_distinguished_equiv W A B new e
      hnew hclass)


-- @@ L196-211 verbatim
/-- Reverse the preceding distinguished-component birth into a maximum
move. -/
theorem maximum_of_distinguished_equiv
    {X Y : FramedLevelSet n} (V : TamedField X) (W : TamedField Y)
    (A B : Set (Set E))
    (new : W.SelectedOrbitIndex B)
    (e : V.SelectedOrbitIndex A ≃
      {O : W.SelectedOrbitIndex B // O ≠ new})
    (hnew : W.orbitFrameClass new.1 = 1)
    (hclass : ∀ O : V.SelectedOrbitIndex A,
      V.orbitFrameClass O.1 = W.orbitFrameClass (e O).1.1) :
    IndexedMorseLedgerMove .maximum
      (W.selectedFrameLedger B) (V.selectedFrameLedger A) := by
  exact .maximum (V.selectedFrameLedger A)
    (V.selectedFrameLedger_perm_cons_of_distinguished_equiv W A B new e
      hnew hclass) (.refl _)


-- @@ L213-226 verbatim
/-- A geometric transport of all old components onto the complement of one
class-one newborn component is already the full minimum ledger move. -/
theorem minimum_of_distinguished_complement_transport
    {X Y : FramedLevelSet n} (V : TamedField X) (W : TamedField Y)
    (A B : Set (Set E))
    (new : W.SelectedOrbitIndex B)
    (T : V.SelectedDeltaTransport W A
      (B \ {((new.1 : W.OrbitIndex) : Set E)}))
    (hnew : W.orbitFrameClass new.1 = 1) :
    IndexedMorseLedgerMove .minimum
      (V.selectedFrameLedger A) (W.selectedFrameLedger B) := by
  exact .minimum (V.selectedFrameLedger A) (.refl _)
    (TamedField.SelectedDeltaTransport.selectedFrameLedger_perm_cons_of_distinguished_complement
      V W new T hnew)


-- @@ L228-242 verbatim
/-- The same transported-complement package read backwards is the full
maximum move. -/
theorem maximum_of_distinguished_complement_transport
    {X Y : FramedLevelSet n} (V : TamedField X) (W : TamedField Y)
    (A B : Set (Set E))
    (new : W.SelectedOrbitIndex B)
    (T : V.SelectedDeltaTransport W A
      (B \ {((new.1 : W.OrbitIndex) : Set E)}))
    (hnew : W.orbitFrameClass new.1 = 1) :
    IndexedMorseLedgerMove .maximum
      (W.selectedFrameLedger B) (V.selectedFrameLedger A) := by
  exact .maximum (V.selectedFrameLedger A)
    (TamedField.SelectedDeltaTransport.selectedFrameLedger_perm_cons_of_distinguished_complement
      V W new T hnew)
    (.refl _)


-- @@ L244-264 verbatim
/-- Every index-correct event move preserves the complete ledger delta. -/
theorem delta_eq {index : MorseIndexTwo} {before after : MorseLedger}
    (M : IndexedMorseLedgerMove index before after) :
    before.delta = after.delta := by
  cases M with
  | minimum tail hbefore hafter =>
      exact (MorseLedger.delta_eq_of_perm hbefore).trans
        ((MorseLedgerStep.birth tail).delta_eq.trans
          (MorseLedger.delta_eq_of_perm hafter).symm)
  | maximum tail hbefore hafter =>
      exact (MorseLedger.delta_eq_of_perm hbefore).trans
        ((MorseLedgerStep.death tail).delta_eq.trans
          (MorseLedger.delta_eq_of_perm hafter).symm)
  | saddleMerge β₁ β₂ βhat tail hsplice hbefore hafter =>
      exact (MorseLedger.delta_eq_of_perm hbefore).trans
        ((MorseLedgerStep.saddleMerge β₁ β₂ βhat tail hsplice).delta_eq.trans
          (MorseLedger.delta_eq_of_perm hafter).symm)
  | saddleSplit β₁ β₂ βhat tail hsplice hbefore hafter =>
      exact (MorseLedger.delta_eq_of_perm hbefore).trans
        ((MorseLedgerStep.saddleSplit β₁ β₂ βhat tail hsplice).delta_eq.trans
          (MorseLedger.delta_eq_of_perm hafter).symm)


-- @@ L266-266 verbatim
end IndexedMorseLedgerMove


-- @@ L268-285 verbatim
/-- Tail-aware positive-sheet geometry at one event.  The ledgers are extracted
from the actual complete positive orbit families on the two regular bracket
slices; the only local input is the index-correct birth/death/splice move. -/
structure PositiveEventLedgerMoveData
    (C : SignedFramedLevelCobordism S₀ S₁)
    (P : MorsePosition C.cobordism)
    (t : ℝ) (ht : t ∈ P.eventTimes) where
  beforeField : TamedField
    (SlabTamedField.sliceFLSAt C.cobordism.toLevelCobordismData
      (P.eventBracket t ht).before (P.eventBracket t ht).before_regular)
  afterField : TamedField
    (SlabTamedField.sliceFLSAt C.cobordism.toLevelCobordismData
      (P.eventBracket t ht).after (P.eventBracket t ht).after_regular)
  move : IndexedMorseLedgerMove (P.eventModel t ht).index
    ((C.sliceSign (P.eventBracket t ht).before
      (P.eventBracket t ht).before_regular).positiveFrameLedger beforeField)
    ((C.sliceSign (P.eventBracket t ht).after
      (P.eventBracket t ht).after_regular).positiveFrameLedger afterField)


-- @@ L287-287 verbatim
namespace PositiveEventLedgerMoveData


-- @@ L289-289 verbatim
variable {C : SignedFramedLevelCobordism S₀ S₁}

-- @@ L290-290 verbatim
variable {P : MorsePosition C.cobordism}

-- @@ L291-291 verbatim
variable {t : ℝ} {ht : t ∈ P.eventTimes}


-- @@ L293-313 verbatim
/-- An actual index-correct ledger move proves equality of the complete positive
slice deltas while retaining arbitrary exterior frame classes in its tail. -/
theorem slice_positiveDelta_eq (D : PositiveEventLedgerMoveData C P t ht) :
    (C.sliceSign (P.eventBracket t ht).before
        (P.eventBracket t ht).before_regular).positiveDelta =
      (C.sliceSign (P.eventBracket t ht).after
        (P.eventBracket t ht).after_regular).positiveDelta := by
  let Sbefore := C.sliceSign (P.eventBracket t ht).before
    (P.eventBracket t ht).before_regular
  let Safter := C.sliceSign (P.eventBracket t ht).after
    (P.eventBracket t ht).after_regular
  calc
    Sbefore.positiveDelta = Sbefore.positiveFramedDelta D.beforeField :=
      Sbefore.positiveDelta_eq D.beforeField
    _ = (Sbefore.positiveFrameLedger D.beforeField).delta :=
      (Sbefore.positiveFrameLedger_delta D.beforeField).symm
    _ = (Safter.positiveFrameLedger D.afterField).delta := D.move.delta_eq
    _ = Safter.positiveFramedDelta D.afterField :=
      Safter.positiveFrameLedger_delta D.afterField
    _ = Safter.positiveDelta :=
      (Safter.positiveDelta_eq D.afterField).symm


-- @@ L315-325 verbatim
/-- Package the ledger calculation with the canonical isolating bracket. -/
def toEventDeltaCrossing (D : PositiveEventLedgerMoveData C P t ht) :
    EventDeltaCrossing C (P.eventCenter t ht) where
  before := (P.eventBracket t ht).before
  after := (P.eventBracket t ht).after
  before_lt := (P.eventBracket t ht).before_lt
  lt_after := (P.eventBracket t ht).lt_after
  before_regular := (P.eventBracket t ht).before_regular
  after_regular := (P.eventBracket t ht).after_regular
  isolates := (P.eventBracket t ht).isolates
  delta_eq := D.slice_positiveDelta_eq


-- @@ L327-327 verbatim
end PositiveEventLedgerMoveData


-- @@ L329-329 verbatim
/-! ## Sign-aware event resolution -/


-- @@ L331-344 verbatim
/-- The geometrically correct component resolution of one signed Morse event.

Membership in `positiveCenters` or `negativeCenters` is retained in the
constructors, so the two alternatives cannot be used for the wrong sheet. -/
inductive SignedEventComponentTransportData
    (C : SignedFramedLevelCobordism S₀ S₁)
    (P : MorsePosition C.cobordism) (hn : 2 ≤ n)
    (t : ℝ) (ht : t ∈ P.eventTimes) : Type
  | positive
      (hcenter : P.eventCenter t ht ∈ (C.labelMorsePosition P).positiveCenters)
      (data : FramedEventComponentTransportData C P hn t ht)
  | negative
      (hcenter : P.eventCenter t ht ∈ (C.labelMorsePosition P).negativeCenters)
      (data : NegativeEventPositiveExteriorTransportData C P t ht)


-- @@ L346-346 verbatim
namespace SignedEventComponentTransportData


-- @@ L348-348 verbatim
variable {C : SignedFramedLevelCobordism S₀ S₁}

-- @@ L349-349 verbatim
variable {P : MorsePosition C.cobordism} {hn : 2 ≤ n}

-- @@ L350-350 verbatim
variable {t : ℝ} {ht : t ∈ P.eventTimes}


-- @@ L352-362 verbatim
/-- Both sign-correct alternatives produce the same chronological crossing
consumed by the finite Morse schedule. -/
def toEventDeltaCrossing
    (D : SignedEventComponentTransportData C P hn t ht) :
    EventDeltaCrossing C (P.eventCenter t ht) := by
  cases D with
  | positive _ K =>
      exact K.toFramedEventExcisionData.toEventDeltaCrossing C
        (P.eventModel t ht) (P.eventDeltaModel hn t ht)
  | negative _ K =>
      exact K.toEventDeltaCrossing


-- @@ L364-364 verbatim
end SignedEventComponentTransportData


-- @@ L366-366 verbatim
namespace MorsePosition


-- @@ L368-368 verbatim
variable {C : SignedFramedLevelCobordism S₀ S₁}


-- @@ L370-390 verbatim
/-- Existing positive/negative center separation chooses the correct event
resolution branch.  No independent sign-decision hypothesis is introduced. -/
theorem signedEventComponentTransportData_of_branches
    (P : MorsePosition C.cobordism) (hn : 2 ≤ n)
    (positive : ∀ (t : ℝ) (ht : t ∈ P.eventTimes),
      P.eventCenter t ht ∈ (C.labelMorsePosition P).positiveCenters →
        Nonempty (FramedEventComponentTransportData C P hn t ht))
    (negative : ∀ (t : ℝ) (ht : t ∈ P.eventTimes),
      P.eventCenter t ht ∈ (C.labelMorsePosition P).negativeCenters →
        Nonempty (NegativeEventPositiveExteriorTransportData C P t ht))
    (t : ℝ) (ht : t ∈ P.eventTimes) :
    Nonempty (SignedEventComponentTransportData C P hn t ht) := by
  have hcenter :
      P.eventCenter t ht ∈ (C.labelMorsePosition P).position.centers := by
    exact P.eventCenter_mem t ht
  rcases (C.labelMorsePosition P).event_mem_positive_or_negative hcenter with
    hpositive | hnegative
  · obtain ⟨D⟩ := positive t ht hpositive
    exact ⟨SignedEventComponentTransportData.positive hpositive D⟩
  · obtain ⟨D⟩ := negative t ht hnegative
    exact ⟨SignedEventComponentTransportData.negative hnegative D⟩


-- @@ L392-400 verbatim
/-- A sign-aware component resolution at every event gives the complete family
of induction-ready crossings. -/
theorem eventDeltaCrossings_of_signedComponentTransports
    (P : MorsePosition C.cobordism) (hn : 2 ≤ n)
    (K : ∀ (t : ℝ) (ht : t ∈ P.eventTimes),
      Nonempty (SignedEventComponentTransportData C P hn t ht)) :
    P.EventDeltaCrossings := by
  intro t ht
  exact ⟨(K t ht).some.toEventDeltaCrossing⟩


-- @@ L402-414 verbatim
/-- Branchwise positive-event excision and negative-event exterior transport
are sufficient for every chronological crossing. -/
theorem eventDeltaCrossings_of_labeledComponentTransports
    (P : MorsePosition C.cobordism) (hn : 2 ≤ n)
    (positive : ∀ (t : ℝ) (ht : t ∈ P.eventTimes),
      P.eventCenter t ht ∈ (C.labelMorsePosition P).positiveCenters →
        Nonempty (FramedEventComponentTransportData C P hn t ht))
    (negative : ∀ (t : ℝ) (ht : t ∈ P.eventTimes),
      P.eventCenter t ht ∈ (C.labelMorsePosition P).negativeCenters →
        Nonempty (NegativeEventPositiveExteriorTransportData C P t ht)) :
    P.EventDeltaCrossings :=
  P.eventDeltaCrossings_of_signedComponentTransports hn fun t ht =>
    P.signedEventComponentTransportData_of_branches hn positive negative t ht


-- @@ L416-428 verbatim
/-- End-to-end signed delta invariance with the impossible negative-event local
model comparison removed. -/
theorem endpoint_positiveDelta_eq_of_labeledComponentTransports
    (P : MorsePosition C.cobordism) (hn : 2 ≤ n)
    (positive : ∀ (t : ℝ) (ht : t ∈ P.eventTimes),
      P.eventCenter t ht ∈ (C.labelMorsePosition P).positiveCenters →
        Nonempty (FramedEventComponentTransportData C P hn t ht))
    (negative : ∀ (t : ℝ) (ht : t ∈ P.eventTimes),
      P.eventCenter t ht ∈ (C.labelMorsePosition P).negativeCenters →
        Nonempty (NegativeEventPositiveExteriorTransportData C P t ht)) :
    S₀.positiveDelta = S₁.positiveDelta :=
  P.endpoint_positiveDelta_eq_of_eventCrossings
    (P.eventDeltaCrossings_of_labeledComponentTransports hn positive negative)


-- @@ L430-449 verbatim
/-- The corrected minimal event kernel: a positive event supplies one
index-correct ledger move with an arbitrary exterior tail, while a negative
event supplies only transport of the positive exterior components. -/
theorem eventDeltaCrossings_of_labeledLedgerMoves
    (P : MorsePosition C.cobordism)
    (positive : ∀ (t : ℝ) (ht : t ∈ P.eventTimes),
      P.eventCenter t ht ∈ (C.labelMorsePosition P).positiveCenters →
        Nonempty (PositiveEventLedgerMoveData C P t ht))
    (negative : ∀ (t : ℝ) (ht : t ∈ P.eventTimes),
      P.eventCenter t ht ∈ (C.labelMorsePosition P).negativeCenters →
        Nonempty (NegativeEventPositiveExteriorTransportData C P t ht)) :
    P.EventDeltaCrossings := by
  intro t ht
  have hcenter :
      P.eventCenter t ht ∈ (C.labelMorsePosition P).position.centers := by
    exact P.eventCenter_mem t ht
  rcases (C.labelMorsePosition P).event_mem_positive_or_negative hcenter with
    hpositive | hnegative
  · exact ⟨(positive t ht hpositive).some.toEventDeltaCrossing⟩
  · exact ⟨(negative t ht hnegative).some.toEventDeltaCrossing⟩


-- @@ L451-464 verbatim
/-- Tail-aware event moves and negative-sheet exterior transport prove the
original endpoint invariant without any comparison of complete circles with a
fixed literal local model. -/
theorem endpoint_positiveDelta_eq_of_labeledLedgerMoves
    (P : MorsePosition C.cobordism)
    (positive : ∀ (t : ℝ) (ht : t ∈ P.eventTimes),
      P.eventCenter t ht ∈ (C.labelMorsePosition P).positiveCenters →
        Nonempty (PositiveEventLedgerMoveData C P t ht))
    (negative : ∀ (t : ℝ) (ht : t ∈ P.eventTimes),
      P.eventCenter t ht ∈ (C.labelMorsePosition P).negativeCenters →
        Nonempty (NegativeEventPositiveExteriorTransportData C P t ht)) :
    S₀.positiveDelta = S₁.positiveDelta :=
  P.endpoint_positiveDelta_eq_of_eventCrossings
    (P.eventDeltaCrossings_of_labeledLedgerMoves positive negative)


-- @@ L466-466 verbatim
end MorsePosition


-- @@ L468-468 verbatim
end Submission
