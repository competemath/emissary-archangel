import Mathlib
import Submission.IndexedMorsePositionAssembly
import Submission.SignedMorseLedgerResolution


-- @@ L5-25 verbatim
/-!
# Retaining the production Morse construction through signed event resolution

The assumption-free Morse existence theorem is a two-stage construction: a
shared-cutoff perturbation is followed by a value-separating perturbation.  A
single composed `SignedMorsePerturbation` is convenient for the old public
interface, but it forgets the finite cover, the installed critical events, and
their owners.  Those are exactly the data needed by the local positive-event
geometry.

This module retains the complete production witness.  Its `signedOutput` is
formed by the two signed pullbacks themselves, so its underlying cobordism is
definitionally the output carrying `StableCriticalValueShiftData`'s indexed
Morse position.  Consequently no equality cast and no choice-based
`MorseAtlas.toMorsePosition` occurs in the event-resolution path.

The final theorem of the module also removes an unnecessarily strong earlier
interface: positive ledger moves need only be constructed for these actual
production packages, rather than for every arbitrary perturbation and every
arbitrary Morse position.
-/


-- @@ L27-27 verbatim
set_option autoImplicit false

-- @@ L28-28 verbatim
noncomputable section


-- @@ L30-30 verbatim
namespace Submission


-- @@ L32-32 verbatim
open Set


-- @@ L34-34 verbatim
variable {n : ℕ}


-- @@ L36-36 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L38-52 verbatim
/-- All choices made by the proved shared-cutoff/value-separation construction,
retained together instead of being erased after producing a bare Morse atlas. -/
structure ValueSeparatedSignedMorsePackage
    {X₀ X₁ : FramedLevelSet n} {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}
    (C : SignedFramedLevelCobordism S₀ S₁) where
  indices : Finset C.cobordism.fiber
  cover : FiniteIFTSurfaceCover C.cobordism (↥indices)
  lower : ℝ
  upper : ℝ
  support : Set E'
  cutoff : SmoothCutoff
    (compactInteriorFiber C.cobordism lower upper) support
  first : cover.SharedCutoffMorseData cutoff
  second :
    FiniteIFTSurfaceCover.SharedCutoffMorseData.StableCriticalValueShiftData first


-- @@ L54-54 verbatim
namespace ValueSeparatedSignedMorsePackage


-- @@ L56-56 verbatim
variable {X₀ X₁ : FramedLevelSet n} {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}

-- @@ L57-57 verbatim
variable {C : SignedFramedLevelCobordism S₀ S₁}


-- @@ L59-62 verbatim
/-- The signed output after the first, shared-cutoff pullback. -/
def firstSignedOutput (D : ValueSeparatedSignedMorsePackage C) :
    SignedFramedLevelCobordism S₀ S₁ :=
  D.first.amplitude.toVerticalAmplitude.pullbackSigned C


-- @@ L64-70 verbatim
/-- The actual two-stage signed output.  Keeping the two pullbacks staged makes
its underlying unsigned cobordism definitionally equal to the value-separated
output on which the installed event models live. -/
def signedOutput (D : ValueSeparatedSignedMorsePackage C) :
    SignedFramedLevelCobordism S₀ S₁ :=
  D.second.toCriticalValueShiftData.amplitude.toVerticalAmplitude.pullbackSigned
    D.firstSignedOutput


-- @@ L72-74 verbatim
@[simp] theorem firstSignedOutput_cobordism
    (D : ValueSeparatedSignedMorsePackage C) :
    D.firstSignedOutput.cobordism = D.first.output := rfl


-- @@ L76-79 verbatim
@[simp] theorem signedOutput_cobordism
    (D : ValueSeparatedSignedMorsePackage C) :
    D.signedOutput.cobordism =
      D.second.toCriticalValueShiftData.output := rfl


-- @@ L81-85 verbatim
/-- The exact production schedule, indexed by duplicate-free global critical
events and storing the transported installed model at every center. -/
def position (D : ValueSeparatedSignedMorsePackage C) :
    MorsePosition D.signedOutput.cobordism :=
  D.second.toIndexedMorsePosition


-- @@ L87-89 verbatim
@[simp] theorem position_eq_indexed
    (D : ValueSeparatedSignedMorsePackage C) :
    D.position = D.second.toIndexedMorsePosition := rfl


-- @@ L91-96 verbatim
/-- The duplicate-free global event underlying a chronological event of the
retained production schedule. -/
def chronologicalGlobalEvent (D : ValueSeparatedSignedMorsePackage C)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    FiniteIFTSurfaceCover.SharedCutoffMorseData.GlobalCriticalEvent D.first :=
  D.second.chronologicalGlobalEvent t ht


-- @@ L98-106 verbatim
/-- The chronological model is exactly the transported production event. -/
theorem eventModel_eq_transportedStandardMorseEvent
    (D : ValueSeparatedSignedMorsePackage C)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    D.position.eventModel t ht =
      D.second.shiftedCenter_chronologicalGlobalEvent t ht ▸
        D.second.toCriticalValueShiftData.transportedStandardMorseEvent
          (D.chronologicalGlobalEvent t ht) :=
  D.second.eventModel_eq_transportedStandardMorseEvent t ht


-- @@ L108-116 verbatim
/-- In particular the retained chronological index is the installed owner
model's index, with no `Nonempty.some` choice in between. -/
theorem eventModel_index_eq_ownerModel
    (D : ValueSeparatedSignedMorsePackage C)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    (D.position.eventModel t ht).index =
      (D.second.toCriticalValueShiftData.ownerModel
        (D.chronologicalGlobalEvent t ht)).index :=
  D.second.eventModel_index_eq_ownerModel t ht


-- @@ L118-134 verbatim
/-- Every signed framed cobordism has a retained production package. -/
theorem nonempty (C : SignedFramedLevelCobordism S₀ S₁) :
    Nonempty (ValueSeparatedSignedMorsePackage C) := by
  obtain ⟨s, ⟨B⟩⟩ := exists_finiteIFTSurfaceCover C.cobordism
  obtain ⟨a, b, U, χ, _ha, _hab, _hb, _hU, ⟨R⟩⟩ :=
    FiniteIFTSurfaceCover.SharedCutoffMorseData.exists_globalCutoffMorseData B
  obtain ⟨S⟩ := R.nonempty_stableCriticalValueShiftData
  exact ⟨{
    indices := s
    cover := B
    lower := a
    upper := b
    support := U
    cutoff := χ
    first := R
    second := S
  }⟩


-- @@ L136-140 verbatim
/-- A fixed production package, useful when consumers prefer data rather than
an existential theorem. -/
def chosen (C : SignedFramedLevelCobordism S₀ S₁) :
    ValueSeparatedSignedMorsePackage C :=
  (nonempty C).some


-- @@ L142-142 verbatim
end ValueSeparatedSignedMorsePackage


-- @@ L144-144 verbatim
/-! ## Direct signed event resolution on the retained output -/


-- @@ L146-159 verbatim
/-- A production package whose actual positive events have been resolved into
tail-aware ledger moves.  Negative events require no additional field: the
localized slab transport already transports the whole positive exterior. -/
structure ValueSeparatedPositiveLedgerResolution
    {X₀ X₁ : FramedLevelSet n} {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}
    (C : SignedFramedLevelCobordism S₀ S₁) where
  package : ValueSeparatedSignedMorsePackage C
  positiveMoves : ∀ (t : ℝ) (ht : t ∈ package.position.eventTimes),
    package.position.eventCenter t ht ∈
        (package.signedOutput.labelMorsePosition
          package.position).positiveCenters →
      Nonempty
        (PositiveEventLedgerMoveData
          package.signedOutput package.position t ht)


-- @@ L161-161 verbatim
namespace ValueSeparatedPositiveLedgerResolution


-- @@ L163-163 verbatim
variable {X₀ X₁ : FramedLevelSet n} {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}

-- @@ L164-164 verbatim
variable {C : SignedFramedLevelCobordism S₀ S₁}


-- @@ L166-175 verbatim
/-- The retained chronological schedule proves equality of the endpoint
positive deltas directly; composing the two amplitudes is unnecessary. -/
theorem endpoint_positiveDelta_eq
    (D : ValueSeparatedPositiveLedgerResolution C) :
    S₀.positiveDelta = S₁.positiveDelta :=
  D.package.position.endpoint_positiveDelta_eq_of_labeledLedgerMoves
    D.positiveMoves
    (fun _t _ht hnegative =>
      NegativeEventPositiveExteriorTransportData.nonempty_of_negative_event
        hnegative)


-- @@ L177-177 verbatim
end ValueSeparatedPositiveLedgerResolution


-- @@ L179-200 verbatim
/-- It is enough to resolve positive events for the actual packages produced by
the assumption-free construction.  This is the production replacement for the
older callback quantified over arbitrary perturbations and arbitrary Morse
positions. -/
theorem signedCobordismDeltaInvariant_of_valueSeparatedPositiveMoves
    (positive : ∀ {X Y : FramedLevelSet n}
      {S : FiberSign X} {T : FiberSign Y}
      (C : SignedFramedLevelCobordism S T)
      (D : ValueSeparatedSignedMorsePackage C)
      (t : ℝ) (ht : t ∈ D.position.eventTimes),
      D.position.eventCenter t ht ∈
          (D.signedOutput.labelMorsePosition D.position).positiveCenters →
        Nonempty
          (PositiveEventLedgerMoveData
            D.signedOutput D.position t ht)) :
    SignedCobordismDeltaInvariant n where
  eq_of_nonempty := by
    intro X Y S T hC
    obtain ⟨C⟩ := hC
    obtain ⟨D⟩ := ValueSeparatedSignedMorsePackage.nonempty C
    exact (ValueSeparatedPositiveLedgerResolution.mk D
      (positive C D)).endpoint_positiveDelta_eq


-- @@ L202-245 verbatim
/-- Production-facing three-way event dispatcher.  Each branch sees the exact
owner-preserving schedule of a retained package, rather than an arbitrary
choice-based Morse position. -/
theorem signedCobordismDeltaInvariant_of_valueSeparatedIndexedPositiveMoves
    (minimum : ∀ {X Y : FramedLevelSet n}
      {S : FiberSign X} {T : FiberSign Y}
      (C : SignedFramedLevelCobordism S T)
      (D : ValueSeparatedSignedMorsePackage C)
      (t : ℝ) (ht : t ∈ D.position.eventTimes),
      D.position.eventCenter t ht ∈
          (D.signedOutput.labelMorsePosition D.position).positiveCenters →
      (D.position.eventModel t ht).index = .minimum →
        Nonempty
          (PositiveEventLedgerMoveData
            D.signedOutput D.position t ht))
    (saddle : ∀ {X Y : FramedLevelSet n}
      {S : FiberSign X} {T : FiberSign Y}
      (C : SignedFramedLevelCobordism S T)
      (D : ValueSeparatedSignedMorsePackage C)
      (t : ℝ) (ht : t ∈ D.position.eventTimes),
      D.position.eventCenter t ht ∈
          (D.signedOutput.labelMorsePosition D.position).positiveCenters →
      (D.position.eventModel t ht).index = .saddle →
        Nonempty
          (PositiveEventLedgerMoveData
            D.signedOutput D.position t ht))
    (maximum : ∀ {X Y : FramedLevelSet n}
      {S : FiberSign X} {T : FiberSign Y}
      (C : SignedFramedLevelCobordism S T)
      (D : ValueSeparatedSignedMorsePackage C)
      (t : ℝ) (ht : t ∈ D.position.eventTimes),
      D.position.eventCenter t ht ∈
          (D.signedOutput.labelMorsePosition D.position).positiveCenters →
      (D.position.eventModel t ht).index = .maximum →
        Nonempty
          (PositiveEventLedgerMoveData
            D.signedOutput D.position t ht)) :
    SignedCobordismDeltaInvariant n :=
  signedCobordismDeltaInvariant_of_valueSeparatedPositiveMoves
    fun C D t ht hpositive => by
      cases hindex : (D.position.eventModel t ht).index with
      | minimum => exact minimum C D t ht hpositive hindex
      | saddle => exact saddle C D t ht hpositive hindex
      | maximum => exact maximum C D t ht hpositive hindex


-- @@ L247-247 verbatim
end Submission
