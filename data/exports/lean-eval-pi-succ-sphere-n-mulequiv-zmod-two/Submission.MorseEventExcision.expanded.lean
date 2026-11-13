import Mathlib
import Submission.MorseEventDelta
import Submission.MorseScheduleDelta
import Submission.MorseLedgerGeometry


-- @@ L6-25 verbatim
/-!
# Framed excision at one Morse event

For a general event, the delta of a nearby complete slice is not the delta of
the local birth/saddle model alone.  It is the sum of the local contribution
and the unchanged exterior contribution.  This file formalizes exactly that
decomposition at the level of orbit components.

The geometric input is deliberately below the level of delta equality:

* a bijection between the selected local orbit components and the components
  of the literal standard model, preserving each framed contribution;
* a bijection between the exterior positive components before and after the
  event, again preserving each framed contribution.

Finite sums then prove cancellation of the exterior and hence delta invariance
across the event.  If the exterior contribution happens to vanish, the data
also produces the stronger `EventDeltaComparison` used by the first schedule
API.
-/


-- @@ L27-27 verbatim
noncomputable section


-- @@ L29-29 verbatim
open Set

-- @@ L30-30 verbatim
open scoped BigOperators


-- @@ L32-32 verbatim
namespace Submission


-- @@ L34-34 verbatim
variable {n : ℕ}


-- @@ L36-36 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L38-38 verbatim
/-! ## Partial transport of selected orbit components -/


-- @@ L40-40 verbatim
namespace TamedField


-- @@ L42-42 verbatim
variable {X Y : FramedLevelSet n} (V : TamedField X) (W : TamedField Y)


-- @@ L44-49 verbatim
/-- The finite set of orbit indices whose underlying orbit belongs to `A`.
Keeping the selection as a `Finset`, rather than an arbitrary subtype, gives
Lean the canonical finite instance needed for the transport sum. -/
def selectedOrbitFinset (A : Set (Set E)) : Finset V.OrbitIndex := by
  classical
  exact Finset.univ.filter fun O => (O : Set E) ∈ A


-- @@ L51-54 verbatim
@[simp]
theorem mem_selectedOrbitFinset {A : Set (Set E)} (O : V.OrbitIndex) :
    O ∈ V.selectedOrbitFinset A ↔ (O : Set E) ∈ A := by
  simp [selectedOrbitFinset]


-- @@ L56-64 verbatim
/-- A bijection between two selected finite families of orbit components which
preserves their individual framed-circle contributions.  Unlike
`DeltaTransport`, this does not require a bijection of all components. -/
structure SelectedDeltaTransport (A B : Set (Set E)) where
  orbitEquiv :
    {O // O ∈ V.selectedOrbitFinset A} ≃
      {O // O ∈ W.selectedOrbitFinset B}
  contribution_eq : ∀ O,
    V.orbitContribution O.1 = W.orbitContribution (orbitEquiv O).1


-- @@ L66-72 verbatim
/-- `deltaOn` is the sum over its finite selection of orbit indices. -/
theorem deltaOn_eq_sum_selected (A : Set (Set E)) :
    V.deltaOn A =
      ∑ O ∈ V.selectedOrbitFinset A, V.orbitContribution O := by
  classical
  unfold deltaOn selectedOrbitFinset
  rw [← Finset.sum_filter]


-- @@ L74-82 verbatim
/-- Rewrite a sum over a `Finset` as a finite-type sum over its membership
subtype.  This is the form on which an equivalence transports the sum. -/
theorem sum_selected_eq_sum_subtype (A : Set (Set E)) :
    (∑ O ∈ V.selectedOrbitFinset A, V.orbitContribution O) =
      ∑ O : {O // O ∈ V.selectedOrbitFinset A},
        V.orbitContribution O.1 := by
  classical
  rw [← Finset.sum_attach]
  rfl


-- @@ L84-84 verbatim
namespace SelectedDeltaTransport


-- @@ L86-92 verbatim
/-- Selected component transport preserves the corresponding partial delta. -/
theorem deltaOn_eq {A B : Set (Set E)}
    (T : V.SelectedDeltaTransport W A B) :
    V.deltaOn A = W.deltaOn B := by
  rw [V.deltaOn_eq_sum_selected A, W.deltaOn_eq_sum_selected B,
    V.sum_selected_eq_sum_subtype A, W.sum_selected_eq_sum_subtype B]
  exact Fintype.sum_equiv T.orbitEquiv _ _ T.contribution_eq


-- @@ L94-94 verbatim
end SelectedDeltaTransport


-- @@ L96-117 verbatim
/-- Split a selected collection into a subcollection and its complement inside
that collection. -/
theorem deltaOn_eq_add_sdiff {A B : Set (Set E)} (hAB : A ⊆ B) :
    V.deltaOn B = V.deltaOn A + V.deltaOn (B \ A) := by
  have hdis : Disjoint A (B \ A) := by
    rw [Set.disjoint_left]
    intro O hOA hOB
    exact hOB.2 hOA
  have hunion : A ∪ (B \ A) = B := by
    ext O
    constructor
    · rintro (hOA | hOB)
      · exact hAB hOA
      · exact hOB.1
    · intro hOB
      by_cases hOA : O ∈ A
      · exact Or.inl hOA
      · exact Or.inr ⟨hOB, hOA⟩
  calc
    V.deltaOn B = V.deltaOn (A ∪ (B \ A)) := congrArg V.deltaOn hunion.symm
    _ = V.deltaOn A + V.deltaOn (B \ A) :=
      V.deltaOn_union_of_disjoint hdis


-- @@ L119-119 verbatim
end TamedField


-- @@ L121-121 verbatim
/-! ## Geometric excision data -/


-- @@ L123-123 verbatim
variable {X₀ X₁ : FramedLevelSet n}

-- @@ L124-124 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}


-- @@ L126-166 verbatim
/-- Orbit-level framed excision around one isolated standard Morse event.

The four transport fields are constructive geometric obligations: they ask for
actual component equivalences and equality of the corresponding frame-loop
contributions.  No delta equality is a field of this structure. -/
structure FramedEventExcisionData
    (C : SignedFramedLevelCobordism S₀ S₁)
    {center : EuclideanSpace ℝ (Fin (n + 2))}
    (M : StandardMorseEventAt C.cobordism center)
    (D : LocalSignedEventModel n) where
  before : ℝ
  after : ℝ
  before_lt : before < tcoord center
  lt_after : tcoord center < after
  before_regular : sliceRegular C.cobordism.G before
  after_regular : sliceRegular C.cobordism.G after
  isolates : ∀ v, v ∈ timeCritical C.cobordism.G →
    tcoord v ∈ Icc before after → v = center
  beforeField : TamedField
    (SlabTamedField.sliceFLSAt C.cobordism.toLevelCobordismData
      before before_regular)
  afterField : TamedField
    (SlabTamedField.sliceFLSAt C.cobordism.toLevelCobordismData
      after after_regular)
  sourceField : TamedField D.source
  targetField : TamedField D.target
  beforeLocal : Set (Set E)
  afterLocal : Set (Set E)
  beforeLocal_positive : beforeLocal ⊆
    (C.sliceSign before before_regular).positiveOrbitCollection beforeField
  afterLocal_positive : afterLocal ⊆
    (C.sliceSign after after_regular).positiveOrbitCollection afterField
  sourceLocalTransport : beforeField.SelectedDeltaTransport sourceField
    beforeLocal (D.sourceSign.positiveOrbitCollection sourceField)
  targetLocalTransport : afterField.SelectedDeltaTransport targetField
    afterLocal (D.targetSign.positiveOrbitCollection targetField)
  exteriorTransport : beforeField.SelectedDeltaTransport afterField
    ((C.sliceSign before before_regular).positiveOrbitCollection beforeField \
      beforeLocal)
    ((C.sliceSign after after_regular).positiveOrbitCollection afterField \
      afterLocal)


-- @@ L168-168 verbatim
namespace FramedEventExcisionData


-- @@ L170-170 verbatim
variable (C : SignedFramedLevelCobordism S₀ S₁)

-- @@ L171-171 verbatim
variable {center : EuclideanSpace ℝ (Fin (n + 2))}

-- @@ L172-172 verbatim
variable (M : StandardMorseEventAt C.cobordism center)

-- @@ L173-173 verbatim
variable (D : LocalSignedEventModel n)

-- @@ L174-174 verbatim
variable (F : FramedEventExcisionData C M D)


-- @@ L176-206 verbatim
/-- The delta of the complete incoming slice is the local standard-model delta
plus the exterior contribution. -/
theorem before_positiveDelta_eq_model_add_exterior :
    (C.sliceSign F.before F.before_regular).positiveDelta =
      D.sourceSign.positiveDelta +
        F.beforeField.deltaOn
          ((C.sliceSign F.before F.before_regular).positiveOrbitCollection
            F.beforeField \ F.beforeLocal) := by
  let Sbefore := C.sliceSign F.before F.before_regular
  let A := Sbefore.positiveOrbitCollection F.beforeField
  let Eout := A \ F.beforeLocal
  have hpartition : F.beforeField.deltaOn A =
      F.beforeField.deltaOn F.beforeLocal + F.beforeField.deltaOn Eout :=
    F.beforeField.deltaOn_eq_add_sdiff F.beforeLocal_positive
  have hlocal : F.beforeField.deltaOn F.beforeLocal =
      F.sourceField.deltaOn
        (D.sourceSign.positiveOrbitCollection F.sourceField) :=
    F.sourceLocalTransport.deltaOn_eq
  calc
    Sbefore.positiveDelta = Sbefore.positiveFramedDelta F.beforeField :=
      Sbefore.positiveDelta_eq F.beforeField
    _ = F.beforeField.deltaOn A := rfl
    _ = F.beforeField.deltaOn F.beforeLocal + F.beforeField.deltaOn Eout :=
      hpartition
    _ = F.sourceField.deltaOn
          (D.sourceSign.positiveOrbitCollection F.sourceField) +
          F.beforeField.deltaOn Eout := by rw [hlocal]
    _ = D.sourceSign.positiveFramedDelta F.sourceField +
          F.beforeField.deltaOn Eout := rfl
    _ = D.sourceSign.positiveDelta + F.beforeField.deltaOn Eout := by
      rw [D.sourceSign.positiveDelta_eq F.sourceField]


-- @@ L208-237 verbatim
/-- The analogous decomposition of the outgoing slice. -/
theorem after_positiveDelta_eq_model_add_exterior :
    (C.sliceSign F.after F.after_regular).positiveDelta =
      D.targetSign.positiveDelta +
        F.afterField.deltaOn
          ((C.sliceSign F.after F.after_regular).positiveOrbitCollection
            F.afterField \ F.afterLocal) := by
  let Safter := C.sliceSign F.after F.after_regular
  let A := Safter.positiveOrbitCollection F.afterField
  let Eout := A \ F.afterLocal
  have hpartition : F.afterField.deltaOn A =
      F.afterField.deltaOn F.afterLocal + F.afterField.deltaOn Eout :=
    F.afterField.deltaOn_eq_add_sdiff F.afterLocal_positive
  have hlocal : F.afterField.deltaOn F.afterLocal =
      F.targetField.deltaOn
        (D.targetSign.positiveOrbitCollection F.targetField) :=
    F.targetLocalTransport.deltaOn_eq
  calc
    Safter.positiveDelta = Safter.positiveFramedDelta F.afterField :=
      Safter.positiveDelta_eq F.afterField
    _ = F.afterField.deltaOn A := rfl
    _ = F.afterField.deltaOn F.afterLocal + F.afterField.deltaOn Eout :=
      hpartition
    _ = F.targetField.deltaOn
          (D.targetSign.positiveOrbitCollection F.targetField) +
          F.afterField.deltaOn Eout := by rw [hlocal]
    _ = D.targetSign.positiveFramedDelta F.targetField +
          F.afterField.deltaOn Eout := rfl
    _ = D.targetSign.positiveDelta + F.afterField.deltaOn Eout := by
      rw [D.targetSign.positiveDelta_eq F.targetField]


-- @@ L239-248 verbatim
/-- The exterior positive orbit family has the same partial delta on both
sides of the event. -/
theorem exterior_delta_eq :
    F.beforeField.deltaOn
        ((C.sliceSign F.before F.before_regular).positiveOrbitCollection
          F.beforeField \ F.beforeLocal) =
      F.afterField.deltaOn
        ((C.sliceSign F.after F.after_regular).positiveOrbitCollection
          F.afterField \ F.afterLocal) :=
  F.exteriorTransport.deltaOn_eq


-- @@ L250-258 verbatim
/-- **Framed excision theorem.**  The standard local computation and the
componentwise exterior transport imply equality of the actual complete-slice
deltas. -/
theorem slice_positiveDelta_eq :
    (C.sliceSign F.before F.before_regular).positiveDelta =
      (C.sliceSign F.after F.after_regular).positiveDelta := by
  rw [F.before_positiveDelta_eq_model_add_exterior C M D,
    F.after_positiveDelta_eq_model_add_exterior C M D,
    D.delta_eq, F.exterior_delta_eq C M D]


-- @@ L260-270 verbatim
/-- Orbit-level excision produces exactly the complete-slice crossing consumed
by chronological induction. -/
def toEventDeltaCrossing : EventDeltaCrossing C center where
  before := F.before
  after := F.after
  before_lt := F.before_lt
  lt_after := F.lt_after
  before_regular := F.before_regular
  after_regular := F.after_regular
  isolates := F.isolates
  delta_eq := F.slice_positiveDelta_eq C M D


-- @@ L272-293 verbatim
/-- If there is no exterior contribution, framed excision specializes to the
stronger comparison record expected by `MorseScheduleDelta`. -/
noncomputable def toEventDeltaComparison
    (hexterior : F.beforeField.deltaOn
      ((C.sliceSign F.before F.before_regular).positiveOrbitCollection
        F.beforeField \ F.beforeLocal) = 0) :
    EventDeltaComparison C M D where
  before := F.before
  after := F.after
  before_lt := F.before_lt
  lt_after := F.lt_after
  before_regular := F.before_regular
  after_regular := F.after_regular
  isolates := F.isolates
  source_delta := by
    rw [F.before_positiveDelta_eq_model_add_exterior C M D, hexterior, add_zero]
  target_delta := by
    have hafter : F.afterField.deltaOn
        ((C.sliceSign F.after F.after_regular).positiveOrbitCollection
          F.afterField \ F.afterLocal) = 0 := by
      rw [← F.exterior_delta_eq C M D, hexterior]
    rw [F.after_positiveDelta_eq_model_add_exterior C M D, hafter, add_zero]


-- @@ L295-295 verbatim
end FramedEventExcisionData


-- @@ L297-297 verbatim
/-! ## Chronological wrapper -/


-- @@ L299-299 verbatim
namespace MorsePosition


-- @@ L301-301 verbatim
variable {C : SignedFramedLevelCobordism S₀ S₁}


-- @@ L303-307 verbatim
/-- Orbit-level excision data for every event in the finite schedule. -/
abbrev FramedEventExcisions (P : MorsePosition C.cobordism) (hn : 2 ≤ n) :=
  ∀ (t : ℝ) (ht : t ∈ P.eventTimes),
    Nonempty (FramedEventExcisionData C (P.eventModel t ht)
      (P.eventDeltaModel hn t ht))


-- @@ L309-316 verbatim
/-- Framed excision at every event yields the complete-slice crossing family
needed by the finite schedule, with no hypothesis on the exterior delta. -/
theorem eventDeltaCrossingsOfFramedExcisions
    (P : MorsePosition C.cobordism) (hn : 2 ≤ n)
    (K : P.FramedEventExcisions hn) : P.EventDeltaCrossings := by
  intro t ht
  exact ⟨(K t ht).some.toEventDeltaCrossing C (P.eventModel t ht)
    (P.eventDeltaModel hn t ht)⟩


-- @@ L318-329 verbatim
/-- Every supplied orbit-level excision package proves the actual slice equality
at its event, without a zero-exterior hypothesis. -/
theorem slice_positiveDelta_eq_of_framedExcision
    (P : MorsePosition C.cobordism) (hn : 2 ≤ n)
    (K : P.FramedEventExcisions hn)
    (t : ℝ) (ht : t ∈ P.eventTimes) :
    let F := (K t ht).some
    (C.sliceSign F.before F.before_regular).positiveDelta =
      (C.sliceSign F.after F.after_regular).positiveDelta := by
  dsimp
  exact (K t ht).some.slice_positiveDelta_eq C (P.eventModel t ht)
    (P.eventDeltaModel hn t ht)


-- @@ L331-339 verbatim
/-- The corrected end-to-end Morse theorem: local standard calculations,
orbit-level framed excision (including arbitrary exterior components), regular
slab transport, and finite chronological induction prove endpoint invariance. -/
theorem endpoint_positiveDelta_eq_of_framedExcisions
    (P : MorsePosition C.cobordism) (hn : 2 ≤ n)
    (K : P.FramedEventExcisions hn) :
    S₀.positiveDelta = S₁.positiveDelta :=
  P.endpoint_positiveDelta_eq_of_eventCrossings
    (P.eventDeltaCrossingsOfFramedExcisions hn K)


-- @@ L341-354 verbatim
/-- Zero exterior contribution converts orbit-level excision data into the
legacy `EventDeltaComparisons` family used by the completed finite induction. -/
theorem eventDeltaComparisonsOfFramedExcisions
    (P : MorsePosition C.cobordism) (hn : 2 ≤ n)
    (K : P.FramedEventExcisions hn)
    (hzero : ∀ (t : ℝ) (ht : t ∈ P.eventTimes),
      let F := (K t ht).some
      F.beforeField.deltaOn
        ((C.sliceSign F.before F.before_regular).positiveOrbitCollection
          F.beforeField \ F.beforeLocal) = 0) :
    P.EventDeltaComparisons hn := by
  intro t ht
  exact ⟨(K t ht).some.toEventDeltaComparison C (P.eventModel t ht)
    (P.eventDeltaModel hn t ht) (hzero t ht)⟩


-- @@ L356-356 verbatim
end MorsePosition


-- @@ L358-358 verbatim
end Submission
