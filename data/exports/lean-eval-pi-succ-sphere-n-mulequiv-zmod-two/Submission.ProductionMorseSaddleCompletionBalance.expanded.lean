import Submission.ProductionMorseSaddleSupply


-- @@ L3-11 verbatim
/-!
# Cardinality completion for production saddle exterior flow

The production saddle flow already gives an injective map on exterior orbit
components.  Consequently its residual surjectivity field is forced by a
finite cardinality equality.  This file packages that reduction for both
chronological merge and split events: callers provide only the relevant local
noncollision statement(s) and equality of the two exterior component counts.
-/


-- @@ L13-13 verbatim
set_option autoImplicit false

-- @@ L14-14 verbatim
set_option maxHeartbeats 2400000


-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-18 verbatim
open Set Function


-- @@ L20-20 verbatim
namespace Submission


-- @@ L22-22 verbatim
variable {n : ℕ}


-- @@ L24-24 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L26-26 verbatim
variable {X₀ X₁ : FramedLevelSet n}

-- @@ L27-27 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}

-- @@ L28-28 verbatim
variable {SC : SignedFramedLevelCobordism S₀ S₁}


-- @@ L30-30 verbatim
namespace ValueSeparatedSignedMorsePackage


-- @@ L32-32 verbatim
/-! ## Merge balance -/


-- @@ L34-54 verbatim
/-- The exact residual data needed to complete a merge exterior flow once
midpoint capture is fixed.  Surjectivity is deliberately absent. -/
structure ChronologicalSaddleMergeExteriorComponentBalance
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (hmidpoint : D.ChronologicalSaddleMergeExteriorMidpointCapture
      t ht hindex) : Type where
  target_ne_outgoing : ∀
      O : {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
        (D.chronologicalSaddleMergeExteriorSourceFamily t ht hindex)},
    (((D.chronologicalSaddleMergeExteriorFlowCore t ht hindex
      (D.chronologicalWindowRadius_sq_le_safeTime t ht) hmidpoint).targetOrbit O :
        (D.chronologicalAfterField t ht).OrbitIndex) : Set E₁) ≠
      ((D.chronologicalSaddlePositiveOrbit t ht hindex .negative :
        (D.chronologicalAfterField t ht).OrbitIndex) : Set E₁)
  card_eq :
    ((D.chronologicalBeforeField t ht).selectedOrbitFinset
      (D.chronologicalSaddleMergeExteriorSourceFamily t ht hindex)).card =
    ((D.chronologicalAfterField t ht).selectedOrbitFinset
      (D.chronologicalSaddleMergeExteriorTargetFamily t ht hindex)).card


-- @@ L56-56 verbatim
namespace ChronologicalSaddleMergeExteriorComponentBalance


-- @@ L58-58 verbatim
variable {D : ValueSeparatedSignedMorsePackage SC}

-- @@ L59-59 verbatim
variable {t : ℝ} {ht : t ∈ D.position.eventTimes}

-- @@ L60-60 verbatim
variable {hindex : (D.position.eventModel t ht).index = .saddle}

-- @@ L61-62 verbatim
variable {hmidpoint : D.ChronologicalSaddleMergeExteriorMidpointCapture
  t ht hindex}


-- @@ L64-87 verbatim
/-- The forced target orbit, now regarded as an element of the requested
merge exterior target family. -/
def targetMap
    (K : D.ChronologicalSaddleMergeExteriorComponentBalance
      t ht hindex hmidpoint) :
    {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
      (D.chronologicalSaddleMergeExteriorSourceFamily t ht hindex)} →
    {Q // Q ∈ (D.chronologicalAfterField t ht).selectedOrbitFinset
      (D.chronologicalSaddleMergeExteriorTargetFamily t ht hindex)} := by
  intro O
  let H := D.chronologicalSaddleMergeExteriorFlowCore t ht hindex
    (D.chronologicalWindowRadius_sq_le_safeTime t ht) hmidpoint
  refine ⟨H.targetOrbit O, ?_⟩
  apply ((D.chronologicalAfterField t ht).mem_selectedOrbitFinset _).mpr
  constructor
  · have hsource : (O.1 : Set E₁) ∈
        D.chronologicalSaddleNegativeCollection t ht :=
      ((D.chronologicalBeforeField t ht).mem_selectedOrbitFinset O.1).mp
        O.2 |>.1.1
    exact ((D.chronologicalAfterField t ht).mem_selectedOrbitFinset _).mp
      (D.chronologicalSaddleTargetOrbit_mem_positive t ht _
        (D.chronologicalWindowRadius_sq_le_safeTime t ht)
        hmidpoint O hsource)
  · simpa [H] using K.target_ne_outgoing O


-- @@ L89-97 verbatim
theorem targetMap_injective
    (K : D.ChronologicalSaddleMergeExteriorComponentBalance
      t ht hindex hmidpoint) :
    Function.Injective K.targetMap := by
  intro O P hOP
  apply (D.chronologicalSaddleMergeExteriorFlowCore t ht hindex
    (D.chronologicalWindowRadius_sq_le_safeTime t ht)
    hmidpoint).targetOrbit_injective
  exact congrArg Subtype.val hOP


-- @@ L99-111 verbatim
theorem targetMap_surjective
    (K : D.ChronologicalSaddleMergeExteriorComponentBalance
      t ht hindex hmidpoint) :
    Function.Surjective K.targetMap := by
  have hcard : Fintype.card
      {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
        (D.chronologicalSaddleMergeExteriorSourceFamily t ht hindex)} =
      Fintype.card
      {Q // Q ∈ (D.chronologicalAfterField t ht).selectedOrbitFinset
        (D.chronologicalSaddleMergeExteriorTargetFamily t ht hindex)} := by
    simpa only [Fintype.card_coe] using K.card_eq
  exact ((Fintype.bijective_iff_injective_and_card K.targetMap).mpr
    ⟨K.targetMap_injective, hcard⟩).surjective


-- @@ L113-123 verbatim
/-- Fill the old merge completion contract, including its formerly explicit
surjectivity field. -/
def toCompletion
    (K : D.ChronologicalSaddleMergeExteriorComponentBalance
      t ht hindex hmidpoint) :
    D.ChronologicalSaddleMergeExteriorCompletion t ht hindex
      (D.chronologicalWindowRadius_sq_le_safeTime t ht) hmidpoint where
  target_ne_outgoing := K.target_ne_outgoing
  target_surjective Q := by
    obtain ⟨O, hO⟩ := K.targetMap_surjective Q
    exact ⟨O, congrArg Subtype.val hO⟩


-- @@ L125-131 verbatim
/-- Package the fixed midpoint and cardinal completion as the exact flow
supply consumed by the production saddle adapter. -/
def toFlowSupply
    (K : D.ChronologicalSaddleMergeExteriorComponentBalance
      t ht hindex hmidpoint) :
    D.ChronologicalSaddleMergeFlowSupply t ht hindex :=
  ⟨hmidpoint, K.toCompletion⟩


-- @@ L133-133 verbatim
end ChronologicalSaddleMergeExteriorComponentBalance


-- @@ L135-135 verbatim
/-! ## Split balance -/


-- @@ L137-165 verbatim
/-- Split analogue: both distinguished positive-side branch components must
be avoided, and cardinality then forces exhaustion of their complement. -/
structure ChronologicalSaddleSplitExteriorComponentBalance
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (hmidpoint : D.ChronologicalSaddleSplitExteriorMidpointCapture
      t ht hindex) : Type where
  target_ne_negative : ∀
      O : {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
        (D.chronologicalSaddleSplitExteriorSourceFamily t ht hindex)},
    (((D.chronologicalSaddleSplitExteriorFlowCore t ht hindex
      (D.chronologicalWindowRadius_sq_le_safeTime t ht) hmidpoint).targetOrbit O :
        (D.chronologicalAfterField t ht).OrbitIndex) : Set E₁) ≠
      ((D.chronologicalSaddlePositiveOrbit t ht hindex .negative :
        (D.chronologicalAfterField t ht).OrbitIndex) : Set E₁)
  target_ne_positive : ∀
      O : {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
        (D.chronologicalSaddleSplitExteriorSourceFamily t ht hindex)},
    (((D.chronologicalSaddleSplitExteriorFlowCore t ht hindex
      (D.chronologicalWindowRadius_sq_le_safeTime t ht) hmidpoint).targetOrbit O :
        (D.chronologicalAfterField t ht).OrbitIndex) : Set E₁) ≠
      ((D.chronologicalSaddlePositiveOrbit t ht hindex .positive :
        (D.chronologicalAfterField t ht).OrbitIndex) : Set E₁)
  card_eq :
    ((D.chronologicalBeforeField t ht).selectedOrbitFinset
      (D.chronologicalSaddleSplitExteriorSourceFamily t ht hindex)).card =
    ((D.chronologicalAfterField t ht).selectedOrbitFinset
      (D.chronologicalSaddleSplitExteriorTargetFamily t ht hindex)).card


-- @@ L167-167 verbatim
namespace ChronologicalSaddleSplitExteriorComponentBalance


-- @@ L169-169 verbatim
variable {D : ValueSeparatedSignedMorsePackage SC}

-- @@ L170-170 verbatim
variable {t : ℝ} {ht : t ∈ D.position.eventTimes}

-- @@ L171-171 verbatim
variable {hindex : (D.position.eventModel t ht).index = .saddle}

-- @@ L172-173 verbatim
variable {hmidpoint : D.ChronologicalSaddleSplitExteriorMidpointCapture
  t ht hindex}


-- @@ L175-198 verbatim
def targetMap
    (K : D.ChronologicalSaddleSplitExteriorComponentBalance
      t ht hindex hmidpoint) :
    {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
      (D.chronologicalSaddleSplitExteriorSourceFamily t ht hindex)} →
    {Q // Q ∈ (D.chronologicalAfterField t ht).selectedOrbitFinset
      (D.chronologicalSaddleSplitExteriorTargetFamily t ht hindex)} := by
  intro O
  let H := D.chronologicalSaddleSplitExteriorFlowCore t ht hindex
    (D.chronologicalWindowRadius_sq_le_safeTime t ht) hmidpoint
  refine ⟨H.targetOrbit O, ?_⟩
  apply ((D.chronologicalAfterField t ht).mem_selectedOrbitFinset _).mpr
  constructor
  · constructor
    · have hsource : (O.1 : Set E₁) ∈
          D.chronologicalSaddleNegativeCollection t ht :=
        ((D.chronologicalBeforeField t ht).mem_selectedOrbitFinset O.1).mp
          O.2 |>.1
      exact ((D.chronologicalAfterField t ht).mem_selectedOrbitFinset _).mp
        (D.chronologicalSaddleTargetOrbit_mem_positive t ht _
          (D.chronologicalWindowRadius_sq_le_safeTime t ht)
          hmidpoint O hsource)
    · simpa [H] using K.target_ne_negative O
  · simpa [H] using K.target_ne_positive O


-- @@ L200-208 verbatim
theorem targetMap_injective
    (K : D.ChronologicalSaddleSplitExteriorComponentBalance
      t ht hindex hmidpoint) :
    Function.Injective K.targetMap := by
  intro O P hOP
  apply (D.chronologicalSaddleSplitExteriorFlowCore t ht hindex
    (D.chronologicalWindowRadius_sq_le_safeTime t ht)
    hmidpoint).targetOrbit_injective
  exact congrArg Subtype.val hOP


-- @@ L210-222 verbatim
theorem targetMap_surjective
    (K : D.ChronologicalSaddleSplitExteriorComponentBalance
      t ht hindex hmidpoint) :
    Function.Surjective K.targetMap := by
  have hcard : Fintype.card
      {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
        (D.chronologicalSaddleSplitExteriorSourceFamily t ht hindex)} =
      Fintype.card
      {Q // Q ∈ (D.chronologicalAfterField t ht).selectedOrbitFinset
        (D.chronologicalSaddleSplitExteriorTargetFamily t ht hindex)} := by
    simpa only [Fintype.card_coe] using K.card_eq
  exact ((Fintype.bijective_iff_injective_and_card K.targetMap).mpr
    ⟨K.targetMap_injective, hcard⟩).surjective


-- @@ L224-233 verbatim
def toCompletion
    (K : D.ChronologicalSaddleSplitExteriorComponentBalance
      t ht hindex hmidpoint) :
    D.ChronologicalSaddleSplitExteriorCompletion t ht hindex
      (D.chronologicalWindowRadius_sq_le_safeTime t ht) hmidpoint where
  target_ne_negative := K.target_ne_negative
  target_ne_positive := K.target_ne_positive
  target_surjective Q := by
    obtain ⟨O, hO⟩ := K.targetMap_surjective Q
    exact ⟨O, congrArg Subtype.val hO⟩


-- @@ L235-239 verbatim
def toFlowSupply
    (K : D.ChronologicalSaddleSplitExteriorComponentBalance
      t ht hindex hmidpoint) :
    D.ChronologicalSaddleSplitFlowSupply t ht hindex :=
  ⟨hmidpoint, K.toCompletion⟩


-- @@ L241-241 verbatim
end ChronologicalSaddleSplitExteriorComponentBalance


-- @@ L243-243 verbatim
end ValueSeparatedSignedMorsePackage


-- @@ L245-245 verbatim
end Submission
