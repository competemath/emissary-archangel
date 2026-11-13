import Submission.ProductionMorseSaddleOrientedTopologyBridge


-- @@ L3-28 verbatim
/-!
# Canonical compact flow core for the oriented saddle arcs

The production saddle field already chosen in
`ProductionMorseChronologicalWindow` has enough safe time, but its compact
core is the complement of the half-cover ball.  The four marked critical ends
used by `SaddlePuncturedCriticalArcPairingData` lie strictly *inside* that
ball.  Consequently that field cannot directly instantiate
`ChronologicalSaddleOrientedArcFlowData`: even the endpoints of the chosen
mate arcs are outside its core.

This file builds the smallest useful replacement automatically.  It takes the
finite union of the four chosen mate-arc images, proves that union compact and
slab-regular, and chooses the corresponding compact time field.  The remaining
contract is stated without concealment:

* the already fixed chronological displacement must be safe for this new
  arc-dependent field;
* its eight flowed endpoints must have the labelled local chart captures;
* equality of the two regular local orbits must recover the transverse
  punctured critical arc.

The first two bullets are exactly the residual local short-flow estimates; the
third is the residual global complement-arc theorem.  Given them, the adapter
constructs the production flow data and invokes the oriented topology bridge.
-/


-- @@ L30-30 verbatim
set_option autoImplicit false

-- @@ L31-31 verbatim
set_option maxHeartbeats 2400000


-- @@ L33-33 verbatim
noncomputable section


-- @@ L35-35 verbatim
open Set Function Metric

-- @@ L36-36 verbatim
open scoped RealInnerProductSpace Topology unitInterval


-- @@ L38-38 verbatim
namespace Submission


-- @@ L40-40 verbatim
variable {n : ℕ}


-- @@ L42-42 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L44-44 verbatim
variable {X₀ X₁ : FramedLevelSet n}

-- @@ L45-45 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}

-- @@ L46-46 verbatim
variable {SC : SignedFramedLevelCobordism S₀ S₁}


-- @@ L48-48 verbatim
namespace ValueSeparatedSignedMorsePackage


-- @@ L50-50 verbatim
variable {D : ValueSeparatedSignedMorsePackage SC}

-- @@ L51-51 verbatim
variable {t : ℝ} {ht : t ∈ D.position.eventTimes}

-- @@ L52-52 verbatim
variable {hindex : (D.position.eventModel t ht).index = .saddle}


-- @@ L54-54 verbatim
local notation "rho" => D.chronologicalSaddleBoundaryRadius t ht

-- @@ L55-55 verbatim
local notation "a" => D.chronologicalWindowRadius t ht


-- @@ L57-59 verbatim
local instance : Fintype SaddleBranch where
  elems := {.positive, .negative}
  complete b := by cases b <;> simp


-- @@ L61-61 verbatim
/-! ## The finite chosen-arc core -/


-- @@ L63-69 verbatim
/-- The union of the images of the four chosen critical mate arcs. -/
def chronologicalSaddleChosenMateArcCore
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht)) : Set E' :=
  ⋃ p : SaddleBranch × SaddleBranch, Set.range (A.chosenMateArc p).toPath


-- @@ L71-80 verbatim
theorem chosenMateArc_mem_chronologicalSaddleChosenMateArcCore
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht))
    (p : SaddleBranch × SaddleBranch) (u : I) :
    (A.chosenMateArc p).toPath u ∈
      chronologicalSaddleChosenMateArcCore (D := D) (t := t) (ht := ht) A := by
  apply Set.mem_iUnion.2
  exact ⟨p, ⟨u, rfl⟩⟩


-- @@ L82-91 verbatim
theorem isCompact_chronologicalSaddleChosenMateArcCore
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht)) :
    IsCompact
      (chronologicalSaddleChosenMateArcCore (D := D) (t := t) (ht := ht) A) := by
  apply isCompact_iUnion
  intro p
  exact isCompact_range (A.chosenMateArc p).toPath.continuous


-- @@ L93-103 verbatim
theorem chronologicalSaddleChosenMateArcCore_subset_puncturedCriticalSlice
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht)) :
    chronologicalSaddleChosenMateArcCore (D := D) (t := t) (ht := ht) A ⊆
      StandardMorseEventAt.puncturedCriticalSlice
        D.signedOutput.cobordism (D.position.eventCenter t ht) := by
  intro x hx
  obtain ⟨p, u, rfl⟩ := Set.mem_iUnion.mp hx
  exact (A.chosenMateArc p).mem_exterior u


-- @@ L105-131 verbatim
/-- Critical-value separation makes every point of the finite chosen-arc core
slab-regular.  This is the same isolation argument used for the full punctured
critical slice, specialized here so the adapter does not require a larger
global compact core. -/
theorem chronologicalSaddleChosenMateArcCore_subset_slabRegularSet
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht)) :
    chronologicalSaddleChosenMateArcCore (D := D) (t := t) (ht := ht) A ⊆
      slabRegularSet
        D.signedOutput.cobordism.toLevelCobordismData.G := by
  intro x hx
  have hpunct :=
    chronologicalSaddleChosenMateArcCore_subset_puncturedCriticalSlice
      (D := D) (t := t) (ht := ht) A hx
  have hspatial : Surjective
      (spatialDeriv D.signedOutput.cobordism.G x) := by
    by_contra hnot
    have hcritical : x ∈ timeCritical D.signedOutput.cobordism.G :=
      ⟨hpunct.1, hnot⟩
    have hcenter : x = D.position.eventCenter t ht :=
      D.chronologicalCriticalSlice_isolated t ht x hcritical hpunct.2.1
    exact hpunct.2.2 hcenter
  apply mem_slabRegularSet_of_spatial_surjective
  · exact D.signedOutput.cobordism.regular x hpunct.1
  · exact hspatial


-- @@ L133-147 verbatim
/-- The canonical compact time field attached to the actual chosen mate arcs.
Unlike the production half-core field, this core contains the four marked
critical ends by construction. -/
noncomputable def chronologicalSaddleChosenMateArcTimeField
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht)) :
    CompactTimeTamedField
      D.signedOutput.cobordism.toLevelCobordismData
      (D.chronologicalSaddleChosenMateArcCore t ht A) :=
  (exists_compactTimeTamedField
    D.signedOutput.cobordism.toLevelCobordismData
    (D.isCompact_chronologicalSaddleChosenMateArcCore t ht A)
    (D.chronologicalSaddleChosenMateArcCore_subset_slabRegularSet t ht A)).some


-- @@ L149-149 verbatim
/-! ## Why the existing half-core field is not the required arc field -/


-- @@ L151-162 verbatim
/-- The preselected chronological displacement is safe for the existing
production saddle half-core field. -/
theorem chronologicalSaddleCriticalExteriorTimeField_sq_le_safeTime
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    D.chronologicalWindowRadius t ht ^ 2 ≤
      (D.chronologicalSaddleCriticalExteriorTimeField t ht).safeTime := by
  have h := D.chronologicalWindowRadius_sq_le_safeTime t ht
  rw [abs_of_nonneg (sq_nonneg _)] at h
  change D.chronologicalWindowRadius t ht ^ 2 ≤
    (D.chronologicalCriticalExteriorTimeField t ht).safeTime
  exact h


-- @@ L164-195 verbatim
/-- Every marked critical end is strictly inside the half-cover ball. -/
theorem chronologicalSaddleCriticalBoundaryEnd_dist_lt_half_cover
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (p : SaddleBranch × SaddleBranch) :
    dist ((D.position.eventModel t ht).saddleCriticalBoundaryEnd p
        (D.chronologicalSaddleBoundaryRadius t ht))
        (D.position.eventCenter t ht) <
      (D.position.eventModel t ht).fiberCoverRadius / 2 := by
  have hrho : 0 < D.chronologicalSaddleBoundaryRadius t ht :=
    D.chronologicalSaddleBoundaryRadius_pos t ht
  have hzero : (0 : ℝ) ^ 2 <
      D.chronologicalSaddleBoundaryRadius t ht ^ 2 := by
    nlinarith [sq_pos_of_pos hrho]
  have hparam :
      ‖saddleCriticalBoundaryEndParam p
          (D.chronologicalSaddleBoundaryRadius t ht)‖ <
        (D.chronologicalEventEmbeddedShrink t ht).radius := by
    calc
      ‖saddleCriticalBoundaryEndParam p
          (D.chronologicalSaddleBoundaryRadius t ht)‖ =
          D.chronologicalSaddleBoundaryRadius t ht := by
        exact norm_saddlePositiveBoundaryEndParam p.1 p.2 hrho hzero
      _ < (D.chronologicalEventEmbeddedShrink t ht).radius :=
        D.chronologicalSaddleBoundaryRadius_lt_embedded t ht
  have hdist :=
    D.chronologicalEventEmbeddedShrink_param_dist_lt_half_cover
      t ht hparam
  simpa [StandardMorseEventAt.saddleCriticalBoundaryEnd,
    saddleCriticalBoundaryEndParam,
    StandardMorseEventAt.saddlePositiveBoundaryEnd,
    StandardMorseEventAt.localPoint] using hdist


-- @@ L197-214 verbatim
/-- Therefore no marked critical end belongs to the canonical saddle
half-exterior core. -/
theorem chronologicalSaddleCriticalBoundaryEnd_not_mem_halfExteriorCore
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (p : SaddleBranch × SaddleBranch) :
    (D.position.eventModel t ht).saddleCriticalBoundaryEnd p
        (D.chronologicalSaddleBoundaryRadius t ht) ∉
      criticalSliceExteriorCore
        D.signedOutput.cobordism.toLevelCobordismData
        (D.position.eventCenter t ht)
        (tcoord (D.position.eventCenter t ht))
        ((D.position.eventModel t ht).fiberCoverRadius / 2) := by
  intro hmem
  rw [mem_criticalSliceExteriorCore] at hmem
  exact (not_le_of_gt
    (D.chronologicalSaddleCriticalBoundaryEnd_dist_lt_half_cover t ht p))
      hmem.2.2


-- @@ L216-236 verbatim
/-- In particular, the chosen mate-arc core cannot be a subcore of the
canonical half-exterior field.  This rules out a direct `restrict` adapter. -/
theorem chronologicalSaddleChosenMateArcCore_not_subset_halfExteriorCore
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht)) :
    ¬ D.chronologicalSaddleChosenMateArcCore t ht A ⊆
      criticalSliceExteriorCore
        D.signedOutput.cobordism.toLevelCobordismData
        (D.position.eventCenter t ht)
        (tcoord (D.position.eventCenter t ht))
        ((D.position.eventModel t ht).fiberCoverRadius / 2) := by
  intro hsub
  let p : SaddleBranch × SaddleBranch := (.negative, .negative)
  apply D.chronologicalSaddleCriticalBoundaryEnd_not_mem_halfExteriorCore t ht p
  apply hsub
  have hmem := D.chosenMateArc_mem_chronologicalSaddleChosenMateArcCore
    t ht A p 0
  rw [(A.chosenMateArc p).toPath.source] at hmem
  exact hmem


-- @@ L238-238 verbatim
/-! ## Minimal residual contract and adapter -/


-- @@ L240-256 verbatim
/-- What remains after the compact core and its time field have been
constructed automatically.  These are quantitative facts about the newly
chosen arc-dependent field, not consequences of the half-core field's safe
bound. -/
structure ChronologicalSaddleChosenMateArcFlowCompatibility
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht)) : Type where
  safe : a ^ 2 ≤
    (D.chronologicalSaddleChosenMateArcTimeField t ht A).safeTime
  positiveEndpoint : ∀ p,
    ChronologicalSaddlePositiveEndpointCapture
      (D := D) (t := t) (ht := ht)
      (D.chronologicalSaddleChosenMateArcTimeField t ht A) p
  negativeEndpoint : ∀ p,
    ChronologicalSaddleNegativeEndpointCapture
      (D := D) (t := t) (ht := ht)
      (D.chronologicalSaddleChosenMateArcTimeField t ht A) p


-- @@ L258-258 verbatim
namespace ChronologicalSaddleChosenMateArcFlowCompatibility


-- @@ L260-262 verbatim
variable {A :
  (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
    (D.chronologicalSaddleBoundaryRadius t ht)}


-- @@ L264-277 verbatim
/-- Fill every structural field of the oriented-arc flow data from the
automatically chosen finite arc core and the residual short-flow estimates. -/
def toChronologicalSaddleOrientedArcFlowData
    (F : ChronologicalSaddleChosenMateArcFlowCompatibility
      (D := D) (t := t) (ht := ht) A) :
    ChronologicalSaddleOrientedArcFlowData
      (D := D) (t := t) (ht := ht) A where
  K := D.chronologicalSaddleChosenMateArcCore t ht A
  field := D.chronologicalSaddleChosenMateArcTimeField t ht A
  chosenMateArc_mem :=
    D.chosenMateArc_mem_chronologicalSaddleChosenMateArcCore t ht A
  safe := F.safe
  positiveEndpoint := F.positiveEndpoint
  negativeEndpoint := F.negativeEndpoint


-- @@ L279-279 verbatim
end ChronologicalSaddleChosenMateArcFlowCompatibility


-- @@ L281-296 verbatim
/-- Shortest honest production adapter.  `A` supplies the actual oriented
punctured critical arcs; `F` supplies only the local short-flow estimates for
their automatically constructed compact field; `H` is the remaining global
regular-orbit complement-arc theorem. -/
theorem chronologicalSaddleTopologyDichotomy_of_puncturedCriticalArcPairing
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht))
    (F : ChronologicalSaddleChosenMateArcFlowCompatibility
      (D := D) (t := t) (ht := ht) A)
    (H : ChronologicalSaddleRegularOrbitArcRecovery
      (D := D) (t := t) (ht := ht) (hindex := hindex)) :
    D.ChronologicalSaddleMergeTopology t ht hindex ∨
      D.ChronologicalSaddleSplitTopology t ht hindex :=
  chronologicalSaddleTopologyDichotomy_of_orientedExteriorArcs
    (D := D) (t := t) (ht := ht) (hindex := hindex)
    A F.toChronologicalSaddleOrientedArcFlowData H


-- @@ L298-298 verbatim
end ValueSeparatedSignedMorsePackage


-- @@ L300-300 verbatim
end Submission
