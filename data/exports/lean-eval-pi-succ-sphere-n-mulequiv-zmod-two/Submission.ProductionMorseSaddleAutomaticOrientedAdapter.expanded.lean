import Submission.ProductionMorseSaddleOrientedShortFlowAdapter
import Submission.ProductionMorseSaddlePuncturedArcFlow


-- @@ L4-12 verbatim
/-!
# Automatic production adapter for oriented saddle arcs

This file combines the arbitrarily small production fiber cover with radial
transport of the punctured critical pairing.  The auxiliary boundary radius
is chosen before either compact time field.  Consequently one can later pick
one genuinely small regular displacement which is safe both for the chosen
mate arcs and for the exterior cyclic cuts.
-/


-- @@ L14-14 verbatim
set_option autoImplicit false

-- @@ L15-15 verbatim
set_option maxHeartbeats 2400000


-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
open Set Function Metric Filter

-- @@ L20-20 verbatim
open scoped RealInnerProductSpace Topology unitInterval


-- @@ L22-22 verbatim
namespace Submission


-- @@ L24-24 verbatim
variable {n : ℕ}


-- @@ L26-26 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

-- @@ L27-27 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L28-28 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L30-30 verbatim
/-! ## A nonlocal cut incident to a prescribed four-orbit mark -/


-- @@ L32-32 verbatim
namespace SimpleClosedOrbitParam.CyclicMarking


-- @@ L34-34 verbatim
variable {X : FramedLevelSet n} {V : TamedField X}

-- @@ L35-35 verbatim
variable {P : SimpleClosedOrbitParam X V}


-- @@ L37-41 verbatim
/-- The cyclic cut leaving a specified label in a four-marked orbit. -/
noncomputable def outgoingCutIndexFour
    (A : P.CyclicMarking 3) (l : Fin 4) : Fin 4 :=
  Fin.lastCases (Fin.last 3)
    (fun j : Fin 3 => j.castSucc) (A.sortedLabel.symm l)


-- @@ L43-47 verbatim
/-- The cyclic cut entering a specified label in a four-marked orbit. -/
noncomputable def incomingCutIndexFour
    (A : P.CyclicMarking 3) (l : Fin 4) : Fin 4 :=
  Fin.cases (Fin.last 3)
    (fun j : Fin 3 => j.castSucc) (A.sortedLabel.symm l)


-- @@ L49-61 verbatim
private theorem cyclicCutSourceLabel_outgoingRankFour
    (A : P.CyclicMarking 3) (r : Fin 4) :
    A.cyclicCutSourceLabel
        (Fin.lastCases (Fin.last 3)
          (fun j : Fin 3 => j.castSucc) r) =
      A.sortedLabel r := by
  induction r using Fin.lastCases with
  | last =>
      simp only [cyclicCutSourceLabel]
      rw [Fin.lastCases_last, Fin.lastCases_last]
  | cast j =>
      simp only [cyclicCutSourceLabel]
      rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc]


-- @@ L63-75 verbatim
private theorem cyclicCutTargetLabel_incomingRankFour
    (A : P.CyclicMarking 3) (r : Fin 4) :
    A.cyclicCutTargetLabel
        (Fin.cases (Fin.last 3)
          (fun j : Fin 3 => j.castSucc) r) =
      A.sortedLabel r := by
  induction r using Fin.cases with
  | zero =>
      simp only [cyclicCutTargetLabel]
      rw [Fin.cases_zero, Fin.lastCases_last]
  | succ j =>
      simp only [cyclicCutTargetLabel]
      rw [Fin.cases_succ, Fin.lastCases_castSucc]


-- @@ L77-82 verbatim
@[simp] theorem cyclicCutSourceLabel_outgoingCutIndexFour
    (A : P.CyclicMarking 3) (l : Fin 4) :
    A.cyclicCutSourceLabel (A.outgoingCutIndexFour l) = l := by
  rw [outgoingCutIndexFour,
    A.cyclicCutSourceLabel_outgoingRankFour]
  exact A.sortedLabel.apply_symm_apply l


-- @@ L84-89 verbatim
@[simp] theorem cyclicCutTargetLabel_incomingCutIndexFour
    (A : P.CyclicMarking 3) (l : Fin 4) :
    A.cyclicCutTargetLabel (A.incomingCutIndexFour l) = l := by
  rw [incomingCutIndexFour,
    A.cyclicCutTargetLabel_incomingRankFour]
  exact A.sortedLabel.apply_symm_apply l


-- @@ L91-111 verbatim
theorem cyclicCutSourceLabel_ne_targetLabel_four
    (A : P.CyclicMarking 3) (i : Fin 4) :
    A.cyclicCutSourceLabel i ≠ A.cyclicCutTargetLabel i := by
  induction i using Fin.lastCases with
  | last =>
      intro h
      simp only [cyclicCutSourceLabel, cyclicCutTargetLabel] at h
      rw [Fin.lastCases_last, Fin.lastCases_last] at h
      have h' : A.sortedLabel (Fin.last 3) = A.sortedLabel 0 := by
        exact h
      have hindex := A.sortedLabel.injective h'
      have hval := congrArg Fin.val hindex
      norm_num at hval
  | cast j =>
      intro h
      simp only [cyclicCutSourceLabel, cyclicCutTargetLabel] at h
      rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc] at h
      have h' : A.sortedLabel j.castSucc = A.sortedLabel j.succ := by
        exact h
      exact (Fin.castSucc_lt_succ : j.castSucc < j.succ).ne
        (A.sortedLabel.injective h')


-- @@ L113-122 verbatim
theorem outgoingCutIndexFour_ne_incomingCutIndexFour
    (A : P.CyclicMarking 3) (l : Fin 4) :
    A.outgoingCutIndexFour l ≠ A.incomingCutIndexFour l := by
  intro h
  apply A.cyclicCutSourceLabel_ne_targetLabel_four
    (A.outgoingCutIndexFour l)
  calc
    A.cyclicCutSourceLabel (A.outgoingCutIndexFour l) = l := by simp
    _ = A.cyclicCutTargetLabel (A.incomingCutIndexFour l) := by simp
    _ = A.cyclicCutTargetLabel (A.outgoingCutIndexFour l) := by rw [h]


-- @@ L124-130 verbatim
theorem point_mem_cyclicCutRange_outgoingCutIndexFour
    (A : P.CyclicMarking 3) (l : Fin 4) :
    A.point l ∈ A.cyclicCutRange (A.outgoingCutIndexFour l) := by
  rw [← A.range_cyclicCutPath]
  refine ⟨0, ?_⟩
  rw [Path.source]
  simp


-- @@ L132-138 verbatim
theorem point_mem_cyclicCutRange_incomingCutIndexFour
    (A : P.CyclicMarking 3) (l : Fin 4) :
    A.point l ∈ A.cyclicCutRange (A.incomingCutIndexFour l) := by
  rw [← A.range_cyclicCutPath]
  refine ⟨1, ?_⟩
  rw [Path.target]
  simp


-- @@ L140-171 verbatim
/-- If one cut is designated local and a second cut does not contain the
specified mark, one of the two incident cuts is different from both.  This
is the finite selector needed to extract a genuinely exterior cut. -/
theorem exists_incidentCutIndexFour_ne_two
    (A : P.CyclicMarking 3) (l : Fin 4) (i j : Fin 4)
    (hnotj : A.point l ∉ A.cyclicCutRange j) :
    ∃ r : Fin 4, r ≠ i ∧ r ≠ j ∧
      (A.cyclicCutSourceLabel r = l ∨
        A.cyclicCutTargetLabel r = l) := by
  classical
  let outgoing := A.outgoingCutIndexFour l
  let incoming := A.incomingCutIndexFour l
  have hne : outgoing ≠ incoming :=
    A.outgoingCutIndexFour_ne_incomingCutIndexFour l
  have houtj : outgoing ≠ j := by
    intro h
    apply hnotj
    rw [← h]
    exact A.point_mem_cyclicCutRange_outgoingCutIndexFour l
  have hinj : incoming ≠ j := by
    intro h
    apply hnotj
    rw [← h]
    exact A.point_mem_cyclicCutRange_incomingCutIndexFour l
  by_cases houti : outgoing = i
  · refine ⟨incoming, ?_, hinj, Or.inr ?_⟩
    · intro hini
      apply hne
      exact houti.trans hini.symm
    · exact A.cyclicCutTargetLabel_incomingCutIndexFour l
  · exact ⟨outgoing, houti, houtj,
      Or.inl (A.cyclicCutSourceLabel_outgoingCutIndexFour l)⟩


-- @@ L173-173 verbatim
end SimpleClosedOrbitParam.CyclicMarking


-- @@ L175-175 verbatim
variable {X₀ X₁ : FramedLevelSet n}

-- @@ L176-176 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}

-- @@ L177-177 verbatim
variable {SC : SignedFramedLevelCobordism S₀ S₁}


-- @@ L179-179 verbatim
namespace ValueSeparatedSignedMorsePackage


-- @@ L181-181 verbatim
variable {D : ValueSeparatedSignedMorsePackage SC}

-- @@ L182-182 verbatim
variable {t : ℝ} {ht : t ∈ D.position.eventTimes}


-- @@ L184-186 verbatim
local instance : Fintype SaddleBranch where
  elems := {.positive, .negative}
  complete b := by cases b <;> simp


-- @@ L188-212 verbatim
/-- A production-local auxiliary boundary.  The endpoint cover is used for
flow capture.  The center cover, with target radius exactly `radius`, proves
that every cyclic cut avoiding the open radius ball lies in a fixed ambient
exterior slab. -/
structure ChronologicalSaddleAuxiliaryLocalData : Type where
  radius : ℝ
  radius_pos : 0 < radius
  radius_lt_embedded :
    radius < (D.chronologicalEventEmbeddedShrink t ht).radius
  endpointCoverRadius : ℝ
  endpointCoverRadius_pos : 0 < endpointCoverRadius
  endpointCover : ∀ (p : SaddleBranch × SaddleBranch) (v : E'),
    dist v ((D.position.eventModel t ht).saddleCriticalBoundaryEnd p radius) <
        endpointCoverRadius →
    D.signedOutput.cobordism.G v = 0 →
    ∃ u : E₂,
      ‖u‖ < (D.chronologicalEventEmbeddedShrink t ht).radius ∧
      (D.position.eventModel t ht).param u = v
  centerCoverRadius : ℝ
  centerCoverRadius_pos : 0 < centerCoverRadius
  centerCover : ∀ v : E',
    dist v (D.position.eventCenter t ht) < centerCoverRadius →
    D.signedOutput.cobordism.G v = 0 →
    ∃ u : E₂, ‖u‖ < radius ∧
      (D.position.eventModel t ht).param u = v


-- @@ L214-245 verbatim
/-- The two production cover theorems canonically supply the auxiliary local
data; there is no residual chart contract. -/
noncomputable def chronologicalSaddleAuxiliaryLocalData
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    ChronologicalSaddleAuxiliaryLocalData
      (D := D) (t := t) (ht := ht) := by
  classical
  let T := D.chronologicalEventEmbeddedShrink t ht
  let hEndpoint := D.exists_smallSaddleBoundaryRadius_endpointCover t ht
  let sigma : ℝ := hEndpoint.choose
  have hsigma : 0 < sigma := hEndpoint.choose_spec.1
  have hsigmaT : sigma < T.radius := hEndpoint.choose_spec.2.1
  let hDelta := hEndpoint.choose_spec.2.2
  let delta : ℝ := hDelta.choose
  have hdelta : 0 < delta := hDelta.choose_spec.1
  have hend := hDelta.choose_spec.2
  let hCenter :=
    D.eventModel_covers_fiber_within_morseRadius t ht hsigma
  let epsilon : ℝ := hCenter.choose
  have hepsilon : 0 < epsilon := hCenter.choose_spec.1
  have hcenter := hCenter.choose_spec.2
  exact {
    radius := sigma
    radius_pos := hsigma
    radius_lt_embedded := hsigmaT
    endpointCoverRadius := delta
    endpointCoverRadius_pos := hdelta
    endpointCover := hend
    centerCoverRadius := epsilon
    centerCoverRadius_pos := hepsilon
    centerCover := hcenter }


-- @@ L247-247 verbatim
namespace ChronologicalSaddleAuxiliaryLocalData


-- @@ L249-250 verbatim
variable (L : ChronologicalSaddleAuxiliaryLocalData
  (D := D) (t := t) (ht := ht))


-- @@ L252-265 verbatim
/-- Transport the actual global pairing from the chronological radius to the
auxiliary cover radius. -/
noncomputable def pairing
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht)) :
    (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      L.radius :=
  StandardMorseEventAt.EmbeddedShrink.changeSaddlePuncturedCriticalArcPairingRadius
    (D.chronologicalEventEmbeddedShrink t ht)
    (D.chronologicalEventFullRadiusSmooth t ht) hindex
    (D.chronologicalSaddleBoundaryRadius_pos t ht) L.radius_pos
    (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht)
    L.radius_lt_embedded A


-- @@ L267-273 verbatim
/-- Finite critical core of the four chosen auxiliary mate arcs. -/
def mateArcCore
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht)) : Set E' :=
  ⋃ p : SaddleBranch × SaddleBranch,
    Set.range ((L.pairing hindex A).chosenMateArc p).toPath


-- @@ L275-283 verbatim
theorem chosenMateArc_mem_mateArcCore
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht))
    (p : SaddleBranch × SaddleBranch) (u : I) :
    ((L.pairing hindex A).chosenMateArc p).toPath u ∈
      L.mateArcCore hindex A := by
  apply Set.mem_iUnion.2
  exact ⟨p, ⟨u, rfl⟩⟩


-- @@ L285-292 verbatim
theorem isCompact_mateArcCore
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht)) :
    IsCompact (L.mateArcCore hindex A) := by
  apply isCompact_iUnion
  intro p
  exact isCompact_range ((L.pairing hindex A).chosenMateArc p).toPath.continuous


-- @@ L294-309 verbatim
theorem mateArcCore_subset_slabRegularSet
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht)) :
    L.mateArcCore hindex A ⊆
      slabRegularSet D.signedOutput.cobordism.G := by
  intro z hz
  obtain ⟨p, u, rfl⟩ := Set.mem_iUnion.mp hz
  have hpunct := ((L.pairing hindex A).chosenMateArc p).mem_exterior u
  have hspatial : Surjective
      (spatialDeriv D.signedOutput.cobordism.G
        (((L.pairing hindex A).chosenMateArc p).toPath u)) := by
    exact StandardMorseEventAt.puncturedCriticalSlice_spatialDeriv_surjective
      (P := D.position) (ht := ht) hpunct
  exact mem_slabRegularSet_of_spatial_surjective
    (D.signedOutput.cobordism.regular _ hpunct.1) hspatial


-- @@ L311-322 verbatim
/-- Common compact field for all four auxiliary mate arcs. -/
noncomputable def mateArcTimeField
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht)) :
    CompactTimeTamedField
      D.signedOutput.cobordism.toLevelCobordismData
      (L.mateArcCore hindex A) :=
  (exists_compactTimeTamedField
    D.signedOutput.cobordism.toLevelCobordismData
    (L.isCompact_mateArcCore hindex A)
    (L.mateArcCore_subset_slabRegularSet hindex A)).some


-- @@ L324-331 verbatim
/-- Fixed exterior slab determined by the arbitrarily small center cover.
It is chosen before the regular displacement and therefore breaks the
otherwise circular dependency between a cyclic cut and its safe flow time. -/
def exteriorSlabCore : Set E' :=
  slabFiber D.signedOutput.cobordism.toLevelCobordismData
      (D.position.eventBracket t ht).before
      (D.position.eventBracket t ht).after ∩
    {z | L.centerCoverRadius ≤ dist z (D.position.eventCenter t ht)}


-- @@ L333-338 verbatim
theorem isCompact_exteriorSlabCore : IsCompact L.exteriorSlabCore := by
  apply (isCompact_slabFiber
    D.signedOutput.cobordism.toLevelCobordismData
    (D.position.eventBracket t ht).before
    (D.position.eventBracket t ht).after).inter_right
  exact isClosed_le continuous_const (continuous_id.dist continuous_const)


-- @@ L340-357 verbatim
theorem exteriorSlabCore_subset_slabRegularSet :
    L.exteriorSlabCore ⊆ slabRegularSet D.signedOutput.cobordism.G := by
  intro z hz
  rw [exteriorSlabCore] at hz
  have hspatial : Surjective
      (spatialDeriv D.signedOutput.cobordism.G z) := by
    by_contra hnot
    have hcritical : z ∈ timeCritical D.signedOutput.cobordism.G :=
      ⟨hz.1.1, hnot⟩
    have hzc : z = D.position.eventCenter t ht :=
      (D.position.eventBracket t ht).isolates z hcritical hz.1.2
    have hdist := hz.2
    change L.centerCoverRadius ≤
      dist z (D.position.eventCenter t ht) at hdist
    rw [hzc, dist_self] at hdist
    exact (not_lt_of_ge hdist) L.centerCoverRadius_pos
  exact mem_slabRegularSet_of_spatial_surjective
    (D.signedOutput.cobordism.regular z hz.1.1) hspatial


-- @@ L359-367 verbatim
/-- Common field used later to flow any center-avoiding cyclic cut back to
the critical slice. -/
noncomputable def exteriorSlabTimeField :
    CompactTimeTamedField
      D.signedOutput.cobordism.toLevelCobordismData L.exteriorSlabCore :=
  (exists_compactTimeTamedField
    D.signedOutput.cobordism.toLevelCobordismData
    L.isCompact_exteriorSlabCore
    L.exteriorSlabCore_subset_slabRegularSet).some


-- @@ L369-369 verbatim
end ChronologicalSaddleAuxiliaryLocalData


-- @@ L371-371 verbatim
end ValueSeparatedSignedMorsePackage


-- @@ L373-373 verbatim
end Submission
