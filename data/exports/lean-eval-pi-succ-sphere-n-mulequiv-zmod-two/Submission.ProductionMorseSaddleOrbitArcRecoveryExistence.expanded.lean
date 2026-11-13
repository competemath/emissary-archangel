import Submission.ProductionMorseSaddleOrientedTopologyBridge
import Submission.ProductionMorseSaddleAutomaticOrientedAdapter
import Submission.ProductionMorseSaddleFlowCompatibilityExistence


-- @@ L5-32 verbatim
/-!
# Existence of the regular-orbit arc recovery bridge

This file proves the converse half of the saddle topology dichotomy contract,
`ChronologicalSaddleRegularOrbitArcRecovery`: if the two distinct local
branches of a chronological production saddle lie on one complete regular
orbit, then deleting the local saddle segments leaves an honest transverse
critical exterior arc.

The construction follows the prepared route:

* transport the branch-orbit equality from the fixed chronological window
  slice to an automatically small recovery slice;
* mark all four chart-boundary ends on the common intrinsic orbit and use the
  four-mark cut classification to select one exterior cyclic cut incident to
  the `(negative, negative)` end;
* show that this cut lies in a fixed compact exterior slab avoiding a
  center-cover ball, flow it back to the critical level with the associated
  compact time-tamed field, and capture its two flowed endpoints inside the
  labelled quadrants at the four marked critical ends;
* pin down the surviving transverse label with the uniqueness and finite
  orientation dichotomy of the given punctured critical arc pairing.

The only hypotheses consumed are the punctured critical arc pairing data `A`
and the endpoint-local fiber cover `L`, exactly the hypotheses already present
in the final consumer
`chronologicalSaddleTopologyDichotomy_of_endpointLocalFiberCover`.
-/


-- @@ L34-34 verbatim
set_option autoImplicit false

-- @@ L35-35 verbatim
set_option maxHeartbeats 2400000


-- @@ L37-37 verbatim
noncomputable section


-- @@ L39-39 verbatim
open Set Function Metric Filter

-- @@ L40-40 verbatim
open scoped RealInnerProductSpace Topology unitInterval


-- @@ L42-42 verbatim
namespace Submission


-- @@ L44-44 verbatim
variable {n : ℕ}


-- @@ L46-46 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

-- @@ L47-47 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L48-48 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L50-50 verbatim
/-! ## Endpoint labels of four-mark cyclic cuts -/


-- @@ L52-52 verbatim
namespace SimpleClosedOrbitParam.CyclicMarking


-- @@ L54-54 verbatim
variable {X : FramedLevelSet n} {V : TamedField X}

-- @@ L55-55 verbatim
variable {P : SimpleClosedOrbitParam X V}


-- @@ L57-81 verbatim
/-- A marked point lying on a uniformly indexed cyclic cut is one of the two
endpoint labels of that cut. -/
theorem point_mem_cyclicCutRange_eq_label {k : ℕ}
    (A : P.CyclicMarking k) (i : Fin (k + 1)) (j : Fin (k + 1))
    (hj : A.point j ∈ A.cyclicCutRange i) :
    j = A.cyclicCutSourceLabel i ∨ j = A.cyclicCutTargetLabel i := by
  induction i using Fin.lastCases with
  | last =>
      rw [A.cyclicCutRange_last] at hj
      rcases A.point_mem_range_wrapSubpath j hj with h | h
      · left
        rw [h]
        simp only [cyclicCutSourceLabel, Fin.lastCases_last]
      · right
        rw [h]
        simp only [cyclicCutTargetLabel, Fin.lastCases_last]
  | cast q =>
      rw [A.cyclicCutRange_castSucc] at hj
      rcases A.point_mem_range_adjacentSubpath q j hj with h | h
      · left
        rw [h]
        simp only [cyclicCutSourceLabel, Fin.lastCases_castSucc]
      · right
        rw [h]
        simp only [cyclicCutTargetLabel, Fin.lastCases_castSucc]


-- @@ L83-140 verbatim
/-- On a four-marked orbit, two cyclic cuts with the same unordered endpoint
label pair coincide. -/
theorem cutIndexFour_eq_of_labelPair
    (A : P.CyclicMarking 3) {r i : Fin 4}
    (h : (A.cyclicCutSourceLabel r = A.cyclicCutSourceLabel i ∧
          A.cyclicCutTargetLabel r = A.cyclicCutTargetLabel i) ∨
        (A.cyclicCutSourceLabel r = A.cyclicCutTargetLabel i ∧
          A.cyclicCutTargetLabel r = A.cyclicCutSourceLabel i)) :
    r = i := by
  induction r using Fin.lastCases with
  | last =>
      induction i using Fin.lastCases with
      | last => rfl
      | cast qi =>
          exfalso
          have hqi := qi.isLt
          simp only [cyclicCutSourceLabel, cyclicCutTargetLabel,
            Fin.lastCases_last, Fin.lastCases_castSucc] at h
          rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · have e1 := congrArg Fin.val (A.sortedLabel.injective h1)
            simp only [Fin.val_last, Fin.coe_castSucc] at e1
            omega
          · have e1 := congrArg Fin.val (A.sortedLabel.injective h1)
            have e2 := congrArg Fin.val (A.sortedLabel.injective h2)
            simp only [Fin.val_last, Fin.val_succ, Fin.val_zero,
              Fin.coe_castSucc] at e1 e2
            omega
  | cast qr =>
      induction i using Fin.lastCases with
      | last =>
          exfalso
          have hqr := qr.isLt
          simp only [cyclicCutSourceLabel, cyclicCutTargetLabel,
            Fin.lastCases_last, Fin.lastCases_castSucc] at h
          rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · have e1 := congrArg Fin.val (A.sortedLabel.injective h1)
            simp only [Fin.val_last, Fin.coe_castSucc] at e1
            omega
          · have e1 := congrArg Fin.val (A.sortedLabel.injective h1)
            have e2 := congrArg Fin.val (A.sortedLabel.injective h2)
            simp only [Fin.val_last, Fin.val_succ, Fin.val_zero,
              Fin.coe_castSucc] at e1 e2
            omega
      | cast qi =>
          have hqr := qr.isLt
          have hqi := qi.isLt
          simp only [cyclicCutSourceLabel, cyclicCutTargetLabel,
            Fin.lastCases_castSucc] at h
          rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · have e1 := congrArg Fin.val (A.sortedLabel.injective h1)
            simp only [Fin.coe_castSucc] at e1
            apply congrArg Fin.castSucc
            exact Fin.ext e1
          · exfalso
            have e1 := congrArg Fin.val (A.sortedLabel.injective h1)
            have e2 := congrArg Fin.val (A.sortedLabel.injective h2)
            simp only [Fin.val_succ, Fin.coe_castSucc] at e1 e2
            omega


-- @@ L142-173 verbatim
/-- Two four-mark cyclic cuts incident to the same two distinct marked labels
coincide. -/
theorem cutIndexFour_eq_of_endpointLabels
    (A : P.CyclicMarking 3) {r i : Fin 4} {l₀ l₁ : Fin 4} (hne : l₀ ≠ l₁)
    (hr0 : A.cyclicCutSourceLabel r = l₀ ∨ A.cyclicCutTargetLabel r = l₀)
    (hr1 : A.cyclicCutSourceLabel r = l₁ ∨ A.cyclicCutTargetLabel r = l₁)
    (hi0 : A.cyclicCutSourceLabel i = l₀ ∨ A.cyclicCutTargetLabel i = l₀)
    (hi1 : A.cyclicCutSourceLabel i = l₁ ∨ A.cyclicCutTargetLabel i = l₁) :
    r = i := by
  have hrpair : (A.cyclicCutSourceLabel r = l₀ ∧
      A.cyclicCutTargetLabel r = l₁) ∨
      (A.cyclicCutSourceLabel r = l₁ ∧ A.cyclicCutTargetLabel r = l₀) := by
    rcases hr0 with h0 | h0 <;> rcases hr1 with h1 | h1
    · exact absurd (h0.symm.trans h1) hne
    · exact Or.inl ⟨h0, h1⟩
    · exact Or.inr ⟨h1, h0⟩
    · exact absurd (h0.symm.trans h1) hne
  have hipair : (A.cyclicCutSourceLabel i = l₀ ∧
      A.cyclicCutTargetLabel i = l₁) ∨
      (A.cyclicCutSourceLabel i = l₁ ∧ A.cyclicCutTargetLabel i = l₀) := by
    rcases hi0 with h0 | h0 <;> rcases hi1 with h1 | h1
    · exact absurd (h0.symm.trans h1) hne
    · exact Or.inl ⟨h0, h1⟩
    · exact Or.inr ⟨h1, h0⟩
    · exact absurd (h0.symm.trans h1) hne
  apply A.cutIndexFour_eq_of_labelPair
  rcases hrpair with ⟨hr0', hr1'⟩ | ⟨hr0', hr1'⟩ <;>
    rcases hipair with ⟨hi0', hi1'⟩ | ⟨hi0', hi1'⟩
  · exact Or.inl ⟨hr0'.trans hi0'.symm, hr1'.trans hi1'.symm⟩
  · exact Or.inr ⟨hr0'.trans hi1'.symm, hr1'.trans hi0'.symm⟩
  · exact Or.inr ⟨hr0'.trans hi1'.symm, hr1'.trans hi0'.symm⟩
  · exact Or.inl ⟨hr0'.trans hi0'.symm, hr1'.trans hi1'.symm⟩


-- @@ L175-175 verbatim
end SimpleClosedOrbitParam.CyclicMarking


-- @@ L177-177 verbatim
variable {X₀ X₁ : FramedLevelSet n}

-- @@ L178-178 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}

-- @@ L179-179 verbatim
variable {SC : SignedFramedLevelCobordism S₀ S₁}


-- @@ L181-181 verbatim
namespace ValueSeparatedSignedMorsePackage


-- @@ L183-183 verbatim
variable {D : ValueSeparatedSignedMorsePackage SC}

-- @@ L184-184 verbatim
variable {t : ℝ} {ht : t ∈ D.position.eventTimes}


-- @@ L186-186 verbatim
local notation "rho" => D.chronologicalSaddleBoundaryRadius t ht

-- @@ L187-187 verbatim
local notation "aWin" => D.chronologicalWindowRadius t ht


-- @@ L189-189 verbatim
/-! ## Recovery-specific auxiliary local data -/


-- @@ L191-218 verbatim
/-- Auxiliary local cover data at the fixed chronological boundary radius:
the endpoint covers come from the given endpoint-local fiber cover, and the
center cover has target parameter radius exactly the chronological radius. -/
noncomputable def chronologicalSaddleRecoveryAuxiliaryData
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) :
    ChronologicalSaddleAuxiliaryLocalData (D := D) (t := t) (ht := ht) := by
  classical
  let hCenter := D.eventModel_covers_fiber_within_morseRadius t ht
    (D.chronologicalSaddleBoundaryRadius_pos t ht)
  exact {
    radius := D.chronologicalSaddleBoundaryRadius t ht
    radius_pos := D.chronologicalSaddleBoundaryRadius_pos t ht
    radius_lt_embedded := D.chronologicalSaddleBoundaryRadius_lt_embedded t ht
    endpointCoverRadius := saddleFourEndMin L.radius
    endpointCoverRadius_pos := saddleFourEndMin_pos L.radius_pos
    endpointCover := by
      intro p v hv hz
      obtain ⟨u, hu, hup⟩ := L.cover p v
        (hv.trans_le (saddleFourEndMin_le L.radius p)) hz
      exact ⟨u,
        hu.trans (D.chronologicalSaddleEndpointParamRadius_lt_embedded t ht),
        hup⟩
    centerCoverRadius := hCenter.choose
    centerCoverRadius_pos := hCenter.choose_spec.1
    centerCover := hCenter.choose_spec.2 }


-- @@ L220-230 verbatim
/-- A single positive margin at each marked critical end which is below the
endpoint cover radius and below both signed-branch separation radii. -/
noncomputable def chronologicalSaddleRecoveryMargin
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht))
    (p : SaddleBranch × SaddleBranch) : ℝ :=
  min (L.radius p)
    (min (D.chronologicalSaddlePositiveBranchRadius t ht p)
      (D.chronologicalSaddleNegativeBranchRadius t ht p))


-- @@ L232-241 verbatim
theorem chronologicalSaddleRecoveryMargin_pos
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht))
    (p : SaddleBranch × SaddleBranch) :
    0 < D.chronologicalSaddleRecoveryMargin t ht L p :=
  lt_min (L.radius_pos p)
    (lt_min (D.chronologicalSaddlePositiveBranchRadius_pos t ht p)
      (D.chronologicalSaddleNegativeBranchRadius_pos t ht p))


-- @@ L243-250 verbatim
theorem chronologicalSaddleRecoveryMargin_le_cover
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht))
    (p : SaddleBranch × SaddleBranch) :
    D.chronologicalSaddleRecoveryMargin t ht L p ≤ L.radius p :=
  min_le_left _ _


-- @@ L252-260 verbatim
theorem chronologicalSaddleRecoveryMargin_le_positiveBranch
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht))
    (p : SaddleBranch × SaddleBranch) :
    D.chronologicalSaddleRecoveryMargin t ht L p ≤
      D.chronologicalSaddlePositiveBranchRadius t ht p :=
  (min_le_right _ _).trans (min_le_left _ _)


-- @@ L262-270 verbatim
theorem chronologicalSaddleRecoveryMargin_le_negativeBranch
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht))
    (p : SaddleBranch × SaddleBranch) :
    D.chronologicalSaddleRecoveryMargin t ht L p ≤
      D.chronologicalSaddleNegativeBranchRadius t ht p :=
  (min_le_right _ _).trans (min_le_right _ _)


-- @@ L272-272 verbatim
/-! ## Ambient continuity of the marked boundary ends in the level scale -/


-- @@ L274-286 verbatim
/-- At scale zero, the transposed negative boundary end is the marked
critical end. -/
theorem saddleNegativeBoundaryEnd_zero_eq_criticalBoundaryEnd
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (p : SaddleBranch × SaddleBranch) :
    (D.position.eventModel t ht).saddleNegativeBoundaryEnd p.2 p.1
        (D.chronologicalSaddleBoundaryRadius t ht) 0 =
      (D.position.eventModel t ht).saddleCriticalBoundaryEnd p
        (D.chronologicalSaddleBoundaryRadius t ht) :=
  congrArg (D.position.eventModel t ht).localPoint
    (saddleCriticalBoundaryEndParam_eq_negative p
      (D.chronologicalSaddleBoundaryRadius t ht)).symm


-- @@ L288-315 verbatim
theorem continuousAt_saddlePositiveBoundaryEnd_scale
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (p : SaddleBranch × SaddleBranch) :
    ContinuousAt (fun c : ℝ =>
      (D.position.eventModel t ht).saddlePositiveBoundaryEnd p.1 p.2
        (D.chronologicalSaddleBoundaryRadius t ht) c) 0 := by
  let M := D.position.eventModel t ht
  let T := D.chronologicalEventEmbeddedShrink t ht
  let H := D.chronologicalEventFullRadiusSmooth t ht
  have hrho : 0 < D.chronologicalSaddleBoundaryRadius t ht :=
    D.chronologicalSaddleBoundaryRadius_pos t ht
  have hparam : Continuous (fun c : ℝ =>
      saddlePositiveBoundaryEndParam p.1 p.2
        (D.chronologicalSaddleBoundaryRadius t ht) c) := by
    rcases p with ⟨b, e⟩
    cases b <;> cases e <;>
      simp only [saddlePositiveBoundaryEndParam, saddlePositiveArc,
        saddleBoundaryParameter, pairToMorseParam, signedBranch] <;>
      fun_prop
  have hnorm0 : ‖saddlePositiveBoundaryEndParam p.1 p.2
      (D.chronologicalSaddleBoundaryRadius t ht) 0‖ < M.radius := by
    rw [norm_saddlePositiveBoundaryEndParam p.1 p.2 hrho
      (by nlinarith [sq_pos_of_pos hrho])]
    exact (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht).trans_le
      T.radius_le
  exact ((H.differentiableAt _ hnorm0).continuousAt).comp
    hparam.continuousAt


-- @@ L317-344 verbatim
theorem continuousAt_saddleNegativeBoundaryEnd_scale
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (p : SaddleBranch × SaddleBranch) :
    ContinuousAt (fun c : ℝ =>
      (D.position.eventModel t ht).saddleNegativeBoundaryEnd p.2 p.1
        (D.chronologicalSaddleBoundaryRadius t ht) c) 0 := by
  let M := D.position.eventModel t ht
  let T := D.chronologicalEventEmbeddedShrink t ht
  let H := D.chronologicalEventFullRadiusSmooth t ht
  have hrho : 0 < D.chronologicalSaddleBoundaryRadius t ht :=
    D.chronologicalSaddleBoundaryRadius_pos t ht
  have hparam : Continuous (fun c : ℝ =>
      saddleNegativeBoundaryEndParam p.2 p.1
        (D.chronologicalSaddleBoundaryRadius t ht) c) := by
    rcases p with ⟨b, e⟩
    cases b <;> cases e <;>
      simp only [saddleNegativeBoundaryEndParam, saddleNegativeArc,
        saddleBoundaryParameter, pairToMorseParam, signedBranch] <;>
      fun_prop
  have hnorm0 : ‖saddleNegativeBoundaryEndParam p.2 p.1
      (D.chronologicalSaddleBoundaryRadius t ht) 0‖ < M.radius := by
    rw [norm_saddleNegativeBoundaryEndParam p.2 p.1 hrho
      (by nlinarith [sq_pos_of_pos hrho])]
    exact (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht).trans_le
      T.radius_le
  exact ((H.differentiableAt _ hnorm0).continuousAt).comp
    hparam.continuousAt


-- @@ L346-346 verbatim
/-! ## The recovery flow scale -/


-- @@ L348-373 verbatim
/-- A displacement scale which is safe for the fixed exterior slab field and
keeps the flowed marked boundary ends within the recovery margins of all four
labelled critical ends, on both regular sides. -/
structure ChronologicalSaddleRecoveryScale
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) : Type where
  scale : ℝ
  scale_pos : 0 < scale
  scale_lt_window : scale < aWin
  safe : scale ^ 2 ≤
    (D.chronologicalSaddleRecoveryAuxiliaryData t ht
      L).exteriorSlabTimeField.safeTime
  positive_close : ∀ p : SaddleBranch × SaddleBranch,
    dist ((D.position.eventModel t ht).saddlePositiveBoundaryEnd p.1 p.2
        rho scale)
      ((D.position.eventModel t ht).saddleCriticalBoundaryEnd p rho) +
      ((D.chronologicalSaddleRecoveryAuxiliaryData t ht
        L).exteriorSlabTimeField.base.bound : ℝ) * scale ^ 2 <
      D.chronologicalSaddleRecoveryMargin t ht L p
  negative_close : ∀ p : SaddleBranch × SaddleBranch,
    dist ((D.position.eventModel t ht).saddleNegativeBoundaryEnd p.2 p.1
        rho scale)
      ((D.position.eventModel t ht).saddleCriticalBoundaryEnd p rho) +
      ((D.chronologicalSaddleRecoveryAuxiliaryData t ht
        L).exteriorSlabTimeField.base.bound : ℝ) * scale ^ 2 <
      D.chronologicalSaddleRecoveryMargin t ht L p


-- @@ L375-530 verbatim
theorem nonempty_chronologicalSaddleRecoveryScale
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) :
    Nonempty (ChronologicalSaddleRecoveryScale
      (D := D) (t := t) (ht := ht) L) := by
  classical
  let M := D.position.eventModel t ht
  let R := (D.chronologicalSaddleRecoveryAuxiliaryData t ht
    L).exteriorSlabTimeField
  let B : ℝ := (R.base.bound : ℝ)
  have hB : 0 ≤ B := R.base.bound.coe_nonneg
  -- positive-side margin gap
  let posGap : ℝ → ℝ := fun x => saddleFourEndMin (fun p =>
    D.chronologicalSaddleRecoveryMargin t ht L p -
      (dist (M.saddlePositiveBoundaryEnd p.1 p.2
          (D.chronologicalSaddleBoundaryRadius t ht) x)
        (M.saddleCriticalBoundaryEnd p
          (D.chronologicalSaddleBoundaryRadius t ht)) + B * x ^ 2))
  let negGap : ℝ → ℝ := fun x => saddleFourEndMin (fun p =>
    D.chronologicalSaddleRecoveryMargin t ht L p -
      (dist (M.saddleNegativeBoundaryEnd p.2 p.1
          (D.chronologicalSaddleBoundaryRadius t ht) x)
        (M.saddleCriticalBoundaryEnd p
          (D.chronologicalSaddleBoundaryRadius t ht)) + B * x ^ 2))
  have hcomp : ∀ p : SaddleBranch × SaddleBranch,
      ContinuousAt (fun x : ℝ =>
        D.chronologicalSaddleRecoveryMargin t ht L p -
          (dist (M.saddlePositiveBoundaryEnd p.1 p.2
              (D.chronologicalSaddleBoundaryRadius t ht) x)
            (M.saddleCriticalBoundaryEnd p
              (D.chronologicalSaddleBoundaryRadius t ht)) + B * x ^ 2)) 0 := by
    intro p
    exact continuousAt_const.sub
      (((D.continuousAt_saddlePositiveBoundaryEnd_scale t ht p).dist
          continuousAt_const).add
        (continuousAt_const.mul (continuousAt_id.pow 2)))
  have hcompN : ∀ p : SaddleBranch × SaddleBranch,
      ContinuousAt (fun x : ℝ =>
        D.chronologicalSaddleRecoveryMargin t ht L p -
          (dist (M.saddleNegativeBoundaryEnd p.2 p.1
              (D.chronologicalSaddleBoundaryRadius t ht) x)
            (M.saddleCriticalBoundaryEnd p
              (D.chronologicalSaddleBoundaryRadius t ht)) + B * x ^ 2)) 0 := by
    intro p
    exact continuousAt_const.sub
      (((D.continuousAt_saddleNegativeBoundaryEnd_scale t ht p).dist
          continuousAt_const).add
        (continuousAt_const.mul (continuousAt_id.pow 2)))
  have hposCont : ContinuousAt posGap 0 := by
    simp only [posGap, saddleFourEndMin]
    exact (hcomp _).min ((hcomp _).min ((hcomp _).min (hcomp _)))
  have hnegCont : ContinuousAt negGap 0 := by
    simp only [negGap, saddleFourEndMin]
    exact (hcompN _).min ((hcompN _).min ((hcompN _).min (hcompN _)))
  have hposVal : 0 < posGap 0 := by
    show 0 < saddleFourEndMin (fun p =>
      D.chronologicalSaddleRecoveryMargin t ht L p -
        (dist (M.saddlePositiveBoundaryEnd p.1 p.2
            (D.chronologicalSaddleBoundaryRadius t ht) (0 : ℝ))
          (M.saddleCriticalBoundaryEnd p
            (D.chronologicalSaddleBoundaryRadius t ht)) + B * (0 : ℝ) ^ 2))
    apply saddleFourEndMin_pos
    intro p
    have h0 : M.saddlePositiveBoundaryEnd p.1 p.2
        (D.chronologicalSaddleBoundaryRadius t ht) (0 : ℝ) =
        M.saddleCriticalBoundaryEnd p
          (D.chronologicalSaddleBoundaryRadius t ht) := rfl
    rw [h0, dist_self]
    simpa using D.chronologicalSaddleRecoveryMargin_pos t ht L p
  have hnegVal : 0 < negGap 0 := by
    show 0 < saddleFourEndMin (fun p =>
      D.chronologicalSaddleRecoveryMargin t ht L p -
        (dist (M.saddleNegativeBoundaryEnd p.2 p.1
            (D.chronologicalSaddleBoundaryRadius t ht) (0 : ℝ))
          (M.saddleCriticalBoundaryEnd p
            (D.chronologicalSaddleBoundaryRadius t ht)) + B * (0 : ℝ) ^ 2))
    apply saddleFourEndMin_pos
    intro p
    have h0 : M.saddleNegativeBoundaryEnd p.2 p.1
        (D.chronologicalSaddleBoundaryRadius t ht) (0 : ℝ) =
        M.saddleCriticalBoundaryEnd p
          (D.chronologicalSaddleBoundaryRadius t ht) :=
      D.saddleNegativeBoundaryEnd_zero_eq_criticalBoundaryEnd t ht p
    rw [h0, dist_self]
    simpa using D.chronologicalSaddleRecoveryMargin_pos t ht L p
  have hposMem : posGap ⁻¹' Set.Ioi (0 : ℝ) ∈ nhds (0 : ℝ) :=
    hposCont.preimage_mem_nhds (Ioi_mem_nhds hposVal)
  have hnegMem : negGap ⁻¹' Set.Ioi (0 : ℝ) ∈ nhds (0 : ℝ) :=
    hnegCont.preimage_mem_nhds (Ioi_mem_nhds hnegVal)
  have hsafeN : {x : ℝ | x ^ 2 < R.safeTime} ∈ nhds (0 : ℝ) := by
    have hlim : Tendsto (fun x : ℝ => x ^ 2) (nhds 0) (nhds 0) := by
      have hcont : ContinuousAt (fun x : ℝ => x ^ 2) 0 :=
        continuousAt_id.pow 2
      simpa using hcont.tendsto
    exact hlim (Iio_mem_nhds R.safeTime_pos)
  have hgood : {x : ℝ | x ^ 2 < R.safeTime} ∩
      (posGap ⁻¹' Set.Ioi (0 : ℝ) ∩ negGap ⁻¹' Set.Ioi (0 : ℝ)) ∈
        nhds (0 : ℝ) :=
    Filter.inter_mem hsafeN (Filter.inter_mem hposMem hnegMem)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hgood
  let c := min (D.chronologicalWindowRadius t ht) δ
  let b := c / 2
  have hc : 0 < c := lt_min (D.chronologicalWindowRadius_pos t ht) hδ
  have hb : 0 < b := div_pos hc (by norm_num)
  have hbc : b < c := by
    dsimp [b]
    linarith
  have hba : b < D.chronologicalWindowRadius t ht :=
    hbc.trans_le (min_le_left _ _)
  have hbδ : dist b (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hb]
    exact hbc.trans_le (min_le_right _ _)
  have hbGood := hball hbδ
  refine ⟨{
    scale := b
    scale_pos := hb
    scale_lt_window := hba
    safe := hbGood.1.le
    positive_close := ?_
    negative_close := ?_ }⟩
  · intro p
    have hgap := hbGood.2.1
    have hle := saddleFourEndMin_le (fun p =>
      D.chronologicalSaddleRecoveryMargin t ht L p -
        (dist (M.saddlePositiveBoundaryEnd p.1 p.2
            (D.chronologicalSaddleBoundaryRadius t ht) b)
          (M.saddleCriticalBoundaryEnd p
            (D.chronologicalSaddleBoundaryRadius t ht)) + B * b ^ 2)) p
    have hgap' : (0 : ℝ) < posGap b := hgap
    have : (0 : ℝ) <
        D.chronologicalSaddleRecoveryMargin t ht L p -
          (dist (M.saddlePositiveBoundaryEnd p.1 p.2
              (D.chronologicalSaddleBoundaryRadius t ht) b)
            (M.saddleCriticalBoundaryEnd p
              (D.chronologicalSaddleBoundaryRadius t ht)) + B * b ^ 2) :=
      lt_of_lt_of_le hgap' hle
    linarith
  · intro p
    have hgap := hbGood.2.2
    have hle := saddleFourEndMin_le (fun p =>
      D.chronologicalSaddleRecoveryMargin t ht L p -
        (dist (M.saddleNegativeBoundaryEnd p.2 p.1
            (D.chronologicalSaddleBoundaryRadius t ht) b)
          (M.saddleCriticalBoundaryEnd p
            (D.chronologicalSaddleBoundaryRadius t ht)) + B * b ^ 2)) p
    have hgap' : (0 : ℝ) < negGap b := hgap
    have : (0 : ℝ) <
        D.chronologicalSaddleRecoveryMargin t ht L p -
          (dist (M.saddleNegativeBoundaryEnd p.2 p.1
              (D.chronologicalSaddleBoundaryRadius t ht) b)
            (M.saddleCriticalBoundaryEnd p
              (D.chronologicalSaddleBoundaryRadius t ht)) + B * b ^ 2) :=
      lt_of_lt_of_le hgap' hle
    linarith


-- @@ L532-539 verbatim
/-- Canonical choice of the recovery displacement scale. -/
noncomputable def chronologicalSaddleRecoveryScale
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) :
    ChronologicalSaddleRecoveryScale (D := D) (t := t) (ht := ht) L :=
  (nonempty_chronologicalSaddleRecoveryScale D t ht L).some


-- @@ L541-550 verbatim
theorem chronologicalSaddleRecoveryScale_sq_lt_window_sq
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) :
    (D.chronologicalSaddleRecoveryScale t ht L).scale ^ 2 <
      D.chronologicalWindowRadius t ht ^ 2 := by
  let Q := D.chronologicalSaddleRecoveryScale t ht L
  exact (sq_lt_sq₀ Q.scale_pos.le
    (D.chronologicalWindowRadius_pos t ht).le).2 Q.scale_lt_window


-- @@ L552-563 verbatim
theorem chronologicalSaddleRecoveryScale_sq_lt_saddleBoundary_sq
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) :
    (D.chronologicalSaddleRecoveryScale t ht L).scale ^ 2 <
      D.chronologicalSaddleBoundaryRadius t ht ^ 2 := by
  let Q := D.chronologicalSaddleRecoveryScale t ht L
  exact (sq_lt_sq₀ Q.scale_pos.le
    (D.chronologicalSaddleBoundaryRadius_pos t ht).le).2
    (Q.scale_lt_window.trans
      (D.chronologicalWindowRadius_lt_saddleBoundaryRadius t ht))


-- @@ L565-565 verbatim
/-! ## The two recovery regular slices -/


-- @@ L567-573 verbatim
def chronologicalSaddleRecoveryBeforeTime
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) : ℝ :=
  tcoord (D.position.eventCenter t ht) -
    (D.chronologicalSaddleRecoveryScale t ht L).scale ^ 2


-- @@ L575-581 verbatim
def chronologicalSaddleRecoveryAfterTime
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) : ℝ :=
  tcoord (D.position.eventCenter t ht) +
    (D.chronologicalSaddleRecoveryScale t ht L).scale ^ 2


-- @@ L583-605 verbatim
private theorem recoveryEventTime_eq_of_mem_chronologicalBracket
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    {s : ℝ} (hsEvent : s ∈ D.position.eventTimes)
    (hs : s ∈ Icc (D.position.eventBracket t ht).before
      (D.position.eventBracket t ht).after) :
    s = t := by
  let v := D.position.eventCenter s hsEvent
  have hvCritical : v ∈ timeCritical D.signedOutput.cobordism.G :=
    (D.position.eventCenter_mem_coreCriticalPoints s hsEvent).1
  have hvInterval : tcoord v ∈
      Icc (D.position.eventBracket t ht).before
        (D.position.eventBracket t ht).after := by
    change tcoord (D.position.eventCenter s hsEvent) ∈ _
    rw [D.position.eventCenter_time s hsEvent]
    exact hs
  have hvEq : v = D.position.eventCenter t ht :=
    (D.position.eventBracket t ht).isolates v hvCritical hvInterval
  calc
    s = tcoord (D.position.eventCenter s hsEvent) :=
      (D.position.eventCenter_time s hsEvent).symm
    _ = tcoord (D.position.eventCenter t ht) := congrArg tcoord hvEq
    _ = t := D.position.eventCenter_time t ht


-- @@ L607-633 verbatim
theorem regularSlab_chronologicalSaddleRecoveryAfter_to_window
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) :
    regularSlab D.signedOutput.cobordism.G
      (D.chronologicalSaddleRecoveryAfterTime t ht L)
      (D.chronologicalAfterTime t ht) := by
  rw [D.position.regularSlab_iff_avoid_eventTimes]
  intro s hsEvent hs
  have hcenterShort : tcoord (D.position.eventCenter t ht) <
      D.chronologicalSaddleRecoveryAfterTime t ht L := by
    rw [chronologicalSaddleRecoveryAfterTime]
    exact lt_add_of_pos_right _
      (sq_pos_of_pos (D.chronologicalSaddleRecoveryScale t ht L).scale_pos)
  have hsBracket : s ∈ Icc (D.position.eventBracket t ht).before
      (D.position.eventBracket t ht).after := by
    constructor
    · exact (D.position.eventBracket t ht).before_lt.le.trans
        (hcenterShort.le.trans hs.1)
    · exact hs.2.trans
        (D.chronologicalAfterTime_mem_bracket t ht).2.le
  have hst : s = t :=
    D.recoveryEventTime_eq_of_mem_chronologicalBracket t ht hsEvent hsBracket
  have htShort : t < D.chronologicalSaddleRecoveryAfterTime t ht L :=
    (D.position.eventCenter_time t ht).symm.trans_lt hcenterShort
  exact (not_le_of_gt htShort) (hst ▸ hs.1)


-- @@ L635-660 verbatim
theorem regularSlab_window_to_chronologicalSaddleRecoveryBefore
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) :
    regularSlab D.signedOutput.cobordism.G
      (D.chronologicalBeforeTime t ht)
      (D.chronologicalSaddleRecoveryBeforeTime t ht L) := by
  rw [D.position.regularSlab_iff_avoid_eventTimes]
  intro s hsEvent hs
  have hshortCenter : D.chronologicalSaddleRecoveryBeforeTime t ht L <
      tcoord (D.position.eventCenter t ht) := by
    rw [chronologicalSaddleRecoveryBeforeTime]
    exact sub_lt_self _
      (sq_pos_of_pos (D.chronologicalSaddleRecoveryScale t ht L).scale_pos)
  have hsBracket : s ∈ Icc (D.position.eventBracket t ht).before
      (D.position.eventBracket t ht).after := by
    constructor
    · exact (D.chronologicalBeforeTime_mem_bracket t ht).1.le.trans hs.1
    · exact hs.2.trans
        (hshortCenter.le.trans (D.position.eventBracket t ht).lt_after.le)
  have hst : s = t :=
    D.recoveryEventTime_eq_of_mem_chronologicalBracket t ht hsEvent hsBracket
  have hshortT : D.chronologicalSaddleRecoveryBeforeTime t ht L < t :=
    hshortCenter.trans_eq (D.position.eventCenter_time t ht)
  exact (not_le_of_gt hshortT) (hst ▸ hs.2)


-- @@ L662-675 verbatim
theorem chronologicalSaddleRecoveryAfterTime_regular
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) :
    sliceRegular D.signedOutput.cobordism.G
      (D.chronologicalSaddleRecoveryAfterTime t ht L) :=
  (D.regularSlab_chronologicalSaddleRecoveryAfter_to_window t ht
    L).sliceRegular
    ⟨le_rfl, by
      rw [chronologicalSaddleRecoveryAfterTime, chronologicalAfterTime]
      simpa [add_comm] using add_le_add_left
        (D.chronologicalSaddleRecoveryScale_sq_lt_window_sq t ht L).le
        (tcoord (D.position.eventCenter t ht))⟩


-- @@ L677-690 verbatim
theorem chronologicalSaddleRecoveryBeforeTime_regular
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) :
    sliceRegular D.signedOutput.cobordism.G
      (D.chronologicalSaddleRecoveryBeforeTime t ht L) :=
  (D.regularSlab_window_to_chronologicalSaddleRecoveryBefore t ht
    L).sliceRegular
    ⟨by
      rw [chronologicalBeforeTime, chronologicalSaddleRecoveryBeforeTime]
      exact sub_le_sub_left
        (D.chronologicalSaddleRecoveryScale_sq_lt_window_sq t ht L).le _,
      le_rfl⟩


-- @@ L692-699 verbatim
def chronologicalSaddleRecoveryAfterSlice
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) : FramedLevelSet n :=
  SlabTamedField.sliceFLSAt D.signedOutput.cobordism.toLevelCobordismData
    (D.chronologicalSaddleRecoveryAfterTime t ht L)
    (D.chronologicalSaddleRecoveryAfterTime_regular t ht L)


-- @@ L701-708 verbatim
def chronologicalSaddleRecoveryBeforeSlice
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) : FramedLevelSet n :=
  SlabTamedField.sliceFLSAt D.signedOutput.cobordism.toLevelCobordismData
    (D.chronologicalSaddleRecoveryBeforeTime t ht L)
    (D.chronologicalSaddleRecoveryBeforeTime_regular t ht L)


-- @@ L710-716 verbatim
noncomputable def chronologicalSaddleRecoveryAfterField
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) :
    TamedField (D.chronologicalSaddleRecoveryAfterSlice t ht L) :=
  (D.chronologicalSaddleRecoveryAfterSlice t ht L).exists_tamedField.some


-- @@ L718-724 verbatim
noncomputable def chronologicalSaddleRecoveryBeforeField
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) :
    TamedField (D.chronologicalSaddleRecoveryBeforeSlice t ht L) :=
  (D.chronologicalSaddleRecoveryBeforeSlice t ht L).exists_tamedField.some


-- @@ L726-742 verbatim
noncomputable def chronologicalSaddleRecoveryPositiveOrbit
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht))
    (branch : SaddleBranch) :
    (D.chronologicalSaddleRecoveryAfterField t ht L).OrbitIndex :=
  (D.chronologicalEventEmbeddedShrink t ht).saddlePositiveBranchOrbitIndex
    hindex branch
    (D.chronologicalSaddleBoundaryRadius t ht)
    (D.chronologicalSaddleRecoveryScale t ht L).scale
    (D.chronologicalSaddleBoundaryRadius_pos t ht)
    (D.chronologicalSaddleRecoveryScale_sq_lt_saddleBoundary_sq t ht L)
    (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht)
    (D.chronologicalSaddleRecoveryAfterTime_regular t ht L)
    (D.chronologicalSaddleRecoveryAfterField t ht L)


-- @@ L744-760 verbatim
noncomputable def chronologicalSaddleRecoveryNegativeOrbit
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht))
    (branch : SaddleBranch) :
    (D.chronologicalSaddleRecoveryBeforeField t ht L).OrbitIndex :=
  (D.chronologicalEventEmbeddedShrink t ht).saddleNegativeBranchOrbitIndex
    hindex branch
    (D.chronologicalSaddleBoundaryRadius t ht)
    (D.chronologicalSaddleRecoveryScale t ht L).scale
    (D.chronologicalSaddleBoundaryRadius_pos t ht)
    (D.chronologicalSaddleRecoveryScale_sq_lt_saddleBoundary_sq t ht L)
    (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht)
    (D.chronologicalSaddleRecoveryBeforeTime_regular t ht L)
    (D.chronologicalSaddleRecoveryBeforeField t ht L)


-- @@ L762-762 verbatim
/-! ## Transport of the recovery orbits to the fixed window slices -/


-- @@ L764-773 verbatim
noncomputable def chronologicalSaddleRecoveryAfterToWindowSlabField
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) :
    SlabTamedField D.signedOutput.cobordism.toLevelCobordismData
      (D.chronologicalSaddleRecoveryAfterTime t ht L)
      (D.chronologicalAfterTime t ht) :=
  (exists_slabTamedField D.signedOutput.cobordism.toLevelCobordismData
    (D.regularSlab_chronologicalSaddleRecoveryAfter_to_window t ht L)).some


-- @@ L775-784 verbatim
noncomputable def chronologicalSaddleWindowToRecoveryBeforeSlabField
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) :
    SlabTamedField D.signedOutput.cobordism.toLevelCobordismData
      (D.chronologicalBeforeTime t ht)
      (D.chronologicalSaddleRecoveryBeforeTime t ht L) :=
  (exists_slabTamedField D.signedOutput.cobordism.toLevelCobordismData
    (D.regularSlab_window_to_chronologicalSaddleRecoveryBefore t ht L)).some


-- @@ L786-808 verbatim
noncomputable def chronologicalSaddleRecoveryAfterToWindowOrbitEquiv
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) :
    (D.chronologicalSaddleRecoveryAfterField t ht L).OrbitIndex ≃
      (D.chronologicalAfterField t ht).OrbitIndex := by
  let hreg := D.regularSlab_chronologicalSaddleRecoveryAfter_to_window t ht L
  let W := D.chronologicalSaddleRecoveryAfterToWindowSlabField t ht L
  have hs : D.chronologicalSaddleRecoveryAfterTime t ht L ∈
      Icc (D.chronologicalSaddleRecoveryAfterTime t ht L)
        (D.chronologicalAfterTime t ht) :=
    ⟨le_rfl, by
      rw [chronologicalSaddleRecoveryAfterTime, chronologicalAfterTime]
      simpa [add_comm] using add_le_add_left
        (D.chronologicalSaddleRecoveryScale_sq_lt_window_sq t ht L).le
        (tcoord (D.position.eventCenter t ht))⟩
  have ha : D.chronologicalAfterTime t ht ∈
      Icc (D.chronologicalSaddleRecoveryAfterTime t ht L)
        (D.chronologicalAfterTime t ht) := ⟨hs.2, le_rfl⟩
  exact W.sliceOrbitEquiv hreg hs ha
    (D.chronologicalSaddleRecoveryAfterField t ht L)
    (D.chronologicalAfterField t ht)


-- @@ L810-831 verbatim
noncomputable def chronologicalSaddleRecoveryBeforeToWindowOrbitEquiv
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) :
    (D.chronologicalSaddleRecoveryBeforeField t ht L).OrbitIndex ≃
      (D.chronologicalBeforeField t ht).OrbitIndex := by
  let hreg := D.regularSlab_window_to_chronologicalSaddleRecoveryBefore t ht L
  let W := D.chronologicalSaddleWindowToRecoveryBeforeSlabField t ht L
  have ha : D.chronologicalBeforeTime t ht ∈
      Icc (D.chronologicalBeforeTime t ht)
        (D.chronologicalSaddleRecoveryBeforeTime t ht L) :=
    ⟨le_rfl, by
      rw [chronologicalBeforeTime, chronologicalSaddleRecoveryBeforeTime]
      exact sub_le_sub_left
        (D.chronologicalSaddleRecoveryScale_sq_lt_window_sq t ht L).le _⟩
  have hs : D.chronologicalSaddleRecoveryBeforeTime t ht L ∈
      Icc (D.chronologicalBeforeTime t ht)
        (D.chronologicalSaddleRecoveryBeforeTime t ht L) := ⟨ha.2, le_rfl⟩
  exact W.sliceOrbitEquiv hreg hs ha
    (D.chronologicalSaddleRecoveryBeforeField t ht L)
    (D.chronologicalBeforeField t ht)


-- @@ L833-998 verbatim
/-- The transported recovery positive branch orbit is the chronological
positive branch orbit. -/
theorem chronologicalSaddleRecoveryAfterToWindowOrbitEquiv_branch
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht))
    (branch : SaddleBranch) :
    D.chronologicalSaddleRecoveryAfterToWindowOrbitEquiv t ht L
        (D.chronologicalSaddleRecoveryPositiveOrbit t ht hindex L branch) =
      D.chronologicalSaddlePositiveOrbit t ht hindex branch := by
  let M := D.position.eventModel t ht
  let T := D.chronologicalEventEmbeddedShrink t ht
  let H := D.chronologicalEventFullRadiusSmooth t ht
  let Q := D.chronologicalSaddleRecoveryScale t ht L
  let b := Q.scale
  let afix := D.chronologicalWindowRadius t ht
  let r := D.chronologicalSaddleBoundaryRadius t ht
  let sourceTime := D.chronologicalSaddleRecoveryAfterTime t ht L
  let targetTime := D.chronologicalAfterTime t ht
  let hreg := D.regularSlab_chronologicalSaddleRecoveryAfter_to_window t ht L
  let W := D.chronologicalSaddleRecoveryAfterToWindowSlabField t ht L
  let Vshort := D.chronologicalSaddleRecoveryAfterField t ht L
  let Vtarget := D.chronologicalAfterField t ht
  let Oshort := D.chronologicalSaddleRecoveryPositiveOrbit
    t ht hindex L branch
  let c : C(I, ℝ) := {
    toFun := fun q => b + (q : ℝ) * (afix - b)
    continuous_toFun :=
      continuous_const.add (continuous_subtype_val.mul continuous_const) }
  have hbc (q : I) : b ≤ c q := by
    dsimp [c]
    have hq₀ : 0 ≤ (q : ℝ) := q.property.1
    have hab : 0 < afix - b := sub_pos.mpr Q.scale_lt_window
    nlinarith
  have hca (q : I) : c q ≤ afix := by
    dsimp [c]
    have hq₁ : (q : ℝ) ≤ 1 := q.property.2
    have hab : 0 < afix - b := sub_pos.mpr Q.scale_lt_window
    nlinarith
  have hcpos (q : I) : 0 < c q := Q.scale_pos.trans_le (hbc q)
  have hcr (q : I) : c q < r :=
    (hca q).trans_lt (D.chronologicalWindowRadius_lt_saddleBoundaryRadius t ht)
  have hcsq (q : I) : (c q) ^ 2 < r ^ 2 :=
    (sq_lt_sq₀ (hcpos q).le
      (D.chronologicalSaddleBoundaryRadius_pos t ht).le).2 (hcr q)
  let u : I → E₂ := fun q =>
    saddlePositiveBoundaryEndParam branch .negative r (c q)
  have hucont : Continuous u := by
    dsimp [u, c]
    cases branch <;>
      simp [saddlePositiveBoundaryEndParam, saddlePositiveArc,
        saddleBoundaryParameter, pairToMorseParam, signedBranch] <;>
      fun_prop
  have huRadius (q : I) : ‖u q‖ < M.radius := by
    rw [show ‖u q‖ = r from
      norm_saddlePositiveBoundaryEndParam branch .negative
        (D.chronologicalSaddleBoundaryRadius_pos t ht) (hcsq q)]
    exact (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht).trans_le
      T.radius_le
  let z : C(I, E') := {
    toFun := fun q => M.param (u q)
    continuous_toFun := by
      rw [continuous_iff_continuousAt]
      intro q
      exact (H.differentiableAt (u q) (huRadius q)).continuousAt.comp'
        hucont.continuousAt }
  let tau : C(I, ℝ) := {
    toFun := fun q => afix ^ 2 - (c q) ^ 2
    continuous_toFun := continuous_const.sub (c.continuous.pow 2) }
  let gamma : C(I, E₁) := {
    toFun := fun q => spacePart (W.flow (z q) (tau q))
    continuous_toFun := continuous_spacePart.comp
      (W.continuous_flow_uncurry.comp
        (z.continuous.prodMk tau.continuous)) }
  have hsourceMem (q : I) :
      tcoord (D.position.eventCenter t ht) + (c q) ^ 2 ∈
        Icc sourceTime targetTime := by
    have hbSq : b ^ 2 ≤ (c q) ^ 2 :=
      (sq_le_sq₀ Q.scale_pos.le (hcpos q).le).2 (hbc q)
    have hcSq : (c q) ^ 2 ≤ afix ^ 2 :=
      (sq_le_sq₀ (hcpos q).le
        (D.chronologicalWindowRadius_pos t ht).le).2 (hca q)
    constructor
    · simpa [sourceTime, chronologicalSaddleRecoveryAfterTime, b, Q] using
        add_le_add_left hbSq (tcoord (D.position.eventCenter t ht))
    · simpa [targetTime, chronologicalAfterTime, afix] using
        add_le_add_left hcSq (tcoord (D.position.eventCenter t ht))
  have htargetMem : targetTime ∈ Icc sourceTime targetTime := by
    refine ⟨?_, le_rfl⟩
    simpa [sourceTime, targetTime, chronologicalSaddleRecoveryAfterTime,
      chronologicalAfterTime, b, afix, Q, add_comm] using add_le_add_left
        (D.chronologicalSaddleRecoveryScale_sq_lt_window_sq t ht L).le
        (tcoord (D.position.eventCenter t ht))
  have hzFiber (q : I) : D.signedOutput.cobordism.G (z q) = 0 := by
    exact M.param_fiber (u q) (huRadius q)
  have hzTime (q : I) : tcoord (z q) =
      tcoord (D.position.eventCenter t ht) + (c q) ^ 2 := by
    have htime := M.time_model (u q) (huRadius q)
    rw [hindex] at htime
    simpa [z, u, saddlePositiveBoundaryEndParam] using htime
  have hgammaFiber : ∀ q,
      gamma q ∈ (D.chronologicalAfterSlice t ht).fiber := by
    intro q
    have hx : spacePart (z q) ∈ SlabTamedField.sliceFiber
        D.signedOutput.cobordism.toLevelCobordismData
        (tcoord (D.position.eventCenter t ht) + (c q) ^ 2) := by
      change D.signedOutput.cobordism.G
        (cobSpaceTime (spacePart (z q))
          (tcoord (D.position.eventCenter t ht) + (c q) ^ 2)) = 0
      rw [← hzTime q, spaceTime_spacePart]
      exact hzFiber q
    have hmap := W.sliceTransport_mapsTo hreg (hsourceMem q) htargetMem hx
    have hzst : cobSpaceTime (spacePart (z q))
        (tcoord (D.position.eventCenter t ht) + (c q) ^ 2) = z q := by
      rw [← hzTime q, spaceTime_spacePart]
    rw [SlabTamedField.sliceTransport, hzst] at hmap
    change D.signedOutput.cobordism.toLevelCobordismData.G
      (cobSpaceTime (gamma q) targetTime) = 0
    simpa [SlabTamedField.sliceFiber, gamma, tau, targetTime,
      chronologicalAfterTime, afix] using hmap
  have hgamma₀ : gamma 0 =
      W.sliceTransport sourceTime targetTime
        (spacePart (T.saddlePositiveBranchBase branch r b)) := by
    have hz₀Time : tcoord (z 0) = sourceTime := by
      simpa [sourceTime, chronologicalSaddleRecoveryAfterTime, c, b, Q] using
        hzTime 0
    have hz₀st : cobSpaceTime (spacePart (z 0)) sourceTime = z 0 := by
      rw [← hz₀Time, spaceTime_spacePart]
    have hz₀Base : z 0 = T.saddlePositiveBranchBase branch r b := by
      simp [z, u, c,
        StandardMorseEventAt.EmbeddedShrink.saddlePositiveBranchBase,
        StandardMorseEventAt.saddlePositiveBoundaryEnd,
        StandardMorseEventAt.localPoint, M, T, b, r, Q]
    rw [SlabTamedField.sliceTransport, ← hz₀Base, hz₀st]
    simp [gamma, tau, z, u, c, sourceTime, targetTime,
      chronologicalSaddleRecoveryAfterTime, chronologicalAfterTime,
      StandardMorseEventAt.EmbeddedShrink.saddlePositiveBranchBase,
      StandardMorseEventAt.saddlePositiveBoundaryEnd,
      StandardMorseEventAt.localPoint, M, T, afix, b, r, Q]
  have hgamma₁ : gamma 1 =
      spacePart (T.saddlePositiveBranchBase branch r afix) := by
    simp [gamma, tau, z, u, c,
      StandardMorseEventAt.EmbeddedShrink.saddlePositiveBranchBase,
      StandardMorseEventAt.saddlePositiveBoundaryEnd,
      StandardMorseEventAt.localPoint, M, T, afix, b, r, Q]
  have hpath := Vtarget.continuousMap_mem_orbit gamma hgammaFiber 1
  rw [hgamma₀, hgamma₁] at hpath
  have hbaseOrbit : spacePart (T.saddlePositiveBranchBase branch r b) ∈
      Vshort.orbit (Vshort.orbitPoint Oshort) := by
    rw [← Vshort.orbitPoint_orbit Oshort]
    exact Vshort.mem_orbit_self _
  have hshortMem : sourceTime ∈ Icc sourceTime targetTime :=
    ⟨le_rfl, htargetMem.1⟩
  have hmapOrbit := W.sliceTransport_mapsTo_orbit hreg
    hshortMem htargetMem Vshort Vtarget
      (Vshort.orbitPoint_mem_fiber Oshort) hbaseOrbit
  have hsame := Vtarget.orbit_eq_of_mem hmapOrbit
  rw [hsame] at hpath
  apply Subtype.ext
  change Vtarget.orbit
      (W.sliceTransport sourceTime targetTime (Vshort.orbitPoint Oshort)) =
    Vtarget.orbit
      (spacePart (T.saddlePositiveBranchBase branch r afix))
  exact (Vtarget.orbit_eq_of_mem hpath).symm


-- @@ L1000-1165 verbatim
/-- The transported recovery negative branch orbit is the chronological
negative branch orbit. -/
theorem chronologicalSaddleRecoveryBeforeToWindowOrbitEquiv_branch
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht))
    (branch : SaddleBranch) :
    D.chronologicalSaddleRecoveryBeforeToWindowOrbitEquiv t ht L
        (D.chronologicalSaddleRecoveryNegativeOrbit t ht hindex L branch) =
      D.chronologicalSaddleNegativeOrbit t ht hindex branch := by
  let M := D.position.eventModel t ht
  let T := D.chronologicalEventEmbeddedShrink t ht
  let H := D.chronologicalEventFullRadiusSmooth t ht
  let Q := D.chronologicalSaddleRecoveryScale t ht L
  let b := Q.scale
  let afix := D.chronologicalWindowRadius t ht
  let r := D.chronologicalSaddleBoundaryRadius t ht
  let sourceTime := D.chronologicalSaddleRecoveryBeforeTime t ht L
  let targetTime := D.chronologicalBeforeTime t ht
  let hreg := D.regularSlab_window_to_chronologicalSaddleRecoveryBefore t ht L
  let W := D.chronologicalSaddleWindowToRecoveryBeforeSlabField t ht L
  let Vshort := D.chronologicalSaddleRecoveryBeforeField t ht L
  let Vtarget := D.chronologicalBeforeField t ht
  let Oshort := D.chronologicalSaddleRecoveryNegativeOrbit
    t ht hindex L branch
  let c : C(I, ℝ) := {
    toFun := fun q => b + (q : ℝ) * (afix - b)
    continuous_toFun :=
      continuous_const.add (continuous_subtype_val.mul continuous_const) }
  have hbc (q : I) : b ≤ c q := by
    dsimp [c]
    have hq₀ : 0 ≤ (q : ℝ) := q.property.1
    have hab : 0 < afix - b := sub_pos.mpr Q.scale_lt_window
    nlinarith
  have hca (q : I) : c q ≤ afix := by
    dsimp [c]
    have hq₁ : (q : ℝ) ≤ 1 := q.property.2
    have hab : 0 < afix - b := sub_pos.mpr Q.scale_lt_window
    nlinarith
  have hcpos (q : I) : 0 < c q := Q.scale_pos.trans_le (hbc q)
  have hcr (q : I) : c q < r :=
    (hca q).trans_lt (D.chronologicalWindowRadius_lt_saddleBoundaryRadius t ht)
  have hcsq (q : I) : (c q) ^ 2 < r ^ 2 :=
    (sq_lt_sq₀ (hcpos q).le
      (D.chronologicalSaddleBoundaryRadius_pos t ht).le).2 (hcr q)
  let u : I → E₂ := fun q =>
    saddleNegativeBoundaryEndParam branch .negative r (c q)
  have hucont : Continuous u := by
    dsimp [u, c]
    cases branch <;>
      simp [saddleNegativeBoundaryEndParam, saddleNegativeArc,
        saddleBoundaryParameter, pairToMorseParam, signedBranch] <;>
      fun_prop
  have huRadius (q : I) : ‖u q‖ < M.radius := by
    rw [show ‖u q‖ = r from
      norm_saddleNegativeBoundaryEndParam branch .negative
        (D.chronologicalSaddleBoundaryRadius_pos t ht) (hcsq q)]
    exact (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht).trans_le
      T.radius_le
  let z : C(I, E') := {
    toFun := fun q => M.param (u q)
    continuous_toFun := by
      rw [continuous_iff_continuousAt]
      intro q
      exact (H.differentiableAt (u q) (huRadius q)).continuousAt.comp'
        hucont.continuousAt }
  let tau : C(I, ℝ) := {
    toFun := fun q => (c q) ^ 2 - afix ^ 2
    continuous_toFun := (c.continuous.pow 2).sub continuous_const }
  let gamma : C(I, E₁) := {
    toFun := fun q => spacePart (W.flow (z q) (tau q))
    continuous_toFun := continuous_spacePart.comp
      (W.continuous_flow_uncurry.comp
        (z.continuous.prodMk tau.continuous)) }
  have hsourceMem (q : I) :
      tcoord (D.position.eventCenter t ht) - (c q) ^ 2 ∈
        Icc targetTime sourceTime := by
    have hbSq : b ^ 2 ≤ (c q) ^ 2 :=
      (sq_le_sq₀ Q.scale_pos.le (hcpos q).le).2 (hbc q)
    have hcSq : (c q) ^ 2 ≤ afix ^ 2 :=
      (sq_le_sq₀ (hcpos q).le
        (D.chronologicalWindowRadius_pos t ht).le).2 (hca q)
    constructor
    · simpa [targetTime, chronologicalBeforeTime, afix] using
        sub_le_sub_left hcSq (tcoord (D.position.eventCenter t ht))
    · simpa [sourceTime, chronologicalSaddleRecoveryBeforeTime, b, Q] using
        sub_le_sub_left hbSq (tcoord (D.position.eventCenter t ht))
  have htargetMem : targetTime ∈ Icc targetTime sourceTime := by
    refine ⟨le_rfl, ?_⟩
    simpa [sourceTime, targetTime, chronologicalSaddleRecoveryBeforeTime,
      chronologicalBeforeTime, b, afix, Q] using sub_le_sub_left
        (D.chronologicalSaddleRecoveryScale_sq_lt_window_sq t ht L).le
        (tcoord (D.position.eventCenter t ht))
  have hzFiber (q : I) : D.signedOutput.cobordism.G (z q) = 0 := by
    exact M.param_fiber (u q) (huRadius q)
  have hzTime (q : I) : tcoord (z q) =
      tcoord (D.position.eventCenter t ht) - (c q) ^ 2 := by
    have htime := M.time_model (u q) (huRadius q)
    rw [hindex] at htime
    simpa [z, u, saddleNegativeBoundaryEndParam, sub_eq_add_neg] using htime
  have hgammaFiber : ∀ q,
      gamma q ∈ (D.chronologicalBeforeSlice t ht).fiber := by
    intro q
    have hx : spacePart (z q) ∈ SlabTamedField.sliceFiber
        D.signedOutput.cobordism.toLevelCobordismData
        (tcoord (D.position.eventCenter t ht) - (c q) ^ 2) := by
      change D.signedOutput.cobordism.G
        (cobSpaceTime (spacePart (z q))
          (tcoord (D.position.eventCenter t ht) - (c q) ^ 2)) = 0
      rw [← hzTime q, spaceTime_spacePart]
      exact hzFiber q
    have hmap := W.sliceTransport_mapsTo hreg (hsourceMem q) htargetMem hx
    have hzst : cobSpaceTime (spacePart (z q))
        (tcoord (D.position.eventCenter t ht) - (c q) ^ 2) = z q := by
      rw [← hzTime q, spaceTime_spacePart]
    rw [SlabTamedField.sliceTransport, hzst] at hmap
    change D.signedOutput.cobordism.toLevelCobordismData.G
      (cobSpaceTime (gamma q) targetTime) = 0
    simpa [SlabTamedField.sliceFiber, gamma, tau, targetTime,
      chronologicalBeforeTime, afix] using hmap
  have hgamma₀ : gamma 0 =
      W.sliceTransport sourceTime targetTime
        (spacePart (T.saddleNegativeBranchBase branch r b)) := by
    have hz₀Time : tcoord (z 0) = sourceTime := by
      simpa [sourceTime, chronologicalSaddleRecoveryBeforeTime, c, b, Q] using
        hzTime 0
    have hz₀st : cobSpaceTime (spacePart (z 0)) sourceTime = z 0 := by
      rw [← hz₀Time, spaceTime_spacePart]
    have hz₀Base : z 0 = T.saddleNegativeBranchBase branch r b := by
      simp [z, u, c,
        StandardMorseEventAt.EmbeddedShrink.saddleNegativeBranchBase,
        StandardMorseEventAt.saddleNegativeBoundaryEnd,
        StandardMorseEventAt.localPoint, M, T, b, r, Q]
    rw [SlabTamedField.sliceTransport, ← hz₀Base, hz₀st]
    simp [gamma, tau, z, u, c, sourceTime, targetTime,
      chronologicalSaddleRecoveryBeforeTime, chronologicalBeforeTime,
      StandardMorseEventAt.EmbeddedShrink.saddleNegativeBranchBase,
      StandardMorseEventAt.saddleNegativeBoundaryEnd,
      StandardMorseEventAt.localPoint, M, T, afix, b, r, Q]
  have hgamma₁ : gamma 1 =
      spacePart (T.saddleNegativeBranchBase branch r afix) := by
    simp [gamma, tau, z, u, c,
      StandardMorseEventAt.EmbeddedShrink.saddleNegativeBranchBase,
      StandardMorseEventAt.saddleNegativeBoundaryEnd,
      StandardMorseEventAt.localPoint, M, T, afix, b, r, Q]
  have hpath := Vtarget.continuousMap_mem_orbit gamma hgammaFiber 1
  rw [hgamma₀, hgamma₁] at hpath
  have hbaseOrbit : spacePart (T.saddleNegativeBranchBase branch r b) ∈
      Vshort.orbit (Vshort.orbitPoint Oshort) := by
    rw [← Vshort.orbitPoint_orbit Oshort]
    exact Vshort.mem_orbit_self _
  have hshortMem : sourceTime ∈ Icc targetTime sourceTime :=
    ⟨htargetMem.2, le_rfl⟩
  have hmapOrbit := W.sliceTransport_mapsTo_orbit hreg
    hshortMem htargetMem Vshort Vtarget
      (Vshort.orbitPoint_mem_fiber Oshort) hbaseOrbit
  have hsame := Vtarget.orbit_eq_of_mem hmapOrbit
  rw [hsame] at hpath
  apply Subtype.ext
  change Vtarget.orbit
      (W.sliceTransport sourceTime targetTime (Vshort.orbitPoint Oshort)) =
    Vtarget.orbit
      (spacePart (T.saddleNegativeBranchBase branch r afix))
  exact (Vtarget.orbit_eq_of_mem hpath).symm


-- @@ L1167-1167 verbatim
/-! ## Critical endpoint capture for the exterior slab flow -/


-- @@ L1169-1252 verbatim
/-- A safe flow from a point close to a marked critical end lands in the
zero fiber at the critical level and is captured by the endpoint-local cover
with both quadrant signs of that end. -/
theorem exists_chronologicalSaddleRecoveryCapture
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht))
    {K : Set E'}
    (R : CompactTimeTamedField
      D.signedOutput.cobordism.toLevelCobordismData K)
    (p : SaddleBranch × SaddleBranch)
    {x₀ : E'} (hx₀K : x₀ ∈ K)
    (hx₀fiber : D.signedOutput.cobordism.G x₀ = 0)
    {cs d : ℝ} (habs : |d| = cs ^ 2) (hd : |d| ≤ R.safeTime)
    (htx : tcoord x₀ + d = tcoord (D.position.eventCenter t ht))
    (hclose : dist x₀
        ((D.position.eventModel t ht).saddleCriticalBoundaryEnd p
          (D.chronologicalSaddleBoundaryRadius t ht)) +
        (R.base.bound : ℝ) * cs ^ 2 <
      D.chronologicalSaddleRecoveryMargin t ht L p) :
    ∃ u : E₂, ‖u‖ < (D.chronologicalEventEmbeddedShrink t ht).radius ∧
      (D.position.eventModel t ht).param u = R.base.flow x₀ d ∧
      0 < signedBranch p.1 (u 0) ∧ 0 < signedBranch p.2 (u 1) ∧
      morseQuadratic .saddle (u 0, u 1) = 0 := by
  let M := D.position.eventModel t ht
  let w := R.base.flow x₀ d
  have hw_move : dist w x₀ ≤ (R.base.bound : ℝ) * cs ^ 2 := by
    calc
      dist w x₀ = dist (R.base.flow x₀ d) (R.base.flow x₀ 0) := by simp [w]
      _ ≤ (R.base.bound : ℝ) * |d - 0| := R.base.dist_flow_self_le x₀ d 0
      _ = (R.base.bound : ℝ) * cs ^ 2 := by rw [sub_zero, habs]
  have hw_crit : dist w (M.saddleCriticalBoundaryEnd p
      (D.chronologicalSaddleBoundaryRadius t ht)) <
      D.chronologicalSaddleRecoveryMargin t ht L p := by
    calc
      dist w (M.saddleCriticalBoundaryEnd p
          (D.chronologicalSaddleBoundaryRadius t ht)) ≤
          dist w x₀ + dist x₀ (M.saddleCriticalBoundaryEnd p
            (D.chronologicalSaddleBoundaryRadius t ht)) :=
        dist_triangle _ _ _
      _ < D.chronologicalSaddleRecoveryMargin t ht L p := by
        have := hw_move
        linarith
  have hwfiber : D.signedOutput.cobordism.G w = 0 :=
    R.flow_mem_fiber hx₀fiber d
  obtain ⟨u, hu, hup⟩ := L.cover p w
    (hw_crit.trans_le (D.chronologicalSaddleRecoveryMargin_le_cover t ht L p))
    hwfiber
  have hcritParam : M.param (saddleCriticalBoundaryEndParam p
      (D.chronologicalSaddleBoundaryRadius t ht)) =
      M.saddleCriticalBoundaryEnd p
        (D.chronologicalSaddleBoundaryRadius t ht) := rfl
  have hdistu : dist (M.param u)
      (M.param (saddleCriticalBoundaryEndParam p
        (D.chronologicalSaddleBoundaryRadius t ht))) <
      D.chronologicalSaddlePositiveBranchRadius t ht p := by
    rw [hup, hcritParam]
    exact hw_crit.trans_le
      (D.chronologicalSaddleRecoveryMargin_le_positiveBranch t ht L p)
  have hdistu' : dist (M.param u)
      (M.param (saddleCriticalBoundaryEndParam p
        (D.chronologicalSaddleBoundaryRadius t ht))) <
      D.chronologicalSaddleNegativeBranchRadius t ht p := by
    rw [hup, hcritParam]
    exact hw_crit.trans_le
      (D.chronologicalSaddleRecoveryMargin_le_negativeBranch t ht L p)
  have hsign1 : 0 < signedBranch p.1 (u 0) :=
    D.chronologicalSaddlePositiveBranchRadius_spec t ht p u hu hdistu
  have hsign2 : 0 < signedBranch p.2 (u 1) :=
    D.chronologicalSaddleNegativeBranchRadius_spec t ht p u hu hdistu'
  have huM : ‖u‖ < M.radius :=
    hu.trans_le (D.chronologicalSaddleEndpointParamRadius_le_eventRadius t ht)
  have htw : tcoord w = tcoord (D.position.eventCenter t ht) := by
    rw [R.tcoord_flow hx₀K hd]
    exact htx
  have hq := M.time_model u huM
  rw [hindex] at hq
  rw [hup, htw] at hq
  have hquad : morseQuadratic .saddle (u 0, u 1) = 0 := by linarith
  exact ⟨u,
    hu.trans (D.chronologicalSaddleEndpointParamRadius_lt_embedded t ht),
    hup, hsign1, hsign2, hquad⟩


-- @@ L1254-1254 verbatim
/-! ## Pinning the transverse label with the pairing dichotomy -/


-- @@ L1256-1294 verbatim
private theorem chronologicalSaddleRecovery_pin_positive
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht))
    {x : SaddleBranch × SaddleBranch} (hx : x.1 = SaddleBranch.positive)
    (harc : Nonempty (SaddleCriticalExteriorArc
      (fun p => (D.position.eventModel t ht).saddleCriticalBoundaryEnd p
        (D.chronologicalSaddleBoundaryRadius t ht))
      (StandardMorseEventAt.puncturedCriticalSlice
        D.signedOutput.cobordism (D.position.eventCenter t ht))
      (SaddleBranch.negative, SaddleBranch.negative) x)) :
    Nonempty (SaddleCriticalExteriorArc
      (fun p => (D.position.eventModel t ht).saddleCriticalBoundaryEnd p
        (D.chronologicalSaddleBoundaryRadius t ht))
      (StandardMorseEventAt.puncturedCriticalSlice
        D.signedOutput.cobordism (D.position.eventCenter t ht))
      (SaddleBranch.negative, SaddleBranch.negative)
      (SaddleBranch.positive, SaddleBranch.negative)) := by
  have hne : x ≠ (SaddleBranch.negative, SaddleBranch.negative) := by
    intro h
    rw [h] at hx
    simp at hx
  have hmate : x = A.mate (SaddleBranch.negative, SaddleBranch.negative) :=
    A.eq_mate_of_ne_arc hne harc
  rcases StandardMorseEventAt.saddleExteriorArcPairing_eq_flipSecond_or_eq_flipFirst
      (D.position.eventModel t ht)
      (StandardMorseEventAt.puncturedCriticalSlice
        D.signedOutput.cobordism (D.position.eventCenter t ht))
      (D.chronologicalSaddleBoundaryRadius t ht)
      (D.chronologicalSaddleBoundaryRadius_pos t ht) A with hs | hf
  · exfalso
    rw [hs (SaddleBranch.negative, SaddleBranch.negative)] at hmate
    rw [hmate] at hx
    simp [saddleBranchEndFlipSecond, SaddleBranch.other] at hx
  · rw [hf (SaddleBranch.negative, SaddleBranch.negative)] at hmate
    have hxeq : x = (SaddleBranch.positive, SaddleBranch.negative) := by
      simpa [saddleBranchEndFlipFirst, SaddleBranch.other] using hmate
    rwa [hxeq] at harc


-- @@ L1296-1334 verbatim
private theorem chronologicalSaddleRecovery_pin_negative
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht))
    {x : SaddleBranch × SaddleBranch} (hx : x.2 = SaddleBranch.positive)
    (harc : Nonempty (SaddleCriticalExteriorArc
      (fun p => (D.position.eventModel t ht).saddleCriticalBoundaryEnd p
        (D.chronologicalSaddleBoundaryRadius t ht))
      (StandardMorseEventAt.puncturedCriticalSlice
        D.signedOutput.cobordism (D.position.eventCenter t ht))
      (SaddleBranch.negative, SaddleBranch.negative) x)) :
    Nonempty (SaddleCriticalExteriorArc
      (fun p => (D.position.eventModel t ht).saddleCriticalBoundaryEnd p
        (D.chronologicalSaddleBoundaryRadius t ht))
      (StandardMorseEventAt.puncturedCriticalSlice
        D.signedOutput.cobordism (D.position.eventCenter t ht))
      (SaddleBranch.negative, SaddleBranch.negative)
      (SaddleBranch.negative, SaddleBranch.positive)) := by
  have hne : x ≠ (SaddleBranch.negative, SaddleBranch.negative) := by
    intro h
    rw [h] at hx
    simp at hx
  have hmate : x = A.mate (SaddleBranch.negative, SaddleBranch.negative) :=
    A.eq_mate_of_ne_arc hne harc
  rcases StandardMorseEventAt.saddleExteriorArcPairing_eq_flipSecond_or_eq_flipFirst
      (D.position.eventModel t ht)
      (StandardMorseEventAt.puncturedCriticalSlice
        D.signedOutput.cobordism (D.position.eventCenter t ht))
      (D.chronologicalSaddleBoundaryRadius t ht)
      (D.chronologicalSaddleBoundaryRadius_pos t ht) A with hs | hf
  · rw [hs (SaddleBranch.negative, SaddleBranch.negative)] at hmate
    have hxeq : x = (SaddleBranch.negative, SaddleBranch.positive) := by
      simpa [saddleBranchEndFlipSecond, SaddleBranch.other] using hmate
    rwa [hxeq] at harc
  · exfalso
    rw [hf (SaddleBranch.negative, SaddleBranch.negative)] at hmate
    rw [hmate] at hx
    simp [saddleBranchEndFlipFirst, SaddleBranch.other] at hx


-- @@ L1336-1336 verbatim
/-! ## The positive-slice recovery arc -/


-- @@ L1338-1685 verbatim
theorem chronologicalSaddleRecovery_positiveArc
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht))
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht))
    (heq : D.chronologicalSaddlePositiveOrbit t ht hindex .negative =
      D.chronologicalSaddlePositiveOrbit t ht hindex .positive) :
    Nonempty (SaddleCriticalExteriorArc
      (fun p => (D.position.eventModel t ht).saddleCriticalBoundaryEnd p
        (D.chronologicalSaddleBoundaryRadius t ht))
      (StandardMorseEventAt.puncturedCriticalSlice
        D.signedOutput.cobordism (D.position.eventCenter t ht))
      (SaddleBranch.negative, SaddleBranch.negative)
      (SaddleBranch.positive, SaddleBranch.negative)) := by
  classical
  let M := D.position.eventModel t ht
  let T := D.chronologicalEventEmbeddedShrink t ht
  let H := D.chronologicalEventFullRadiusSmooth t ht
  let Q := D.chronologicalSaddleRecoveryScale t ht L
  let cs : ℝ := Q.scale
  let Laux := D.chronologicalSaddleRecoveryAuxiliaryData t ht L
  let R := Laux.exteriorSlabTimeField
  let r := D.chronologicalSaddleBoundaryRadius t ht
  have hrho : 0 < r := D.chronologicalSaddleBoundaryRadius_pos t ht
  have hsq : cs ^ 2 < r ^ 2 :=
    D.chronologicalSaddleRecoveryScale_sq_lt_saddleBoundary_sq t ht L
  have hltT : r < T.radius :=
    D.chronologicalSaddleBoundaryRadius_lt_embedded t ht
  have hrM : r < M.radius := hltT.trans_le T.radius_le
  let hreg := D.chronologicalSaddleRecoveryAfterTime_regular t ht L
  let V := D.chronologicalSaddleRecoveryAfterField t ht L
  -- transported branch-orbit equality
  have hshort : D.chronologicalSaddleRecoveryPositiveOrbit t ht hindex
        L .negative =
      D.chronologicalSaddleRecoveryPositiveOrbit t ht hindex L .positive := by
    apply (D.chronologicalSaddleRecoveryAfterToWindowOrbitEquiv
      t ht L).injective
    rw [D.chronologicalSaddleRecoveryAfterToWindowOrbitEquiv_branch
        t ht hindex L .negative,
      D.chronologicalSaddleRecoveryAfterToWindowOrbitEquiv_branch
        t ht hindex L .positive]
    exact heq
  have horbit : T.saddlePositiveBranchOrbitIndex hindex .negative r cs
        (D.chronologicalSaddleBoundaryRadius_pos t ht)
        (D.chronologicalSaddleRecoveryScale_sq_lt_saddleBoundary_sq t ht L)
        (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht) hreg V =
      T.saddlePositiveBranchOrbitIndex hindex .positive r cs
        (D.chronologicalSaddleBoundaryRadius_pos t ht)
        (D.chronologicalSaddleRecoveryScale_sq_lt_saddleBoundary_sq t ht L)
        (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht) hreg V :=
    hshort
  -- four-mark uniform exterior cuts on the common orbit
  obtain ⟨i, j, hij, hi, hj, havoid⟩ :=
    T.saddlePositiveCommonOrbit_exists_uniformExteriorCuts hindex r cs
      (D.chronologicalSaddleBoundaryRadius_pos t ht) Q.scale_pos
      (D.chronologicalSaddleRecoveryScale_sq_lt_saddleBoundary_sq t ht L)
      (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht) hreg V horbit
  let A4 := T.saddlePositiveCommonOrbitCyclicMarking hindex r cs
    (D.chronologicalSaddleBoundaryRadius_pos t ht)
    (D.chronologicalSaddleRecoveryScale_sq_lt_saddleBoundary_sq t ht L)
    (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht) hreg V horbit
  let l0 : Fin 4 :=
    finFourOfSaddleBranchPair (SaddleBranch.negative, SaddleBranch.negative)
  let l1 : Fin 4 :=
    finFourOfSaddleBranchPair (SaddleBranch.negative, SaddleBranch.positive)
  -- the two γ₋ endpoints as marks
  have hpt0 : A4.point l0 ∈ Set.range
      (T.saddlePositiveSpatialSegment .negative r cs
        (D.chronologicalSaddleBoundaryRadius_pos t ht)
        (D.chronologicalSaddleRecoveryScale_sq_lt_saddleBoundary_sq t ht L)
        (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht)) := by
    refine ⟨0, ?_⟩
    simp [A4, l0,
      StandardMorseEventAt.EmbeddedShrink.saddlePositiveSpatialSegment,
      StandardMorseEventAt.EmbeddedShrink.saddlePositiveCommonOrbitCyclicMarking,
      finFourOfSaddleBranchPair, saddleBranchPairOfFinFour]
  have hpt1 : A4.point l1 ∈ Set.range
      (T.saddlePositiveSpatialSegment .negative r cs
        (D.chronologicalSaddleBoundaryRadius_pos t ht)
        (D.chronologicalSaddleRecoveryScale_sq_lt_saddleBoundary_sq t ht L)
        (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht)) := by
    refine ⟨1, ?_⟩
    simp [A4, l1,
      StandardMorseEventAt.EmbeddedShrink.saddlePositiveSpatialSegment,
      StandardMorseEventAt.EmbeddedShrink.saddlePositiveCommonOrbitCyclicMarking,
      finFourOfSaddleBranchPair, saddleBranchPairOfFinFour]
  have hdisj := T.saddlePositiveSpatialSegments_disjoint hindex r cs
    (D.chronologicalSaddleBoundaryRadius_pos t ht) Q.scale_pos
    (D.chronologicalSaddleRecoveryScale_sq_lt_saddleBoundary_sq t ht L)
    (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht)
  have hnotj : A4.point l0 ∉ A4.cyclicCutRange j := by
    intro hmem
    rw [← hj] at hmem
    exact Set.disjoint_left.mp hdisj hpt0 hmem
  obtain ⟨rc, hri, hrj, hrl⟩ :=
    A4.exists_incidentCutIndexFour_ne_two l0 i j hnotj
  -- the local cut i is incident to both marks of the negative branch
  have hl0i : l0 = A4.cyclicCutSourceLabel i ∨
      l0 = A4.cyclicCutTargetLabel i :=
    A4.point_mem_cyclicCutRange_eq_label i l0 (hi ▸ hpt0)
  have hl1i : l1 = A4.cyclicCutSourceLabel i ∨
      l1 = A4.cyclicCutTargetLabel i :=
    A4.point_mem_cyclicCutRange_eq_label i l1 (hi ▸ hpt1)
  have hi0 : A4.cyclicCutSourceLabel i = l0 ∨
      A4.cyclicCutTargetLabel i = l0 := by
    rcases hl0i with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  have hi1 : A4.cyclicCutSourceLabel i = l1 ∨
      A4.cyclicCutTargetLabel i = l1 := by
    rcases hl1i with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  have hne01 : l0 ≠ l1 := by
    intro h
    have := congrArg saddleBranchPairOfFinFour h
    simp [l0, l1] at this
  have hstr := A4.cyclicCutSourceLabel_ne_targetLabel_four rc
  -- ambient identification of the four marks on the recovery slice
  have hmarkAmb : ∀ l : Fin 4,
      cobSpaceTime (A4.point l)
          (D.chronologicalSaddleRecoveryAfterTime t ht L) =
        M.saddlePositiveBoundaryEnd (saddleBranchPairOfFinFour l).1
          (saddleBranchPairOfFinFour l).2 r cs := by
    intro l
    show cobSpaceTime (A4.point l)
        (tcoord (D.position.eventCenter t ht) + cs ^ 2) =
      M.saddlePositiveBoundaryEnd (saddleBranchPairOfFinFour l).1
        (saddleBranchPairOfFinFour l).2 r cs
    have hpt : A4.point l = spacePart (M.saddlePositiveBoundaryEnd
        (saddleBranchPairOfFinFour l).1 (saddleBranchPairOfFinFour l).2
        r cs) := rfl
    rw [hpt]
    have htX : tcoord (M.saddlePositiveBoundaryEnd
        (saddleBranchPairOfFinFour l).1 (saddleBranchPairOfFinFour l).2
        r cs) = tcoord (D.position.eventCenter t ht) + cs ^ 2 :=
      M.saddlePositiveBoundaryEnd_time hindex _ _ hrho hsq hrM
    calc
      cobSpaceTime (spacePart (M.saddlePositiveBoundaryEnd
          (saddleBranchPairOfFinFour l).1 (saddleBranchPairOfFinFour l).2
          r cs)) (tcoord (D.position.eventCenter t ht) + cs ^ 2) =
          cobSpaceTime (spacePart (M.saddlePositiveBoundaryEnd
            (saddleBranchPairOfFinFour l).1 (saddleBranchPairOfFinFour l).2
            r cs)) (tcoord (M.saddlePositiveBoundaryEnd
              (saddleBranchPairOfFinFour l).1
              (saddleBranchPairOfFinFour l).2 r cs)) := by rw [htX]
      _ = M.saddlePositiveBoundaryEnd (saddleBranchPairOfFinFour l).1
            (saddleBranchPairOfFinFour l).2 r cs := spaceTime_spacePart _
  -- the exterior cut lies in the fixed exterior slab core
  have hcutMem : ∀ w : I,
      A4.cyclicCutAmbientPath rc w ∈ Laux.exteriorSlabCore := by
    intro w
    have htw : tcoord (A4.cyclicCutAmbientPath rc w) =
        tcoord (D.position.eventCenter t ht) + cs ^ 2 := by
      show tcoord (cobSpaceTime (A4.cyclicCutPath rc w)
          (D.chronologicalSaddleRecoveryAfterTime t ht L)) =
        tcoord (D.position.eventCenter t ht) + cs ^ 2
      rw [tcoord_spaceTime]
      rfl
    have hfib : D.signedOutput.cobordism.toLevelCobordismData.G
        (A4.cyclicCutAmbientPath rc w) = 0 :=
      A4.cyclicCutAmbientPath_fiber rc w
    refine ⟨⟨hfib, ?_⟩, ?_⟩
    · show tcoord (A4.cyclicCutAmbientPath rc w) ∈
        Icc (D.position.eventBracket t ht).before
          (D.position.eventBracket t ht).after
      rw [htw]
      constructor
      · exact (D.position.eventBracket t ht).before_lt.le.trans
          (le_add_of_nonneg_right (sq_nonneg _))
      · have hc2 : cs ^ 2 ≤ D.chronologicalWindowRadius t ht ^ 2 :=
          (D.chronologicalSaddleRecoveryScale_sq_lt_window_sq t ht L).le
        have hle : tcoord (D.position.eventCenter t ht) + cs ^ 2 ≤
            D.chronologicalAfterTime t ht := by
          rw [chronologicalAfterTime]
          linarith
        exact hle.trans (D.chronologicalAfterTime_mem_bracket t ht).2.le
    · show Laux.centerCoverRadius ≤
        dist (A4.cyclicCutAmbientPath rc w) (D.position.eventCenter t ht)
      by_contra hlt
      rw [not_le] at hlt
      obtain ⟨u', hu', hup⟩ := Laux.centerCover _ hlt hfib
      have huM' : ‖u'‖ < M.radius := hu'.trans hrM
      have hquad' : morseQuadratic .saddle (u' 0, u' 1) = cs ^ 2 := by
        have htm := M.time_model u' huM'
        rw [hindex, hup, htw] at htm
        linarith
      apply havoid rc hri hrj u' hquad' hu'
      rw [hup]
      have hsp : spacePart (A4.cyclicCutAmbientPath rc w) =
          A4.cyclicCutPath rc w := by
        show spacePart (cobSpaceTime (A4.cyclicCutPath rc w)
            (D.chronologicalSaddleRecoveryAfterTime t ht L)) =
          A4.cyclicCutPath rc w
        rw [spacePart_spaceTime]
      rw [hsp, ← A4.range_cyclicCutPath rc]
      exact ⟨w, rfl⟩
  -- flow the cut back to the critical level
  let gammaZ := A4.cyclicCutRegularZeroPath rc
  have hgammaK : ∀ w : I, gammaZ.toPath w ∈ Laux.exteriorSlabCore :=
    hcutMem
  have hd : |(-(cs ^ 2))| ≤ R.safeTime := by
    rw [abs_neg, abs_of_nonneg (sq_nonneg cs)]
    exact Q.safe
  have habs : |(-(cs ^ 2))| = cs ^ 2 := by
    rw [abs_neg, abs_of_nonneg (sq_nonneg cs)]
  have htime : ∀ w : I,
      tcoord (gammaZ.toPath w) + (-(cs ^ 2)) =
        tcoord (D.position.eventCenter t ht) := by
    intro w
    have htw : tcoord (A4.cyclicCutAmbientPath rc w) =
        tcoord (D.position.eventCenter t ht) + cs ^ 2 := by
      show tcoord (cobSpaceTime (A4.cyclicCutPath rc w)
          (D.chronologicalSaddleRecoveryAfterTime t ht L)) =
        tcoord (D.position.eventCenter t ht) + cs ^ 2
      rw [tcoord_spaceTime]
      rfl
    have : tcoord (gammaZ.toPath w) =
        tcoord (D.position.eventCenter t ht) + cs ^ 2 := htw
    rw [this]
    ring
  -- source endpoint capture
  have hsrcK : M.saddlePositiveBoundaryEnd
      (saddleBranchPairOfFinFour (A4.cyclicCutSourceLabel rc)).1
      (saddleBranchPairOfFinFour (A4.cyclicCutSourceLabel rc)).2 r cs ∈
      Laux.exteriorSlabCore := by
    rw [← hmarkAmb (A4.cyclicCutSourceLabel rc)]
    have h0 := hcutMem 0
    rwa [(A4.cyclicCutAmbientPath rc).source] at h0
  have htgtK : M.saddlePositiveBoundaryEnd
      (saddleBranchPairOfFinFour (A4.cyclicCutTargetLabel rc)).1
      (saddleBranchPairOfFinFour (A4.cyclicCutTargetLabel rc)).2 r cs ∈
      Laux.exteriorSlabCore := by
    rw [← hmarkAmb (A4.cyclicCutTargetLabel rc)]
    have h1 := hcutMem 1
    rwa [(A4.cyclicCutAmbientPath rc).target] at h1
  obtain ⟨u, huT, huP, hu1, hu2, huq⟩ :=
    D.exists_chronologicalSaddleRecoveryCapture t ht hindex L R
      (saddleBranchPairOfFinFour (A4.cyclicCutSourceLabel rc)) hsrcK
      (M.saddlePositiveBoundaryEnd_fiber _ _ hrho hsq hrM)
      habs hd
      (by
        rw [M.saddlePositiveBoundaryEnd_time hindex _ _ hrho hsq hrM]
        ring)
      (Q.positive_close (saddleBranchPairOfFinFour
        (A4.cyclicCutSourceLabel rc)))
  obtain ⟨v, hvT, hvP, hv1, hv2, hvq⟩ :=
    D.exists_chronologicalSaddleRecoveryCapture t ht hindex L R
      (saddleBranchPairOfFinFour (A4.cyclicCutTargetLabel rc)) htgtK
      (M.saddlePositiveBoundaryEnd_fiber _ _ hrho hsq hrM)
      habs hd
      (by
        rw [M.saddlePositiveBoundaryEnd_time hindex _ _ hrho hsq hrM]
        ring)
      (Q.positive_close (saddleBranchPairOfFinFour
        (A4.cyclicCutTargetLabel rc)))
  -- assemble the punctured critical arc
  have harcN : Nonempty (SaddleCriticalExteriorArc
      (fun p => M.saddleCriticalBoundaryEnd p r)
      (StandardMorseEventAt.puncturedCriticalSlice
        D.signedOutput.cobordism (D.position.eventCenter t ht))
      (saddleBranchPairOfFinFour (A4.cyclicCutSourceLabel rc))
      (saddleBranchPairOfFinFour (A4.cyclicCutTargetLabel rc))) := by
    refine ⟨T.saddleCriticalExteriorArcOfSafeFlowWithLocalCaptures H hindex
      R gammaZ hgammaK (-(cs ^ 2)) hd htime r hrho hltT
      (saddleBranchPairOfFinFour (A4.cyclicCutSourceLabel rc))
      (saddleBranchPairOfFinFour (A4.cyclicCutTargetLabel rc))
      u v huT hvT ?_ ?_ hu1 hu2 hv1 hv2 ?_ ?_⟩
    · rw [huq]
      norm_num
    · rw [hvq]
      norm_num
    · exact (congrArg (fun z => R.base.flow z (-(cs ^ 2)))
        (hmarkAmb (A4.cyclicCutSourceLabel rc))).trans huP.symm
    · exact (congrArg (fun z => R.base.flow z (-(cs ^ 2)))
        (hmarkAmb (A4.cyclicCutTargetLabel rc))).trans hvP.symm
  -- pin down the surviving transverse label
  rcases hrl with hsrc | htgt
  · -- the source label is the (negative, negative) end
    have hpsEq : saddleBranchPairOfFinFour (A4.cyclicCutSourceLabel rc) =
        (SaddleBranch.negative, SaddleBranch.negative) := by
      rw [hsrc]
      simp [l0]
    rw [hpsEq] at harcN
    have hm0 : A4.cyclicCutTargetLabel rc ≠ l0 := by
      intro h
      exact hstr (hsrc.trans h.symm)
    have hm1 : A4.cyclicCutTargetLabel rc ≠ l1 := by
      intro h
      exact hri (A4.cutIndexFour_eq_of_endpointLabels hne01
        (Or.inl hsrc) (Or.inr h) hi0 hi1)
    have hxpos : (saddleBranchPairOfFinFour
        (A4.cyclicCutTargetLabel rc)).1 = SaddleBranch.positive := by
      have hm : A4.cyclicCutTargetLabel rc =
          finFourOfSaddleBranchPair (saddleBranchPairOfFinFour
            (A4.cyclicCutTargetLabel rc)) :=
        (finFourOfSaddleBranchPair_saddleBranchPairOfFinFour _).symm
      rcases hp : saddleBranchPairOfFinFour (A4.cyclicCutTargetLabel rc)
        with ⟨b, e⟩
      cases b with
      | negative =>
          exfalso
          rw [hp] at hm
          cases e with
          | negative => exact hm0 hm
          | positive => exact hm1 hm
      | positive => rfl
    exact D.chronologicalSaddleRecovery_pin_positive t ht A hxpos harcN
  · -- the target label is the (negative, negative) end; reverse the arc
    have hptEq : saddleBranchPairOfFinFour (A4.cyclicCutTargetLabel rc) =
        (SaddleBranch.negative, SaddleBranch.negative) := by
      rw [htgt]
      simp [l0]
    have harcN' : Nonempty (SaddleCriticalExteriorArc
        (fun p => M.saddleCriticalBoundaryEnd p r)
        (StandardMorseEventAt.puncturedCriticalSlice
          D.signedOutput.cobordism (D.position.eventCenter t ht))
        (saddleBranchPairOfFinFour (A4.cyclicCutTargetLabel rc))
        (saddleBranchPairOfFinFour (A4.cyclicCutSourceLabel rc))) :=
      harcN.map fun B => B.symm
    rw [hptEq] at harcN'
    have hm0 : A4.cyclicCutSourceLabel rc ≠ l0 := by
      intro h
      exact hstr (h.trans htgt.symm)
    have hm1 : A4.cyclicCutSourceLabel rc ≠ l1 := by
      intro h
      exact hri (A4.cutIndexFour_eq_of_endpointLabels hne01
        (Or.inr htgt) (Or.inl h) hi0 hi1)
    have hxpos : (saddleBranchPairOfFinFour
        (A4.cyclicCutSourceLabel rc)).1 = SaddleBranch.positive := by
      have hm : A4.cyclicCutSourceLabel rc =
          finFourOfSaddleBranchPair (saddleBranchPairOfFinFour
            (A4.cyclicCutSourceLabel rc)) :=
        (finFourOfSaddleBranchPair_saddleBranchPairOfFinFour _).symm
      rcases hp : saddleBranchPairOfFinFour (A4.cyclicCutSourceLabel rc)
        with ⟨b, e⟩
      cases b with
      | negative =>
          exfalso
          rw [hp] at hm
          cases e with
          | negative => exact hm0 hm
          | positive => exact hm1 hm
      | positive => rfl
    exact D.chronologicalSaddleRecovery_pin_positive t ht A hxpos harcN'


-- @@ L1687-1687 verbatim
/-! ## The negative-slice recovery arc -/


-- @@ L1689-2032 verbatim
theorem chronologicalSaddleRecovery_negativeArc
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht))
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht))
    (heq : D.chronologicalSaddleNegativeOrbit t ht hindex .negative =
      D.chronologicalSaddleNegativeOrbit t ht hindex .positive) :
    Nonempty (SaddleCriticalExteriorArc
      (fun p => (D.position.eventModel t ht).saddleCriticalBoundaryEnd p
        (D.chronologicalSaddleBoundaryRadius t ht))
      (StandardMorseEventAt.puncturedCriticalSlice
        D.signedOutput.cobordism (D.position.eventCenter t ht))
      (SaddleBranch.negative, SaddleBranch.negative)
      (SaddleBranch.negative, SaddleBranch.positive)) := by
  classical
  let M := D.position.eventModel t ht
  let T := D.chronologicalEventEmbeddedShrink t ht
  let H := D.chronologicalEventFullRadiusSmooth t ht
  let Q := D.chronologicalSaddleRecoveryScale t ht L
  let cs : ℝ := Q.scale
  let Laux := D.chronologicalSaddleRecoveryAuxiliaryData t ht L
  let R := Laux.exteriorSlabTimeField
  let r := D.chronologicalSaddleBoundaryRadius t ht
  have hrho : 0 < r := D.chronologicalSaddleBoundaryRadius_pos t ht
  have hsq : cs ^ 2 < r ^ 2 :=
    D.chronologicalSaddleRecoveryScale_sq_lt_saddleBoundary_sq t ht L
  have hltT : r < T.radius :=
    D.chronologicalSaddleBoundaryRadius_lt_embedded t ht
  have hrM : r < M.radius := hltT.trans_le T.radius_le
  let hreg := D.chronologicalSaddleRecoveryBeforeTime_regular t ht L
  let V := D.chronologicalSaddleRecoveryBeforeField t ht L
  -- transported branch-orbit equality
  have hshort : D.chronologicalSaddleRecoveryNegativeOrbit t ht hindex
        L .negative =
      D.chronologicalSaddleRecoveryNegativeOrbit t ht hindex L .positive := by
    apply (D.chronologicalSaddleRecoveryBeforeToWindowOrbitEquiv
      t ht L).injective
    rw [D.chronologicalSaddleRecoveryBeforeToWindowOrbitEquiv_branch
        t ht hindex L .negative,
      D.chronologicalSaddleRecoveryBeforeToWindowOrbitEquiv_branch
        t ht hindex L .positive]
    exact heq
  have horbit : T.saddleNegativeBranchOrbitIndex hindex .negative r cs
        (D.chronologicalSaddleBoundaryRadius_pos t ht)
        (D.chronologicalSaddleRecoveryScale_sq_lt_saddleBoundary_sq t ht L)
        (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht) hreg V =
      T.saddleNegativeBranchOrbitIndex hindex .positive r cs
        (D.chronologicalSaddleBoundaryRadius_pos t ht)
        (D.chronologicalSaddleRecoveryScale_sq_lt_saddleBoundary_sq t ht L)
        (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht) hreg V :=
    hshort
  -- four-mark uniform exterior cuts on the common orbit
  obtain ⟨i, j, hij, hi, hj, havoid⟩ :=
    T.saddleNegativeCommonOrbit_exists_uniformExteriorCuts hindex r cs
      (D.chronologicalSaddleBoundaryRadius_pos t ht) Q.scale_pos
      (D.chronologicalSaddleRecoveryScale_sq_lt_saddleBoundary_sq t ht L)
      (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht) hreg V horbit
  let A4 := T.saddleNegativeCommonOrbitCyclicMarking hindex r cs
    (D.chronologicalSaddleBoundaryRadius_pos t ht)
    (D.chronologicalSaddleRecoveryScale_sq_lt_saddleBoundary_sq t ht L)
    (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht) hreg V horbit
  let l0 : Fin 4 :=
    finFourOfSaddleBranchPair (SaddleBranch.negative, SaddleBranch.negative)
  let l1 : Fin 4 :=
    finFourOfSaddleBranchPair (SaddleBranch.positive, SaddleBranch.negative)
  -- the two endpoints of the b = negative local segment as marks
  have hpt0 : A4.point l0 ∈ Set.range
      (T.saddleNegativeSpatialSegment .negative r cs
        (D.chronologicalSaddleBoundaryRadius_pos t ht)
        (D.chronologicalSaddleRecoveryScale_sq_lt_saddleBoundary_sq t ht L)
        (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht)) := by
    refine ⟨0, ?_⟩
    simp [A4, l0,
      StandardMorseEventAt.EmbeddedShrink.saddleNegativeSpatialSegment,
      StandardMorseEventAt.EmbeddedShrink.saddleNegativeCommonOrbitCyclicMarking,
      finFourOfSaddleBranchPair, saddleBranchPairOfFinFour]
  have hpt1 : A4.point l1 ∈ Set.range
      (T.saddleNegativeSpatialSegment .negative r cs
        (D.chronologicalSaddleBoundaryRadius_pos t ht)
        (D.chronologicalSaddleRecoveryScale_sq_lt_saddleBoundary_sq t ht L)
        (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht)) := by
    refine ⟨1, ?_⟩
    simp [A4, l1,
      StandardMorseEventAt.EmbeddedShrink.saddleNegativeSpatialSegment,
      StandardMorseEventAt.EmbeddedShrink.saddleNegativeCommonOrbitCyclicMarking,
      finFourOfSaddleBranchPair, saddleBranchPairOfFinFour]
  have hdisj := T.saddleNegativeSpatialSegments_disjoint hindex r cs
    (D.chronologicalSaddleBoundaryRadius_pos t ht) Q.scale_pos
    (D.chronologicalSaddleRecoveryScale_sq_lt_saddleBoundary_sq t ht L)
    (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht)
  have hnotj : A4.point l0 ∉ A4.cyclicCutRange j := by
    intro hmem
    rw [← hj] at hmem
    exact Set.disjoint_left.mp hdisj hpt0 hmem
  obtain ⟨rc, hri, hrj, hrl⟩ :=
    A4.exists_incidentCutIndexFour_ne_two l0 i j hnotj
  have hl0i : l0 = A4.cyclicCutSourceLabel i ∨
      l0 = A4.cyclicCutTargetLabel i :=
    A4.point_mem_cyclicCutRange_eq_label i l0 (hi ▸ hpt0)
  have hl1i : l1 = A4.cyclicCutSourceLabel i ∨
      l1 = A4.cyclicCutTargetLabel i :=
    A4.point_mem_cyclicCutRange_eq_label i l1 (hi ▸ hpt1)
  have hi0 : A4.cyclicCutSourceLabel i = l0 ∨
      A4.cyclicCutTargetLabel i = l0 := by
    rcases hl0i with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  have hi1 : A4.cyclicCutSourceLabel i = l1 ∨
      A4.cyclicCutTargetLabel i = l1 := by
    rcases hl1i with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  have hne01 : l0 ≠ l1 := by
    intro h
    have := congrArg saddleBranchPairOfFinFour h
    simp [l0, l1] at this
  have hstr := A4.cyclicCutSourceLabel_ne_targetLabel_four rc
  -- ambient identification of the four marks on the recovery slice
  have hmarkAmb : ∀ l : Fin 4,
      cobSpaceTime (A4.point l)
          (D.chronologicalSaddleRecoveryBeforeTime t ht L) =
        M.saddleNegativeBoundaryEnd (saddleBranchPairOfFinFour l).2
          (saddleBranchPairOfFinFour l).1 r cs := by
    intro l
    show cobSpaceTime (A4.point l)
        (tcoord (D.position.eventCenter t ht) - cs ^ 2) =
      M.saddleNegativeBoundaryEnd (saddleBranchPairOfFinFour l).2
        (saddleBranchPairOfFinFour l).1 r cs
    have hpt : A4.point l = spacePart (M.saddleNegativeBoundaryEnd
        (saddleBranchPairOfFinFour l).2 (saddleBranchPairOfFinFour l).1
        r cs) := rfl
    rw [hpt]
    have htX : tcoord (M.saddleNegativeBoundaryEnd
        (saddleBranchPairOfFinFour l).2 (saddleBranchPairOfFinFour l).1
        r cs) = tcoord (D.position.eventCenter t ht) - cs ^ 2 :=
      M.saddleNegativeBoundaryEnd_time hindex _ _ hrho hsq hrM
    calc
      cobSpaceTime (spacePart (M.saddleNegativeBoundaryEnd
          (saddleBranchPairOfFinFour l).2 (saddleBranchPairOfFinFour l).1
          r cs)) (tcoord (D.position.eventCenter t ht) - cs ^ 2) =
          cobSpaceTime (spacePart (M.saddleNegativeBoundaryEnd
            (saddleBranchPairOfFinFour l).2 (saddleBranchPairOfFinFour l).1
            r cs)) (tcoord (M.saddleNegativeBoundaryEnd
              (saddleBranchPairOfFinFour l).2
              (saddleBranchPairOfFinFour l).1 r cs)) := by rw [htX]
      _ = M.saddleNegativeBoundaryEnd (saddleBranchPairOfFinFour l).2
            (saddleBranchPairOfFinFour l).1 r cs := spaceTime_spacePart _
  -- the exterior cut lies in the fixed exterior slab core
  have hcutMem : ∀ w : I,
      A4.cyclicCutAmbientPath rc w ∈ Laux.exteriorSlabCore := by
    intro w
    have htw : tcoord (A4.cyclicCutAmbientPath rc w) =
        tcoord (D.position.eventCenter t ht) - cs ^ 2 := by
      show tcoord (cobSpaceTime (A4.cyclicCutPath rc w)
          (D.chronologicalSaddleRecoveryBeforeTime t ht L)) =
        tcoord (D.position.eventCenter t ht) - cs ^ 2
      rw [tcoord_spaceTime]
      rfl
    have hfib : D.signedOutput.cobordism.toLevelCobordismData.G
        (A4.cyclicCutAmbientPath rc w) = 0 :=
      A4.cyclicCutAmbientPath_fiber rc w
    refine ⟨⟨hfib, ?_⟩, ?_⟩
    · show tcoord (A4.cyclicCutAmbientPath rc w) ∈
        Icc (D.position.eventBracket t ht).before
          (D.position.eventBracket t ht).after
      rw [htw]
      constructor
      · have hc2 : cs ^ 2 ≤ D.chronologicalWindowRadius t ht ^ 2 :=
          (D.chronologicalSaddleRecoveryScale_sq_lt_window_sq t ht L).le
        have hle : D.chronologicalBeforeTime t ht ≤
            tcoord (D.position.eventCenter t ht) - cs ^ 2 := by
          rw [chronologicalBeforeTime]
          linarith
        exact (D.chronologicalBeforeTime_mem_bracket t ht).1.le.trans hle
      · exact (sub_le_self _ (sq_nonneg _)).trans
          (D.position.eventBracket t ht).lt_after.le
    · show Laux.centerCoverRadius ≤
        dist (A4.cyclicCutAmbientPath rc w) (D.position.eventCenter t ht)
      by_contra hlt
      rw [not_le] at hlt
      obtain ⟨u', hu', hup⟩ := Laux.centerCover _ hlt hfib
      have huM' : ‖u'‖ < M.radius := hu'.trans hrM
      have hquad' : morseQuadratic .saddle (u' 0, u' 1) = -(cs ^ 2) := by
        have htm := M.time_model u' huM'
        rw [hindex, hup, htw] at htm
        linarith
      apply havoid rc hri hrj u' hquad' hu'
      rw [hup]
      have hsp : spacePart (A4.cyclicCutAmbientPath rc w) =
          A4.cyclicCutPath rc w := by
        show spacePart (cobSpaceTime (A4.cyclicCutPath rc w)
            (D.chronologicalSaddleRecoveryBeforeTime t ht L)) =
          A4.cyclicCutPath rc w
        rw [spacePart_spaceTime]
      rw [hsp, ← A4.range_cyclicCutPath rc]
      exact ⟨w, rfl⟩
  -- flow the cut forward to the critical level
  let gammaZ := A4.cyclicCutRegularZeroPath rc
  have hgammaK : ∀ w : I, gammaZ.toPath w ∈ Laux.exteriorSlabCore :=
    hcutMem
  have hd : |cs ^ 2| ≤ R.safeTime := by
    rw [abs_of_nonneg (sq_nonneg cs)]
    exact Q.safe
  have habs : |cs ^ 2| = cs ^ 2 := abs_of_nonneg (sq_nonneg cs)
  have htime : ∀ w : I,
      tcoord (gammaZ.toPath w) + cs ^ 2 =
        tcoord (D.position.eventCenter t ht) := by
    intro w
    have htw : tcoord (A4.cyclicCutAmbientPath rc w) =
        tcoord (D.position.eventCenter t ht) - cs ^ 2 := by
      show tcoord (cobSpaceTime (A4.cyclicCutPath rc w)
          (D.chronologicalSaddleRecoveryBeforeTime t ht L)) =
        tcoord (D.position.eventCenter t ht) - cs ^ 2
      rw [tcoord_spaceTime]
      rfl
    have : tcoord (gammaZ.toPath w) =
        tcoord (D.position.eventCenter t ht) - cs ^ 2 := htw
    rw [this]
    ring
  -- endpoint captures
  have hsrcK : M.saddleNegativeBoundaryEnd
      (saddleBranchPairOfFinFour (A4.cyclicCutSourceLabel rc)).2
      (saddleBranchPairOfFinFour (A4.cyclicCutSourceLabel rc)).1 r cs ∈
      Laux.exteriorSlabCore := by
    rw [← hmarkAmb (A4.cyclicCutSourceLabel rc)]
    have h0 := hcutMem 0
    rwa [(A4.cyclicCutAmbientPath rc).source] at h0
  have htgtK : M.saddleNegativeBoundaryEnd
      (saddleBranchPairOfFinFour (A4.cyclicCutTargetLabel rc)).2
      (saddleBranchPairOfFinFour (A4.cyclicCutTargetLabel rc)).1 r cs ∈
      Laux.exteriorSlabCore := by
    rw [← hmarkAmb (A4.cyclicCutTargetLabel rc)]
    have h1 := hcutMem 1
    rwa [(A4.cyclicCutAmbientPath rc).target] at h1
  obtain ⟨u, huT, huP, hu1, hu2, huq⟩ :=
    D.exists_chronologicalSaddleRecoveryCapture t ht hindex L R
      (saddleBranchPairOfFinFour (A4.cyclicCutSourceLabel rc)) hsrcK
      (M.saddleNegativeBoundaryEnd_fiber _ _ hrho hsq hrM)
      habs hd
      (by
        rw [M.saddleNegativeBoundaryEnd_time hindex _ _ hrho hsq hrM]
        ring)
      (Q.negative_close (saddleBranchPairOfFinFour
        (A4.cyclicCutSourceLabel rc)))
  obtain ⟨v, hvT, hvP, hv1, hv2, hvq⟩ :=
    D.exists_chronologicalSaddleRecoveryCapture t ht hindex L R
      (saddleBranchPairOfFinFour (A4.cyclicCutTargetLabel rc)) htgtK
      (M.saddleNegativeBoundaryEnd_fiber _ _ hrho hsq hrM)
      habs hd
      (by
        rw [M.saddleNegativeBoundaryEnd_time hindex _ _ hrho hsq hrM]
        ring)
      (Q.negative_close (saddleBranchPairOfFinFour
        (A4.cyclicCutTargetLabel rc)))
  -- assemble the punctured critical arc
  have harcN : Nonempty (SaddleCriticalExteriorArc
      (fun p => M.saddleCriticalBoundaryEnd p r)
      (StandardMorseEventAt.puncturedCriticalSlice
        D.signedOutput.cobordism (D.position.eventCenter t ht))
      (saddleBranchPairOfFinFour (A4.cyclicCutSourceLabel rc))
      (saddleBranchPairOfFinFour (A4.cyclicCutTargetLabel rc))) := by
    refine ⟨T.saddleCriticalExteriorArcOfSafeFlowWithLocalCaptures H hindex
      R gammaZ hgammaK (cs ^ 2) hd htime r hrho hltT
      (saddleBranchPairOfFinFour (A4.cyclicCutSourceLabel rc))
      (saddleBranchPairOfFinFour (A4.cyclicCutTargetLabel rc))
      u v huT hvT ?_ ?_ hu1 hu2 hv1 hv2 ?_ ?_⟩
    · rw [huq]
      norm_num
    · rw [hvq]
      norm_num
    · exact (congrArg (fun z => R.base.flow z (cs ^ 2))
        (hmarkAmb (A4.cyclicCutSourceLabel rc))).trans huP.symm
    · exact (congrArg (fun z => R.base.flow z (cs ^ 2))
        (hmarkAmb (A4.cyclicCutTargetLabel rc))).trans hvP.symm
  -- pin down the surviving transverse label
  rcases hrl with hsrc | htgt
  · have hpsEq : saddleBranchPairOfFinFour (A4.cyclicCutSourceLabel rc) =
        (SaddleBranch.negative, SaddleBranch.negative) := by
      rw [hsrc]
      simp [l0]
    rw [hpsEq] at harcN
    have hm0 : A4.cyclicCutTargetLabel rc ≠ l0 := by
      intro h
      exact hstr (hsrc.trans h.symm)
    have hm1 : A4.cyclicCutTargetLabel rc ≠ l1 := by
      intro h
      exact hri (A4.cutIndexFour_eq_of_endpointLabels hne01
        (Or.inl hsrc) (Or.inr h) hi0 hi1)
    have hxpos : (saddleBranchPairOfFinFour
        (A4.cyclicCutTargetLabel rc)).2 = SaddleBranch.positive := by
      have hm : A4.cyclicCutTargetLabel rc =
          finFourOfSaddleBranchPair (saddleBranchPairOfFinFour
            (A4.cyclicCutTargetLabel rc)) :=
        (finFourOfSaddleBranchPair_saddleBranchPairOfFinFour _).symm
      rcases hp : saddleBranchPairOfFinFour (A4.cyclicCutTargetLabel rc)
        with ⟨b, e⟩
      cases e with
      | negative =>
          exfalso
          rw [hp] at hm
          cases b with
          | negative => exact hm0 hm
          | positive => exact hm1 hm
      | positive => rfl
    exact D.chronologicalSaddleRecovery_pin_negative t ht A hxpos harcN
  · have hptEq : saddleBranchPairOfFinFour (A4.cyclicCutTargetLabel rc) =
        (SaddleBranch.negative, SaddleBranch.negative) := by
      rw [htgt]
      simp [l0]
    have harcN' : Nonempty (SaddleCriticalExteriorArc
        (fun p => M.saddleCriticalBoundaryEnd p r)
        (StandardMorseEventAt.puncturedCriticalSlice
          D.signedOutput.cobordism (D.position.eventCenter t ht))
        (saddleBranchPairOfFinFour (A4.cyclicCutTargetLabel rc))
        (saddleBranchPairOfFinFour (A4.cyclicCutSourceLabel rc))) :=
      harcN.map fun B => B.symm
    rw [hptEq] at harcN'
    have hm0 : A4.cyclicCutSourceLabel rc ≠ l0 := by
      intro h
      exact hstr (h.trans htgt.symm)
    have hm1 : A4.cyclicCutSourceLabel rc ≠ l1 := by
      intro h
      exact hri (A4.cutIndexFour_eq_of_endpointLabels hne01
        (Or.inr htgt) (Or.inl h) hi0 hi1)
    have hxpos : (saddleBranchPairOfFinFour
        (A4.cyclicCutSourceLabel rc)).2 = SaddleBranch.positive := by
      have hm : A4.cyclicCutSourceLabel rc =
          finFourOfSaddleBranchPair (saddleBranchPairOfFinFour
            (A4.cyclicCutSourceLabel rc)) :=
        (finFourOfSaddleBranchPair_saddleBranchPairOfFinFour _).symm
      rcases hp : saddleBranchPairOfFinFour (A4.cyclicCutSourceLabel rc)
        with ⟨b, e⟩
      cases e with
      | negative =>
          exfalso
          rw [hp] at hm
          cases b with
          | negative => exact hm0 hm
          | positive => exact hm1 hm
      | positive => rfl
    exact D.chronologicalSaddleRecovery_pin_negative t ht A hxpos harcN'


-- @@ L2034-2034 verbatim
/-! ## The recovery contract -/


-- @@ L2036-2053 verbatim
/-- The regular-orbit arc recovery contract holds for the actual
chronological production saddle, given the punctured critical arc pairing
and the endpoint-local fiber cover already assumed by the final dichotomy
theorem. -/
theorem chronologicalSaddleRegularOrbitArcRecovery_of_endpointLocalFiberCover
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht))
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) :
    ChronologicalSaddleRegularOrbitArcRecovery
      (D := D) (t := t) (ht := ht) (hindex := hindex) where
  positiveArc heq :=
    D.chronologicalSaddleRecovery_positiveArc t ht hindex A L heq
  negativeArc heq :=
    D.chronologicalSaddleRecovery_negativeArc t ht hindex A L heq


-- @@ L2055-2068 verbatim
/-- **Regular-orbit arc recovery from the pairing alone.**  With the
canonical unconditional endpoint-local fiber cover, the sole remaining
hypothesis of the recovery contract is the punctured critical arc pairing
data. -/
theorem chronologicalSaddleRegularOrbitArcRecovery_of_pairing
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht)) :
    ChronologicalSaddleRegularOrbitArcRecovery
      (D := D) (t := t) (ht := ht) (hindex := hindex) :=
  D.chronologicalSaddleRegularOrbitArcRecovery_of_endpointLocalFiberCover
    t ht hindex A (D.chronologicalSaddleEndpointLocalFiberCover t ht)


-- @@ L2070-2084 verbatim
/-- **Production saddle topology from the pairing alone.**  Combining the
arc-recovery construction with the automatic flow-compatibility package,
the merge-or-split dichotomy follows from the punctured critical arc
pairing data with no other hypothesis. -/
theorem chronologicalSaddleTopologyDichotomy_of_pairing
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (A : (D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht)) :
    D.ChronologicalSaddleMergeTopology t ht hindex ∨
      D.ChronologicalSaddleSplitTopology t ht hindex :=
  chronologicalSaddleTopologyDichotomy_of_pairing_and_arcRecovery
    (D := D) (t := t) (ht := ht) hindex A
    (D.chronologicalSaddleRegularOrbitArcRecovery_of_pairing t ht hindex A)


-- @@ L2086-2086 verbatim
end ValueSeparatedSignedMorsePackage


-- @@ L2088-2088 verbatim
end Submission
