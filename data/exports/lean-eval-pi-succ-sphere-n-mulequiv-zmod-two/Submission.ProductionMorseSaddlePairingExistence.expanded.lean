import Submission.ProductionMorseSaddleCriticalArcCutOrder
import Submission.ProductionMorseSaddleOrbitArcRecoveryExistence


-- @@ L4-37 verbatim
/-!
# Existence of the punctured critical-arc pairing data from parity

This file removes the last structural hypothesis of the production saddle
analysis: given only the oriented cut parity
(`ChronologicalSaddleOrientedCutParity`), the full punctured critical-arc
pairing data `SaddlePuncturedCriticalArcPairingData` exists at the fixed
chronological boundary radius.

The construction is a two-case orbit analysis on the recovery slices, using
no pairing input whatsoever:

* If the two positive local branch orbits at the chronological window are
  **distinct**, each positive local branch lies on its own regular closed
  orbit through exactly its two chart-boundary ends.  The complementary
  cyclic cut of the branch segment on that two-marked orbit avoids the whole
  open chart uniformly (`saddlePositiveBranch_exists_uniformExteriorCut`),
  hence lies in the fixed compact exterior slab; flowing it back to the
  critical level and capturing its endpoints in the labelled quadrants
  produces an honest punctured critical arc joining the two ends
  `(b, negative)` and `(b, positive)` of every branch `b`.  These are
  exactly the `flipSecond` candidate mate arcs, and
  `chronologicalSaddlePairingData_of_parity_of_flipSecond_arcs` finishes.

* If the two positive local branch orbits **coincide**, the parity residual
  forces the two negative local branch orbits to be distinct, and the same
  construction on the negative recovery slice produces the `flipFirst`
  candidate arcs joining `(negative, b)` and `(positive, b)`;
  `chronologicalSaddlePairingData_of_parity_of_flipFirst_arcs` finishes.

All orientation and uniqueness obligations are discharged by the checker
separation theorem `chronologicalSaddle_arc_checker_ne_of_parity`, whose only
input is the same parity residual.
-/


-- @@ L39-39 verbatim
set_option autoImplicit false

-- @@ L40-40 verbatim
set_option maxHeartbeats 2400000


-- @@ L42-42 verbatim
noncomputable section


-- @@ L44-44 verbatim
open Set Function Metric Filter

-- @@ L45-45 verbatim
open scoped RealInnerProductSpace Topology unitInterval


-- @@ L47-47 verbatim
namespace Submission


-- @@ L49-49 verbatim
variable {n : ℕ}


-- @@ L51-51 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

-- @@ L52-52 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L53-53 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L55-55 verbatim
/-! ## Two-mark cyclic cuts have distinct endpoint labels -/


-- @@ L57-57 verbatim
namespace SimpleClosedOrbitParam.CyclicMarking


-- @@ L59-59 verbatim
variable {X : FramedLevelSet n} {V : TamedField X}

-- @@ L60-60 verbatim
variable {P : SimpleClosedOrbitParam X V}


-- @@ L62-82 verbatim
/-- On a two-marked orbit, either cyclic cut joins the two distinct marked
labels. -/
theorem cyclicCutSourceLabel_ne_targetLabel_two
    (A : P.CyclicMarking 1) (i : Fin 2) :
    A.cyclicCutSourceLabel i ≠ A.cyclicCutTargetLabel i := by
  induction i using Fin.lastCases with
  | last =>
      intro h
      simp only [cyclicCutSourceLabel, cyclicCutTargetLabel] at h
      rw [Fin.lastCases_last, Fin.lastCases_last] at h
      have h' : A.sortedLabel (Fin.last 1) = A.sortedLabel 0 := h
      have hindex := A.sortedLabel.injective h'
      have hval := congrArg Fin.val hindex
      norm_num at hval
  | cast j =>
      intro h
      simp only [cyclicCutSourceLabel, cyclicCutTargetLabel] at h
      rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc] at h
      have h' : A.sortedLabel j.castSucc = A.sortedLabel j.succ := h
      exact (Fin.castSucc_lt_succ : j.castSucc < j.succ).ne
        (A.sortedLabel.injective h')


-- @@ L84-84 verbatim
end SimpleClosedOrbitParam.CyclicMarking


-- @@ L86-86 verbatim
variable {X₀ X₁ : FramedLevelSet n}

-- @@ L87-87 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}

-- @@ L88-88 verbatim
variable {SC : SignedFramedLevelCobordism S₀ S₁}


-- @@ L90-90 verbatim
namespace ValueSeparatedSignedMorsePackage


-- @@ L92-92 verbatim
variable {D : ValueSeparatedSignedMorsePackage SC}

-- @@ L93-93 verbatim
variable {t : ℝ} {ht : t ∈ D.position.eventTimes}


-- @@ L95-95 verbatim
/-! ## The two-end markings on the recovery slices -/


-- @@ L97-120 verbatim
/-- The two chart-boundary ends of one positive local branch, marked on its
own recovery-slice orbit. -/
noncomputable def chronologicalSaddleRecoveryPositiveMarking
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) (b : SaddleBranch) :
    ((D.chronologicalEventEmbeddedShrink t ht).saddlePositiveBranchOrbitParam
      hindex b (D.chronologicalSaddleBoundaryRadius t ht)
      (D.chronologicalSaddleRecoveryScale t ht L).scale
      (D.chronologicalSaddleBoundaryRadius_pos t ht)
      (D.chronologicalSaddleRecoveryScale_sq_lt_saddleBoundary_sq t ht L)
      (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht)
      (D.chronologicalSaddleRecoveryAfterTime_regular t ht L)
      (D.chronologicalSaddleRecoveryAfterField t ht L)).CyclicMarking 1 :=
  (D.chronologicalEventEmbeddedShrink t ht).saddlePositiveBranchCyclicMarking
    hindex b (D.chronologicalSaddleBoundaryRadius t ht)
    (D.chronologicalSaddleRecoveryScale t ht L).scale
    (D.chronologicalSaddleBoundaryRadius_pos t ht)
    (D.chronologicalSaddleRecoveryScale_sq_lt_saddleBoundary_sq t ht L)
    (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht)
    (D.chronologicalSaddleRecoveryAfterTime_regular t ht L)
    (D.chronologicalSaddleRecoveryAfterField t ht L)


-- @@ L122-145 verbatim
/-- The two chart-boundary ends of one negative local branch, marked on its
own recovery-slice orbit. -/
noncomputable def chronologicalSaddleRecoveryNegativeMarking
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht)) (b : SaddleBranch) :
    ((D.chronologicalEventEmbeddedShrink t ht).saddleNegativeBranchOrbitParam
      hindex b (D.chronologicalSaddleBoundaryRadius t ht)
      (D.chronologicalSaddleRecoveryScale t ht L).scale
      (D.chronologicalSaddleBoundaryRadius_pos t ht)
      (D.chronologicalSaddleRecoveryScale_sq_lt_saddleBoundary_sq t ht L)
      (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht)
      (D.chronologicalSaddleRecoveryBeforeTime_regular t ht L)
      (D.chronologicalSaddleRecoveryBeforeField t ht L)).CyclicMarking 1 :=
  (D.chronologicalEventEmbeddedShrink t ht).saddleNegativeBranchCyclicMarking
    hindex b (D.chronologicalSaddleBoundaryRadius t ht)
    (D.chronologicalSaddleRecoveryScale t ht L).scale
    (D.chronologicalSaddleBoundaryRadius_pos t ht)
    (D.chronologicalSaddleRecoveryScale_sq_lt_saddleBoundary_sq t ht L)
    (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht)
    (D.chronologicalSaddleRecoveryBeforeTime_regular t ht L)
    (D.chronologicalSaddleRecoveryBeforeField t ht L)


-- @@ L147-147 verbatim
/-! ## Flow-back of one chart-avoiding two-mark cyclic cut -/


-- @@ L149-352 verbatim
/-- One uniformly chart-avoiding cyclic cut of a positive-branch two-mark
orbit flows back to a punctured critical arc between the two labelled ends
of that branch. -/
theorem chronologicalSaddleDistinctPositive_cutArc
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht))
    (b : SaddleBranch) (e : Fin 2)
    (havoid : ∀ u : E₂,
      morseQuadratic .saddle (u 0, u 1) =
        (D.chronologicalSaddleRecoveryScale t ht L).scale ^ 2 →
      ‖u‖ < D.chronologicalSaddleBoundaryRadius t ht →
      spacePart ((D.position.eventModel t ht).param u) ∈
        ((D.chronologicalSaddleRecoveryPositiveOrbit t ht hindex L b :
          (D.chronologicalSaddleRecoveryAfterField t ht L).OrbitIndex) :
            Set E₁) →
      spacePart ((D.position.eventModel t ht).param u) ∉
        (D.chronologicalSaddleRecoveryPositiveMarking t ht hindex L
          b).cyclicCutRange e) :
    Nonempty (SaddleCriticalExteriorArc
      (fun p => (D.position.eventModel t ht).saddleCriticalBoundaryEnd p
        (D.chronologicalSaddleBoundaryRadius t ht))
      (StandardMorseEventAt.puncturedCriticalSlice
        D.signedOutput.cobordism (D.position.eventCenter t ht))
      (b, saddleBranchOfFinTwo
        ((D.chronologicalSaddleRecoveryPositiveMarking t ht hindex L
          b).cyclicCutSourceLabel e))
      (b, saddleBranchOfFinTwo
        ((D.chronologicalSaddleRecoveryPositiveMarking t ht hindex L
          b).cyclicCutTargetLabel e))) := by
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
  let A2 := D.chronologicalSaddleRecoveryPositiveMarking t ht hindex L b
  -- ambient identification of the two marks on the recovery slice
  have hmarkAmb : ∀ l : Fin 2,
      cobSpaceTime (A2.point l)
          (D.chronologicalSaddleRecoveryAfterTime t ht L) =
        M.saddlePositiveBoundaryEnd b (saddleBranchOfFinTwo l) r cs := by
    intro l
    show cobSpaceTime (A2.point l)
        (tcoord (D.position.eventCenter t ht) + cs ^ 2) =
      M.saddlePositiveBoundaryEnd b (saddleBranchOfFinTwo l) r cs
    have hpt : A2.point l = spacePart (M.saddlePositiveBoundaryEnd b
        (saddleBranchOfFinTwo l) r cs) := rfl
    rw [hpt]
    have htX : tcoord (M.saddlePositiveBoundaryEnd b
        (saddleBranchOfFinTwo l) r cs) =
        tcoord (D.position.eventCenter t ht) + cs ^ 2 :=
      M.saddlePositiveBoundaryEnd_time hindex _ _ hrho hsq hrM
    calc
      cobSpaceTime (spacePart (M.saddlePositiveBoundaryEnd b
          (saddleBranchOfFinTwo l) r cs))
          (tcoord (D.position.eventCenter t ht) + cs ^ 2) =
          cobSpaceTime (spacePart (M.saddlePositiveBoundaryEnd b
            (saddleBranchOfFinTwo l) r cs))
            (tcoord (M.saddlePositiveBoundaryEnd b
              (saddleBranchOfFinTwo l) r cs)) := by rw [htX]
      _ = M.saddlePositiveBoundaryEnd b (saddleBranchOfFinTwo l) r cs :=
        spaceTime_spacePart _
  -- the exterior cut lies in the fixed exterior slab core
  have hcutMem : ∀ w : I,
      A2.cyclicCutAmbientPath e w ∈ Laux.exteriorSlabCore := by
    intro w
    have htw : tcoord (A2.cyclicCutAmbientPath e w) =
        tcoord (D.position.eventCenter t ht) + cs ^ 2 := by
      show tcoord (cobSpaceTime (A2.cyclicCutPath e w)
          (D.chronologicalSaddleRecoveryAfterTime t ht L)) =
        tcoord (D.position.eventCenter t ht) + cs ^ 2
      rw [tcoord_spaceTime]
      rfl
    have hfib : D.signedOutput.cobordism.toLevelCobordismData.G
        (A2.cyclicCutAmbientPath e w) = 0 :=
      A2.cyclicCutAmbientPath_fiber e w
    refine ⟨⟨hfib, ?_⟩, ?_⟩
    · show tcoord (A2.cyclicCutAmbientPath e w) ∈
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
        dist (A2.cyclicCutAmbientPath e w) (D.position.eventCenter t ht)
      by_contra hlt
      rw [not_le] at hlt
      obtain ⟨u', hu', hup⟩ := Laux.centerCover _ hlt hfib
      have huM' : ‖u'‖ < M.radius := hu'.trans hrM
      have hquad' : morseQuadratic .saddle (u' 0, u' 1) = cs ^ 2 := by
        have htm := M.time_model u' huM'
        rw [hindex, hup, htw] at htm
        linarith
      have hsp : spacePart (A2.cyclicCutAmbientPath e w) =
          A2.cyclicCutPath e w := by
        show spacePart (cobSpaceTime (A2.cyclicCutPath e w)
            (D.chronologicalSaddleRecoveryAfterTime t ht L)) =
          A2.cyclicCutPath e w
        rw [spacePart_spaceTime]
      have hmemCut : spacePart (M.param u') ∈ A2.cyclicCutRange e := by
        rw [hup, hsp, ← A2.range_cyclicCutPath e]
        exact ⟨w, rfl⟩
      have horbitMem : spacePart (M.param u') ∈
          ((D.chronologicalSaddleRecoveryPositiveOrbit t ht hindex L b :
            (D.chronologicalSaddleRecoveryAfterField t ht L).OrbitIndex) :
              Set E₁) := by
        have hx := hmemCut
        rw [← A2.range_cyclicCutPath e] at hx
        obtain ⟨w', hw'⟩ := hx
        rw [(D.chronologicalSaddleRecoveryAfterField t ht
          L).orbitPoint_orbit, ← hw']
        exact A2.cyclicCutPath_mem_orbit e w'
      exact havoid u' hquad' hu' horbitMem hmemCut
  -- flow the cut back to the critical level
  let gammaZ := A2.cyclicCutRegularZeroPath e
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
    have htw : tcoord (A2.cyclicCutAmbientPath e w) =
        tcoord (D.position.eventCenter t ht) + cs ^ 2 := by
      show tcoord (cobSpaceTime (A2.cyclicCutPath e w)
          (D.chronologicalSaddleRecoveryAfterTime t ht L)) =
        tcoord (D.position.eventCenter t ht) + cs ^ 2
      rw [tcoord_spaceTime]
      rfl
    have hthis : tcoord (gammaZ.toPath w) =
        tcoord (D.position.eventCenter t ht) + cs ^ 2 := htw
    rw [hthis]
    ring
  -- endpoint captures
  have hsrcK : M.saddlePositiveBoundaryEnd b
      (saddleBranchOfFinTwo (A2.cyclicCutSourceLabel e)) r cs ∈
      Laux.exteriorSlabCore := by
    rw [← hmarkAmb (A2.cyclicCutSourceLabel e)]
    have h0 := hcutMem 0
    rwa [(A2.cyclicCutAmbientPath e).source] at h0
  have htgtK : M.saddlePositiveBoundaryEnd b
      (saddleBranchOfFinTwo (A2.cyclicCutTargetLabel e)) r cs ∈
      Laux.exteriorSlabCore := by
    rw [← hmarkAmb (A2.cyclicCutTargetLabel e)]
    have h1 := hcutMem 1
    rwa [(A2.cyclicCutAmbientPath e).target] at h1
  obtain ⟨u, huT, huP, hu1, hu2, huq⟩ :=
    D.exists_chronologicalSaddleRecoveryCapture t ht hindex L R
      (b, saddleBranchOfFinTwo (A2.cyclicCutSourceLabel e)) hsrcK
      (M.saddlePositiveBoundaryEnd_fiber _ _ hrho hsq hrM)
      habs hd
      (by
        rw [M.saddlePositiveBoundaryEnd_time hindex _ _ hrho hsq hrM]
        ring)
      (Q.positive_close
        (b, saddleBranchOfFinTwo (A2.cyclicCutSourceLabel e)))
  obtain ⟨v, hvT, hvP, hv1, hv2, hvq⟩ :=
    D.exists_chronologicalSaddleRecoveryCapture t ht hindex L R
      (b, saddleBranchOfFinTwo (A2.cyclicCutTargetLabel e)) htgtK
      (M.saddlePositiveBoundaryEnd_fiber _ _ hrho hsq hrM)
      habs hd
      (by
        rw [M.saddlePositiveBoundaryEnd_time hindex _ _ hrho hsq hrM]
        ring)
      (Q.positive_close
        (b, saddleBranchOfFinTwo (A2.cyclicCutTargetLabel e)))
  -- assemble the punctured critical arc
  refine ⟨T.saddleCriticalExteriorArcOfSafeFlowWithLocalCaptures H hindex
    R gammaZ hgammaK (-(cs ^ 2)) hd htime r hrho hltT
    (b, saddleBranchOfFinTwo (A2.cyclicCutSourceLabel e))
    (b, saddleBranchOfFinTwo (A2.cyclicCutTargetLabel e))
    u v huT hvT ?_ ?_ hu1 hu2 hv1 hv2 ?_ ?_⟩
  · rw [huq]
    norm_num
  · rw [hvq]
    norm_num
  · exact (congrArg (fun z => R.base.flow z (-(cs ^ 2)))
      (hmarkAmb (A2.cyclicCutSourceLabel e))).trans huP.symm
  · exact (congrArg (fun z => R.base.flow z (-(cs ^ 2)))
      (hmarkAmb (A2.cyclicCutTargetLabel e))).trans hvP.symm


-- @@ L354-556 verbatim
/-- Negative-slice counterpart: one uniformly chart-avoiding cyclic cut of a
negative-branch two-mark orbit flows forward to a punctured critical arc
between the two labelled ends of that branch. -/
theorem chronologicalSaddleDistinctNegative_cutArc
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht))
    (b : SaddleBranch) (e : Fin 2)
    (havoid : ∀ u : E₂,
      morseQuadratic .saddle (u 0, u 1) =
        -((D.chronologicalSaddleRecoveryScale t ht L).scale ^ 2) →
      ‖u‖ < D.chronologicalSaddleBoundaryRadius t ht →
      spacePart ((D.position.eventModel t ht).param u) ∈
        ((D.chronologicalSaddleRecoveryNegativeOrbit t ht hindex L b :
          (D.chronologicalSaddleRecoveryBeforeField t ht L).OrbitIndex) :
            Set E₁) →
      spacePart ((D.position.eventModel t ht).param u) ∉
        (D.chronologicalSaddleRecoveryNegativeMarking t ht hindex L
          b).cyclicCutRange e) :
    Nonempty (SaddleCriticalExteriorArc
      (fun p => (D.position.eventModel t ht).saddleCriticalBoundaryEnd p
        (D.chronologicalSaddleBoundaryRadius t ht))
      (StandardMorseEventAt.puncturedCriticalSlice
        D.signedOutput.cobordism (D.position.eventCenter t ht))
      (saddleBranchOfFinTwo
        ((D.chronologicalSaddleRecoveryNegativeMarking t ht hindex L
          b).cyclicCutSourceLabel e), b)
      (saddleBranchOfFinTwo
        ((D.chronologicalSaddleRecoveryNegativeMarking t ht hindex L
          b).cyclicCutTargetLabel e), b)) := by
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
  let A2 := D.chronologicalSaddleRecoveryNegativeMarking t ht hindex L b
  -- ambient identification of the two marks on the recovery slice
  have hmarkAmb : ∀ l : Fin 2,
      cobSpaceTime (A2.point l)
          (D.chronologicalSaddleRecoveryBeforeTime t ht L) =
        M.saddleNegativeBoundaryEnd b (saddleBranchOfFinTwo l) r cs := by
    intro l
    show cobSpaceTime (A2.point l)
        (tcoord (D.position.eventCenter t ht) - cs ^ 2) =
      M.saddleNegativeBoundaryEnd b (saddleBranchOfFinTwo l) r cs
    have hpt : A2.point l = spacePart (M.saddleNegativeBoundaryEnd b
        (saddleBranchOfFinTwo l) r cs) := rfl
    rw [hpt]
    have htX : tcoord (M.saddleNegativeBoundaryEnd b
        (saddleBranchOfFinTwo l) r cs) =
        tcoord (D.position.eventCenter t ht) - cs ^ 2 :=
      M.saddleNegativeBoundaryEnd_time hindex _ _ hrho hsq hrM
    calc
      cobSpaceTime (spacePart (M.saddleNegativeBoundaryEnd b
          (saddleBranchOfFinTwo l) r cs))
          (tcoord (D.position.eventCenter t ht) - cs ^ 2) =
          cobSpaceTime (spacePart (M.saddleNegativeBoundaryEnd b
            (saddleBranchOfFinTwo l) r cs))
            (tcoord (M.saddleNegativeBoundaryEnd b
              (saddleBranchOfFinTwo l) r cs)) := by rw [htX]
      _ = M.saddleNegativeBoundaryEnd b (saddleBranchOfFinTwo l) r cs :=
        spaceTime_spacePart _
  -- the exterior cut lies in the fixed exterior slab core
  have hcutMem : ∀ w : I,
      A2.cyclicCutAmbientPath e w ∈ Laux.exteriorSlabCore := by
    intro w
    have htw : tcoord (A2.cyclicCutAmbientPath e w) =
        tcoord (D.position.eventCenter t ht) - cs ^ 2 := by
      show tcoord (cobSpaceTime (A2.cyclicCutPath e w)
          (D.chronologicalSaddleRecoveryBeforeTime t ht L)) =
        tcoord (D.position.eventCenter t ht) - cs ^ 2
      rw [tcoord_spaceTime]
      rfl
    have hfib : D.signedOutput.cobordism.toLevelCobordismData.G
        (A2.cyclicCutAmbientPath e w) = 0 :=
      A2.cyclicCutAmbientPath_fiber e w
    refine ⟨⟨hfib, ?_⟩, ?_⟩
    · show tcoord (A2.cyclicCutAmbientPath e w) ∈
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
        dist (A2.cyclicCutAmbientPath e w) (D.position.eventCenter t ht)
      by_contra hlt
      rw [not_le] at hlt
      obtain ⟨u', hu', hup⟩ := Laux.centerCover _ hlt hfib
      have huM' : ‖u'‖ < M.radius := hu'.trans hrM
      have hquad' : morseQuadratic .saddle (u' 0, u' 1) = -(cs ^ 2) := by
        have htm := M.time_model u' huM'
        rw [hindex, hup, htw] at htm
        linarith
      have hsp : spacePart (A2.cyclicCutAmbientPath e w) =
          A2.cyclicCutPath e w := by
        show spacePart (cobSpaceTime (A2.cyclicCutPath e w)
            (D.chronologicalSaddleRecoveryBeforeTime t ht L)) =
          A2.cyclicCutPath e w
        rw [spacePart_spaceTime]
      have hmemCut : spacePart (M.param u') ∈ A2.cyclicCutRange e := by
        rw [hup, hsp, ← A2.range_cyclicCutPath e]
        exact ⟨w, rfl⟩
      have horbitMem : spacePart (M.param u') ∈
          ((D.chronologicalSaddleRecoveryNegativeOrbit t ht hindex L b :
            (D.chronologicalSaddleRecoveryBeforeField t ht L).OrbitIndex) :
              Set E₁) := by
        have hx := hmemCut
        rw [← A2.range_cyclicCutPath e] at hx
        obtain ⟨w', hw'⟩ := hx
        rw [(D.chronologicalSaddleRecoveryBeforeField t ht
          L).orbitPoint_orbit, ← hw']
        exact A2.cyclicCutPath_mem_orbit e w'
      exact havoid u' hquad' hu' horbitMem hmemCut
  -- flow the cut forward to the critical level
  let gammaZ := A2.cyclicCutRegularZeroPath e
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
    have htw : tcoord (A2.cyclicCutAmbientPath e w) =
        tcoord (D.position.eventCenter t ht) - cs ^ 2 := by
      show tcoord (cobSpaceTime (A2.cyclicCutPath e w)
          (D.chronologicalSaddleRecoveryBeforeTime t ht L)) =
        tcoord (D.position.eventCenter t ht) - cs ^ 2
      rw [tcoord_spaceTime]
      rfl
    have hthis : tcoord (gammaZ.toPath w) =
        tcoord (D.position.eventCenter t ht) - cs ^ 2 := htw
    rw [hthis]
    ring
  -- endpoint captures
  have hsrcK : M.saddleNegativeBoundaryEnd b
      (saddleBranchOfFinTwo (A2.cyclicCutSourceLabel e)) r cs ∈
      Laux.exteriorSlabCore := by
    rw [← hmarkAmb (A2.cyclicCutSourceLabel e)]
    have h0 := hcutMem 0
    rwa [(A2.cyclicCutAmbientPath e).source] at h0
  have htgtK : M.saddleNegativeBoundaryEnd b
      (saddleBranchOfFinTwo (A2.cyclicCutTargetLabel e)) r cs ∈
      Laux.exteriorSlabCore := by
    rw [← hmarkAmb (A2.cyclicCutTargetLabel e)]
    have h1 := hcutMem 1
    rwa [(A2.cyclicCutAmbientPath e).target] at h1
  obtain ⟨u, huT, huP, hu1, hu2, huq⟩ :=
    D.exists_chronologicalSaddleRecoveryCapture t ht hindex L R
      (saddleBranchOfFinTwo (A2.cyclicCutSourceLabel e), b) hsrcK
      (M.saddleNegativeBoundaryEnd_fiber _ _ hrho hsq hrM)
      habs hd
      (by
        rw [M.saddleNegativeBoundaryEnd_time hindex _ _ hrho hsq hrM]
        ring)
      (Q.negative_close
        (saddleBranchOfFinTwo (A2.cyclicCutSourceLabel e), b))
  obtain ⟨v, hvT, hvP, hv1, hv2, hvq⟩ :=
    D.exists_chronologicalSaddleRecoveryCapture t ht hindex L R
      (saddleBranchOfFinTwo (A2.cyclicCutTargetLabel e), b) htgtK
      (M.saddleNegativeBoundaryEnd_fiber _ _ hrho hsq hrM)
      habs hd
      (by
        rw [M.saddleNegativeBoundaryEnd_time hindex _ _ hrho hsq hrM]
        ring)
      (Q.negative_close
        (saddleBranchOfFinTwo (A2.cyclicCutTargetLabel e), b))
  -- assemble the punctured critical arc
  refine ⟨T.saddleCriticalExteriorArcOfSafeFlowWithLocalCaptures H hindex
    R gammaZ hgammaK (cs ^ 2) hd htime r hrho hltT
    (saddleBranchOfFinTwo (A2.cyclicCutSourceLabel e), b)
    (saddleBranchOfFinTwo (A2.cyclicCutTargetLabel e), b)
    u v huT hvT ?_ ?_ hu1 hu2 hv1 hv2 ?_ ?_⟩
  · rw [huq]
    norm_num
  · rw [hvq]
    norm_num
  · exact (congrArg (fun z => R.base.flow z (cs ^ 2))
      (hmarkAmb (A2.cyclicCutSourceLabel e))).trans huP.symm
  · exact (congrArg (fun z => R.base.flow z (cs ^ 2))
      (hmarkAmb (A2.cyclicCutTargetLabel e))).trans hvP.symm


-- @@ L558-558 verbatim
/-! ## Distinct branch orbits give both same-branch mate arcs -/


-- @@ L560-646 verbatim
/-- If the two positive window branch orbits are distinct, every positive
local branch is joined to itself: there is a punctured critical arc between
its two labelled ends `(b, negative)` and `(b, positive)`. -/
theorem chronologicalSaddleDistinctPositive_arc
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht))
    (hne : D.chronologicalSaddlePositiveOrbit t ht hindex .negative ≠
      D.chronologicalSaddlePositiveOrbit t ht hindex .positive)
    (b : SaddleBranch) :
    Nonempty (SaddleCriticalExteriorArc
      (fun p => (D.position.eventModel t ht).saddleCriticalBoundaryEnd p
        (D.chronologicalSaddleBoundaryRadius t ht))
      (StandardMorseEventAt.puncturedCriticalSlice
        D.signedOutput.cobordism (D.position.eventCenter t ht))
      (b, SaddleBranch.negative) (b, SaddleBranch.positive)) := by
  classical
  let T := D.chronologicalEventEmbeddedShrink t ht
  let Q := D.chronologicalSaddleRecoveryScale t ht L
  let cs : ℝ := Q.scale
  let r := D.chronologicalSaddleBoundaryRadius t ht
  let hreg := D.chronologicalSaddleRecoveryAfterTime_regular t ht L
  let V := D.chronologicalSaddleRecoveryAfterField t ht L
  -- transported branch-orbit distinctness
  have hshort : D.chronologicalSaddleRecoveryPositiveOrbit t ht hindex
        L .negative ≠
      D.chronologicalSaddleRecoveryPositiveOrbit t ht hindex L .positive := by
    intro h
    apply hne
    have h2 := congrArg
      (D.chronologicalSaddleRecoveryAfterToWindowOrbitEquiv t ht L) h
    rwa [D.chronologicalSaddleRecoveryAfterToWindowOrbitEquiv_branch
        t ht hindex L .negative,
      D.chronologicalSaddleRecoveryAfterToWindowOrbitEquiv_branch
        t ht hindex L .positive] at h2
  have hOrbNe : T.saddlePositiveBranchOrbitIndex hindex .negative r cs
        (D.chronologicalSaddleBoundaryRadius_pos t ht)
        (D.chronologicalSaddleRecoveryScale_sq_lt_saddleBoundary_sq t ht L)
        (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht) hreg V ≠
      T.saddlePositiveBranchOrbitIndex hindex .positive r cs
        (D.chronologicalSaddleBoundaryRadius_pos t ht)
        (D.chronologicalSaddleRecoveryScale_sq_lt_saddleBoundary_sq t ht L)
        (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht) hreg V :=
    hshort
  -- the uniform exterior cut of the branch orbit
  have hcut := T.saddlePositiveBranch_exists_uniformExteriorCut hindex b
    r cs (D.chronologicalSaddleBoundaryRadius_pos t ht) Q.scale_pos
    (D.chronologicalSaddleRecoveryScale_sq_lt_saddleBoundary_sq t ht L)
    (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht) hreg V hOrbNe
  let A2 := D.chronologicalSaddleRecoveryPositiveMarking t ht hindex L b
  have hlabne := fun e =>
    SimpleClosedOrbitParam.CyclicMarking.cyclicCutSourceLabel_ne_targetLabel_two
      A2 e
  have harcCut : ∃ e : Fin 2, Nonempty (SaddleCriticalExteriorArc
      (fun p => (D.position.eventModel t ht).saddleCriticalBoundaryEnd p
        (D.chronologicalSaddleBoundaryRadius t ht))
      (StandardMorseEventAt.puncturedCriticalSlice
        D.signedOutput.cobordism (D.position.eventCenter t ht))
      (b, saddleBranchOfFinTwo (A2.cyclicCutSourceLabel e))
      (b, saddleBranchOfFinTwo (A2.cyclicCutTargetLabel e))) := by
    rcases hcut with ⟨hlocal, havoid⟩ | ⟨hlocal, havoid⟩
    · refine ⟨Fin.last 1,
        D.chronologicalSaddleDistinctPositive_cutArc t ht hindex L b
          (Fin.last 1) ?_⟩
      intro u hq hn ho
      rw [SimpleClosedOrbitParam.CyclicMarking.cyclicCutRange_last]
      exact havoid u hq hn ho
    · refine ⟨(0 : Fin 1).castSucc,
        D.chronologicalSaddleDistinctPositive_cutArc t ht hindex L b
          ((0 : Fin 1).castSucc) ?_⟩
      intro u hq hn ho
      rw [SimpleClosedOrbitParam.CyclicMarking.cyclicCutRange_castSucc]
      exact havoid u hq hn ho
  obtain ⟨e, harc⟩ := harcCut
  have h01 : ∀ l : Fin 2, l = 0 ∨ l = 1 := by decide
  rcases h01 (A2.cyclicCutSourceLabel e) with hs | hs <;>
    rcases h01 (A2.cyclicCutTargetLabel e) with htg | htg
  · exact absurd (hs.trans htg.symm) (hlabne e)
  · rw [hs, htg, saddleBranchOfFinTwo_zero, saddleBranchOfFinTwo_one]
      at harc
    exact harc
  · rw [hs, htg, saddleBranchOfFinTwo_one, saddleBranchOfFinTwo_zero]
      at harc
    exact harc.map fun B => B.symm
  · exact absurd (hs.trans htg.symm) (hlabne e)


-- @@ L648-734 verbatim
/-- If the two negative window branch orbits are distinct, every negative
local branch is joined to itself: there is a punctured critical arc between
its two labelled ends `(negative, b)` and `(positive, b)`. -/
theorem chronologicalSaddleDistinctNegative_arc
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (L : ChronologicalSaddleEndpointLocalFiberCover
      (D := D) (t := t) (ht := ht))
    (hne : D.chronologicalSaddleNegativeOrbit t ht hindex .negative ≠
      D.chronologicalSaddleNegativeOrbit t ht hindex .positive)
    (b : SaddleBranch) :
    Nonempty (SaddleCriticalExteriorArc
      (fun p => (D.position.eventModel t ht).saddleCriticalBoundaryEnd p
        (D.chronologicalSaddleBoundaryRadius t ht))
      (StandardMorseEventAt.puncturedCriticalSlice
        D.signedOutput.cobordism (D.position.eventCenter t ht))
      (SaddleBranch.negative, b) (SaddleBranch.positive, b)) := by
  classical
  let T := D.chronologicalEventEmbeddedShrink t ht
  let Q := D.chronologicalSaddleRecoveryScale t ht L
  let cs : ℝ := Q.scale
  let r := D.chronologicalSaddleBoundaryRadius t ht
  let hreg := D.chronologicalSaddleRecoveryBeforeTime_regular t ht L
  let V := D.chronologicalSaddleRecoveryBeforeField t ht L
  -- transported branch-orbit distinctness
  have hshort : D.chronologicalSaddleRecoveryNegativeOrbit t ht hindex
        L .negative ≠
      D.chronologicalSaddleRecoveryNegativeOrbit t ht hindex L .positive := by
    intro h
    apply hne
    have h2 := congrArg
      (D.chronologicalSaddleRecoveryBeforeToWindowOrbitEquiv t ht L) h
    rwa [D.chronologicalSaddleRecoveryBeforeToWindowOrbitEquiv_branch
        t ht hindex L .negative,
      D.chronologicalSaddleRecoveryBeforeToWindowOrbitEquiv_branch
        t ht hindex L .positive] at h2
  have hOrbNe : T.saddleNegativeBranchOrbitIndex hindex .negative r cs
        (D.chronologicalSaddleBoundaryRadius_pos t ht)
        (D.chronologicalSaddleRecoveryScale_sq_lt_saddleBoundary_sq t ht L)
        (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht) hreg V ≠
      T.saddleNegativeBranchOrbitIndex hindex .positive r cs
        (D.chronologicalSaddleBoundaryRadius_pos t ht)
        (D.chronologicalSaddleRecoveryScale_sq_lt_saddleBoundary_sq t ht L)
        (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht) hreg V :=
    hshort
  -- the uniform exterior cut of the branch orbit
  have hcut := T.saddleNegativeBranch_exists_uniformExteriorCut hindex b
    r cs (D.chronologicalSaddleBoundaryRadius_pos t ht) Q.scale_pos
    (D.chronologicalSaddleRecoveryScale_sq_lt_saddleBoundary_sq t ht L)
    (D.chronologicalSaddleBoundaryRadius_lt_embedded t ht) hreg V hOrbNe
  let A2 := D.chronologicalSaddleRecoveryNegativeMarking t ht hindex L b
  have hlabne := fun e =>
    SimpleClosedOrbitParam.CyclicMarking.cyclicCutSourceLabel_ne_targetLabel_two
      A2 e
  have harcCut : ∃ e : Fin 2, Nonempty (SaddleCriticalExteriorArc
      (fun p => (D.position.eventModel t ht).saddleCriticalBoundaryEnd p
        (D.chronologicalSaddleBoundaryRadius t ht))
      (StandardMorseEventAt.puncturedCriticalSlice
        D.signedOutput.cobordism (D.position.eventCenter t ht))
      (saddleBranchOfFinTwo (A2.cyclicCutSourceLabel e), b)
      (saddleBranchOfFinTwo (A2.cyclicCutTargetLabel e), b)) := by
    rcases hcut with ⟨hlocal, havoid⟩ | ⟨hlocal, havoid⟩
    · refine ⟨Fin.last 1,
        D.chronologicalSaddleDistinctNegative_cutArc t ht hindex L b
          (Fin.last 1) ?_⟩
      intro u hq hn ho
      rw [SimpleClosedOrbitParam.CyclicMarking.cyclicCutRange_last]
      exact havoid u hq hn ho
    · refine ⟨(0 : Fin 1).castSucc,
        D.chronologicalSaddleDistinctNegative_cutArc t ht hindex L b
          ((0 : Fin 1).castSucc) ?_⟩
      intro u hq hn ho
      rw [SimpleClosedOrbitParam.CyclicMarking.cyclicCutRange_castSucc]
      exact havoid u hq hn ho
  obtain ⟨e, harc⟩ := harcCut
  have h01 : ∀ l : Fin 2, l = 0 ∨ l = 1 := by decide
  rcases h01 (A2.cyclicCutSourceLabel e) with hs | hs <;>
    rcases h01 (A2.cyclicCutTargetLabel e) with htg | htg
  · exact absurd (hs.trans htg.symm) (hlabne e)
  · rw [hs, htg, saddleBranchOfFinTwo_zero, saddleBranchOfFinTwo_one]
      at harc
    exact harc
  · rw [hs, htg, saddleBranchOfFinTwo_one, saddleBranchOfFinTwo_zero]
      at harc
    exact harc.map fun B => B.symm
  · exact absurd (hs.trans htg.symm) (hlabne e)


-- @@ L736-736 verbatim
/-! ## Pairing data existence from parity -/


-- @@ L738-785 verbatim
/-- **Existence of the punctured critical-arc pairing data from parity.**

The oriented cut parity alone produces the full pairing data at the fixed
chronological boundary radius.  If the two positive window branch orbits are
distinct, the positive-slice recovery construction supplies the `flipSecond`
candidate mate arcs; if they coincide, the parity residual forces the two
negative window branch orbits apart and the negative-slice construction
supplies the `flipFirst` candidate mate arcs.  In both cases all uniqueness
and orientation obligations are discharged by the checker separation theorem
from the same parity. -/
theorem nonempty_saddlePuncturedCriticalArcPairingData_of_parity
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (Par : ChronologicalSaddleOrientedCutParity D t ht hindex) :
    Nonempty ((D.position.eventModel t ht).SaddlePuncturedCriticalArcPairingData
      (D.chronologicalSaddleBoundaryRadius t ht)) := by
  classical
  let L := D.chronologicalSaddleEndpointLocalFiberCover t ht
  by_cases hpos : D.chronologicalSaddlePositiveOrbit t ht hindex .negative =
      D.chronologicalSaddlePositiveOrbit t ht hindex .positive
  · -- common positive orbit: parity forces distinct negative orbits
    have hnegne : D.chronologicalSaddleNegativeOrbit t ht hindex .negative ≠
        D.chronologicalSaddleNegativeOrbit t ht hindex .positive :=
      Par.positive_common_excludes_negative hpos
    refine ⟨chronologicalSaddlePairingData_of_parity_of_flipFirst_arcs
      D t ht hindex Par ?_⟩
    rintro ⟨b1, b2⟩
    have harc := D.chronologicalSaddleDistinctNegative_arc t ht hindex L
      hnegne b2
    cases b1 with
    | negative =>
        simpa [saddleBranchEndFlipFirst, SaddleBranch.other] using harc
    | positive =>
        simpa [saddleBranchEndFlipFirst, SaddleBranch.other] using
          harc.map fun B => B.symm
  · -- distinct positive orbits: the positive-slice construction applies
    refine ⟨chronologicalSaddlePairingData_of_parity_of_flipSecond_arcs
      D t ht hindex Par ?_⟩
    rintro ⟨b1, b2⟩
    have harc := D.chronologicalSaddleDistinctPositive_arc t ht hindex L
      hpos b1
    cases b2 with
    | negative =>
        simpa [saddleBranchEndFlipSecond, SaddleBranch.other] using harc
    | positive =>
        simpa [saddleBranchEndFlipSecond, SaddleBranch.other] using
          harc.map fun B => B.symm


-- @@ L787-787 verbatim
end ValueSeparatedSignedMorsePackage


-- @@ L789-789 verbatim
end Submission
