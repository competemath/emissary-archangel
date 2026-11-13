import Submission.ProductionMorseDefiniteReverseTransport


-- @@ L3-15 verbatim
/-!
# Definite-event exterior/nonlocal separation

The chronological radius now contains two quantitative margins: the local
Morse circle lies in the inner half of the complete-cover ball, while one
half-step of the bounded exterior flow moves by less than the other half.
Consequently a critical-exterior midpoint cannot flow onto the born minimum
circle, in either forward time or the reverse presentation of a maximum.

These two distance contradictions close the last conditional inputs in the
definite-event component balances and construct the uniform `Kmin`/`Kmax`
families without additional geometric hypotheses.
-/


-- @@ L17-17 verbatim
set_option autoImplicit false

-- @@ L18-18 verbatim
set_option maxHeartbeats 2400000


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
open Set Function Metric

-- @@ L23-23 verbatim
open scoped RealInnerProductSpace Topology unitInterval


-- @@ L25-25 verbatim
namespace Submission


-- @@ L27-27 verbatim
variable {a : ℕ}

-- @@ L28-28 verbatim
variable {X₀ X₁ : FramedLevelSet (a + 2)}

-- @@ L29-29 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}

-- @@ L30-30 verbatim
variable {SC : SignedFramedLevelCobordism S₀ S₁}


-- @@ L32-32 verbatim
local notation "Eₐ" => EuclideanSpace ℝ (Fin (a + 3))

-- @@ L33-33 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (a + 4))


-- @@ L35-35 verbatim
namespace ValueSeparatedSignedMorsePackage


-- @@ L37-114 verbatim
/-- A forward exterior cylinder at a minimum cannot land on the born local
circle: its critical midpoint is outside the cover, whereas the local endpoint
and the entire allowed flow displacement together fit strictly inside it. -/
theorem chronologicalMinimumForwardNoncollision
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .minimum) :
    D.ChronologicalMinimumForwardNoncollision t ht hpositive hindex := by
  intro O hcollision
  let F := ChronologicalMinimumExteriorFlowControl.canonical
    (D := D) (t := t) (ht := ht)
    (hpositive := hpositive) (hindex := hindex)
  let H := D.chronologicalMinimumExteriorFlowCore
    t ht F.safe F.midpointCapture
  let L := D.chronologicalMinimumLocalParam t ht hindex
  let p : E' := (D.position.eventModel t ht).definiteCircle
    (D.chronologicalWindowRadius t ht) 0
  have hpL : spacePart p = L.p := by
    change spacePart ((D.position.eventModel t ht).definiteCircle
        (D.chronologicalWindowRadius t ht) 0) =
      spacePart ((D.position.eventModel t ht).definiteCircle
        (D.chronologicalWindowRadius t ht)
        (2 * Real.pi * (((0 : I) : ℝ))))
    norm_num
  have hpTarget : L.p ∈ (H.targetOrbit O : Set Eₐ) := by
    rw [hcollision]
    change L.p ∈ (D.chronologicalMinimumLocalField t ht).orbit L.p
    exact (D.chronologicalMinimumLocalField t ht).mem_orbit_self L.p
  rw [H.targetOrbit_coe O] at hpTarget
  obtain ⟨q, hq⟩ :=
    (H.positiveParam O).exists_curve_eq_of_mem_orbit hpTarget
  change H.positiveCurve O q = L.p at hq
  have hend : H.R.base.flow (H.coreLoop O q) H.ε = p := by
    calc
      H.R.base.flow (H.coreLoop O q) H.ε =
          cobSpaceTime (H.positiveCurve O q) (H.t + H.ε) := by
        rw [← H.positiveEndpoint_time O q]
        exact (spaceTime_spacePart _).symm
      _ = cobSpaceTime L.p (D.chronologicalAfterTime t ht) := by
        rw [hq]
        rfl
      _ = p := by
        rw [← hpL, chronologicalAfterTime]
        rw [← (D.position.eventModel t ht).minimumCircle_time hindex
          (theta := 0) (D.chronologicalWindowRadius_pos t ht).le
          ((D.chronologicalWindowRadius_lt_embedded t ht).trans_le
            (D.chronologicalEventEmbeddedShrink t ht).radius_le)]
        exact spaceTime_spacePart p
  have hyfar : (D.position.eventModel t ht).fiberCoverRadius ≤
      dist (H.coreLoop O q) (D.position.eventCenter t ht) :=
    (mem_criticalSliceExteriorCore H.C H.criticalCenter
      (H.coreLoop O q) H.t H.r).mp (H.coreLoop_mem O q) |>.2.2
  have hmove : dist (H.coreLoop O q) p ≤
      (H.R.base.bound : ℝ) * D.chronologicalWindowRadius t ht ^ 2 := by
    calc
      dist (H.coreLoop O q) p =
          dist (H.R.base.flow (H.coreLoop O q) 0)
            (H.R.base.flow (H.coreLoop O q) H.ε) := by
        simp [hend]
      _ ≤ (H.R.base.bound : ℝ) * |0 - H.ε| :=
        H.R.base.dist_flow_self_le (H.coreLoop O q) 0 H.ε
      _ = (H.R.base.bound : ℝ) *
          D.chronologicalWindowRadius t ht ^ 2 := by
        rw [show H.ε = D.chronologicalWindowRadius t ht ^ 2 by rfl]
        rw [sub_eq_neg_add, add_zero, abs_neg,
          abs_of_nonneg (sq_nonneg _)]
  have hpclose : dist p (D.position.eventCenter t ht) <
      (D.position.eventModel t ht).fiberCoverRadius / 2 :=
    D.chronologicalDefiniteCircle_dist_lt_half_cover t ht 0
  have hmoveshort : (H.R.base.bound : ℝ) *
        D.chronologicalWindowRadius t ht ^ 2 <
      (D.position.eventModel t ht).fiberCoverRadius / 2 :=
    D.chronologicalWindowRadius_flowDistance_lt_half_cover t ht
  have htriangle := dist_triangle (H.coreLoop O q) p
    (D.position.eventCenter t ht)
  nlinarith


-- @@ L116-203 verbatim
/-- In the reverse presentation of a maximum, an exterior cylinder cannot hit
the dying local circle.  Transport of orbit indices preserves their underlying
sets, so the same cover-distance contradiction applies verbatim. -/
theorem chronologicalMaximumReverseNoncollision
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .maximum) :
    D.ChronologicalMaximumReverseNoncollision t ht hpositive hindex := by
  intro O hcollision
  let H := D.chronologicalMaximumReverseExteriorFlowCore t ht hindex
  let eSource := D.chronologicalMaximumReverseSourceEquiv t ht
  let eTarget := D.chronologicalMaximumReverseTargetOrbitEquiv t ht
  let OH := eSource O
  let Q := eTarget.symm (H.targetOrbit OH)
  let V := D.chronologicalMaximumLocalField t ht
  let L := D.chronologicalMaximumLocalParam t ht hindex
  let p : E' := (D.position.eventModel t ht).definiteCircle
    (D.chronologicalWindowRadius t ht) 0
  have hpL : spacePart p = L.p := by
    change spacePart ((D.position.eventModel t ht).definiteCircle
        (D.chronologicalWindowRadius t ht) 0) =
      spacePart ((D.position.eventModel t ht).definiteCircle
        (D.chronologicalWindowRadius t ht)
        (2 * Real.pi * (((0 : I) : ℝ))))
    norm_num
  have hpQ : L.p ∈ (Q : Set Eₐ) := by
    change L.p ∈
      (D.chronologicalMaximumReverseTargetOrbit t ht hindex O : Set Eₐ)
    rw [hcollision]
    change L.p ∈ V.orbit L.p
    exact V.mem_orbit_self L.p
  have hQtarget : (Q : Set Eₐ) = (H.targetOrbit OH : Set Eₐ) := by
    change ((((V.orbitIndexTransportEquiv
      (D.chronologicalBeforeSlice_eq_reverseBeforeSlice t ht)).symm
        (H.targetOrbit OH)) : V.OrbitIndex) : Set Eₐ) = _
    exact V.orbitIndexTransportEquiv_symm_val
      (D.chronologicalBeforeSlice_eq_reverseBeforeSlice t ht)
      (H.targetOrbit OH)
  rw [hQtarget, H.targetOrbit_coe OH] at hpQ
  obtain ⟨q, hq⟩ :=
    (H.positiveParam OH).exists_curve_eq_of_mem_orbit hpQ
  change H.positiveCurve OH q = L.p at hq
  have hend : H.R.base.flow (H.coreLoop OH q) H.ε = p := by
    calc
      H.R.base.flow (H.coreLoop OH q) H.ε =
          cobSpaceTime (H.positiveCurve OH q) (H.t + H.ε) := by
        rw [← H.positiveEndpoint_time OH q]
        exact (spaceTime_spacePart _).symm
      _ = cobSpaceTime L.p (D.chronologicalBeforeTime t ht) := by
        rw [hq]
        rfl
      _ = p := by
        rw [← hpL, chronologicalBeforeTime]
        rw [← (D.position.eventModel t ht).maximumCircle_time hindex
          (theta := 0) (D.chronologicalWindowRadius_pos t ht).le
          ((D.chronologicalWindowRadius_lt_embedded t ht).trans_le
            (D.chronologicalEventEmbeddedShrink t ht).radius_le)]
        exact spaceTime_spacePart p
  have hyfar : (D.position.eventModel t ht).fiberCoverRadius ≤
      dist (H.coreLoop OH q) (D.position.eventCenter t ht) :=
    (mem_criticalSliceExteriorCore H.C H.criticalCenter
      (H.coreLoop OH q) H.t H.r).mp (H.coreLoop_mem OH q) |>.2.2
  have hmove : dist (H.coreLoop OH q) p ≤
      (H.R.base.bound : ℝ) * D.chronologicalWindowRadius t ht ^ 2 := by
    calc
      dist (H.coreLoop OH q) p =
          dist (H.R.base.flow (H.coreLoop OH q) 0)
            (H.R.base.flow (H.coreLoop OH q) H.ε) := by
        simp [hend]
      _ ≤ (H.R.base.bound : ℝ) * |0 - H.ε| :=
        H.R.base.dist_flow_self_le (H.coreLoop OH q) 0 H.ε
      _ = (H.R.base.bound : ℝ) *
          D.chronologicalWindowRadius t ht ^ 2 := by
        rw [show H.ε = -(D.chronologicalWindowRadius t ht ^ 2) by rfl]
        rw [sub_neg_eq_add, zero_add,
          abs_of_nonneg (sq_nonneg _)]
  have hpclose : dist p (D.position.eventCenter t ht) <
      (D.position.eventModel t ht).fiberCoverRadius / 2 :=
    D.chronologicalDefiniteCircle_dist_lt_half_cover t ht 0
  have hmoveshort : (H.R.base.bound : ℝ) *
        D.chronologicalWindowRadius t ht ^ 2 <
      (D.position.eventModel t ht).fiberCoverRadius / 2 :=
    D.chronologicalWindowRadius_flowDistance_lt_half_cover t ht
  have htriangle := dist_triangle (H.coreLoop OH q) p
    (D.position.eventCenter t ht)
  nlinarith


-- @@ L205-205 verbatim
end ValueSeparatedSignedMorsePackage


-- @@ L207-207 verbatim
/-! ## Unconditional uniform definite-event cardinality kits -/


-- @@ L209-213 verbatim
theorem productionMorseMinimumForwardNoncollisions (a : ℕ) :
    ProductionMorseMinimumForwardNoncollisions a := by
  intro X Y S T C D t ht hpositive hindex
  exact D.chronologicalMinimumForwardNoncollision
    t ht hpositive hindex


-- @@ L215-219 verbatim
theorem productionMorseMaximumReverseNoncollisions (a : ℕ) :
    ProductionMorseMaximumReverseNoncollisions a := by
  intro X Y S T C D t ht hpositive hindex
  exact D.chronologicalMaximumReverseNoncollision
    t ht hpositive hindex


-- @@ L221-226 verbatim
/-- Actual dimension-uniform minimum cardinality kits, with the noncollision
and cardinality balance both derived from the canonical flow. -/
theorem productionMorseMinimumExteriorCardinalityKits {a : ℕ} :
    ProductionMorseMinimumExteriorCardinalityKits a :=
  productionMorseMinimumExteriorCardinalityKits_of_forward_noncollision
    (productionMorseMinimumForwardNoncollisions a)


-- @@ L228-233 verbatim
/-- Actual dimension-uniform maximum cardinality kits, derived by the reverse
canonical flow. -/
theorem productionMorseMaximumExteriorCardinalityKits {a : ℕ} :
    ProductionMorseMaximumExteriorCardinalityKits a :=
  productionMorseMaximumExteriorCardinalityKits_of_reverse_noncollision
    (productionMorseMaximumReverseNoncollisions a)


-- @@ L235-235 verbatim
end Submission
