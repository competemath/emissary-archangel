import Submission.ProductionMorseSaddleExteriorSource


-- @@ L3-15 verbatim
/-!
# Quantitative half-core capture at production saddles

The chronological exterior field moves every point by less than half of the
complete event-cover radius during one half crossing.  Consequently, a point
which starts outside the full cover ball reaches the critical slice outside
the concentric half-radius ball.  This argument is purely quantitative and
does not use the definite/saddle classification of the critical fiber.

The final two theorems specialize this estimate to the reduced merge and
split source families.  They are the automatic midpoint facts used when the
saddle exterior core is taken with radius `fiberCoverRadius / 2`.
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
variable {n : ℕ}


-- @@ L29-29 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L30-30 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L32-32 verbatim
variable {X₀ X₁ : FramedLevelSet n}

-- @@ L33-33 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}

-- @@ L34-34 verbatim
variable {SC : SignedFramedLevelCobordism S₀ S₁}


-- @@ L36-36 verbatim
namespace ValueSeparatedSignedMorsePackage


-- @@ L38-102 verbatim
/-- A point in the full-radius exterior slab reaches the critical slice
outside the half-radius cover ball. -/
theorem chronologicalExteriorSlabMidpoint_mem_halfCriticalCore
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    {p : E'}
    (hp : p ∈ D.chronologicalExteriorSlabCore t ht)
    (hptime : tcoord p = D.chronologicalBeforeTime t ht) :
    (D.chronologicalSaddleCriticalExteriorTimeField t ht).base.flow p
        (D.chronologicalWindowRadius t ht ^ 2) ∈
      criticalSliceExteriorCore
        D.signedOutput.cobordism.toLevelCobordismData
        (D.position.eventCenter t ht)
        (tcoord (D.position.eventCenter t ht))
        ((D.position.eventModel t ht).fiberCoverRadius / 2) := by
  let R := D.chronologicalExteriorSlabTimeField t ht
  let s := D.chronologicalWindowRadius t ht ^ 2
  change R.base.flow p s ∈ criticalSliceExteriorCore
    D.signedOutput.cobordism.toLevelCobordismData
    (D.position.eventCenter t ht)
    (tcoord (D.position.eventCenter t ht))
    ((D.position.eventModel t ht).fiberCoverRadius / 2)
  have hsafe : |s| ≤ R.safeTime := by
    simpa [R, s, chronologicalCriticalExteriorTimeField] using
      D.chronologicalWindowRadius_sq_le_safeTime t ht
  have hp' := hp
  rw [chronologicalExteriorSlabCore] at hp'
  have hpfiber : p ∈
      D.signedOutput.cobordism.toLevelCobordismData.fiber :=
    hp'.1.1
  have hyfiber : R.base.flow p s ∈
      D.signedOutput.cobordism.toLevelCobordismData.fiber :=
    R.flow_mem_fiber hpfiber s
  have hytime : tcoord (R.base.flow p s) =
      tcoord (D.position.eventCenter t ht) := by
    calc
      tcoord (R.base.flow p s) = tcoord p + s := R.tcoord_flow hp hsafe
      _ = tcoord (D.position.eventCenter t ht) := by
        rw [hptime]
        simp only [chronologicalBeforeTime]
        dsimp [s]
        ring
  have hmove : dist p (R.base.flow p s) ≤
      (R.base.bound : ℝ) * s := by
    calc
      dist p (R.base.flow p s) =
          dist (R.base.flow p 0) (R.base.flow p s) := by simp
      _ ≤ (R.base.bound : ℝ) * |0 - s| :=
        R.base.dist_flow_self_le p 0 s
      _ = (R.base.bound : ℝ) * s := by
        rw [sub_eq_neg_add, add_zero, abs_neg,
          abs_of_nonneg (sq_nonneg _)]
  have hmoveShort : (R.base.bound : ℝ) * s <
      (D.position.eventModel t ht).fiberCoverRadius / 2 := by
    simpa [R, s, chronologicalCriticalExteriorTimeField] using
      D.chronologicalWindowRadius_flowDistance_lt_half_cover t ht
  have hpFar : (D.position.eventModel t ht).fiberCoverRadius ≤
      dist p (D.position.eventCenter t ht) := hp'.2
  have htriangle := dist_triangle p (R.base.flow p s)
    (D.position.eventCenter t ht)
  have hyFar : (D.position.eventModel t ht).fiberCoverRadius / 2 ≤
      dist (R.base.flow p s) (D.position.eventCenter t ht) := by
    nlinarith
  rw [mem_criticalSliceExteriorCore]
  exact ⟨hyfiber, hytime, hyFar⟩


-- @@ L104-168 verbatim
/-- Reverse-time analogue: a full-radius exterior point on the later slice
reaches the same half-radius critical exterior under time `-radius²`. -/
theorem chronologicalExteriorSlabReverseMidpoint_mem_halfCriticalCore
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    {p : E'}
    (hp : p ∈ D.chronologicalExteriorSlabCore t ht)
    (hptime : tcoord p = D.chronologicalAfterTime t ht) :
    (D.chronologicalSaddleCriticalExteriorTimeField t ht).base.flow p
        (-(D.chronologicalWindowRadius t ht ^ 2)) ∈
      criticalSliceExteriorCore
        D.signedOutput.cobordism.toLevelCobordismData
        (D.position.eventCenter t ht)
        (tcoord (D.position.eventCenter t ht))
        ((D.position.eventModel t ht).fiberCoverRadius / 2) := by
  let R := D.chronologicalExteriorSlabTimeField t ht
  let s := D.chronologicalWindowRadius t ht ^ 2
  change R.base.flow p (-s) ∈ criticalSliceExteriorCore
    D.signedOutput.cobordism.toLevelCobordismData
    (D.position.eventCenter t ht)
    (tcoord (D.position.eventCenter t ht))
    ((D.position.eventModel t ht).fiberCoverRadius / 2)
  have hsafe : |-s| ≤ R.safeTime := by
    simpa [R, s, chronologicalCriticalExteriorTimeField] using
      D.chronologicalWindowRadius_sq_le_safeTime t ht
  have hp' := hp
  rw [chronologicalExteriorSlabCore] at hp'
  have hpfiber : p ∈
      D.signedOutput.cobordism.toLevelCobordismData.fiber :=
    hp'.1.1
  have hyfiber : R.base.flow p (-s) ∈
      D.signedOutput.cobordism.toLevelCobordismData.fiber :=
    R.flow_mem_fiber hpfiber (-s)
  have hytime : tcoord (R.base.flow p (-s)) =
      tcoord (D.position.eventCenter t ht) := by
    calc
      tcoord (R.base.flow p (-s)) = tcoord p + (-s) :=
        R.tcoord_flow hp hsafe
      _ = tcoord (D.position.eventCenter t ht) := by
        rw [hptime]
        simp only [chronologicalAfterTime]
        dsimp [s]
        ring
  have hmove : dist p (R.base.flow p (-s)) ≤
      (R.base.bound : ℝ) * s := by
    calc
      dist p (R.base.flow p (-s)) =
          dist (R.base.flow p 0) (R.base.flow p (-s)) := by simp
      _ ≤ (R.base.bound : ℝ) * |0 - (-s)| :=
        R.base.dist_flow_self_le p 0 (-s)
      _ = (R.base.bound : ℝ) * s := by
        rw [sub_neg_eq_add, zero_add, abs_of_nonneg (sq_nonneg _)]
  have hmoveShort : (R.base.bound : ℝ) * s <
      (D.position.eventModel t ht).fiberCoverRadius / 2 := by
    simpa [R, s, chronologicalCriticalExteriorTimeField] using
      D.chronologicalWindowRadius_flowDistance_lt_half_cover t ht
  have hpFar : (D.position.eventModel t ht).fiberCoverRadius ≤
      dist p (D.position.eventCenter t ht) := hp'.2
  have htriangle := dist_triangle p (R.base.flow p (-s))
    (D.position.eventCenter t ht)
  have hyFar : (D.position.eventModel t ht).fiberCoverRadius / 2 ≤
      dist (R.base.flow p (-s)) (D.position.eventCenter t ht) := by
    nlinarith
  rw [mem_criticalSliceExteriorCore]
  exact ⟨hyfiber, hytime, hyFar⟩


-- @@ L170-195 verbatim
/-- Every retained merge-source loop has its midpoint in the automatic
half-radius critical exterior core. -/
theorem chronologicalSaddleMergeHalfCoreMidpointCapture
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle) :
    ∀ (O : {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
          (D.chronologicalSaddleMergeExteriorSourceFamily t ht hindex)})
        (q : I),
      (D.chronologicalSaddleCriticalExteriorTimeField t ht).base.flow
          ((D.chronologicalBeforeField t ht).intrinsicSimpleClosedOrbitParam O.1
            |>.exteriorAmbientLoop q)
          (D.chronologicalWindowRadius t ht ^ 2) ∈
        criticalSliceExteriorCore
          D.signedOutput.cobordism.toLevelCobordismData
          (D.position.eventCenter t ht)
          (tcoord (D.position.eventCenter t ht))
          ((D.position.eventModel t ht).fiberCoverRadius / 2) := by
  intro O q
  apply D.chronologicalExteriorSlabMidpoint_mem_halfCriticalCore t ht
  · apply D.chronologicalSaddleMergeSourcePoint_mem_exteriorSlabCore
      t ht hindex O
    rw [(D.chronologicalBeforeField t ht).orbitPoint_orbit O.1]
    exact (D.chronologicalBeforeField t ht).intrinsicSimpleClosedOrbitParam
      O.1 |>.curve_mem_orbit q
  · simp [SimpleClosedOrbitParam.exteriorAmbientLoop]


-- @@ L197-226 verbatim
/-- Split analogue.  The topology equality identifies the two negative-side
local branch indices, so deleting one representative makes every retained
source orbit fully exterior. -/
theorem chronologicalSaddleSplitHalfCoreMidpointCapture
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (hbranches :
      D.chronologicalSaddleNegativeOrbit t ht hindex .negative =
        D.chronologicalSaddleNegativeOrbit t ht hindex .positive) :
    ∀ (O : {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
          (D.chronologicalSaddleSplitExteriorSourceFamily t ht hindex)})
        (q : I),
      (D.chronologicalSaddleCriticalExteriorTimeField t ht).base.flow
          ((D.chronologicalBeforeField t ht).intrinsicSimpleClosedOrbitParam O.1
            |>.exteriorAmbientLoop q)
          (D.chronologicalWindowRadius t ht ^ 2) ∈
        criticalSliceExteriorCore
          D.signedOutput.cobordism.toLevelCobordismData
          (D.position.eventCenter t ht)
          (tcoord (D.position.eventCenter t ht))
          ((D.position.eventModel t ht).fiberCoverRadius / 2) := by
  intro O q
  apply D.chronologicalExteriorSlabMidpoint_mem_halfCriticalCore t ht
  · apply D.chronologicalSaddleSplitSourcePoint_mem_exteriorSlabCore
      t ht hindex hbranches O
    rw [(D.chronologicalBeforeField t ht).orbitPoint_orbit O.1]
    exact (D.chronologicalBeforeField t ht).intrinsicSimpleClosedOrbitParam
      O.1 |>.curve_mem_orbit q
  · simp [SimpleClosedOrbitParam.exteriorAmbientLoop]


-- @@ L228-235 verbatim
/-- The quantitative estimate closes the exact merge midpoint contract used
by the production saddle supply; no additional hypothesis is needed. -/
theorem chronologicalSaddleMergeExteriorMidpointCapture
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle) :
    D.ChronologicalSaddleMergeExteriorMidpointCapture t ht hindex :=
  D.chronologicalSaddleMergeHalfCoreMidpointCapture t ht hindex


-- @@ L237-246 verbatim
/-- For a split, the global negative-branch equality already present in the
topology supply is exactly what makes the reduced source family exterior. -/
theorem chronologicalSaddleSplitExteriorMidpointCapture
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (H : D.ChronologicalSaddleSplitTopology t ht hindex) :
    D.ChronologicalSaddleSplitExteriorMidpointCapture t ht hindex :=
  D.chronologicalSaddleSplitHalfCoreMidpointCapture
    t ht hindex H.negative_eq


-- @@ L248-248 verbatim
end ValueSeparatedSignedMorsePackage


-- @@ L250-250 verbatim
end Submission
