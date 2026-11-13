import Submission.ProductionMorseSaddleReverseTransport
import Submission.ProductionMorseSaddleBranchSeparation


-- @@ L4-15 verbatim
/-!
# Automatic noncollision for production saddle transport

Every retained saddle source orbit is outside the complete event-cover ball.
The two half-steps of the canonical exterior flow move it by less than half
of that cover radius in total, whereas the central point of each distinguished
local branch lies strictly inside the half-cover ball.  Hence no transported
exterior orbit can collide with a distinguished branch component.

This closes all three forward and all three reverse noncollision conditions
used by the merge/split cardinality adapters.
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


-- @@ L29-29 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (a + 3))

-- @@ L30-30 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (a + 4))


-- @@ L32-32 verbatim
/-! ## Quantitative two-half separation -/


-- @@ L34-34 verbatim
namespace ValueSeparatedSignedMorsePackage


-- @@ L36-36 verbatim
variable {X₀ X₁ : FramedLevelSet (a + 2)}

-- @@ L37-37 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}

-- @@ L38-38 verbatim
variable {SC : SignedFramedLevelCobordism S₀ S₁}


-- @@ L40-90 verbatim
/-- The chronological-radius construction actually gives a quarter-cover
bound for one half-step.  The older public estimate only recorded the weaker
half-cover consequence needed by definite events. -/
theorem chronologicalWindowRadius_flowDistance_lt_quarter_cover
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    ((D.chronologicalCriticalExteriorTimeField t ht).base.bound : ℝ) *
        D.chronologicalWindowRadius t ht ^ 2 <
      (D.position.eventModel t ht).fiberCoverRadius / 4 := by
  let b : ℝ :=
    ((D.chronologicalCriticalExteriorTimeField t ht).base.bound : ℝ)
  let rho := (D.position.eventModel t ht).fiberCoverRadius
  let q := D.chronologicalExteriorFlowSeparationTime t ht
  let m := min
    (min
      (min (D.chronologicalEventEmbeddedShrink t ht).radius
        (D.position.eventBracket t ht).modelRadius)
      (Real.sqrt
        (D.chronologicalCriticalExteriorTimeField t ht).safeTime))
    (Real.sqrt q)
  have hb : 0 ≤ b :=
    (D.chronologicalCriticalExteriorTimeField t ht).base.bound.coe_nonneg
  have hrho : 0 < rho :=
    (D.position.eventModel t ht).fiberCoverRadius_pos
  have hq : 0 < q := D.chronologicalExteriorFlowSeparationTime_pos t ht
  have hmsqrt : m ≤ Real.sqrt q := min_le_right _ _
  have hm : 0 < m := lt_min
    (lt_min
      (lt_min
        (D.chronologicalEventEmbeddedShrink t ht).radius_pos
        (D.position.eventBracket t ht).modelRadius_pos)
      (Real.sqrt_pos.2
        (D.chronologicalCriticalExteriorTimeField t ht).safeTime_pos))
    (Real.sqrt_pos.2 hq)
  have hmnonneg : 0 ≤ m := hm.le
  have hmsq : m ^ 2 ≤ q := by
    calc
      m ^ 2 ≤ (Real.sqrt q) ^ 2 :=
        (sq_le_sq₀ hmnonneg (Real.sqrt_nonneg q)).2 hmsqrt
      _ = q := Real.sq_sqrt hq.le
  have hhalf : (m / 2) ^ 2 ≤ q / 4 := by
    nlinarith
  have hqeq : q * (b + 1) = rho := by
    dsimp [q, chronologicalExteriorFlowSeparationTime, b, rho]
    exact div_mul_cancel₀ _ (by nlinarith)
  have hbq : b * q < rho := by
    nlinarith
  have hbhalf : b * (m / 2) ^ 2 ≤ b * (q / 4) :=
    mul_le_mul_of_nonneg_left hhalf hb
  change b * (m / 2) ^ 2 < rho / 4
  nlinarith


-- @@ L92-103 verbatim
/-- Both half-steps together move by less than half the cover radius. -/
theorem chronologicalWindowRadius_doubleFlowDistance_lt_half_cover
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) :
    ((D.chronologicalCriticalExteriorTimeField t ht).base.bound : ℝ) *
        |2 * D.chronologicalWindowRadius t ht ^ 2| <
      (D.position.eventModel t ht).fiberCoverRadius / 2 := by
  have h := D.chronologicalWindowRadius_flowDistance_lt_quarter_cover t ht
  have hs : 0 ≤ D.chronologicalWindowRadius t ht ^ 2 := sq_nonneg _
  rw [abs_of_nonneg (by positivity :
    0 ≤ 2 * D.chronologicalWindowRadius t ht ^ 2)]
  nlinarith


-- @@ L105-105 verbatim
end ValueSeparatedSignedMorsePackage


-- @@ L107-108 verbatim
/-! A route-independent distance contradiction for a complete two-half
critical-exterior cylinder. -/


-- @@ L110-110 verbatim
namespace CanonicalCriticalExteriorFlowCore


-- @@ L112-112 verbatim
variable {C : LevelCobordismData (a + 2)}

-- @@ L113-113 verbatim
variable {criticalCenter : E'} {t r ε : ℝ}

-- @@ L114-115 verbatim
variable {R : CompactTimeTamedField C
  (criticalSliceExteriorCore C criticalCenter t r)}

-- @@ L116-116 verbatim
variable {hneg : sliceRegular C.G (t - ε)}

-- @@ L117-117 verbatim
variable {hpos : sliceRegular C.G (t + ε)}

-- @@ L118-119 verbatim
variable {Vneg : TamedField
  (SlabTamedField.sliceFLSAt C (t - ε) hneg)}

-- @@ L120-121 verbatim
variable {Vpos : TamedField
  (SlabTamedField.sliceFLSAt C (t + ε) hpos)}

-- @@ L122-122 verbatim
variable {A : Set (Set E₁)}


-- @@ L124-171 verbatim
/-- An exterior source at distance at least `2r` cannot be transported onto
a component containing a point strictly inside the `r`-ball when the total
two-half displacement is less than `r`. -/
theorem targetOrbit_ne_of_source_far_and_inner_point
    (H : CanonicalCriticalExteriorFlowCore (a + 2))
    (O : {O // O ∈ H.Vneg.selectedOrbitFinset H.A})
    (Q : Set E₁) (p : E')
    (hpQ : spacePart p ∈ Q)
    (hptime : tcoord p = H.t + H.ε)
    (hpclose : dist p H.criticalCenter < H.r)
    (hsourceFar : ∀ q : I,
      2 * H.r ≤ dist ((H.negativeParam O).exteriorAmbientLoop q)
        H.criticalCenter)
    (hmove : (H.R.base.bound : ℝ) * |2 * H.ε| < H.r) :
    ((H.targetOrbit O : H.Vpos.OrbitIndex) : Set E₁) ≠ Q := by
  intro hcollision
  have hpTarget : spacePart p ∈
      ((H.targetOrbit O : H.Vpos.OrbitIndex) : Set E₁) := by
    rw [hcollision]
    exact hpQ
  rw [H.targetOrbit_coe O] at hpTarget
  obtain ⟨q, hq⟩ :=
    (H.positiveParam O).exists_curve_eq_of_mem_orbit hpTarget
  change H.positiveCurve O q = spacePart p at hq
  have hend : H.R.base.flow (H.coreLoop O q) H.ε = p := by
    calc
      H.R.base.flow (H.coreLoop O q) H.ε =
          cobSpaceTime (H.positiveCurve O q) (H.t + H.ε) := by
        rw [← H.positiveEndpoint_time O q]
        exact (spaceTime_spacePart _).symm
      _ = cobSpaceTime (spacePart p) (tcoord p) := by rw [hq, hptime]
      _ = p := spaceTime_spacePart p
  let x := (H.negativeParam O).exteriorAmbientLoop q
  have hflow2 : H.R.base.flow x (2 * H.ε) = p := by
    calc
      H.R.base.flow x (2 * H.ε) =
          H.R.base.flow (H.R.base.flow x H.ε) H.ε := by
        simpa [two_mul] using
          (congrFun (H.R.base.flow_shift x H.ε) H.ε).symm
      _ = p := by
        change H.R.base.flow (H.coreLoop O q) H.ε = p
        exact hend
  have hdist : dist x p ≤ (H.R.base.bound : ℝ) * |2 * H.ε| := by
    rw [← hflow2]
    simpa using H.R.base.dist_flow_self_le x 0 (2 * H.ε)
  have htriangle := dist_triangle x p H.criticalCenter
  have hfar := hsourceFar q
  nlinarith


-- @@ L173-173 verbatim
end CanonicalCriticalExteriorFlowCore


-- @@ L175-175 verbatim
/-! ## Forward merge/split noncollision -/


-- @@ L177-177 verbatim
namespace ValueSeparatedSignedMorsePackage


-- @@ L179-179 verbatim
variable {X₀ X₁ : FramedLevelSet (a + 2)}

-- @@ L180-180 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}

-- @@ L181-181 verbatim
variable {SC : SignedFramedLevelCobordism S₀ S₁}


-- @@ L183-256 verbatim
/-- A merge exterior cylinder cannot hit either positive local branch. -/
theorem chronologicalSaddleMergeForwardTargetOrbit_ne_branch
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (O : {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
      (D.chronologicalSaddleMergeExteriorSourceFamily t ht hindex)})
    (b : SaddleBranch) :
    (((D.chronologicalSaddleMergeExteriorFlowCore t ht hindex
      (D.chronologicalWindowRadius_sq_le_safeTime t ht)
      (D.chronologicalSaddleMergeExteriorMidpointCapture t ht hindex)
      ).targetOrbit O : (D.chronologicalAfterField t ht).OrbitIndex) :
        Set E₁) ≠
      ((D.chronologicalSaddlePositiveOrbit t ht hindex b :
        (D.chronologicalAfterField t ht).OrbitIndex) : Set E₁) := by
  let hm := D.chronologicalSaddleMergeExteriorMidpointCapture t ht hindex
  let H := D.chronologicalSaddleMergeExteriorFlowCore t ht hindex
    (D.chronologicalWindowRadius_sq_le_safeTime t ht) hm
  let p : E' := (D.position.eventModel t ht).saddlePositiveBranch b
    (D.chronologicalWindowRadius t ht) 0
  apply H.targetOrbit_ne_of_source_far_and_inner_point O
    ((D.chronologicalSaddlePositiveOrbit t ht hindex b :
      (D.chronologicalAfterField t ht).OrbitIndex) : Set E₁) p
  · exact D.chronologicalSaddlePositiveBranch_mem_distinguishedOrbit
      t ht hindex b
  · have hu : ‖pairToMorseParam (saddlePositiveArc b
          (D.chronologicalWindowRadius t ht) 0)‖ <
        (D.position.eventModel t ht).radius := by
      have hsq := norm_pairToMorseParam_saddlePositiveArc_sq b
        (D.chronologicalWindowRadius t ht) 0
      have hnonneg : 0 ≤ ‖pairToMorseParam (saddlePositiveArc b
          (D.chronologicalWindowRadius t ht) 0)‖ := norm_nonneg _
      have hnorm : ‖pairToMorseParam (saddlePositiveArc b
          (D.chronologicalWindowRadius t ht) 0)‖ =
          D.chronologicalWindowRadius t ht := by
        norm_num at hsq
        nlinarith [D.chronologicalWindowRadius_pos t ht]
      rw [hnorm]
      exact (D.chronologicalWindowRadius_lt_embedded t ht).trans_le
        (D.chronologicalEventEmbeddedShrink t ht).radius_le
    have hpTime : tcoord p = D.chronologicalAfterTime t ht := by
      calc
        tcoord p = tcoord (D.position.eventCenter t ht) +
            D.chronologicalWindowRadius t ht ^ 2 :=
          (D.position.eventModel t ht).saddlePositiveBranch_time
            hindex b (D.chronologicalWindowRadius t ht) 0 hu
        _ = D.chronologicalAfterTime t ht := rfl
    calc
      tcoord p = D.chronologicalAfterTime t ht := hpTime
      _ = H.t + H.ε := rfl
  · exact D.chronologicalSaddlePositiveBranch_dist_lt_half_cover t ht b
  · intro q
    have hx : (H.negativeParam O).exteriorAmbientLoop q ∈
        D.chronologicalExteriorSlabCore t ht := by
      apply D.chronologicalSaddleMergeSourcePoint_mem_exteriorSlabCore
        t ht hindex O
      rw [(D.chronologicalBeforeField t ht).orbitPoint_orbit O.1]
      exact (H.negativeParam O).curve_mem_orbit q
    rw [chronologicalExteriorSlabCore] at hx
    have hr : H.r =
        (D.position.eventModel t ht).fiberCoverRadius / 2 := rfl
    calc
      2 * H.r = (D.position.eventModel t ht).fiberCoverRadius := by
        rw [hr]
        ring
      _ ≤ dist ((H.negativeParam O).exteriorAmbientLoop q)
          (D.position.eventCenter t ht) := hx.2
      _ = dist ((H.negativeParam O).exteriorAmbientLoop q)
          H.criticalCenter := rfl
  · change
      ((D.chronologicalCriticalExteriorTimeField t ht).base.bound : ℝ) *
          |2 * D.chronologicalWindowRadius t ht ^ 2| <
        (D.position.eventModel t ht).fiberCoverRadius / 2
    exact D.chronologicalWindowRadius_doubleFlowDistance_lt_half_cover t ht


-- @@ L258-333 verbatim
/-- A split exterior cylinder cannot hit either positive local branch. -/
theorem chronologicalSaddleSplitForwardTargetOrbit_ne_branch
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (Htop : D.ChronologicalSaddleSplitTopology t ht hindex)
    (O : {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
      (D.chronologicalSaddleSplitExteriorSourceFamily t ht hindex)})
    (b : SaddleBranch) :
    (((D.chronologicalSaddleSplitExteriorFlowCore t ht hindex
      (D.chronologicalWindowRadius_sq_le_safeTime t ht)
      (D.chronologicalSaddleSplitExteriorMidpointCapture t ht hindex Htop)
      ).targetOrbit O : (D.chronologicalAfterField t ht).OrbitIndex) :
        Set E₁) ≠
      ((D.chronologicalSaddlePositiveOrbit t ht hindex b :
        (D.chronologicalAfterField t ht).OrbitIndex) : Set E₁) := by
  let hm := D.chronologicalSaddleSplitExteriorMidpointCapture
    t ht hindex Htop
  let H := D.chronologicalSaddleSplitExteriorFlowCore t ht hindex
    (D.chronologicalWindowRadius_sq_le_safeTime t ht) hm
  let p : E' := (D.position.eventModel t ht).saddlePositiveBranch b
    (D.chronologicalWindowRadius t ht) 0
  apply H.targetOrbit_ne_of_source_far_and_inner_point O
    ((D.chronologicalSaddlePositiveOrbit t ht hindex b :
      (D.chronologicalAfterField t ht).OrbitIndex) : Set E₁) p
  · exact D.chronologicalSaddlePositiveBranch_mem_distinguishedOrbit
      t ht hindex b
  · have hu : ‖pairToMorseParam (saddlePositiveArc b
          (D.chronologicalWindowRadius t ht) 0)‖ <
        (D.position.eventModel t ht).radius := by
      have hsq := norm_pairToMorseParam_saddlePositiveArc_sq b
        (D.chronologicalWindowRadius t ht) 0
      have hnonneg : 0 ≤ ‖pairToMorseParam (saddlePositiveArc b
          (D.chronologicalWindowRadius t ht) 0)‖ := norm_nonneg _
      have hnorm : ‖pairToMorseParam (saddlePositiveArc b
          (D.chronologicalWindowRadius t ht) 0)‖ =
          D.chronologicalWindowRadius t ht := by
        norm_num at hsq
        nlinarith [D.chronologicalWindowRadius_pos t ht]
      rw [hnorm]
      exact (D.chronologicalWindowRadius_lt_embedded t ht).trans_le
        (D.chronologicalEventEmbeddedShrink t ht).radius_le
    have hpTime : tcoord p = D.chronologicalAfterTime t ht := by
      calc
        tcoord p = tcoord (D.position.eventCenter t ht) +
            D.chronologicalWindowRadius t ht ^ 2 :=
          (D.position.eventModel t ht).saddlePositiveBranch_time
            hindex b (D.chronologicalWindowRadius t ht) 0 hu
        _ = D.chronologicalAfterTime t ht := rfl
    calc
      tcoord p = D.chronologicalAfterTime t ht := hpTime
      _ = H.t + H.ε := rfl
  · exact D.chronologicalSaddlePositiveBranch_dist_lt_half_cover t ht b
  · intro q
    have hx : (H.negativeParam O).exteriorAmbientLoop q ∈
        D.chronologicalExteriorSlabCore t ht := by
      apply D.chronologicalSaddleSplitSourcePoint_mem_exteriorSlabCore
        t ht hindex Htop.negative_eq O
      rw [(D.chronologicalBeforeField t ht).orbitPoint_orbit O.1]
      exact (H.negativeParam O).curve_mem_orbit q
    rw [chronologicalExteriorSlabCore] at hx
    have hr : H.r =
        (D.position.eventModel t ht).fiberCoverRadius / 2 := rfl
    calc
      2 * H.r = (D.position.eventModel t ht).fiberCoverRadius := by
        rw [hr]
        ring
      _ ≤ dist ((H.negativeParam O).exteriorAmbientLoop q)
          (D.position.eventCenter t ht) := hx.2
      _ = dist ((H.negativeParam O).exteriorAmbientLoop q)
          H.criticalCenter := rfl
  · change
      ((D.chronologicalCriticalExteriorTimeField t ht).base.bound : ℝ) *
          |2 * D.chronologicalWindowRadius t ht ^ 2| <
        (D.position.eventModel t ht).fiberCoverRadius / 2
    exact D.chronologicalWindowRadius_doubleFlowDistance_lt_half_cover t ht


-- @@ L335-344 verbatim
/-- The single merge-side forward noncollision is automatic. -/
theorem chronologicalSaddleMergeForwardNoncollision
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle) :
    D.ChronologicalSaddleMergeForwardNoncollision t ht hindex := by
  constructor
  intro O
  exact D.chronologicalSaddleMergeForwardTargetOrbit_ne_branch
    t ht hindex O .negative


-- @@ L346-359 verbatim
/-- Both split-side forward noncollisions are automatic. -/
theorem chronologicalSaddleSplitForwardNoncollision
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (Htop : D.ChronologicalSaddleSplitTopology t ht hindex) :
    D.ChronologicalSaddleSplitForwardNoncollision t ht hindex Htop := by
  constructor
  · intro O
    exact D.chronologicalSaddleSplitForwardTargetOrbit_ne_branch
      t ht hindex Htop O .negative
  · intro O
    exact D.chronologicalSaddleSplitForwardTargetOrbit_ne_branch
      t ht hindex Htop O .positive


-- @@ L361-361 verbatim
/-! ## Reverse merge/split noncollision -/


-- @@ L363-484 verbatim
/-- Generic reverse separation for an after-side exterior orbit.  Endpoint
transport changes only the framed-level-set index, so the same literal ambient
distance contradiction applies. -/
theorem chronologicalSaddleReverseTargetOrbit_ne_branch
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (A : Set (Set E₁))
    (hmidpoint : D.ChronologicalSaddleReverseMidpointCapture t ht A)
    (O : {O // O ∈ (D.chronologicalAfterField t ht).selectedOrbitFinset A})
    (hexterior : (O.1 : Set E₁) ∈
      D.chronologicalExteriorOrbitCollection t ht
        (D.chronologicalAfterTime t ht))
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (b : SaddleBranch) :
    ((D.chronologicalSaddleReverseTargetOrbit t ht A hmidpoint O :
        (D.chronologicalBeforeField t ht).OrbitIndex) : Set E₁) ≠
      ((D.chronologicalSaddleNegativeOrbit t ht hindex b :
        (D.chronologicalBeforeField t ht).OrbitIndex) : Set E₁) := by
  let H := D.chronologicalSaddleReverseExteriorFlowCore t ht A hmidpoint
  let eSource := D.chronologicalSaddleReverseSourceEquiv t ht A
  let eTarget := D.chronologicalSaddleReverseTargetOrbitEquiv t ht
  let OH := eSource O
  let Q := eTarget.symm (H.targetOrbit OH)
  let p : E' := (D.position.eventModel t ht).saddleNegativeBranch b
    (D.chronologicalWindowRadius t ht) 0
  have hcoreNe :
      ((H.targetOrbit OH : H.Vpos.OrbitIndex) : Set E₁) ≠
        ((D.chronologicalSaddleNegativeOrbit t ht hindex b :
          (D.chronologicalBeforeField t ht).OrbitIndex) : Set E₁) := by
    apply H.targetOrbit_ne_of_source_far_and_inner_point OH
      ((D.chronologicalSaddleNegativeOrbit t ht hindex b :
        (D.chronologicalBeforeField t ht).OrbitIndex) : Set E₁) p
    · exact D.chronologicalSaddleNegativeBranch_mem_distinguishedOrbit
        t ht hindex b
    · calc
        tcoord p = D.chronologicalBeforeTime t ht :=
          D.chronologicalSaddleNegativeBranch_time t ht hindex b
        _ = H.t + H.ε := rfl
    · exact D.chronologicalSaddleNegativeBranch_dist_lt_half_cover t ht b
    · intro q
      let P := (D.chronologicalAfterField t ht
        |>.intrinsicSimpleClosedOrbitParam O.1)
      have hloop : (H.negativeParam OH).exteriorAmbientLoop q =
          P.exteriorAmbientLoop q := by
        change cobSpaceTime
            ((D.chronologicalSaddleReverseSourceField t ht
              |>.intrinsicSimpleClosedOrbitParam OH.1).curve q)
            (tcoord (D.position.eventCenter t ht) -
              -(D.chronologicalWindowRadius t ht ^ 2)) =
          cobSpaceTime (P.curve q) (D.chronologicalAfterTime t ht)
        apply congrArg₂ cobSpaceTime
        · change
            ((D.chronologicalAfterField t ht).transport
              (D.chronologicalAfterSlice_eq_reverseAfterSlice t ht)
                |>.intrinsicSimpleClosedOrbitParam OH.1).curve q = P.curve q
          calc
            _ = (D.chronologicalAfterField t ht
                  |>.intrinsicSimpleClosedOrbitParam
                    (((D.chronologicalAfterField t ht
                      |>.selectedOrbitTransportEquiv
                        (D.chronologicalAfterSlice_eq_reverseAfterSlice t ht)
                        A).symm OH).1)).curve q :=
              (D.chronologicalAfterField t ht).transportedIntrinsicCurve_symm
                (D.chronologicalAfterSlice_eq_reverseAfterSlice t ht)
                A OH q
            _ = P.curve q := by
              have hO : (D.chronologicalAfterField t ht
                  |>.selectedOrbitTransportEquiv
                    (D.chronologicalAfterSlice_eq_reverseAfterSlice t ht) A
                  ).symm OH = O := by
                change eSource.symm OH = O
                exact eSource.symm_apply_apply O
              rw [hO]
        · exact D.chronologicalReverseAfterTime_eq t ht
      have hx : P.exteriorAmbientLoop q ∈
          D.chronologicalExteriorSlabCore t ht := by
        apply D.chronologicalOrbitPoint_mem_exteriorSlabCore
          t ht (D.chronologicalAfterTime t ht)
          ⟨(D.chronologicalAfterTime_mem_bracket t ht).1.le,
            (D.chronologicalAfterTime_mem_bracket t ht).2.le⟩
          (D.chronologicalAfterTime_regular t ht)
          (D.chronologicalAfterField t ht) O.1
        · rw [(D.chronologicalAfterField t ht).orbitPoint_orbit O.1]
          exact P.curve_mem_orbit q
        · exact hexterior
      rw [chronologicalExteriorSlabCore] at hx
      have hr : H.r =
          (D.position.eventModel t ht).fiberCoverRadius / 2 := rfl
      calc
        2 * H.r = (D.position.eventModel t ht).fiberCoverRadius := by
          rw [hr]
          ring
        _ ≤ dist (P.exteriorAmbientLoop q)
            (D.position.eventCenter t ht) := hx.2
        _ = dist ((H.negativeParam OH).exteriorAmbientLoop q)
            H.criticalCenter := by
          change dist (P.exteriorAmbientLoop q)
              (D.position.eventCenter t ht) =
            dist ((H.negativeParam OH).exteriorAmbientLoop q)
              (D.position.eventCenter t ht)
          rw [hloop]
    · change
        ((D.chronologicalCriticalExteriorTimeField t ht).base.bound : ℝ) *
            |2 * (-(D.chronologicalWindowRadius t ht ^ 2))| <
          (D.position.eventModel t ht).fiberCoverRadius / 2
      simpa only [mul_neg, abs_neg] using
        D.chronologicalWindowRadius_doubleFlowDistance_lt_half_cover t ht
  have hQtarget : (Q : Set E₁) =
      ((H.targetOrbit OH : H.Vpos.OrbitIndex) : Set E₁) := by
    change ((((D.chronologicalBeforeField t ht).orbitIndexTransportEquiv
      (D.chronologicalBeforeSlice_eq_reverseBeforeSlice t ht)).symm
        (H.targetOrbit OH) :
          (D.chronologicalBeforeField t ht).OrbitIndex) : Set E₁) = _
    exact (D.chronologicalBeforeField t ht).orbitIndexTransportEquiv_symm_val
      (D.chronologicalBeforeSlice_eq_reverseBeforeSlice t ht)
      (H.targetOrbit OH)
  change (Q : Set E₁) ≠
    ((D.chronologicalSaddleNegativeOrbit t ht hindex b :
      (D.chronologicalBeforeField t ht).OrbitIndex) : Set E₁)
  intro hcollision
  apply hcoreNe
  exact hQtarget.symm.trans hcollision


-- @@ L486-509 verbatim
/-- Both merge-side reverse noncollisions are automatic. -/
theorem chronologicalSaddleMergeReverseNoncollision
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (Htop : D.ChronologicalSaddleMergeTopology t ht hindex) :
    D.ChronologicalSaddleMergeReverseNoncollision t ht hindex Htop := by
  constructor
  · intro O
    have hexterior := D.chronologicalSaddleMergeTargetOrbit_mem_exterior
      t ht hindex Htop O.1
      (((D.chronologicalAfterField t ht).mem_selectedOrbitFinset O.1).mp O.2)
    exact D.chronologicalSaddleReverseTargetOrbit_ne_branch t ht
      (D.chronologicalSaddleMergeExteriorTargetFamily t ht hindex)
      (D.chronologicalSaddleMergeReverseMidpointCapture t ht hindex Htop)
      O hexterior hindex .negative
  · intro O
    have hexterior := D.chronologicalSaddleMergeTargetOrbit_mem_exterior
      t ht hindex Htop O.1
      (((D.chronologicalAfterField t ht).mem_selectedOrbitFinset O.1).mp O.2)
    exact D.chronologicalSaddleReverseTargetOrbit_ne_branch t ht
      (D.chronologicalSaddleMergeExteriorTargetFamily t ht hindex)
      (D.chronologicalSaddleMergeReverseMidpointCapture t ht hindex Htop)
      O hexterior hindex .positive


-- @@ L511-525 verbatim
/-- The single split-side reverse noncollision is automatic. -/
theorem chronologicalSaddleSplitReverseNoncollision
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle) :
    D.ChronologicalSaddleSplitReverseNoncollision t ht hindex := by
  constructor
  intro O
  have hexterior := D.chronologicalSaddleSplitTargetOrbit_mem_exterior
    t ht hindex O.1
    (((D.chronologicalAfterField t ht).mem_selectedOrbitFinset O.1).mp O.2)
  exact D.chronologicalSaddleReverseTargetOrbit_ne_branch t ht
    (D.chronologicalSaddleSplitExteriorTargetFamily t ht hindex)
    (D.chronologicalSaddleSplitReverseMidpointCapture t ht hindex)
    O hexterior hindex .negative


-- @@ L527-527 verbatim
/-! ## Noncollision-free completion adapters -/


-- @@ L529-540 verbatim
/-- Merge exterior component balance now follows from topology alone. -/
def chronologicalSaddleMergeAutomaticExteriorComponentBalance
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (Htop : D.ChronologicalSaddleMergeTopology t ht hindex) :
    D.ChronologicalSaddleMergeExteriorComponentBalance t ht hindex
      (D.chronologicalSaddleMergeExteriorMidpointCapture t ht hindex) :=
  D.chronologicalSaddleMergeExteriorComponentBalance_of_transports
    t ht hindex Htop
    (D.chronologicalSaddleMergeForwardNoncollision t ht hindex)
    (D.chronologicalSaddleMergeReverseNoncollision t ht hindex Htop)


-- @@ L542-554 verbatim
/-- Split exterior component balance now follows from topology alone. -/
def chronologicalSaddleSplitAutomaticExteriorComponentBalance
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (Htop : D.ChronologicalSaddleSplitTopology t ht hindex) :
    D.ChronologicalSaddleSplitExteriorComponentBalance t ht hindex
      (D.chronologicalSaddleSplitExteriorMidpointCapture
        t ht hindex Htop) :=
  D.chronologicalSaddleSplitExteriorComponentBalance_of_transports
    t ht hindex Htop
    (D.chronologicalSaddleSplitForwardNoncollision t ht hindex Htop)
    (D.chronologicalSaddleSplitReverseNoncollision t ht hindex)


-- @@ L556-569 verbatim
/-- After automatic noncollision, a merge balanced supply requires only the
global merge topology and actual three-orbit frame splice. -/
def chronologicalSaddleMergeBalancedSupply_of_topologyAndFrame
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (Htop : D.ChronologicalSaddleMergeTopology t ht hindex)
    (hframe : D.ChronologicalSaddleMergeActualFrameClassSupply
      t ht hindex) :
    D.ChronologicalSaddleMergeBalancedSupply t ht hindex where
  topology := Htop
  exterior := D.chronologicalSaddleMergeAutomaticExteriorComponentBalance
    t ht hindex Htop
  frame := hframe


-- @@ L571-583 verbatim
/-- Split counterpart: only topology and the actual frame splice remain. -/
def chronologicalSaddleSplitBalancedSupply_of_topologyAndFrame
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (Htop : D.ChronologicalSaddleSplitTopology t ht hindex)
    (hframe : D.ChronologicalSaddleSplitActualFrameClassSupply
      t ht hindex) :
    D.ChronologicalSaddleSplitBalancedSupply t ht hindex where
  topology := Htop
  exterior := D.chronologicalSaddleSplitAutomaticExteriorComponentBalance
    t ht hindex Htop
  frame := hframe


-- @@ L585-585 verbatim
end ValueSeparatedSignedMorsePackage


-- @@ L587-587 verbatim
end Submission
