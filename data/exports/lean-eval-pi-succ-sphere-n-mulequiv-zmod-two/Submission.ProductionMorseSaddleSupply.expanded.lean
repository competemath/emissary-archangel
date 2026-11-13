import Submission.ProductionMorseSaddleFrameClassAdapter


-- @@ L3-23 verbatim
/-!
# Reduced supplies for actual production saddles

The embedded Morse chart canonically selects the four nearby branch orbits,
but it cannot decide their global connectivity or the resulting splice
identity for the complete orbit frames.  This file separates those genuinely
global facts from all data forced by the production flow.

For the exterior tail, the target component is defined by flowing the
intrinsic source parameter.  Injectivity, target positivity, the target base
point, and the component equivalence are then theorems.  The residual contract
contains only midpoint capture, noncollision with the distinguished local
component(s), and surjectivity; safe time follows from the chronological
radius construction.

For the three distinguished frame classes, the only honest remaining fact is
the splice equation for the three actual orbit classes.  The adapter chooses
both auxiliary exterior classes to be zero and constructs a local
`SaddleModelContract` realizing the two actual incoming classes.  Thus no
unattached witness class is exposed as geometric input.
-/


-- @@ L25-25 verbatim
set_option autoImplicit false

-- @@ L26-26 verbatim
set_option maxHeartbeats 2400000


-- @@ L28-28 verbatim
noncomputable section


-- @@ L30-30 verbatim
open Set Function

-- @@ L31-31 verbatim
open scoped unitInterval


-- @@ L33-33 verbatim
namespace Submission


-- @@ L35-35 verbatim
variable {n : ℕ}


-- @@ L37-37 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L38-38 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L40-40 verbatim
/-! ## Canonical local model from the actual incoming classes -/


-- @@ L42-51 verbatim
/-- Choose the two local angle loops to realize the two actual incoming orbit
classes.  Equivalently, this makes the auxiliary exterior classes in the
class-level adapter definitionally zero. -/
def canonicalSaddleModelForActualClasses
    {Xbefore : FramedLevelSet n} (Vbefore : TamedField Xbefore)
    (O₁ O₂ : Vbefore.OrbitIndex) :
    SaddleModelContract :=
  saddleModelContract
    (SO2AngleLoop.ofZModTwo (Vbefore.orbitFrameClass O₁))
    (SO2AngleLoop.ofZModTwo (Vbefore.orbitFrameClass O₂))


-- @@ L53-62 verbatim
/-- Strict-minimal frame supply: the splice equation on the three complete,
actual orbit classes.  The class decomposition and local saddle model built
below are output, not additional hypotheses. -/
structure SaddleActualFrameClassSupply
    {Xbefore Xafter : FramedLevelSet n}
    (Vbefore : TamedField Xbefore) (Vafter : TamedField Xafter)
    (O₁ O₂ : Vbefore.OrbitIndex) (Ohat : Vafter.OrbitIndex) : Prop where
  frame_splice :
    Vafter.orbitFrameClass Ohat =
      Vbefore.orbitFrameClass O₁ + Vbefore.orbitFrameClass O₂ + 1


-- @@ L64-64 verbatim
namespace SaddleActualFrameClassSupply


-- @@ L66-66 verbatim
variable {Xbefore Xafter : FramedLevelSet n}

-- @@ L67-67 verbatim
variable {Vbefore : TamedField Xbefore} {Vafter : TamedField Xafter}

-- @@ L68-68 verbatim
variable {O₁ O₂ : Vbefore.OrbitIndex} {Ohat : Vafter.OrbitIndex}


-- @@ L70-112 verbatim
/-- Expand the one-equation supply into the exterior-relative class interface.
Both exterior classes are definitionally zero; the local incoming angle loops
are chosen to have exactly the two actual incoming classes. -/
def toRelativeFrameClassData
    (F : SaddleActualFrameClassSupply Vbefore Vafter O₁ O₂ Ohat)
    (hn : 2 ≤ n) :
    SaddleRelativeFrameClassData Vbefore Vafter O₁ O₂ Ohat := by
  let M := canonicalSaddleModelForActualClasses Vbefore O₁ O₂
  have hm : 3 ≤ n + 1 := by omega
  have h₁ :
      loopClassZ2 (M.incoming₁.frame (n + 1))
          (M.incoming₁.frame_closed (n + 1)) =
        Vbefore.orbitFrameClass O₁ := by
    simpa [M, canonicalSaddleModelForActualClasses, saddleModelContract] using
      SO2AngleLoop.loopClassZ2_frame_ofZModTwo hm
        (Vbefore.orbitFrameClass O₁)
  have h₂ :
      loopClassZ2 (M.incoming₂.frame (n + 1))
          (M.incoming₂.frame_closed (n + 1)) =
        Vbefore.orbitFrameClass O₂ := by
    simpa [M, canonicalSaddleModelForActualClasses, saddleModelContract] using
      SO2AngleLoop.loopClassZ2_frame_ofZModTwo hm
        (Vbefore.orbitFrameClass O₂)
  exact {
    exterior₁ := 0
    exterior₂ := 0
    model := M
    incoming₁_class := by simpa using h₁.symm
    incoming₂_class := by simpa using h₂.symm
    outgoing_class := by
      rw [zero_add, zero_add]
      calc
        Vafter.orbitFrameClass Ohat =
            Vbefore.orbitFrameClass O₁ +
              Vbefore.orbitFrameClass O₂ + 1 := F.frame_splice
        _ = loopClassZ2 (M.incoming₁.frame (n + 1))
              (M.incoming₁.frame_closed (n + 1)) +
            loopClassZ2 (M.incoming₂.frame (n + 1))
              (M.incoming₂.frame_closed (n + 1)) + 1 := by
          rw [h₁, h₂]
        _ = loopClassZ2 (M.outgoing.frame (n + 1))
              (M.outgoing.frame_closed (n + 1)) :=
          (M.frame_class_splice hm).symm }


-- @@ L114-114 verbatim
end SaddleActualFrameClassSupply


-- @@ L116-116 verbatim
/-! ## Flow-forced saddle exterior components -/


-- @@ L118-118 verbatim
variable {X₀ X₁ : FramedLevelSet n}

-- @@ L119-119 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}

-- @@ L120-120 verbatim
variable {SC : SignedFramedLevelCobordism S₀ S₁}


-- @@ L122-122 verbatim
namespace ValueSeparatedSignedMorsePackage


-- @@ L124-129 verbatim
/-- Safe time for the common two-half exterior cylinder. -/
abbrev ChronologicalSaddleExteriorSafe
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes) : Prop :=
  |D.chronologicalWindowRadius t ht ^ 2| ≤
    (D.chronologicalSaddleCriticalExteriorTimeField t ht).safeTime


-- @@ L131-150 verbatim
/-- Midpoint capture for an arbitrary selected source family on the negative
chronological slice.  The critical core uses half of the complete local-cover
radius.  Incoming exterior points start outside the full cover and the chosen
half crossing moves them by strictly less than half its radius, so this is the
largest uniform concentric core forced by the quantitative construction. -/
abbrev ChronologicalSaddleExteriorMidpointCapture
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (A : Set (Set E₁)) : Prop :=
  ∀ (O : {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset A})
      (q : I),
    (D.chronologicalSaddleCriticalExteriorTimeField t ht).base.flow
        ((D.chronologicalBeforeField t ht).intrinsicSimpleClosedOrbitParam O.1
          |>.exteriorAmbientLoop q)
        (D.chronologicalWindowRadius t ht ^ 2) ∈
      criticalSliceExteriorCore
        D.signedOutput.cobordism.toLevelCobordismData
        (D.position.eventCenter t ht)
        (tcoord (D.position.eventCenter t ht))
        ((D.position.eventModel t ht).fiberCoverRadius / 2)


-- @@ L152-172 verbatim
/-- The flow core common to merge and split tails. -/
def chronologicalSaddleExteriorFlowCore
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (A : Set (Set E₁))
    (hsafe : D.ChronologicalSaddleExteriorSafe t ht)
    (hmidpoint : D.ChronologicalSaddleExteriorMidpointCapture t ht A) :
    CanonicalCriticalExteriorFlowCore n where
  C := D.signedOutput.cobordism.toLevelCobordismData
  criticalCenter := D.position.eventCenter t ht
  t := tcoord (D.position.eventCenter t ht)
  r := (D.position.eventModel t ht).fiberCoverRadius / 2
  ε := D.chronologicalWindowRadius t ht ^ 2
  R := D.chronologicalSaddleCriticalExteriorTimeField t ht
  hneg := D.chronologicalBeforeTime_regular t ht
  hpos := D.chronologicalAfterTime_regular t ht
  Vneg := D.chronologicalBeforeField t ht
  Vpos := D.chronologicalAfterField t ht
  A := A
  safe := hsafe
  midpoint_mem := hmidpoint


-- @@ L174-253 verbatim
/-- Sign transport along the actual two-half flow makes membership of every
forced target orbit in the positive collection automatic. -/
theorem chronologicalSaddleTargetOrbit_mem_positive
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (A : Set (Set E₁))
    (hsafe : D.ChronologicalSaddleExteriorSafe t ht)
    (hmidpoint : D.ChronologicalSaddleExteriorMidpointCapture t ht A)
    (O : {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset A})
    (hsourcePositive : (O.1 : Set E₁) ∈
      D.chronologicalSaddleNegativeCollection t ht) :
    let H := D.chronologicalSaddleExteriorFlowCore
      t ht A hsafe hmidpoint
    H.targetOrbit O ∈
      (D.chronologicalAfterField t ht).selectedOrbitFinset
        (D.chronologicalSaddlePositiveCollection t ht) := by
  let H := D.chronologicalSaddleExteriorFlowCore
    t ht A hsafe hmidpoint
  let Sneg := D.signedOutput.sliceSign (D.chronologicalBeforeTime t ht)
    (D.chronologicalBeforeTime_regular t ht)
  let Spos := D.signedOutput.sliceSign (D.chronologicalAfterTime t ht)
    (D.chronologicalAfterTime_regular t ht)
  change H.targetOrbit O ∈ H.Vpos.selectedOrbitFinset
    (Spos.positiveOrbitCollection H.Vpos)
  let p := (H.negativeParam O).exteriorAmbientLoop 0
  have hsourceSign : 0 < Sneg (H.Vneg.orbitPoint O.1) :=
    (Sneg.mem_positiveOrbitCollection_iff H.Vneg O.1).mp hsourcePositive
  have hpEq : p = cobSpaceTime (H.Vneg.orbitPoint O.1)
      (D.chronologicalBeforeTime t ht) := by
    change cobSpaceTime ((H.negativeParam O).curve 0) (H.t - H.ε) = _
    apply congrArg₂ cobSpaceTime
    · exact H.Vneg.intrinsicOrbitCurve_zero O.1
    · rfl
  have hstartSign : 0 < D.signedOutput p := by
    rw [hpEq]
    exact hsourceSign
  let γ : C(I, E') :=
    ⟨fun u => H.R.base.flow p ((u : ℝ) * (2 * H.ε)),
      (H.R.base.continuous_flow p).comp
        (continuous_subtype_val.mul continuous_const)⟩
  have hpFiber : H.C.G p = 0 :=
    (H.negativeParam O).exteriorAmbientLoop_fiber 0
  have hγFiber : ∀ u, D.signedOutput.cobordism.G (γ u) = 0 := by
    intro u
    exact H.R.flow_mem_fiber hpFiber _
  have hthrough : 0 < D.signedOutput (γ 1) :=
    (D.signedOutput.pos_iff_of_zeroFiber_path γ hγFiber).mp
      (by simpa [γ] using hstartSign)
  have hdouble : H.R.base.flow p (2 * H.ε) =
      H.R.base.flow (H.R.base.flow p H.ε) H.ε := by
    simpa [two_mul] using
      (congrFun (H.R.base.flow_shift p H.ε) H.ε).symm
  have hendSign : 0 < D.signedOutput
      (H.R.base.flow (H.coreLoop O 0) H.ε) := by
    change 0 < D.signedOutput
      (H.R.base.flow (H.R.base.flow p H.ε) H.ε)
    rw [← hdouble]
    simpa [γ] using hthrough
  have hendEq : cobSpaceTime (H.positiveCurve O 0)
      (D.chronologicalAfterTime t ht) =
      H.R.base.flow (H.coreLoop O 0) H.ε := by
    rw [show D.chronologicalAfterTime t ht = H.t + H.ε by rfl]
    rw [← H.positiveEndpoint_time O 0]
    change cobSpaceTime
      (spacePart (H.R.base.flow (H.coreLoop O 0) H.ε))
      (tcoord (H.R.base.flow (H.coreLoop O 0) H.ε)) = _
    exact spaceTime_spacePart _
  have hbaseSign : 0 < Spos (H.positiveCurve O 0) := by
    change 0 < D.signedOutput (cobSpaceTime (H.positiveCurve O 0)
      (D.chronologicalAfterTime t ht))
    rw [hendEq]
    exact hendSign
  apply (H.Vpos.mem_selectedOrbitFinset (H.targetOrbit O)).mpr
  rw [Spos.mem_positiveOrbitCollection_iff]
  have htargetPoint : H.Vpos.orbitPoint (H.targetOrbit O) ∈
      H.Vpos.orbit (H.positiveCurve O 0) := by
    rw [← H.targetOrbit_coe O, H.Vpos.orbitPoint_orbit]
    exact H.Vpos.mem_orbit_self _
  exact (Spos.pos_iff_of_mem_orbit H.Vpos
    (H.positiveCurve_mem_fiber O 0) htargetPoint).mp hbaseSign


-- @@ L255-255 verbatim
/-! ## Merge/split tail families and exact residual completions -/


-- @@ L257-266 verbatim
abbrev chronologicalSaddleMergeExteriorSourceFamily
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle) :
    Set (Set E₁) :=
  (D.chronologicalSaddleNegativeCollection t ht \
    {((D.chronologicalSaddleNegativeOrbit t ht hindex .negative :
      (D.chronologicalBeforeField t ht).OrbitIndex) : Set E₁)}) \
    {((D.chronologicalSaddleNegativeOrbit t ht hindex .positive :
      (D.chronologicalBeforeField t ht).OrbitIndex) : Set E₁)}


-- @@ L268-275 verbatim
abbrev chronologicalSaddleMergeExteriorTargetFamily
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle) :
    Set (Set E₁) :=
  D.chronologicalSaddlePositiveCollection t ht \
    {((D.chronologicalSaddlePositiveOrbit t ht hindex .negative :
      (D.chronologicalAfterField t ht).OrbitIndex) : Set E₁)}


-- @@ L277-284 verbatim
abbrev chronologicalSaddleSplitExteriorSourceFamily
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle) :
    Set (Set E₁) :=
  D.chronologicalSaddleNegativeCollection t ht \
    {((D.chronologicalSaddleNegativeOrbit t ht hindex .negative :
      (D.chronologicalBeforeField t ht).OrbitIndex) : Set E₁)}


-- @@ L286-295 verbatim
abbrev chronologicalSaddleSplitExteriorTargetFamily
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle) :
    Set (Set E₁) :=
  (D.chronologicalSaddlePositiveCollection t ht \
    {((D.chronologicalSaddlePositiveOrbit t ht hindex .negative :
      (D.chronologicalAfterField t ht).OrbitIndex) : Set E₁)}) \
    {((D.chronologicalSaddlePositiveOrbit t ht hindex .positive :
      (D.chronologicalAfterField t ht).OrbitIndex) : Set E₁)}


-- @@ L297-302 verbatim
abbrev ChronologicalSaddleMergeExteriorMidpointCapture
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle) : Prop :=
  D.ChronologicalSaddleExteriorMidpointCapture t ht
    (D.chronologicalSaddleMergeExteriorSourceFamily t ht hindex)


-- @@ L304-309 verbatim
abbrev ChronologicalSaddleSplitExteriorMidpointCapture
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle) : Prop :=
  D.ChronologicalSaddleExteriorMidpointCapture t ht
    (D.chronologicalSaddleSplitExteriorSourceFamily t ht hindex)


-- @@ L311-320 verbatim
def chronologicalSaddleMergeExteriorFlowCore
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (hsafe : D.ChronologicalSaddleExteriorSafe t ht)
    (hmidpoint : D.ChronologicalSaddleMergeExteriorMidpointCapture
      t ht hindex) : CanonicalCriticalExteriorFlowCore n :=
  D.chronologicalSaddleExteriorFlowCore t ht
    (D.chronologicalSaddleMergeExteriorSourceFamily t ht hindex)
    hsafe hmidpoint


-- @@ L322-331 verbatim
def chronologicalSaddleSplitExteriorFlowCore
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (hsafe : D.ChronologicalSaddleExteriorSafe t ht)
    (hmidpoint : D.ChronologicalSaddleSplitExteriorMidpointCapture
      t ht hindex) : CanonicalCriticalExteriorFlowCore n :=
  D.chronologicalSaddleExteriorFlowCore t ht
    (D.chronologicalSaddleSplitExteriorSourceFamily t ht hindex)
    hsafe hmidpoint


-- @@ L333-356 verbatim
/-- Merge-tail residual: no forced exterior target is the distinguished
outgoing component, and every requested target is reached. -/
structure ChronologicalSaddleMergeExteriorCompletion
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (hsafe : D.ChronologicalSaddleExteriorSafe t ht)
    (hmidpoint : D.ChronologicalSaddleMergeExteriorMidpointCapture
      t ht hindex) : Type where
  target_ne_outgoing : ∀
      O : {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
        (D.chronologicalSaddleMergeExteriorSourceFamily t ht hindex)},
    (((D.chronologicalSaddleMergeExteriorFlowCore
      t ht hindex hsafe hmidpoint).targetOrbit O :
        (D.chronologicalAfterField t ht).OrbitIndex) : Set E₁) ≠
      ((D.chronologicalSaddlePositiveOrbit t ht hindex .negative :
        (D.chronologicalAfterField t ht).OrbitIndex) : Set E₁)
  target_surjective : ∀
      Q : {Q // Q ∈ (D.chronologicalAfterField t ht).selectedOrbitFinset
        (D.chronologicalSaddleMergeExteriorTargetFamily t ht hindex)},
    ∃ O : {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
        (D.chronologicalSaddleMergeExteriorSourceFamily t ht hindex)},
      (D.chronologicalSaddleMergeExteriorFlowCore
        t ht hindex hsafe hmidpoint).targetOrbit O = Q.1


-- @@ L358-389 verbatim
/-- Split-tail residual: the forced exterior targets avoid both distinguished
positive-side branches and exhaust their double complement. -/
structure ChronologicalSaddleSplitExteriorCompletion
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (hsafe : D.ChronologicalSaddleExteriorSafe t ht)
    (hmidpoint : D.ChronologicalSaddleSplitExteriorMidpointCapture
      t ht hindex) : Type where
  target_ne_negative : ∀
      O : {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
        (D.chronologicalSaddleSplitExteriorSourceFamily t ht hindex)},
    (((D.chronologicalSaddleSplitExteriorFlowCore
      t ht hindex hsafe hmidpoint).targetOrbit O :
        (D.chronologicalAfterField t ht).OrbitIndex) : Set E₁) ≠
      ((D.chronologicalSaddlePositiveOrbit t ht hindex .negative :
        (D.chronologicalAfterField t ht).OrbitIndex) : Set E₁)
  target_ne_positive : ∀
      O : {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
        (D.chronologicalSaddleSplitExteriorSourceFamily t ht hindex)},
    (((D.chronologicalSaddleSplitExteriorFlowCore
      t ht hindex hsafe hmidpoint).targetOrbit O :
        (D.chronologicalAfterField t ht).OrbitIndex) : Set E₁) ≠
      ((D.chronologicalSaddlePositiveOrbit t ht hindex .positive :
        (D.chronologicalAfterField t ht).OrbitIndex) : Set E₁)
  target_surjective : ∀
      Q : {Q // Q ∈ (D.chronologicalAfterField t ht).selectedOrbitFinset
        (D.chronologicalSaddleSplitExteriorTargetFamily t ht hindex)},
    ∃ O : {O // O ∈ (D.chronologicalBeforeField t ht).selectedOrbitFinset
        (D.chronologicalSaddleSplitExteriorSourceFamily t ht hindex)},
      (D.chronologicalSaddleSplitExteriorFlowCore
        t ht hindex hsafe hmidpoint).targetOrbit O = Q.1


-- @@ L391-417 verbatim
def saddleMergeFlowInducedPairing_of_completion
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (hsafe : D.ChronologicalSaddleExteriorSafe t ht)
    (hmidpoint : D.ChronologicalSaddleMergeExteriorMidpointCapture
      t ht hindex)
    (P : D.ChronologicalSaddleMergeExteriorCompletion
      t ht hindex hsafe hmidpoint) :
    FlowInducedCanonicalCriticalExteriorPairing
      (D.chronologicalSaddleMergeExteriorFlowCore
        t ht hindex hsafe hmidpoint)
      (D.chronologicalSaddleMergeExteriorTargetFamily t ht hindex) where
  target_mem O := by
    apply ((D.chronologicalAfterField t ht).mem_selectedOrbitFinset _).mpr
    have hsource :
        (O.1 : Set E₁) ∈
          D.chronologicalSaddleMergeExteriorSourceFamily t ht hindex :=
      ((D.chronologicalBeforeField t ht).mem_selectedOrbitFinset O.1).mp O.2
    constructor
    · have htargetPositive :=
        D.chronologicalSaddleTargetOrbit_mem_positive
          t ht _ hsafe hmidpoint O hsource.1.1
      exact ((D.chronologicalAfterField t ht).mem_selectedOrbitFinset _).mp
        htargetPositive
    · simpa using P.target_ne_outgoing O
  target_surjective := P.target_surjective


-- @@ L419-447 verbatim
def saddleSplitFlowInducedPairing_of_completion
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (hsafe : D.ChronologicalSaddleExteriorSafe t ht)
    (hmidpoint : D.ChronologicalSaddleSplitExteriorMidpointCapture
      t ht hindex)
    (P : D.ChronologicalSaddleSplitExteriorCompletion
      t ht hindex hsafe hmidpoint) :
    FlowInducedCanonicalCriticalExteriorPairing
      (D.chronologicalSaddleSplitExteriorFlowCore
        t ht hindex hsafe hmidpoint)
      (D.chronologicalSaddleSplitExteriorTargetFamily t ht hindex) where
  target_mem O := by
    apply ((D.chronologicalAfterField t ht).mem_selectedOrbitFinset _).mpr
    have hsource :
        (O.1 : Set E₁) ∈
          D.chronologicalSaddleSplitExteriorSourceFamily t ht hindex :=
      ((D.chronologicalBeforeField t ht).mem_selectedOrbitFinset O.1).mp O.2
    constructor
    · constructor
      · have htargetPositive :=
          D.chronologicalSaddleTargetOrbit_mem_positive
            t ht _ hsafe hmidpoint O hsource.1
        exact ((D.chronologicalAfterField t ht).mem_selectedOrbitFinset _).mp
          htargetPositive
      · simpa using P.target_ne_negative O
    · simpa using P.target_ne_positive O
  target_surjective := P.target_surjective


-- @@ L449-459 verbatim
/-- Flow-induced merge exterior data with every dependent residual separated.
The safe-time inequality is no longer input: the chronological radius was
chosen to satisfy it. -/
abbrev ChronologicalSaddleMergeFlowSupply
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle) :=
  Σ' hmidpoint : D.ChronologicalSaddleMergeExteriorMidpointCapture
    t ht hindex,
    D.ChronologicalSaddleMergeExteriorCompletion t ht hindex
      (D.chronologicalWindowRadius_sq_le_safeTime t ht) hmidpoint


-- @@ L461-469 verbatim
/-- Flow-induced split analogue. -/
abbrev ChronologicalSaddleSplitFlowSupply
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle) :=
  Σ' hmidpoint : D.ChronologicalSaddleSplitExteriorMidpointCapture
    t ht hindex,
    D.ChronologicalSaddleSplitExteriorCompletion t ht hindex
      (D.chronologicalWindowRadius_sq_le_safeTime t ht) hmidpoint


-- @@ L471-482 verbatim
def saddleMergeExteriorCanonicalPairing_of_flowSupply
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (P : D.ChronologicalSaddleMergeFlowSupply t ht hindex) :
    D.ChronologicalSaddleMergeExteriorCanonicalPairing
      t ht hpositive hindex :=
  (D.saddleMergeFlowInducedPairing_of_completion
    t ht hindex (D.chronologicalWindowRadius_sq_le_safeTime t ht)
      P.1 P.2).toCanonicalCriticalExteriorFlowPairing


-- @@ L484-495 verbatim
def saddleSplitExteriorCanonicalPairing_of_flowSupply
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .saddle)
    (P : D.ChronologicalSaddleSplitFlowSupply t ht hindex) :
    D.ChronologicalSaddleSplitExteriorCanonicalPairing
      t ht hpositive hindex :=
  (D.saddleSplitFlowInducedPairing_of_completion
    t ht hindex (D.chronologicalWindowRadius_sq_le_safeTime t ht)
      P.1 P.2).toCanonicalCriticalExteriorFlowPairing


-- @@ L497-497 verbatim
/-! ## Minimal global topology and complete actual saddle supplies -/


-- @@ L499-512 verbatim
/-- The two global connectivity facts distinguishing a merge.  Neither is
visible in the embedded local chart: the two negative branches must belong to
different global components, while the two positive branches must belong to
the same one. -/
structure ChronologicalSaddleMergeTopology
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle) : Prop where
  negative_ne :
    D.chronologicalSaddleNegativeOrbit t ht hindex .negative ≠
      D.chronologicalSaddleNegativeOrbit t ht hindex .positive
  positive_eq :
    D.chronologicalSaddlePositiveOrbit t ht hindex .negative =
      D.chronologicalSaddlePositiveOrbit t ht hindex .positive


-- @@ L514-524 verbatim
/-- The reverse pair of global connectivity facts distinguishing a split. -/
structure ChronologicalSaddleSplitTopology
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle) : Prop where
  positive_ne :
    D.chronologicalSaddlePositiveOrbit t ht hindex .negative ≠
      D.chronologicalSaddlePositiveOrbit t ht hindex .positive
  negative_eq :
    D.chronologicalSaddleNegativeOrbit t ht hindex .negative =
      D.chronologicalSaddleNegativeOrbit t ht hindex .positive


-- @@ L526-537 verbatim
/-- Strict-minimal frame equation specialized to the three actual merge
orbits. -/
abbrev ChronologicalSaddleMergeActualFrameClassSupply
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle) :=
  SaddleActualFrameClassSupply
    (D.chronologicalBeforeField t ht)
    (D.chronologicalAfterField t ht)
    (D.chronologicalSaddleNegativeOrbit t ht hindex .negative)
    (D.chronologicalSaddleNegativeOrbit t ht hindex .positive)
    (D.chronologicalSaddlePositiveOrbit t ht hindex .negative)


-- @@ L539-551 verbatim
/-- Strict-minimal frame equation specialized to the three actual split orbits,
read from the two-component positive slice back to the one-component negative
slice. -/
abbrev ChronologicalSaddleSplitActualFrameClassSupply
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle) :=
  SaddleActualFrameClassSupply
    (D.chronologicalAfterField t ht)
    (D.chronologicalBeforeField t ht)
    (D.chronologicalSaddlePositiveOrbit t ht hindex .negative)
    (D.chronologicalSaddlePositiveOrbit t ht hindex .positive)
    (D.chronologicalSaddleNegativeOrbit t ht hindex .negative)


-- @@ L553-563 verbatim
/-- All residual merge input after the production flow and local saddle model
have done their forced work.  The three fields are mutually independent:
global branch connectivity, exterior-flow exhaustion, and the single
actual three-orbit frame splice. -/
structure ChronologicalSaddleMergeSupply
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle) where
  topology : D.ChronologicalSaddleMergeTopology t ht hindex
  exterior : D.ChronologicalSaddleMergeFlowSupply t ht hindex
  frame : D.ChronologicalSaddleMergeActualFrameClassSupply t ht hindex


-- @@ L565-572 verbatim
/-- All residual split input, in the same three independent layers. -/
structure ChronologicalSaddleSplitSupply
    (D : ValueSeparatedSignedMorsePackage SC)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (hindex : (D.position.eventModel t ht).index = .saddle) where
  topology : D.ChronologicalSaddleSplitTopology t ht hindex
  exterior : D.ChronologicalSaddleSplitFlowSupply t ht hindex
  frame : D.ChronologicalSaddleSplitActualFrameClassSupply t ht hindex


-- @@ L574-574 verbatim
namespace ChronologicalSaddleMergeSupply


-- @@ L576-576 verbatim
variable {D : ValueSeparatedSignedMorsePackage SC}

-- @@ L577-577 verbatim
variable {t : ℝ} {ht : t ∈ D.position.eventTimes}

-- @@ L578-578 verbatim
variable {hindex : (D.position.eventModel t ht).index = .saddle}


-- @@ L580-596 verbatim
/-- Expand the reduced merge supply to the exact frame-class kit consumed by
the canonical production saddle adapter. -/
def toFrameClassKit
    (P : D.ChronologicalSaddleMergeSupply t ht hindex)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hn : 2 ≤ n) :
    D.ChronologicalSaddleMergeFrameClassKit
      t ht hpositive hindex where
  incoming_ne := by
    intro h
    exact P.topology.negative_ne (congrArg Subtype.val h)
  outgoing_eq := P.topology.positive_eq
  exteriorPairing :=
    D.saddleMergeExteriorCanonicalPairing_of_flowSupply
      t ht hpositive hindex P.exterior
  frameClasses := P.frame.toRelativeFrameClassData hn


-- @@ L598-598 verbatim
end ChronologicalSaddleMergeSupply


-- @@ L600-600 verbatim
namespace ChronologicalSaddleSplitSupply


-- @@ L602-602 verbatim
variable {D : ValueSeparatedSignedMorsePackage SC}

-- @@ L603-603 verbatim
variable {t : ℝ} {ht : t ∈ D.position.eventTimes}

-- @@ L604-604 verbatim
variable {hindex : (D.position.eventModel t ht).index = .saddle}


-- @@ L606-621 verbatim
/-- Split analogue of `ChronologicalSaddleMergeSupply.toFrameClassKit`. -/
def toFrameClassKit
    (P : D.ChronologicalSaddleSplitSupply t ht hindex)
    (hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hn : 2 ≤ n) :
    D.ChronologicalSaddleSplitFrameClassKit
      t ht hpositive hindex where
  incoming_ne := by
    intro h
    exact P.topology.positive_ne (congrArg Subtype.val h)
  outgoing_eq := P.topology.negative_eq
  exteriorPairing :=
    D.saddleSplitExteriorCanonicalPairing_of_flowSupply
      t ht hpositive hindex P.exterior
  frameClasses := P.frame.toRelativeFrameClassData hn


-- @@ L623-623 verbatim
end ChronologicalSaddleSplitSupply


-- @@ L625-625 verbatim
end ValueSeparatedSignedMorsePackage


-- @@ L627-627 verbatim
/-! ## Direct adapter to the final production saddle field -/


-- @@ L629-643 verbatim
/-- A merge-or-split supply family in the exact event quantifier order.  The
sum is the irreducible global orientation choice; all fields of the resulting
frame-class kit are constructed automatically. -/
abbrev ProductionMorseSaddleSupplies (a : ℕ) :=
  ∀ {X Y : FramedLevelSet (a + 2)}
    {S : FiberSign X} {T : FiberSign Y}
    (C : SignedFramedLevelCobordism S T)
    (D : ValueSeparatedSignedMorsePackage C)
    (t : ℝ) (ht : t ∈ D.position.eventTimes)
    (_hpositive : D.position.eventCenter t ht ∈
      (D.signedOutput.labelMorsePosition D.position).positiveCenters)
    (hindex : (D.position.eventModel t ht).index = .saddle),
      Nonempty
        (D.ChronologicalSaddleMergeSupply t ht hindex ⊕
          D.ChronologicalSaddleSplitSupply t ht hindex)


-- @@ L645-653 verbatim
/-- Expand reduced actual supplies to the class kits of the previous adapter. -/
theorem frameClassKits_of_saddleSupplies {a : ℕ}
    (P : ProductionMorseSaddleSupplies a) :
    ProductionMorseSaddleFrameClassKits a := by
  intro X Y S T C D t ht hpositive hindex
  obtain ⟨P⟩ := P C D t ht hpositive hindex
  exact ⟨P.map
    (fun H => H.toFrameClassKit hpositive (by omega))
    (fun H => H.toFrameClassKit hpositive (by omega))⟩


-- @@ L655-674 verbatim
/-- Direct final-field adapter: a caller can use this as the `saddle` field of
`ProductionMorseEventGeometryKit` without mentioning model loops, pairings,
or frame-class splice calculations. -/
theorem saddleGeometry_of_saddleSupplies {a : ℕ}
    (P : ProductionMorseSaddleSupplies a) :
    ∀ {X Y : FramedLevelSet (a + 2)}
      {S : FiberSign X} {T : FiberSign Y}
      (C : SignedFramedLevelCobordism S T)
      (D : ValueSeparatedSignedMorsePackage C)
      (t : ℝ) (ht : t ∈ D.position.eventTimes)
      (hpositive : D.position.eventCenter t ht ∈
        (D.signedOutput.labelMorsePosition D.position).positiveCenters)
      (hindex : (D.position.eventModel t ht).index = .saddle),
        Nonempty
          (D.ChronologicalSaddleMergeCanonicalGeometry
              t ht hpositive hindex ⊕
            D.ChronologicalSaddleSplitCanonicalGeometry
              t ht hpositive hindex) :=
  saddleGeometry_of_frameClassKits
    (frameClassKits_of_saddleSupplies P)


-- @@ L676-676 verbatim
end Submission
