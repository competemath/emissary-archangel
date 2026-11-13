import Mathlib
import Submission.ConcreteConfigurationSignedFramedPermutationRematching
import Submission.SOLocallySmoothCartesianDiscrepancy
import Submission.ConcreteConfigurationBridgeCobordismTraceConnectors


-- @@ L6-23 verbatim
/-!
# Actual matched frame discrepancies at the first bridge head

This module joins the previously independent pieces of the bridge entry:

1. unconditional canonical placement of the bridge fiber;
2. the actual signed/frame-preserving orbit matching, realized by a source
   slot permutation followed by affine rematching;
3. the actual pointwise frame discrepancy `target * source⁻¹` on every matched
   round circle, whose null gauge follows from equality of orbit frame classes;
4. the finite supported gauge endpoint; and
5. the source normalization of the first local head and its exact/spliced
   compact tail.

No equality of global defining maps is asserted at the gauge endpoint.  The
existing `LocalHeadEventData.sourceNormalization` is exactly the categorical
connector from that endpoint into the literal first compact-head source.
-/


-- @@ L25-25 verbatim
set_option autoImplicit false


-- @@ L27-27 verbatim
noncomputable section


-- @@ L29-29 verbatim
open Set Function

-- @@ L30-30 verbatim
open scoped unitInterval Topology ContDiff RealInnerProductSpace


-- @@ L32-32 verbatim
namespace Submission


-- @@ L34-34 verbatim
/-! ## Actual normal-frame loop representatives -/


-- @@ L36-36 verbatim
namespace SignedFramedOrbitEquiv


-- @@ L38-38 verbatim
variable {m : ℕ}

-- @@ L39-39 verbatim
variable {X Y : FramedLevelSet (m + 2)}

-- @@ L40-40 verbatim
variable {V : TamedField X} {W : TamedField Y}

-- @@ L41-41 verbatim
variable {S : FiberSign X} {T : FiberSign Y}


-- @@ L43-53 verbatim
/-- Circle-local representatives of the actual source and target normal-frame
loops.  The class fields identify them with the intrinsic orbit frame classes;
the signed/framed orbit equivalence then forces every matched discrepancy to
be null. -/
structure ActualFrameLoopMatch (M : SignedFramedOrbitEquiv V W S T) where
  source : V.OrbitIndex → LocallySmoothCartesianSOLoop (m + 2)
  target : W.OrbitIndex → LocallySmoothCartesianSOLoop (m + 2)
  source_class : ∀ O : V.OrbitIndex,
    loopClassZ2 (source O).loop (source O).closed = V.orbitFrameClass O
  target_class : ∀ P : W.OrbitIndex,
    loopClassZ2 (target P).loop (target P).closed = W.orbitFrameClass P


-- @@ L55-55 verbatim
namespace ActualFrameLoopMatch


-- @@ L57-57 verbatim
variable {M : SignedFramedOrbitEquiv V W S T}


-- @@ L59-63 verbatim
/-- The actual discrepancy, indexed at the target canonical circle. -/
def discrepancyLoop (F : ActualFrameLoopMatch M) (P : W.OrbitIndex) :
    LocallySmoothCartesianSOLoop (m + 2) :=
  LocallySmoothCartesianSOLoop.discrepancy
    (F.source (M.orbitEquiv.symm P)) (F.target P)


-- @@ L65-78 verbatim
theorem matched_frameClass
    (F : ActualFrameLoopMatch M) (P : W.OrbitIndex) :
    loopClassZ2 (F.source (M.orbitEquiv.symm P)).loop
        (F.source (M.orbitEquiv.symm P)).closed =
      loopClassZ2 (F.target P).loop (F.target P).closed := by
  calc
    loopClassZ2 (F.source (M.orbitEquiv.symm P)).loop
        (F.source (M.orbitEquiv.symm P)).closed =
        V.orbitFrameClass (M.orbitEquiv.symm P) :=
      F.source_class (M.orbitEquiv.symm P)
    _ = W.orbitFrameClass P := by
      simpa using M.orbitEquiv_frameClass (M.orbitEquiv.symm P)
    _ = loopClassZ2 (F.target P).loop (F.target P).closed :=
      (F.target_class P).symm


-- @@ L80-87 verbatim
/-- The null gauge required at every target slot, with no separate class-zero
hypothesis. -/
def nullGauge (F : ActualFrameLoopMatch M) (hm : 0 < m)
    (P : W.OrbitIndex) :
    (F.discrepancyLoop P).NullGaugeData :=
  LocallySmoothCartesianSOLoop.discrepancyNullGaugeData
    (F.source (M.orbitEquiv.symm P)) (F.target P) (by omega)
    (F.matched_frameClass P)


-- @@ L89-93 verbatim
/-- Upgrade the actual discrepancy using the smooth endpoint slice of its
constructed local null gauge. -/
def smoothDiscrepancyLoop (F : ActualFrameLoopMatch M) (hm : 0 < m)
    (P : W.OrbitIndex) : SmoothCartesianSOLoop (m + 2) :=
  (F.nullGauge hm P).toSmoothCartesianSOLoop


-- @@ L95-97 verbatim
def smoothNullGauge (F : ActualFrameLoopMatch M) (hm : 0 < m)
    (P : W.OrbitIndex) : (F.smoothDiscrepancyLoop hm P).NullGaugeData :=
  (F.nullGauge hm P).toSmoothNullGaugeData


-- @@ L99-99 verbatim
end ActualFrameLoopMatch

-- @@ L100-100 verbatim
end SignedFramedOrbitEquiv


-- @@ L102-102 verbatim
/-! ## Placement, actual matching, and the finite gauge endpoint -/


-- @@ L104-104 verbatim
namespace ConcreteConfigurationSignedFramedActualGaugeBridgeEntry


-- @@ L106-106 verbatim
open ConcreteConfigurationMorseReduction

-- @@ L107-107 verbatim
open ConcreteConfigurationBridgeExactReduction

-- @@ L108-108 verbatim
open ConcreteConfigurationBridgeCobordismTrace


-- @@ L110-110 verbatim
variable {m : ℕ} {z : StableSpherePi (m + 2)}

-- @@ L111-111 verbatim
variable {B : BridgeData (m + 2) z}


-- @@ L113-114 verbatim
local notation "Vᴮ" =>
  (ConcreteConfigurationConfigure.field m : TamedField B.fls)


-- @@ L116-119 verbatim
/-- The automatic placement of the bridge source. -/
abbrev sourcePlacement (hm : 0 < m) :
    ConcreteConfigurationConfigure.ComponentPlacementData m B.fls :=
  ConcreteConfigurationConfigure.componentPlacementData m (by omega)


-- @@ L121-121 verbatim
variable {Y : FramedLevelSet (m + 2)} {T : FiberSign Y}

-- @@ L122-122 verbatim
variable {W : TamedField Y}


-- @@ L124-130 verbatim
/-- The placed bridge presentation after the actual permutation/translation
matching ambient. -/
def matchedPlacedX
    (hm : 0 < m)
    (M : SignedFramedOrbitEquiv Vᴮ W B.fiberSign T) :
    FramedLevelSet (m + 2) :=
  (M.matchingAmbient hm).pullback (sourcePlacement (B := B) hm).endpointX


-- @@ L132-138 verbatim
/-- Its transported sign. -/
def matchedPlacedSign
    (hm : 0 < m)
    (M : SignedFramedOrbitEquiv Vᴮ W B.fiberSign T) :
    FiberSign (matchedPlacedX hm M) :=
  (M.matchingAmbient hm).pullbackSign
    ((sourcePlacement (B := B) hm).endpointSign B.fiberSign)


-- @@ L140-149 verbatim
/-- The actual matching stage lands on the target field's canonical circle
union. -/
theorem matchedPlacedX_fiber
    (hm : 0 < m)
    (M : SignedFramedOrbitEquiv Vᴮ W B.fiberSign T) :
    (matchedPlacedX hm M).fiber =
      CanonicalRoundOrbit.targetUnion W (by omega) := by
  exact M.matchingAmbient_pullback_fiber hm
    (sourcePlacement (B := B) hm).endpointX
    (sourcePlacement (B := B) hm).endpoint_fiber


-- @@ L151-158 verbatim
/-- One finite supported gauge carrying all actual matched discrepancies. -/
def discrepancyHomotopy
    (hm : 0 < m)
    (M : SignedFramedOrbitEquiv Vᴮ W B.fiberSign T)
    (F : M.ActualFrameLoopMatch) :=
  SmoothCartesianSOLoop.CanonicalFiniteGauge.homotopy W
    (F.smoothDiscrepancyLoop hm) (F.smoothNullGauge hm)
      (matchedPlacedX hm M)


-- @@ L160-167 verbatim
/-- Sign at the finite-gauge endpoint. -/
def gaugeEndpointSign
    (hm : 0 < m)
    (M : SignedFramedOrbitEquiv Vᴮ W B.fiberSign T)
    (F : M.ActualFrameLoopMatch) :
    FiberSign (discrepancyHomotopy hm M F).toCobordism.X₁ :=
  (matchedPlacedSign hm M).restrict
    (discrepancyHomotopy hm M F).fiber_subset


-- @@ L169-187 verbatim
/-- On every target circle, the endpoint gauge is literally the actual
`target * source⁻¹` discrepancy. -/
@[simp] theorem discrepancyHomotopy_H_one_canonicalPoint
    (hm : 0 < m)
    (M : SignedFramedOrbitEquiv Vᴮ W B.fiberSign T)
    (F : M.ActualFrameLoopMatch) (P : W.OrbitIndex) (theta : ℝ) :
    (discrepancyHomotopy hm M F).H 1
        (CanonicalRoundOrbit.point W (by omega) P theta) =
      SOFrameGauge.toCLM
        ((F.discrepancyLoop P).cartesian
          (Real.cos theta, Real.sin theta))
        ((matchedPlacedX hm M).g
          (CanonicalRoundOrbit.point W (by omega) P theta)) := by
  rw [discrepancyHomotopy,
    SmoothCartesianSOLoop.CanonicalFiniteGauge.homotopy_H_one_canonicalPoint]
  change SOFrameGauge.toCLM
      ((F.nullGauge hm P).Q 1 (Real.cos theta, Real.sin theta)) _ = _
  rw [(F.nullGauge hm P).endpoint_circle _
    (Real.cos_sq_add_sin_sq theta)]


-- @@ L189-203 verbatim
/-- Placement, actual orbit rematching, and the finite discrepancy gauge form
one concrete connector from the bridge sign to the gauge endpoint. -/
theorem nonempty_toGaugeEndpoint
    (hm : 0 < m)
    (M : SignedFramedOrbitEquiv Vᴮ W B.fiberSign T)
    (F : M.ActualFrameLoopMatch) :
    Nonempty (SignedFramedLevelCobordism B.fiberSign
      (gaugeEndpointSign hm M F)) := by
  exact SignedFramedLevelCobordism.nonempty_trans
    ⟨(sourcePlacement (B := B) hm).signedCobordism B.fiberSign⟩
    (SignedFramedLevelCobordism.nonempty_trans
      ⟨(M.matchingAmbient hm).signedCobordism
        ((sourcePlacement (B := B) hm).endpointSign B.fiberSign)⟩
      ⟨(discrepancyHomotopy hm M F).signedCobordism
        (matchedPlacedSign hm M)⟩)


-- @@ L205-205 verbatim
/-! ## Entry into the literal first local head -/


-- @@ L207-243 verbatim
/-- Complete bridge entry through actual orbit/frame matching.  The supplied
trace starts at the literal source-with-tail of its first compact head; the
local-head source normalization is the only connector needed after the gauge
endpoint. -/
def ofActualMatchingGaugeAndLocalHeadTrace
    (hm : 0 < m)
    (Z : ZeroPairSaddleModel m)
    (kind : CompactMoveKind)
    {Y : FramedLevelSet (m + 2)} {T : FiberSign Y}
    {W : TamedField Y}
    (M : SignedFramedOrbitEquiv Vᴮ W B.fiberSign T)
    (F : M.ActualFrameLoopMatch)
    {Q : FramedLevelSet (m + 2)} {U : FiberSign Q}
    (D : LocalHeadEventData (gaugeEndpointSign hm M F)
      U (kind.model m Z))
    (trace : CobordismTrace m Z
      ((kind.model m Z).sourceWithTailSign D.tail)
      (DiagonalStandardConfiguration.standard m
        (ConcreteConfigurationConfigure.positiveLedger
          m B.fiberSign).delta).sign) :
    ConcreteConfigurationBridgeCobordismTrace.Data m B := by
  let P : ConcreteConfigurationBridgeCobordismTrace.Plan m Z
      (ConcreteConfigurationConfigure.positiveLedger m B.fiberSign)
      (ConcreteConfigurationConfigure.negativeLedger m B.fiberSign) :=
    ConcreteConfigurationBridgeCobordismTrace.Plan.ofLocalHeadTrace
      kind D.tail trace
  refine
    { zeroPairSaddle := Z
      plan := P
      initial := ?_ }
  apply SignedFramedLevelCobordism.nonempty_trans
    (nonempty_toGaugeEndpoint hm M F)
  change Nonempty (SignedFramedLevelCobordism
    (gaugeEndpointSign hm M F)
    ((kind.model m Z).sourceWithTailFlat D.tail).sign)
  rw [SpatiallyFlatHeadMove.sourceWithTailFlat_sign]
  exact D.sourceNormalization.toNormalizationData.nonempty_cobordism


-- @@ L245-245 verbatim
/-! ## Sharp specialization: match the literal first exact source -/


-- @@ L247-252 verbatim
/-- The flat presentation at the literal source of the first compact head. -/
abbrev firstSourceFlat
    (Z : ZeroPairSaddleModel m) (kind : CompactMoveKind)
    (tail : FlatSignedConfiguration (m + 2) (compactBackground m)) :
    FlatSignedConfiguration (m + 2) (compactBackground m) :=
  (kind.model m Z).sourceWithTailFlat tail


-- @@ L254-259 verbatim
/-- Its canonical tamed field. -/
abbrev firstSourceField
    (Z : ZeroPairSaddleModel m) (kind : CompactMoveKind)
    (tail : FlatSignedConfiguration (m + 2) (compactBackground m)) :
    TamedField (firstSourceFlat Z kind tail).X :=
  ConcreteConfigurationConfigure.field m


-- @@ L261-295 verbatim
/-- Version in which the actual signed/frame matching targets the literal
first compact-head source itself.  The remaining input `entry` is only the
relative common-fiber normalization from the finite-gauge endpoint to that
literal source; the compact trace then starts exactly at the head. -/
def ofActualFirstHeadMatchingGaugeAndTrace
    (hm : 0 < m)
    (Z : ZeroPairSaddleModel m)
    (kind : CompactMoveKind)
    (tail : FlatSignedConfiguration (m + 2) (compactBackground m))
    (M : SignedFramedOrbitEquiv Vᴮ
      (firstSourceField Z kind tail)
      B.fiberSign (firstSourceFlat Z kind tail).sign)
    (F : M.ActualFrameLoopMatch)
    (entry : RelativeNormalizationData
      (gaugeEndpointSign hm M F)
      (firstSourceFlat Z kind tail).sign
      ((kind.model m Z).placedTail tail).X.fiber)
    (trace : CobordismTrace m Z
      ((kind.model m Z).sourceWithTailSign tail)
      (DiagonalStandardConfiguration.standard m
        (ConcreteConfigurationConfigure.positiveLedger
          m B.fiberSign).delta).sign) :
    ConcreteConfigurationBridgeCobordismTrace.Data m B := by
  let P : ConcreteConfigurationBridgeCobordismTrace.Plan m Z
      (ConcreteConfigurationConfigure.positiveLedger m B.fiberSign)
      (ConcreteConfigurationConfigure.negativeLedger m B.fiberSign) :=
    ConcreteConfigurationBridgeCobordismTrace.Plan.ofLocalHeadTrace
      kind tail trace
  refine
    { zeroPairSaddle := Z
      plan := P
      initial := ?_ }
  exact SignedFramedLevelCobordism.nonempty_trans
    (nonempty_toGaugeEndpoint hm M F)
    entry.toNormalizationData.nonempty_cobordism


-- @@ L297-297 verbatim
end ConcreteConfigurationSignedFramedActualGaugeBridgeEntry

-- @@ L298-298 verbatim
end Submission
