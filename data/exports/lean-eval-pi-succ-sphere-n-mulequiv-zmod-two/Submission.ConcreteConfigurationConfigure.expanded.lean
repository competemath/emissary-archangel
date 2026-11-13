import Mathlib
import Submission.ConcreteConfigurationMoveKit
import Submission.FrameGaugeNormalization
import Submission.MorseLedgerGeometry
import Submission.OrbitUnknottingAdaptiveChordChain


-- @@ L7-29 verbatim
/-!
# Assembly of the concrete configuration theorem

This file narrows the remaining geometric input of
`ConcreteConfigurationMoveKit.Data.configure` to three explicit stages.

1. Move each orbit, relative to all the others, to its canonical round
   circle.  The finite ambient schedule is assembled automatically.
2. Change the defining equations by a smooth pointwise-invertible gauge.
3. Perform the topology-changing reduction of the resulting signed finite
   round-circle configuration to the delta-indexed diagonal standard.

The first stage is now unconditional in dimension at least three.  This file
chooses the already-constructed relative Fourier track, uses its adaptive
finite chord chain, and then assembles all orbit moves.  The older uniform
mesh interface is retained as a compatibility adapter.

Ambient isotopy and gauge change preserve the number of fiber components.
Consequently the third stage is mathematically indispensable for a source
with more components than the diagonal standard.  Its source endpoint is
fully fixed here, so compact saddle and class-one death models need only
instantiate that final, topology-changing field.
-/


-- @@ L31-31 verbatim
set_option autoImplicit false


-- @@ L33-33 verbatim
noncomputable section


-- @@ L35-35 verbatim
open Set Function

-- @@ L36-36 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L38-38 verbatim
namespace Submission

-- @@ L39-39 verbatim
namespace ConcreteConfigurationConfigure


-- @@ L41-41 verbatim
variable (m : ℕ)


-- @@ L43-43 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 3))

-- @@ L44-44 verbatim
local notation "F" => EuclideanSpace ℝ (Fin (m + 2))


-- @@ L46-48 verbatim
/-- The configuration dimension is always at least two. -/
theorem dimension_ge_two : 2 ≤ m + 2 := by
  omega


-- @@ L50-52 verbatim
/-- Fix the already-proved canonical tamed extension once and for all. -/
abbrev field {X : FramedLevelSet (m + 2)} : TamedField X :=
  X.exists_tamedField.some


-- @@ L54-57 verbatim
/-- The positive component ledger enumerated using the canonical field. -/
def positiveLedger {X : FramedLevelSet (m + 2)} (S : FiberSign X) :
    MorseLedger :=
  S.positiveFrameLedger (field m)


-- @@ L59-63 verbatim
/-- The negative component ledger is the positive ledger of the negated
label. -/
def negativeLedger {X : FramedLevelSet (m + 2)} (S : FiberSign X) :
    MorseLedger :=
  S.neg.positiveFrameLedger (field m)


-- @@ L65-70 verbatim
/-- The enumerated positive ledger has the canonical positive delta. -/
theorem positiveDelta_eq_positiveLedger_delta
    {X : FramedLevelSet (m + 2)} (S : FiberSign X) :
    S.positiveDelta = (positiveLedger m S).delta := by
  exact (S.positiveDelta_eq (field m)).trans
    (S.positiveFrameLedger_delta (field m)).symm


-- @@ L72-77 verbatim
/-- The enumerated negative ledger has the canonical negative delta. -/
theorem negativeDelta_eq_negativeLedger_delta
    {X : FramedLevelSet (m + 2)} (S : FiberSign X) :
    S.negativeDelta = (negativeLedger m S).delta := by
  exact (S.negativeDelta_eq (field m)).trans
    (S.neg.positiveFrameLedger_delta (field m)).symm


-- @@ L79-79 verbatim
/-! ## Component placement -/


-- @@ L81-86 verbatim
/-- The local geometric input for the placement stage: one relative
canonical move for every orbit. -/
structure ComponentPlacementData (X : FramedLevelSet (m + 2)) where
  realize : ∀ O : (field m : TamedField X).OrbitIndex,
    Nonempty ((field m : TamedField X).RelativeCanonicalOrbitMove
      (dimension_ge_two m) O)


-- @@ L88-88 verbatim
namespace ComponentPlacementData


-- @@ L90-90 verbatim
variable {m} {X : FramedLevelSet (m + 2)}


-- @@ L92-98 verbatim
/-- Assemble all relative orbit moves into one globally compatible ambient
unknotting. -/
def unknotting (P : ComponentPlacementData m X) :
    SmoothAmbientIsotopy.SupportedCanonicalRoundUnknotting
      (X := X) (V := field m) (dimension_ge_two m) :=
  TamedField.supportedCanonicalRoundUnknottingOfRelativeMoves
    (field m) (dimension_ge_two m) P.realize


-- @@ L100-102 verbatim
/-- The ambient isotopy produced by the finite component schedule. -/
def ambient (P : ComponentPlacementData m X) : SmoothAmbientIsotopy (m + 2) :=
  P.unknotting.ambient


-- @@ L104-107 verbatim
/-- The framed presentation after every component is moved to its canonical
round circle. -/
def endpointX (P : ComponentPlacementData m X) : FramedLevelSet (m + 2) :=
  P.unknotting.endpointX


-- @@ L109-112 verbatim
/-- Transport a sign label through the global placement. -/
def endpointSign (P : ComponentPlacementData m X) (S : FiberSign X) :
    FiberSign P.endpointX :=
  P.unknotting.endpointSign S


-- @@ L114-117 verbatim
/-- The placement stage is an actual signed framed cobordism. -/
def signedCobordism (P : ComponentPlacementData m X) (S : FiberSign X) :
    SignedFramedLevelCobordism S (P.endpointSign S) :=
  P.unknotting.signedCobordism S


-- @@ L119-125 verbatim
/-- The placement endpoint has exactly the canonical finite union of round
circles. -/
theorem endpoint_fiber (P : ComponentPlacementData m X) :
    P.endpointX.fiber =
      CanonicalRoundOrbit.targetUnion (X := X)
        (field m) (dimension_ge_two m) :=
  P.unknotting.ambient_pullback_fiber


-- @@ L127-127 verbatim
end ComponentPlacementData


-- @@ L129-129 verbatim
/-! ## Uniform-mesh adapter -/


-- @@ L131-139 verbatim
/-- Choose the relative Fourier track whose existence is already proved in
dimension at least three. -/
def chosenRelativeTrack {X : FramedLevelSet (m + 2)}
    (h3 : 3 ≤ m + 2) (O : (field m : TamedField X).OrbitIndex) :
    TamedField.FourierRelativeTrack.RelativeEmbeddedCircleTrack
      (V := field m) (dimension_ge_two m) O :=
  Classical.choice
    (TamedField.FourierRelativeTrack.exists_relativeEmbeddedCircleTrack
      (V := field m) (dimension_ge_two m) O h3)


-- @@ L141-148 verbatim
/-- In dimension at least three, the Fourier relative track and its adaptive
chord-chain theorem supply every component move without any mesh or local
step input. -/
theorem componentPlacementData {X : FramedLevelSet (m + 2)}
    (h3 : 3 ≤ m + 2) : ComponentPlacementData m X where
  realize O :=
    TamedField.FourierRelativeTrack.RelativeEmbeddedCircleTrack.nonempty_relativeCanonicalOrbitMove_of_relativeTrack
      (chosenRelativeTrack m h3 O)


-- @@ L150-164 verbatim
/-- An analytic placement interface reduced to local ambient-track steps on
a finite uniform mesh for each component. -/
structure EquisubdivisionPlacementData (X : FramedLevelSet (m + 2))
    (h3 : 3 ≤ m + 2) where
  meshSize : (field m : TamedField X).OrbitIndex → ℕ
  meshSize_pos : ∀ O, 0 < meshSize O
  step : ∀ (O : (field m : TamedField X).OrbitIndex) (k : ℕ),
    k < meshSize O →
      Nonempty
        (TamedField.FourierEmbeddingTrack.AmbientTrackStep
          (chosenRelativeTrack m h3 O).track
          (TamedField.FourierEmbeddingTrack.AmbientTrackChain.equisubdivisionPoint
            (meshSize O) k)
          (TamedField.FourierEmbeddingTrack.AmbientTrackChain.equisubdivisionPoint
            (meshSize O) (k + 1)))


-- @@ L166-166 verbatim
namespace EquisubdivisionPlacementData


-- @@ L168-168 verbatim
variable {m} {X : FramedLevelSet (m + 2)} {h3 : 3 ≤ m + 2}


-- @@ L170-177 verbatim
/-- Uniform local steps assemble first along each track and then across the
finite set of components. -/
theorem toComponentPlacementData (D : EquisubdivisionPlacementData m X h3) :
    ComponentPlacementData m X where
  realize O :=
    TamedField.FourierRelativeTrack.RelativeEmbeddedCircleTrack.nonempty_relativeCanonicalOrbitMove_of_equisubdivision
        (chosenRelativeTrack m h3 O)
        (D.meshSize O) (D.meshSize_pos O) (D.step O)


-- @@ L179-179 verbatim
end EquisubdivisionPlacementData


-- @@ L181-181 verbatim
/-! ## Gauge normalization -/


-- @@ L183-190 verbatim
/-- A smooth path of pointwise-invertible gauges on the placed defining map.
The endpoint presentation and the signed cobordism are derived below. -/
structure FrameGaugeData {X : FramedLevelSet (m + 2)}
    (P : ComponentPlacementData m X) where
  Q : ℝ → E → F →L[ℝ] F
  smooth : ContDiff ℝ ∞ (fun p : ℝ × E => Q p.1 p.2)
  zero : ∀ x, Q 0 x = ContinuousLinearMap.id ℝ F
  bijective : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x, Bijective (Q s x)


-- @@ L192-192 verbatim
namespace FrameGaugeData


-- @@ L194-194 verbatim
variable {m} {X : FramedLevelSet (m + 2)}

-- @@ L195-195 verbatim
variable {P : ComponentPlacementData m X}


-- @@ L197-201 verbatim
/-- The endpoint presentation after frame gauge normalization. -/
def endpointX (G : FrameGaugeData m P) : FramedLevelSet (m + 2) :=
  P.endpointX.gaugeTransform (G.Q 1)
    (contDiff_gauge_slice G.smooth 1)
    (fun x => G.bijective 1 ⟨zero_le_one, le_rfl⟩ x)


-- @@ L203-206 verbatim
/-- The common-fiber defining-map homotopy induced by the gauge path. -/
def homotopy (G : FrameGaugeData m P) :
    DefiningMapHomotopy P.endpointX G.endpointX :=
  DefiningMapHomotopy.ofGauge P.endpointX G.Q G.smooth G.zero G.bijective


-- @@ L208-211 verbatim
/-- The endpoint sign is transported unchanged on the common zero fiber. -/
def endpointSign (G : FrameGaugeData m P) (S : FiberSign X) :
    FiberSign G.endpointX :=
  (P.endpointSign S).restrict G.homotopy.fiber_subset


-- @@ L213-216 verbatim
/-- The gauge stage is an actual signed framed cobordism. -/
def signedCobordism (G : FrameGaugeData m P) (S : FiberSign X) :
    SignedFramedLevelCobordism (P.endpointSign S) (G.endpointSign S) :=
  G.homotopy.signedCobordism (P.endpointSign S)


-- @@ L218-226 verbatim
/-- The transported endpoint label agrees with the direct gauge transport. -/
theorem endpointSign_eq_gaugeTransform (G : FrameGaugeData m P)
    (S : FiberSign X) :
    G.endpointSign S =
      (P.endpointSign S).gaugeTransform (G.Q 1)
        (contDiff_gauge_slice G.smooth 1)
        (fun x => G.bijective 1 ⟨zero_le_one, le_rfl⟩ x) := by
  exact DefiningMapHomotopy.ofGauge_restrict_eq_gaugeTransform
    P.endpointX (P.endpointSign S) G.Q G.smooth G.zero G.bijective


-- @@ L228-228 verbatim
end FrameGaugeData


-- @@ L230-230 verbatim
/-! ## Final topology-changing contract and configure assembly -/


-- @@ L232-244 verbatim
/-- Complete geometric input for one signed presentation.

The `reduction` field is the only topology-changing stage.  Its source is no
longer arbitrary: it is the canonical round-orbit placement with the chosen
frame gauge.  All bookkeeping, placement scheduling, gauge transport, and
cobordism composition are formal consequences. -/
structure Geometry {X : FramedLevelSet (m + 2)} (S : FiberSign X) where
  placement : ComponentPlacementData m X
  gauge : FrameGaugeData m placement
  reduction : Nonempty
    (SignedFramedLevelCobordism (gauge.endpointSign S)
      (ConcreteConfigurationMoveKit.configSign m
        (positiveLedger m S) (negativeLedger m S)))


-- @@ L246-246 verbatim
namespace Geometry


-- @@ L248-248 verbatim
variable {m} {X : FramedLevelSet (m + 2)} {S : FiberSign X}


-- @@ L250-259 verbatim
/-- Compose placement, frame gauge, and the topology-changing reduction. -/
theorem nonempty_configureCobordism (G : Geometry m S) :
    Nonempty
      (SignedFramedLevelCobordism S
        (ConcreteConfigurationMoveKit.configSign m
          (positiveLedger m S) (negativeLedger m S))) :=
  SignedFramedLevelCobordism.nonempty_trans
    ⟨G.placement.signedCobordism S⟩
    (SignedFramedLevelCobordism.nonempty_trans
      ⟨G.gauge.signedCobordism S⟩ G.reduction)


-- @@ L261-261 verbatim
end Geometry


-- @@ L263-274 verbatim
/-- A family of the narrowed geometric witnesses supplies the complete
one-field concrete move kit. -/
theorem dataOfGeometry
    (supply : ∀ {X : FramedLevelSet (m + 2)} (S : FiberSign X),
      Nonempty (Geometry m S)) :
    ConcreteConfigurationMoveKit.Data m where
  configure := by
    intro X S
    refine ⟨positiveLedger m S, negativeLedger m S,
      positiveDelta_eq_positiveLedger_delta m S,
      negativeDelta_eq_negativeLedger_delta m S, ?_⟩
    exact (supply S).some.nonempty_configureCobordism


-- @@ L276-282 verbatim
/-- Direct adapter from the narrowed geometry family to the general
configuration-reduction interface. -/
def toConfigurationReductionKitOfGeometry
    (supply : ∀ {X : FramedLevelSet (m + 2)} (S : FiberSign X),
      Nonempty (Geometry m S)) :
    ConfigurationReductionKit (m + 2) :=
  (dataOfGeometry m supply).toConfigurationReductionKit


-- @@ L284-284 verbatim
end ConcreteConfigurationConfigure

-- @@ L285-285 verbatim
end Submission
