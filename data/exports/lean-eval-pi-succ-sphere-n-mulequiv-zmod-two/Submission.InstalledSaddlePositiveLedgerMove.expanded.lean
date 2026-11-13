import Submission.InstalledSaddleLedgerDecomposition
import Submission.SignedMorseLedgerResolution


-- @@ L4-22 verbatim
/-!
# Installed saddle events as positive ledger moves

This file is the dependent-type adapter between the actual installed saddle
decomposition and the chronological event interface.  The local regular
slices are transported to the canonical event-bracket slices; no new orbit or
frame statement is assumed by that transport.

The two public constructors leave only the genuine geometric inputs explicit:

* the critical exterior connector and its flow endpoint witnesses;
* positivity and distinctness of the installed distinguished orbits;
* framed transport of the exact exterior complements; and
* the exterior-relative frame splice for the three distinguished orbits.

All complete positive orbit collections are the literal collections extracted
from the signed event slices.  The chronological merge/split orientation and
the resulting `PositiveEventLedgerMoveData` are constructed here.
-/


-- @@ L24-24 verbatim
set_option autoImplicit false


-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-28 verbatim
namespace Submission


-- @@ L30-30 verbatim
open Set Function Metric Filter

-- @@ L31-31 verbatim
open scoped RealInnerProductSpace ContDiff Topology unitInterval


-- @@ L33-33 verbatim
variable {n : ℕ}

-- @@ L34-34 verbatim
variable {X₀ X₁ : FramedLevelSet n}

-- @@ L35-35 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}


-- @@ L37-37 verbatim
namespace PositiveEventLedgerMoveData


-- @@ L39-39 verbatim
variable {C : SignedFramedLevelCobordism S₀ S₁}

-- @@ L40-40 verbatim
variable {P : MorsePosition C.cobordism}

-- @@ L41-41 verbatim
variable {t : ℝ} {ht : t ∈ P.eventTimes}


-- @@ L43-46 verbatim
/-- The existence wrapper expected by the global positive-event callback. -/
theorem toNonempty (D : PositiveEventLedgerMoveData C P t ht) :
    Nonempty (PositiveEventLedgerMoveData C P t ht) :=
  ⟨D⟩


-- @@ L48-75 verbatim
/-- Transport a local two-to-one saddle decomposition onto the literal event
bracket slices and package the chronological merge.  Equality elimination
also transports the distinguished orbit indices and the splice proof, so no
compatibility field beyond the two slice equalities is needed. -/
def saddleMerge_of_slice_transport
    {Xbefore Xafter : FramedLevelSet n}
    (hXbefore : Xbefore =
      SlabTamedField.sliceFLSAt C.cobordism.toLevelCobordismData
        (P.eventBracket t ht).before (P.eventBracket t ht).before_regular)
    (hXafter : Xafter =
      SlabTamedField.sliceFLSAt C.cobordism.toLevelCobordismData
        (P.eventBracket t ht).after (P.eventBracket t ht).after_regular)
    (Vbefore : TamedField Xbefore) (Vafter : TamedField Xafter)
    (D : SaddleOrbitLedgerDecomposition Vbefore Vafter
      ((C.sliceSign (P.eventBracket t ht).before
        (P.eventBracket t ht).before_regular).positiveOrbitCollection
          (hXbefore ▸ Vbefore))
      ((C.sliceSign (P.eventBracket t ht).after
        (P.eventBracket t ht).after_regular).positiveOrbitCollection
          (hXafter ▸ Vafter)))
    (hindex : (P.eventModel t ht).index = .saddle)
    (hsplice : Vafter.orbitFrameClass D.outgoing.1 =
      Vbefore.orbitFrameClass D.incoming₁.1 +
        Vbefore.orbitFrameClass D.incoming₂.1 + 1) :
    PositiveEventLedgerMoveData C P t ht := by
  subst Xbefore
  subst Xafter
  exact saddleMerge_of_decomposition hindex Vbefore Vafter D hsplice


-- @@ L77-103 verbatim
/-- The reverse orientation of `saddleMerge_of_slice_transport`: transport a
local two-to-one decomposition whose two-component side is the after slice and
package the chronological split. -/
def saddleSplit_of_slice_transport
    {Xbefore Xafter : FramedLevelSet n}
    (hXbefore : Xbefore =
      SlabTamedField.sliceFLSAt C.cobordism.toLevelCobordismData
        (P.eventBracket t ht).before (P.eventBracket t ht).before_regular)
    (hXafter : Xafter =
      SlabTamedField.sliceFLSAt C.cobordism.toLevelCobordismData
        (P.eventBracket t ht).after (P.eventBracket t ht).after_regular)
    (Vbefore : TamedField Xbefore) (Vafter : TamedField Xafter)
    (D : SaddleOrbitLedgerDecomposition Vafter Vbefore
      ((C.sliceSign (P.eventBracket t ht).after
        (P.eventBracket t ht).after_regular).positiveOrbitCollection
          (hXafter ▸ Vafter))
      ((C.sliceSign (P.eventBracket t ht).before
        (P.eventBracket t ht).before_regular).positiveOrbitCollection
          (hXbefore ▸ Vbefore)))
    (hindex : (P.eventModel t ht).index = .saddle)
    (hsplice : Vbefore.orbitFrameClass D.outgoing.1 =
      Vafter.orbitFrameClass D.incoming₁.1 +
        Vafter.orbitFrameClass D.incoming₂.1 + 1) :
    PositiveEventLedgerMoveData C P t ht := by
  subst Xbefore
  subst Xafter
  exact saddleSplit_of_decomposition hindex Vbefore Vafter D hsplice


-- @@ L105-105 verbatim
end PositiveEventLedgerMoveData


-- @@ L107-107 verbatim
namespace ExactFiniteMorseJetInstallation


-- @@ L109-109 verbatim
variable {C₀ : SignedFramedLevelCobordism S₀ S₁}

-- @@ L110-112 verbatim
variable {ι : Type*} [Fintype ι]
  {B : FiniteIFTSurfaceCover C₀.cobordism ι}
  {G : GenericFiniteIFTSurfaceAtlas B.toSurfaceChartFamily}

-- @@ L113-113 verbatim
variable {K : Set (EuclideanSpace ℝ (Fin (n + 2)))}


-- @@ L115-115 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

-- @@ L116-116 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L118-141 verbatim
/-- The installed slice below the saddle is the event-bracket before slice
whenever their times agree.  Only the defining maps matter; all regularity
proof fields are discharged by proof irrelevance. -/
theorem criticalSaddleNegativeSlice_eq_eventBefore
    (R : ExactFiniteMorseJetInstallation G)
    (P : MorsePosition
      (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism))
    (t : ℝ) (ht : t ∈ P.eventTimes)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (A : ℝ)
    (hbefore : (P.eventBracket t ht).before =
      G.localSeparatedTime p p.2 - A ^ 2) :
    R.criticalSaddleNegativeSlice p hp A (by
      rw [← hbefore]
      exact (P.eventBracket t ht).before_regular) =
      SlabTamedField.sliceFLSAt
        (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism).toLevelCobordismData
        (P.eventBracket t ht).before
        (P.eventBracket t ht).before_regular := by
  rw [FramedLevelSet.mk.injEq]
  funext x
  ext i
  simp [criticalSaddleNegativeSlice, SlabTamedField.sliceFLSAt,
    sliceFLS, hbefore]


-- @@ L143-164 verbatim
/-- The corresponding equality for the installed slice above the saddle. -/
theorem criticalSaddlePositiveSlice_eq_eventAfter
    (R : ExactFiniteMorseJetInstallation G)
    (P : MorsePosition
      (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism))
    (t : ℝ) (ht : t ∈ P.eventTimes)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (A : ℝ)
    (hafter : (P.eventBracket t ht).after =
      G.localSeparatedTime p p.2 + A ^ 2) :
    R.criticalSaddlePositiveSlice p hp A (by
      rw [← hafter]
      exact (P.eventBracket t ht).after_regular) =
      SlabTamedField.sliceFLSAt
        (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism).toLevelCobordismData
        (P.eventBracket t ht).after
        (P.eventBracket t ht).after_regular := by
  rw [FramedLevelSet.mk.injEq]
  funext x
  ext i
  simp [criticalSaddlePositiveSlice, SlabTamedField.sliceFLSAt,
    sliceFLS, hafter]


-- @@ L166-306 verbatim
/-- Actual installed saddle with two components below and one above, packaged
as the chronological positive-ledger merge.  The orbit collections are not
parameters: they are the exact complete positive collections on the event
slices. -/
def negativeTwo_positiveEventLedgerMerge_of_criticalExteriorPath
    (R : ExactFiniteMorseJetInstallation G)
    (T : CompactTimeTamedField
      (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism).toLevelCobordismData K)
    (P : MorsePosition
      (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism))
    (t : ℝ) (ht : t ∈ P.eventTimes)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hlocalIndex : (G.localMorseNormalForm p hp).index = .saddle)
    (heventIndex : (P.eventModel t ht).index = .saddle)
    (d₁ d₂ : SaddleBranch) (r ρ A : ℝ)
    (hrShrink : r ≤ (R.criticalModelShrink p hp).radius)
    (hendpoint₁ : ∃ u : E₂, ‖u‖ < r ∧
      R.criticalSurfaceParam p hp u =
        T.base.flow
          (R.criticalSaddlePositiveBoundaryEnd p hp .negative d₁ ρ 0)
          (A ^ 2) ∧
      0 < signedBranch .negative (u 0) ∧
      morseQuadratic .saddle (u 0, u 1) = A ^ 2)
    (hendpoint₂ : ∃ u : E₂, ‖u‖ < r ∧
      R.criticalSurfaceParam p hp u =
        T.base.flow
          (R.criticalSaddlePositiveBoundaryEnd p hp .positive d₂ ρ 0)
          (A ^ 2) ∧
      0 < signedBranch .positive (u 0) ∧
      morseQuadratic .saddle (u 0, u 1) = A ^ 2)
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hAsafe : A ^ 2 ≤ T.safeTime)
    (hbefore : (P.eventBracket t ht).before =
      G.localSeparatedTime p p.2 - A ^ 2)
    (hafter : (P.eventBracket t ht).after =
      G.localSeparatedTime p p.2 + A ^ 2)
    (Vnegative : TamedField
      (R.criticalSaddleNegativeSlice p hp A (by
        rw [← hbefore]
        exact (P.eventBracket t ht).before_regular)))
    (Vpositive : TamedField
      (R.criticalSaddlePositiveSlice p hp A (by
        rw [← hafter]
        exact (P.eventBracket t ht).after_regular)))
    (η : SpatiallyRegularZeroPath
      (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism).G
      (R.criticalSaddleNegativeBoundaryEnd p hp d₁ .negative ρ 0)
      (R.criticalSaddleNegativeBoundaryEnd p hp d₂ .positive ρ 0))
    (hηK : ∀ q, η.toPath q ∈ K)
    (hηtime : ∀ q, tcoord (η.toPath q) = G.localSeparatedTime p p.2)
    (hnegativeNegative :
      ((R.criticalSaddleNegativeBranchOrbitIndex p hp hlocalIndex .negative ρ A
        hρ hA hρrad _ Vnegative : Vnegative.OrbitIndex) : Set E₁) ∈
        ((R.amplitude.toVerticalAmplitude.pullbackSigned C₀).sliceSign
          (P.eventBracket t ht).before
          (P.eventBracket t ht).before_regular).positiveOrbitCollection
            (R.criticalSaddleNegativeSlice_eq_eventBefore P t ht p hp A hbefore ▸
              Vnegative))
    (hnegativePositive :
      ((R.criticalSaddleNegativeBranchOrbitIndex p hp hlocalIndex .positive ρ A
        hρ hA hρrad _ Vnegative : Vnegative.OrbitIndex) : Set E₁) ∈
        ((R.amplitude.toVerticalAmplitude.pullbackSigned C₀).sliceSign
          (P.eventBracket t ht).before
          (P.eventBracket t ht).before_regular).positiveOrbitCollection
            (R.criticalSaddleNegativeSlice_eq_eventBefore P t ht p hp A hbefore ▸
              Vnegative))
    (hnegativeDistinct :
      R.criticalSaddleNegativeBranchOrbitIndex p hp hlocalIndex .negative ρ A
          hρ hA hρrad _ Vnegative ≠
        R.criticalSaddleNegativeBranchOrbitIndex p hp hlocalIndex .positive ρ A
          hρ hA hρrad _ Vnegative)
    (hpositivePositive :
      ((R.criticalSaddlePositiveBranchOrbitIndex p hp hlocalIndex .positive ρ A
        hρ hA hρrad _ Vpositive : Vpositive.OrbitIndex) : Set E₁) ∈
        ((R.amplitude.toVerticalAmplitude.pullbackSigned C₀).sliceSign
          (P.eventBracket t ht).after
          (P.eventBracket t ht).after_regular).positiveOrbitCollection
            (R.criticalSaddlePositiveSlice_eq_eventAfter P t ht p hp A hafter ▸
              Vpositive))
    (exteriorTransport : Vnegative.SelectedDeltaTransport Vpositive
      ((((R.amplitude.toVerticalAmplitude.pullbackSigned C₀).sliceSign
          (P.eventBracket t ht).before
          (P.eventBracket t ht).before_regular).positiveOrbitCollection
            (R.criticalSaddleNegativeSlice_eq_eventBefore P t ht p hp A hbefore ▸
              Vnegative) \
          {((R.criticalSaddleNegativeBranchOrbitIndex p hp hlocalIndex .negative ρ A
            hρ hA hρrad _ Vnegative : Vnegative.OrbitIndex) : Set E₁)}) \
        {((R.criticalSaddleNegativeBranchOrbitIndex p hp hlocalIndex .positive ρ A
          hρ hA hρrad _ Vnegative : Vnegative.OrbitIndex) : Set E₁)})
      (((R.amplitude.toVerticalAmplitude.pullbackSigned C₀).sliceSign
          (P.eventBracket t ht).after
          (P.eventBracket t ht).after_regular).positiveOrbitCollection
            (R.criticalSaddlePositiveSlice_eq_eventAfter P t ht p hp A hafter ▸
              Vpositive) \
        {((R.criticalSaddlePositiveBranchOrbitIndex p hp hlocalIndex .negative ρ A
          hρ hA hρrad _ Vpositive : Vpositive.OrbitIndex) : Set E₁)}))
    (hsplice :
      Vpositive.orbitFrameClass
          (R.criticalSaddlePositiveBranchOrbitIndex p hp hlocalIndex .negative ρ A
            hρ hA hρrad _ Vpositive) =
        Vnegative.orbitFrameClass
            (R.criticalSaddleNegativeBranchOrbitIndex p hp hlocalIndex .negative ρ A
              hρ hA hρrad _ Vnegative) +
          Vnegative.orbitFrameClass
            (R.criticalSaddleNegativeBranchOrbitIndex p hp hlocalIndex .positive ρ A
              hρ hA hρrad _ Vnegative) + 1) :
    PositiveEventLedgerMoveData
      (R.amplitude.toVerticalAmplitude.pullbackSigned C₀) P t ht := by
  let hregNegative : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism).G
      (G.localSeparatedTime p p.2 - A ^ 2) := by
    rw [← hbefore]
    exact (P.eventBracket t ht).before_regular
  let hregPositive : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism).G
      (G.localSeparatedTime p p.2 + A ^ 2) := by
    rw [← hafter]
    exact (P.eventBracket t ht).after_regular
  let hXbefore := R.criticalSaddleNegativeSlice_eq_eventBefore
    P t ht p hp A hbefore
  let hXafter := R.criticalSaddlePositiveSlice_eq_eventAfter
    P t ht p hp A hafter
  let beforeCollection :=
    ((R.amplitude.toVerticalAmplitude.pullbackSigned C₀).sliceSign
      (P.eventBracket t ht).before
      (P.eventBracket t ht).before_regular).positiveOrbitCollection
        (hXbefore ▸ Vnegative)
  let afterCollection :=
    ((R.amplitude.toVerticalAmplitude.pullbackSigned C₀).sliceSign
      (P.eventBracket t ht).after
      (P.eventBracket t ht).after_regular).positiveOrbitCollection
        (hXafter ▸ Vpositive)
  let D := R.negativeTwo_saddleOrbitLedgerDecomposition_of_criticalExteriorPath
    T p hp hlocalIndex d₁ d₂ r ρ A hrShrink hendpoint₁ hendpoint₂
      hρ hA hρrad hAsafe hregPositive Vpositive hregNegative Vnegative
        η hηK hηtime beforeCollection afterCollection
          hnegativeNegative hnegativePositive hnegativeDistinct
            hpositivePositive exteriorTransport
  exact PositiveEventLedgerMoveData.saddleMerge_of_slice_transport
    hXbefore hXafter Vnegative Vpositive D heventIndex hsplice


-- @@ L308-448 verbatim
/-- Actual installed saddle with one component below and two above, packaged
as the chronological positive-ledger split.  As in the merge constructor, the
one-side branch membership is transported from the branch proved equal by the
critical exterior connector. -/
def positiveTwo_positiveEventLedgerSplit_of_criticalExteriorPath
    (R : ExactFiniteMorseJetInstallation G)
    (T : CompactTimeTamedField
      (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism).toLevelCobordismData K)
    (P : MorsePosition
      (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism))
    (t : ℝ) (ht : t ∈ P.eventTimes)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hlocalIndex : (G.localMorseNormalForm p hp).index = .saddle)
    (heventIndex : (P.eventModel t ht).index = .saddle)
    (d₁ d₂ : SaddleBranch) (r ρ A : ℝ)
    (hrShrink : r ≤ (R.criticalModelShrink p hp).radius)
    (hendpoint₁ : ∃ u : E₂, ‖u‖ < r ∧
      R.criticalSurfaceParam p hp u =
        T.base.flow
          (R.criticalSaddleNegativeBoundaryEnd p hp .negative d₁ ρ 0)
          (-(A ^ 2)) ∧
      0 < signedBranch .negative (u 1) ∧
      morseQuadratic .saddle (u 0, u 1) = -(A ^ 2))
    (hendpoint₂ : ∃ u : E₂, ‖u‖ < r ∧
      R.criticalSurfaceParam p hp u =
        T.base.flow
          (R.criticalSaddleNegativeBoundaryEnd p hp .positive d₂ ρ 0)
          (-(A ^ 2)) ∧
      0 < signedBranch .positive (u 1) ∧
      morseQuadratic .saddle (u 0, u 1) = -(A ^ 2))
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hAsafe : A ^ 2 ≤ T.safeTime)
    (hbefore : (P.eventBracket t ht).before =
      G.localSeparatedTime p p.2 - A ^ 2)
    (hafter : (P.eventBracket t ht).after =
      G.localSeparatedTime p p.2 + A ^ 2)
    (Vnegative : TamedField
      (R.criticalSaddleNegativeSlice p hp A (by
        rw [← hbefore]
        exact (P.eventBracket t ht).before_regular)))
    (Vpositive : TamedField
      (R.criticalSaddlePositiveSlice p hp A (by
        rw [← hafter]
        exact (P.eventBracket t ht).after_regular)))
    (η : SpatiallyRegularZeroPath
      (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism).G
      (R.criticalSaddleNegativeBoundaryEnd p hp .negative d₁ ρ 0)
      (R.criticalSaddleNegativeBoundaryEnd p hp .positive d₂ ρ 0))
    (hηK : ∀ q, η.toPath q ∈ K)
    (hηtime : ∀ q, tcoord (η.toPath q) = G.localSeparatedTime p p.2)
    (hpositiveNegative :
      ((R.criticalSaddlePositiveBranchOrbitIndex p hp hlocalIndex .negative ρ A
        hρ hA hρrad _ Vpositive : Vpositive.OrbitIndex) : Set E₁) ∈
        ((R.amplitude.toVerticalAmplitude.pullbackSigned C₀).sliceSign
          (P.eventBracket t ht).after
          (P.eventBracket t ht).after_regular).positiveOrbitCollection
            (R.criticalSaddlePositiveSlice_eq_eventAfter P t ht p hp A hafter ▸
              Vpositive))
    (hpositivePositive :
      ((R.criticalSaddlePositiveBranchOrbitIndex p hp hlocalIndex .positive ρ A
        hρ hA hρrad _ Vpositive : Vpositive.OrbitIndex) : Set E₁) ∈
        ((R.amplitude.toVerticalAmplitude.pullbackSigned C₀).sliceSign
          (P.eventBracket t ht).after
          (P.eventBracket t ht).after_regular).positiveOrbitCollection
            (R.criticalSaddlePositiveSlice_eq_eventAfter P t ht p hp A hafter ▸
              Vpositive))
    (hpositiveDistinct :
      R.criticalSaddlePositiveBranchOrbitIndex p hp hlocalIndex .negative ρ A
          hρ hA hρrad _ Vpositive ≠
        R.criticalSaddlePositiveBranchOrbitIndex p hp hlocalIndex .positive ρ A
          hρ hA hρrad _ Vpositive)
    (hnegativePositive :
      ((R.criticalSaddleNegativeBranchOrbitIndex p hp hlocalIndex .positive ρ A
        hρ hA hρrad _ Vnegative : Vnegative.OrbitIndex) : Set E₁) ∈
        ((R.amplitude.toVerticalAmplitude.pullbackSigned C₀).sliceSign
          (P.eventBracket t ht).before
          (P.eventBracket t ht).before_regular).positiveOrbitCollection
            (R.criticalSaddleNegativeSlice_eq_eventBefore P t ht p hp A hbefore ▸
              Vnegative))
    (exteriorTransport : Vpositive.SelectedDeltaTransport Vnegative
      ((((R.amplitude.toVerticalAmplitude.pullbackSigned C₀).sliceSign
          (P.eventBracket t ht).after
          (P.eventBracket t ht).after_regular).positiveOrbitCollection
            (R.criticalSaddlePositiveSlice_eq_eventAfter P t ht p hp A hafter ▸
              Vpositive) \
          {((R.criticalSaddlePositiveBranchOrbitIndex p hp hlocalIndex .negative ρ A
            hρ hA hρrad _ Vpositive : Vpositive.OrbitIndex) : Set E₁)}) \
        {((R.criticalSaddlePositiveBranchOrbitIndex p hp hlocalIndex .positive ρ A
          hρ hA hρrad _ Vpositive : Vpositive.OrbitIndex) : Set E₁)})
      (((R.amplitude.toVerticalAmplitude.pullbackSigned C₀).sliceSign
          (P.eventBracket t ht).before
          (P.eventBracket t ht).before_regular).positiveOrbitCollection
            (R.criticalSaddleNegativeSlice_eq_eventBefore P t ht p hp A hbefore ▸
              Vnegative) \
        {((R.criticalSaddleNegativeBranchOrbitIndex p hp hlocalIndex .negative ρ A
          hρ hA hρrad _ Vnegative : Vnegative.OrbitIndex) : Set E₁)}))
    (hsplice :
      Vnegative.orbitFrameClass
          (R.criticalSaddleNegativeBranchOrbitIndex p hp hlocalIndex .negative ρ A
            hρ hA hρrad _ Vnegative) =
        Vpositive.orbitFrameClass
            (R.criticalSaddlePositiveBranchOrbitIndex p hp hlocalIndex .negative ρ A
              hρ hA hρrad _ Vpositive) +
          Vpositive.orbitFrameClass
            (R.criticalSaddlePositiveBranchOrbitIndex p hp hlocalIndex .positive ρ A
              hρ hA hρrad _ Vpositive) + 1) :
    PositiveEventLedgerMoveData
      (R.amplitude.toVerticalAmplitude.pullbackSigned C₀) P t ht := by
  let hregNegative : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism).G
      (G.localSeparatedTime p p.2 - A ^ 2) := by
    rw [← hbefore]
    exact (P.eventBracket t ht).before_regular
  let hregPositive : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism).G
      (G.localSeparatedTime p p.2 + A ^ 2) := by
    rw [← hafter]
    exact (P.eventBracket t ht).after_regular
  let hXbefore := R.criticalSaddleNegativeSlice_eq_eventBefore
    P t ht p hp A hbefore
  let hXafter := R.criticalSaddlePositiveSlice_eq_eventAfter
    P t ht p hp A hafter
  let beforeCollection :=
    ((R.amplitude.toVerticalAmplitude.pullbackSigned C₀).sliceSign
      (P.eventBracket t ht).before
      (P.eventBracket t ht).before_regular).positiveOrbitCollection
        (hXbefore ▸ Vnegative)
  let afterCollection :=
    ((R.amplitude.toVerticalAmplitude.pullbackSigned C₀).sliceSign
      (P.eventBracket t ht).after
      (P.eventBracket t ht).after_regular).positiveOrbitCollection
        (hXafter ▸ Vpositive)
  let D := R.positiveTwo_saddleOrbitLedgerDecomposition_of_criticalExteriorPath
    T p hp hlocalIndex d₁ d₂ r ρ A hrShrink hendpoint₁ hendpoint₂
      hρ hA hρrad hAsafe hregPositive Vpositive hregNegative Vnegative
        η hηK hηtime afterCollection beforeCollection
          hpositiveNegative hpositivePositive hpositiveDistinct
            hnegativePositive exteriorTransport
  exact PositiveEventLedgerMoveData.saddleSplit_of_slice_transport
    hXbefore hXafter Vnegative Vpositive D heventIndex hsplice


-- @@ L450-450 verbatim
end ExactFiniteMorseJetInstallation


-- @@ L452-452 verbatim
end Submission
