import Submission.FramedMorseEventExcision


-- @@ L3-15 verbatim
/-!
# Actual installed saddle decompositions

The installed Morse chart supplies two canonical branch orbit indices on each
nearby regular slice.  A critical-level exterior connector collapses the two
indices on exactly one side.  This file combines that fact with positivity of
the distinguished components, distinctness on the two-component side, and a
transport of the remaining exterior components to build the tail-aware
`SaddleOrbitLedgerDecomposition` consumed by the global event ledger.

No complete orbit is identified with a fixed Cassini circle.  All untouched
components remain in the exterior `SelectedDeltaTransport` tail.
-/


-- @@ L17-17 verbatim
set_option autoImplicit false


-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
namespace Submission


-- @@ L23-23 verbatim
open Set Function Metric Filter

-- @@ L24-24 verbatim
open scoped RealInnerProductSpace ContDiff Topology unitInterval


-- @@ L26-26 verbatim
namespace ExactFiniteMorseJetInstallation


-- @@ L28-28 verbatim
variable {n : ℕ}

-- @@ L29-31 verbatim
variable {C : FramedLevelCobordism n} {ι : Type*} [Fintype ι]
  {B : FiniteIFTSurfaceCover C ι}
  {G : GenericFiniteIFTSurfaceAtlas B.toSurfaceChartFamily}

-- @@ L32-32 verbatim
variable {K : Set (EuclideanSpace ℝ (Fin (n + 2)))}


-- @@ L34-34 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

-- @@ L35-35 verbatim
local notation "E₁" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L37-146 verbatim
/-- If the negative branches are joined by one critical exterior connector,
the installed positive slice is the two-component side and the negative slice
is the one-component side of an actual tail-aware saddle decomposition.

Only the positive membership of the `.positive` negative-side branch is
assumed.  The critical exterior path proves equality with the `.negative`
branch, which is then chosen as the canonical outgoing representative. -/
def positiveTwo_saddleOrbitLedgerDecomposition_of_criticalExteriorPath
    (R : ExactFiniteMorseJetInstallation G)
    (T : CompactTimeTamedField
      (R.amplitude.toVerticalAmplitude.pullback C).toLevelCobordismData K)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
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
    (hregPositive : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (G.localSeparatedTime p p.2 + A ^ 2))
    (Vpositive : TamedField
      (R.criticalSaddlePositiveSlice p hp A hregPositive))
    (hregNegative : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (G.localSeparatedTime p p.2 - A ^ 2))
    (Vnegative : TamedField
      (R.criticalSaddleNegativeSlice p hp A hregNegative))
    (η : SpatiallyRegularZeroPath
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (R.criticalSaddleNegativeBoundaryEnd p hp .negative d₁ ρ 0)
      (R.criticalSaddleNegativeBoundaryEnd p hp .positive d₂ ρ 0))
    (hηK : ∀ q, η.toPath q ∈ K)
    (hηtime : ∀ q, tcoord (η.toPath q) = G.localSeparatedTime p p.2)
    (positiveCollection negativeCollection : Set (Set E₁))
    (hpositiveNegative :
      ((R.criticalSaddlePositiveBranchOrbitIndex p hp hindex .negative ρ A
        hρ hA hρrad hregPositive Vpositive : Vpositive.OrbitIndex) :
          Set E₁) ∈ positiveCollection)
    (hpositivePositive :
      ((R.criticalSaddlePositiveBranchOrbitIndex p hp hindex .positive ρ A
        hρ hA hρrad hregPositive Vpositive : Vpositive.OrbitIndex) :
          Set E₁) ∈ positiveCollection)
    (hpositiveDistinct :
      R.criticalSaddlePositiveBranchOrbitIndex p hp hindex .negative ρ A
          hρ hA hρrad hregPositive Vpositive ≠
        R.criticalSaddlePositiveBranchOrbitIndex p hp hindex .positive ρ A
          hρ hA hρrad hregPositive Vpositive)
    (hnegativePositive :
      ((R.criticalSaddleNegativeBranchOrbitIndex p hp hindex .positive ρ A
        hρ hA hρrad hregNegative Vnegative : Vnegative.OrbitIndex) :
          Set E₁) ∈ negativeCollection)
    (exteriorTransport : Vpositive.SelectedDeltaTransport Vnegative
      ((positiveCollection \
          {((R.criticalSaddlePositiveBranchOrbitIndex p hp hindex .negative ρ A
            hρ hA hρrad hregPositive Vpositive : Vpositive.OrbitIndex) :
              Set E₁)}) \
        {((R.criticalSaddlePositiveBranchOrbitIndex p hp hindex .positive ρ A
          hρ hA hρrad hregPositive Vpositive : Vpositive.OrbitIndex) :
            Set E₁)})
      (negativeCollection \
        {((R.criticalSaddleNegativeBranchOrbitIndex p hp hindex .negative ρ A
          hρ hA hρrad hregNegative Vnegative : Vnegative.OrbitIndex) :
            Set E₁)})) :
    SaddleOrbitLedgerDecomposition Vpositive Vnegative
      positiveCollection negativeCollection := by
  let OpositiveNegative :=
    R.criticalSaddlePositiveBranchOrbitIndex p hp hindex .negative ρ A
      hρ hA hρrad hregPositive Vpositive
  let OpositivePositive :=
    R.criticalSaddlePositiveBranchOrbitIndex p hp hindex .positive ρ A
      hρ hA hρrad hregPositive Vpositive
  let OnegativeNegative :=
    R.criticalSaddleNegativeBranchOrbitIndex p hp hindex .negative ρ A
      hρ hA hρrad hregNegative Vnegative
  let OnegativePositive :=
    R.criticalSaddleNegativeBranchOrbitIndex p hp hindex .positive ρ A
      hρ hA hρrad hregNegative Vnegative
  have hcollapse : OnegativeNegative = OnegativePositive := by
    exact R.criticalSaddleNegativeBranchOrbitIndex_eq_of_criticalExteriorPath
      T p hp hindex d₁ .negative d₂ .positive r ρ A hrShrink
        hendpoint₁ hendpoint₂ hρ hA hρrad hAsafe hregNegative Vnegative
          η hηK hηtime
  have hnegativeNegative : ((OnegativeNegative : Vnegative.OrbitIndex) :
      Set E₁) ∈ negativeCollection := by
    rw [hcollapse]
    exact hnegativePositive
  exact {
    incoming₁ := ⟨OpositiveNegative, hpositiveNegative⟩
    incoming₂ := ⟨OpositivePositive, hpositivePositive⟩
    incoming_ne := by
      intro heq
      exact hpositiveDistinct (congrArg Subtype.val heq)
    outgoing := ⟨OnegativeNegative, hnegativeNegative⟩
    exteriorTransport := exteriorTransport
  }


-- @@ L148-256 verbatim
/-- If the positive branches are joined by one critical exterior connector,
the installed negative slice is the two-component side and the positive slice
is the one-component side of an actual tail-aware saddle decomposition.

As above, membership of only one one-side branch is assumed; equality of the
two positive branch indices is derived from the critical exterior path. -/
def negativeTwo_saddleOrbitLedgerDecomposition_of_criticalExteriorPath
    (R : ExactFiniteMorseJetInstallation G)
    (T : CompactTimeTamedField
      (R.amplitude.toVerticalAmplitude.pullback C).toLevelCobordismData K)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
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
    (hregPositive : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (G.localSeparatedTime p p.2 + A ^ 2))
    (Vpositive : TamedField
      (R.criticalSaddlePositiveSlice p hp A hregPositive))
    (hregNegative : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (G.localSeparatedTime p p.2 - A ^ 2))
    (Vnegative : TamedField
      (R.criticalSaddleNegativeSlice p hp A hregNegative))
    (η : SpatiallyRegularZeroPath
      (R.amplitude.toVerticalAmplitude.pullback C).G
      (R.criticalSaddleNegativeBoundaryEnd p hp d₁ .negative ρ 0)
      (R.criticalSaddleNegativeBoundaryEnd p hp d₂ .positive ρ 0))
    (hηK : ∀ q, η.toPath q ∈ K)
    (hηtime : ∀ q, tcoord (η.toPath q) = G.localSeparatedTime p p.2)
    (negativeCollection positiveCollection : Set (Set E₁))
    (hnegativeNegative :
      ((R.criticalSaddleNegativeBranchOrbitIndex p hp hindex .negative ρ A
        hρ hA hρrad hregNegative Vnegative : Vnegative.OrbitIndex) :
          Set E₁) ∈ negativeCollection)
    (hnegativePositive :
      ((R.criticalSaddleNegativeBranchOrbitIndex p hp hindex .positive ρ A
        hρ hA hρrad hregNegative Vnegative : Vnegative.OrbitIndex) :
          Set E₁) ∈ negativeCollection)
    (hnegativeDistinct :
      R.criticalSaddleNegativeBranchOrbitIndex p hp hindex .negative ρ A
          hρ hA hρrad hregNegative Vnegative ≠
        R.criticalSaddleNegativeBranchOrbitIndex p hp hindex .positive ρ A
          hρ hA hρrad hregNegative Vnegative)
    (hpositivePositive :
      ((R.criticalSaddlePositiveBranchOrbitIndex p hp hindex .positive ρ A
        hρ hA hρrad hregPositive Vpositive : Vpositive.OrbitIndex) :
          Set E₁) ∈ positiveCollection)
    (exteriorTransport : Vnegative.SelectedDeltaTransport Vpositive
      ((negativeCollection \
          {((R.criticalSaddleNegativeBranchOrbitIndex p hp hindex .negative ρ A
            hρ hA hρrad hregNegative Vnegative : Vnegative.OrbitIndex) :
              Set E₁)}) \
        {((R.criticalSaddleNegativeBranchOrbitIndex p hp hindex .positive ρ A
          hρ hA hρrad hregNegative Vnegative : Vnegative.OrbitIndex) :
            Set E₁)})
      (positiveCollection \
        {((R.criticalSaddlePositiveBranchOrbitIndex p hp hindex .negative ρ A
          hρ hA hρrad hregPositive Vpositive : Vpositive.OrbitIndex) :
            Set E₁)})) :
    SaddleOrbitLedgerDecomposition Vnegative Vpositive
      negativeCollection positiveCollection := by
  let OnegativeNegative :=
    R.criticalSaddleNegativeBranchOrbitIndex p hp hindex .negative ρ A
      hρ hA hρrad hregNegative Vnegative
  let OnegativePositive :=
    R.criticalSaddleNegativeBranchOrbitIndex p hp hindex .positive ρ A
      hρ hA hρrad hregNegative Vnegative
  let OpositiveNegative :=
    R.criticalSaddlePositiveBranchOrbitIndex p hp hindex .negative ρ A
      hρ hA hρrad hregPositive Vpositive
  let OpositivePositive :=
    R.criticalSaddlePositiveBranchOrbitIndex p hp hindex .positive ρ A
      hρ hA hρrad hregPositive Vpositive
  have hcollapse : OpositiveNegative = OpositivePositive := by
    exact R.criticalSaddlePositiveBranchOrbitIndex_eq_of_criticalExteriorPath
      T p hp hindex .negative d₁ .positive d₂ r ρ A hrShrink
        hendpoint₁ hendpoint₂ hρ hA hρrad hAsafe hregPositive Vpositive
          η hηK hηtime
  have hpositiveNegative : ((OpositiveNegative : Vpositive.OrbitIndex) :
      Set E₁) ∈ positiveCollection := by
    rw [hcollapse]
    exact hpositivePositive
  exact {
    incoming₁ := ⟨OnegativeNegative, hnegativeNegative⟩
    incoming₂ := ⟨OnegativePositive, hnegativePositive⟩
    incoming_ne := by
      intro heq
      exact hnegativeDistinct (congrArg Subtype.val heq)
    outgoing := ⟨OpositiveNegative, hpositiveNegative⟩
    exteriorTransport := exteriorTransport
  }


-- @@ L258-258 verbatim
end ExactFiniteMorseJetInstallation


-- @@ L260-260 verbatim
end Submission
