import Submission.InstalledSaddlePositiveLedgerMove


-- @@ L3-23 verbatim
/-!
# Geometric inputs for installed positive saddle events

This module discharges three local inputs left explicit by the chronological
installed-saddle ledger constructors.

* A positive installed critical center forces every distinguished local saddle
  branch orbit to belong to the literal positive orbit collection, both on the
  local slices and after transport to the event-bracket slices.
* The existing quantitative short-flow theorem produces the two endpoint
  witnesses from a local fiber cover, branch preservation, and explicit
  small-time inequalities.
* Closed homotopies splitting the actual loops into exterior factors and a
  local saddle contract imply the required frame splice in either
  chronological orientation; a stronger literal-Cassini adapter is retained.

The critical exterior connector, distinctness of the two global orbit
components, exact exterior-complement transport, and construction of the
three closed exterior-relative frame homotopies remain genuinely global
geometric inputs.
-/


-- @@ L25-25 verbatim
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


-- @@ L35-45 verbatim
theorem positiveOrbitCollection_mem_of_slice_transport
    {X Y : FramedLevelSet n} (hXY : X = Y)
    (S : FiberSign X) (T : FiberSign Y) (hST : HEq S T)
    (V : TamedField X)
    (A : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hA : A ∈ S.positiveOrbitCollection V) :
    A ∈ T.positiveOrbitCollection (hXY ▸ V) := by
  subst Y
  have hST' : S = T := eq_of_heq hST
  subst T
  exact hA


-- @@ L47-47 verbatim
namespace ExactFiniteMorseJetInstallation


-- @@ L49-51 verbatim
variable {C : FramedLevelCobordism n} {ι : Type*} [Fintype ι]
  {B : FiniteIFTSurfaceCover C ι}
  {G : GenericFiniteIFTSurfaceAtlas B.toSurfaceChartFamily}


-- @@ L53-53 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)


-- @@ L55-60 verbatim
@[simp] theorem criticalSurfaceParam_zero_for_radialPath
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints) :
    R.criticalSurfaceParam p hp 0 = R.criticalCenter p := by
  rw [criticalSurfaceParam, criticalCenter,
    (G.localMorseNormalForm p hp).param_zero, add_zero]


-- @@ L62-81 verbatim
def criticalSurfaceRadialPath
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (u : E₂) (hu : ‖u‖ < (R.criticalModelShrink p hp).radius) :
    Path (R.criticalCenter p) (R.criticalSurfaceParam p hp u) where
  toContinuousMap := {
    toFun := fun q => R.criticalSurfaceParam p hp ((q : ℝ) • u)
    continuous_toFun := by
      rw [continuous_iff_continuousAt]
      intro q
      apply (R.criticalSurfaceParam_differentiableAt p hp _ ?_).continuousAt.comp'
        ?_
      · have hqnorm : ‖(q : ℝ) • u‖ ≤ ‖u‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg q.2.1]
          nlinarith [q.2.2, norm_nonneg u]
        exact hqnorm.trans_lt hu
      · fun_prop
  }
  source' := by simp
  target' := by simp


-- @@ L83-94 verbatim
theorem criticalSurfaceRadialPath_fiber
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (u : E₂) (hu : ‖u‖ < (R.criticalModelShrink p hp).radius)
    (q : I) :
    (R.amplitude.toVerticalAmplitude.pullback C).G
      (R.criticalSurfaceRadialPath p hp u hu q) = 0 := by
  apply R.criticalSurfaceParam_fiber
  have hqnorm : ‖(q : ℝ) • u‖ ≤ ‖u‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg q.2.1]
    nlinarith [q.2.2, norm_nonneg u]
  exact hqnorm.trans_lt hu


-- @@ L96-96 verbatim
end ExactFiniteMorseJetInstallation


-- @@ L98-98 verbatim
variable {X₀ X₁ : FramedLevelSet n}

-- @@ L99-99 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}

-- @@ L100-100 verbatim
variable {C₀ : SignedFramedLevelCobordism S₀ S₁}


-- @@ L102-102 verbatim
namespace ExactFiniteMorseJetInstallation


-- @@ L104-106 verbatim
variable {ι : Type*} [Fintype ι]
  {B : FiniteIFTSurfaceCover C₀.cobordism ι}
  {G : GenericFiniteIFTSurfaceAtlas B.toSurfaceChartFamily}


-- @@ L108-108 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)

-- @@ L109-109 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L111-156 verbatim
/-- Specialize the positive short-flow endpoint theorem to an explicit
installed positive-side critical boundary end. -/
theorem exists_positiveFlowEndpoint_criticalSaddleBoundaryEnd
    (R : ExactFiniteMorseJetInstallation G)
    {K : Set E'}
    (T : CompactTimeTamedField
      (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism).toLevelCobordismData K)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b e : SaddleBranch) (ρ : ℝ)
    (hρ : 0 < ρ)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hu₀K : R.criticalSaddlePositiveBoundaryEnd p hp b e ρ 0 ∈ K)
    {r εcover εbranch A : ℝ}
    (hrShrink : r ≤ (R.criticalModelShrink p hp).radius)
    (hcover : ∀ v : E', dist v (R.criticalCenter p) < εcover →
      (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism).G v = 0 →
      ∃ u : E₂, ‖u‖ < r ∧ R.criticalSurfaceParam p hp u = v)
    (hbranch : ∀ u : E₂, ‖u‖ < r →
      dist (R.criticalSurfaceParam p hp u)
        (R.criticalSaddlePositiveBoundaryEnd p hp b e ρ 0) < εbranch →
      0 < signedBranch b (u 0))
    (hAsafe : A ^ 2 ≤ T.safeTime)
    (hcenterClose : dist
        (R.criticalSaddlePositiveBoundaryEnd p hp b e ρ 0)
        (R.criticalCenter p) + (T.base.bound : ℝ) * A ^ 2 < εcover)
    (hbranchClose : (T.base.bound : ℝ) * A ^ 2 < εbranch) :
    ∃ u : E₂, ‖u‖ < r ∧
      R.criticalSurfaceParam p hp u =
        T.base.flow
          (R.criticalSaddlePositiveBoundaryEnd p hp b e ρ 0) (A ^ 2) ∧
      0 < signedBranch b (u 0) ∧
      morseQuadratic .saddle (u 0, u 1) = A ^ 2 := by
  apply R.exists_positiveFlowEndpoint_morseParam T p hp hindex b 0
    (saddlePositiveBoundaryEndParam b e ρ 0)
  · rw [norm_saddlePositiveBoundaryEndParam b e hρ]
    · exact hρrad
    · nlinarith
  · simp [saddlePositiveBoundaryEndParam]
  · simpa [criticalSaddlePositiveBoundaryEnd] using hu₀K
  · exact hrShrink
  · exact hcover
  · simpa [criticalSaddlePositiveBoundaryEnd] using hbranch
  · exact hAsafe
  · simpa [criticalSaddlePositiveBoundaryEnd] using hcenterClose
  · exact hbranchClose


-- @@ L158-203 verbatim
/-- Specialize the negative short-flow endpoint theorem to an explicit
installed negative-side critical boundary end. -/
theorem exists_negativeFlowEndpoint_criticalSaddleBoundaryEnd
    (R : ExactFiniteMorseJetInstallation G)
    {K : Set E'}
    (T : CompactTimeTamedField
      (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism).toLevelCobordismData K)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b e : SaddleBranch) (ρ : ℝ)
    (hρ : 0 < ρ)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hu₀K : R.criticalSaddleNegativeBoundaryEnd p hp b e ρ 0 ∈ K)
    {r εcover εbranch A : ℝ}
    (hrShrink : r ≤ (R.criticalModelShrink p hp).radius)
    (hcover : ∀ v : E', dist v (R.criticalCenter p) < εcover →
      (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism).G v = 0 →
      ∃ u : E₂, ‖u‖ < r ∧ R.criticalSurfaceParam p hp u = v)
    (hbranch : ∀ u : E₂, ‖u‖ < r →
      dist (R.criticalSurfaceParam p hp u)
        (R.criticalSaddleNegativeBoundaryEnd p hp b e ρ 0) < εbranch →
      0 < signedBranch b (u 1))
    (hAsafe : A ^ 2 ≤ T.safeTime)
    (hcenterClose : dist
        (R.criticalSaddleNegativeBoundaryEnd p hp b e ρ 0)
        (R.criticalCenter p) + (T.base.bound : ℝ) * A ^ 2 < εcover)
    (hbranchClose : (T.base.bound : ℝ) * A ^ 2 < εbranch) :
    ∃ u : E₂, ‖u‖ < r ∧
      R.criticalSurfaceParam p hp u =
        T.base.flow
          (R.criticalSaddleNegativeBoundaryEnd p hp b e ρ 0) (-(A ^ 2)) ∧
      0 < signedBranch b (u 1) ∧
      morseQuadratic .saddle (u 0, u 1) = -(A ^ 2) := by
  apply R.exists_negativeFlowEndpoint_morseParam T p hp hindex b 1
    (saddleNegativeBoundaryEndParam b e ρ 0)
  · rw [norm_saddleNegativeBoundaryEndParam b e hρ]
    · exact hρrad
    · nlinarith
  · simp [saddleNegativeBoundaryEndParam]
  · simpa [criticalSaddleNegativeBoundaryEnd] using hu₀K
  · exact hrShrink
  · exact hcover
  · simpa [criticalSaddleNegativeBoundaryEnd] using hbranch
  · exact hAsafe
  · simpa [criticalSaddleNegativeBoundaryEnd] using hcenterClose
  · exact hbranchClose


-- @@ L205-260 verbatim
/-- The local fiber-cover and signed-branch-neighborhood theorems supply a
quantitative contract for every sufficiently short positive endpoint flow. -/
theorem exists_positiveBoundaryEnd_shortFlowContract
    (R : ExactFiniteMorseJetInstallation G)
    {K : Set E'}
    (T : CompactTimeTamedField
      (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism).toLevelCobordismData K)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b e : SaddleBranch) (r rInj ρ : ℝ)
    (hr : 0 < r) (hrrInj : r < rInj)
    (hrInjShrink : rInj ≤ (R.criticalModelShrink p hp).radius)
    (hinj : Set.InjOn (R.criticalSurfaceParam p hp)
      (ball (0 : E₂) rInj))
    (hρ : 0 < ρ) (hρrInj : ρ < rInj)
    (hu₀K : R.criticalSaddlePositiveBoundaryEnd p hp b e ρ 0 ∈ K) :
    ∃ εcover > 0, ∃ εbranch > 0,
      ∀ {A : ℝ}, A ^ 2 ≤ T.safeTime →
        dist (R.criticalSaddlePositiveBoundaryEnd p hp b e ρ 0)
            (R.criticalCenter p) + (T.base.bound : ℝ) * A ^ 2 < εcover →
        (T.base.bound : ℝ) * A ^ 2 < εbranch →
        ∃ u : E₂, ‖u‖ < r ∧
          R.criticalSurfaceParam p hp u =
            T.base.flow
              (R.criticalSaddlePositiveBoundaryEnd p hp b e ρ 0) (A ^ 2) ∧
          0 < signedBranch b (u 0) ∧
          morseQuadratic .saddle (u 0, u 1) = A ^ 2 := by
  let u₀ := saddlePositiveBoundaryEndParam b e ρ 0
  have hu₀ : ‖u₀‖ < rInj := by
    rw [norm_saddlePositiveBoundaryEndParam b e hρ]
    · exact hρrInj
    · nlinarith
  have hσ : 0 < saddleBoundaryParameter ρ 0 := by
    unfold saddleBoundaryParameter
    exact Real.sqrt_pos.2 (by nlinarith [sq_pos_of_pos hρ])
  have hsqrtσ : Real.sqrt (saddleBoundaryParameter ρ 0 ^ 2) =
      saddleBoundaryParameter ρ 0 := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hσ]
  have hu₀sign : 0 < signedBranch b (u₀ 0) := by
    cases b <;> cases e <;>
      simpa [u₀, saddlePositiveBoundaryEndParam, saddlePositiveArc, hsqrtσ,
        signedBranch, abs_of_pos hσ] using hσ
  obtain ⟨εcover, hεcover, hcover⟩ :=
    R.covers_fiber_within_criticalSurfaceParam_radius p hp hr
  obtain ⟨εbranch, hεbranch, hbranch⟩ :=
    R.exists_criticalSurfaceParam_signedBranch_neighborhood
      p hp b 0 u₀ hr hrrInj hrInjShrink hinj hu₀ hu₀sign
  refine ⟨εcover, hεcover, εbranch, hεbranch, ?_⟩
  intro A hAsafe hcenterClose hbranchClose
  apply R.exists_positiveFlowEndpoint_criticalSaddleBoundaryEnd
    T p hp hindex b e ρ hρ (hρrInj.trans_le hrInjShrink) hu₀K
      (hrrInj.le.trans hrInjShrink) hcover
  · simpa [u₀, criticalSaddlePositiveBoundaryEnd] using hbranch
  · exact hAsafe
  · exact hcenterClose
  · exact hbranchClose


-- @@ L262-316 verbatim
/-- Negative-time counterpart of `exists_positiveBoundaryEnd_shortFlowContract`. -/
theorem exists_negativeBoundaryEnd_shortFlowContract
    (R : ExactFiniteMorseJetInstallation G)
    {K : Set E'}
    (T : CompactTimeTamedField
      (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism).toLevelCobordismData K)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (b e : SaddleBranch) (r rInj ρ : ℝ)
    (hr : 0 < r) (hrrInj : r < rInj)
    (hrInjShrink : rInj ≤ (R.criticalModelShrink p hp).radius)
    (hinj : Set.InjOn (R.criticalSurfaceParam p hp)
      (ball (0 : E₂) rInj))
    (hρ : 0 < ρ) (hρrInj : ρ < rInj)
    (hu₀K : R.criticalSaddleNegativeBoundaryEnd p hp b e ρ 0 ∈ K) :
    ∃ εcover > 0, ∃ εbranch > 0,
      ∀ {A : ℝ}, A ^ 2 ≤ T.safeTime →
        dist (R.criticalSaddleNegativeBoundaryEnd p hp b e ρ 0)
            (R.criticalCenter p) + (T.base.bound : ℝ) * A ^ 2 < εcover →
        (T.base.bound : ℝ) * A ^ 2 < εbranch →
        ∃ u : E₂, ‖u‖ < r ∧
          R.criticalSurfaceParam p hp u =
            T.base.flow
              (R.criticalSaddleNegativeBoundaryEnd p hp b e ρ 0) (-(A ^ 2)) ∧
          0 < signedBranch b (u 1) ∧
          morseQuadratic .saddle (u 0, u 1) = -(A ^ 2) := by
  let u₀ := saddleNegativeBoundaryEndParam b e ρ 0
  have hu₀ : ‖u₀‖ < rInj := by
    rw [norm_saddleNegativeBoundaryEndParam b e hρ]
    · exact hρrInj
    · nlinarith
  have hσ : 0 < saddleBoundaryParameter ρ 0 := by
    unfold saddleBoundaryParameter
    exact Real.sqrt_pos.2 (by nlinarith [sq_pos_of_pos hρ])
  have hsqrtσ : Real.sqrt (saddleBoundaryParameter ρ 0 ^ 2) =
      saddleBoundaryParameter ρ 0 := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hσ]
  have hu₀sign : 0 < signedBranch b (u₀ 1) := by
    cases b <;> cases e <;>
      simpa [u₀, saddleNegativeBoundaryEndParam, saddleNegativeArc, hsqrtσ,
        signedBranch, abs_of_pos hσ] using hσ
  obtain ⟨εcover, hεcover, hcover⟩ :=
    R.covers_fiber_within_criticalSurfaceParam_radius p hp hr
  obtain ⟨εbranch, hεbranch, hbranch⟩ :=
    R.exists_criticalSurfaceParam_signedBranch_neighborhood
      p hp b 1 u₀ hr hrrInj hrInjShrink hinj hu₀ hu₀sign
  refine ⟨εcover, hεcover, εbranch, hεbranch, ?_⟩
  intro A hAsafe hcenterClose hbranchClose
  apply R.exists_negativeFlowEndpoint_criticalSaddleBoundaryEnd
    T p hp hindex b e ρ hρ (hρrInj.trans_le hrInjShrink) hu₀K
      (hrrInj.le.trans hrInjShrink) hcover
  · simpa [u₀, criticalSaddleNegativeBoundaryEnd] using hbranch
  · exact hAsafe
  · exact hcenterClose
  · exact hbranchClose



-- @@ L319-333 verbatim
/-- The left positive-side endpoint used by the merge constructor lies in the
flow domain whenever the critical exterior connector lies there. -/
theorem positiveBoundaryEnd_mem_of_criticalExteriorPath_zero
    (R : ExactFiniteMorseJetInstallation G)
    {K : Set E'}
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (d₁ d₂ : SaddleBranch) (ρ : ℝ)
    (η : SpatiallyRegularZeroPath
      (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism).G
      (R.criticalSaddleNegativeBoundaryEnd p hp d₁ .negative ρ 0)
      (R.criticalSaddleNegativeBoundaryEnd p hp d₂ .positive ρ 0))
    (hηK : ∀ q, η.toPath q ∈ K) :
    R.criticalSaddlePositiveBoundaryEnd p hp .negative d₁ ρ 0 ∈ K := by
  rw [R.criticalSaddle_boundary_pairing_switch p hp .negative d₁ ρ]
  simpa using hηK 0


-- @@ L335-349 verbatim
/-- The right positive-side endpoint used by the merge constructor also lies
in the flow domain of the critical exterior connector. -/
theorem positiveBoundaryEnd_mem_of_criticalExteriorPath_one
    (R : ExactFiniteMorseJetInstallation G)
    {K : Set E'}
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (d₁ d₂ : SaddleBranch) (ρ : ℝ)
    (η : SpatiallyRegularZeroPath
      (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism).G
      (R.criticalSaddleNegativeBoundaryEnd p hp d₁ .negative ρ 0)
      (R.criticalSaddleNegativeBoundaryEnd p hp d₂ .positive ρ 0))
    (hηK : ∀ q, η.toPath q ∈ K) :
    R.criticalSaddlePositiveBoundaryEnd p hp .positive d₂ ρ 0 ∈ K := by
  rw [R.criticalSaddle_boundary_pairing_switch p hp .positive d₂ ρ]
  simpa using hηK 1


-- @@ L351-364 verbatim
/-- The first negative-side endpoint is the source of the critical exterior
connector and hence lies in its flow domain. -/
theorem negativeBoundaryEnd_mem_of_criticalExteriorPath_zero
    (R : ExactFiniteMorseJetInstallation G)
    {K : Set E'}
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (d₁ d₂ : SaddleBranch) (ρ : ℝ)
    (η : SpatiallyRegularZeroPath
      (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism).G
      (R.criticalSaddleNegativeBoundaryEnd p hp d₁ .negative ρ 0)
      (R.criticalSaddleNegativeBoundaryEnd p hp d₂ .positive ρ 0))
    (hηK : ∀ q, η.toPath q ∈ K) :
    R.criticalSaddleNegativeBoundaryEnd p hp d₁ .negative ρ 0 ∈ K := by
  simpa using hηK 0


-- @@ L366-379 verbatim
/-- The second negative-side endpoint is the target of the critical exterior
connector and hence lies in its flow domain. -/
theorem negativeBoundaryEnd_mem_of_criticalExteriorPath_one
    (R : ExactFiniteMorseJetInstallation G)
    {K : Set E'}
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (d₁ d₂ : SaddleBranch) (ρ : ℝ)
    (η : SpatiallyRegularZeroPath
      (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism).G
      (R.criticalSaddleNegativeBoundaryEnd p hp d₁ .negative ρ 0)
      (R.criticalSaddleNegativeBoundaryEnd p hp d₂ .positive ρ 0))
    (hηK : ∀ q, η.toPath q ∈ K) :
    R.criticalSaddleNegativeBoundaryEnd p hp d₂ .positive ρ 0 ∈ K := by
  simpa using hηK 1


-- @@ L381-460 verbatim
/-- Positivity at the critical center propagates to either distinguished
positive-side branch orbit. -/
theorem positiveBranch_mem_positiveOrbitCollection
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (hcenterPositive :
      0 < (R.amplitude.toVerticalAmplitude.pullbackSigned C₀)
        (R.criticalCenter p))
    (b : SaddleBranch) (ρ A : ℝ)
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism).G
      (G.localSeparatedTime p p.2 + A ^ 2))
    (V : TamedField (R.criticalSaddlePositiveSlice p hp A hreg)) :
    ((R.criticalSaddlePositiveBranchOrbitIndex p hp hindex b ρ A
      hρ hA hρrad hreg V : V.OrbitIndex) :
        Set (EuclideanSpace ℝ (Fin (n + 1)))) ∈
      ((R.amplitude.toVerticalAmplitude.pullbackSigned C₀).sliceSign
        (G.localSeparatedTime p p.2 + A ^ 2) hreg).positiveOrbitCollection V := by
  let Cinstalled := R.amplitude.toVerticalAmplitude.pullbackSigned C₀
  change 0 < Cinstalled (R.criticalCenter p) at hcenterPositive
  let u₀ := saddlePositiveBoundaryEndParam b .negative ρ 0
  have hzeroLevel : (0 : ℝ) ^ 2 < ρ ^ 2 := by nlinarith
  have hu₀ : ‖u₀‖ < (R.criticalModelShrink p hp).radius := by
    rw [norm_saddlePositiveBoundaryEndParam b .negative hρ hzeroLevel]
    exact hρrad
  let γcenter := R.criticalSurfaceRadialPath p hp u₀ hu₀
  have hcenterPathFiber : ∀ q,
      Cinstalled.cobordism.G (γcenter q) = 0 := by
    intro q
    exact R.criticalSurfaceRadialPath_fiber p hp u₀ hu₀ q
  have hcriticalPositive :
      0 < Cinstalled (R.criticalSurfaceParam p hp u₀) := by
    have hsign := Cinstalled.pos_iff_of_zeroFiber_path
      γcenter hcenterPathFiber
    have hstart : 0 < Cinstalled (γcenter 0) := by
      simpa [γcenter] using hcenterPositive
    have hend := hsign.mp hstart
    simpa [γcenter] using hend
  let γtrack := R.criticalSaddlePositiveBoundaryTrack p hp
    b .negative ρ A hρ hA hρrad
  have htrackFiber : ∀ q, Cinstalled.cobordism.G (γtrack q) = 0 := by
    intro q
    exact R.criticalSaddlePositiveBoundaryTrack_fiber p hp
      b .negative ρ A hρ hA hρrad q
  have hboundaryPositive :
      0 < Cinstalled
        (R.criticalSaddlePositiveBoundaryEnd p hp b .negative ρ A) := by
    have hsign := Cinstalled.pos_iff_of_zeroFiber_path γtrack htrackFiber
    have hstart : 0 < Cinstalled (γtrack 0) := by
      simpa [γtrack, u₀, criticalSaddlePositiveBoundaryEnd] using
        hcriticalPositive
    have hend := hsign.mp hstart
    simpa [γtrack] using hend
  let O := R.criticalSaddlePositiveBranchOrbitIndex p hp hindex b ρ A
    hρ hA hρrad hreg V
  let S := Cinstalled.sliceSign
    (G.localSeparatedTime p p.2 + A ^ 2) hreg
  apply (S.mem_positiveOrbitCollection_iff V O).2
  have hpointFiber : spacePart
      (R.criticalSaddlePositiveBoundaryEnd p hp b .negative ρ A) ∈
      (R.criticalSaddlePositiveSlice p hp A hreg).fiber :=
    R.criticalSaddlePositiveBoundaryEnd_mem_slice_fiber p hp hindex
      b .negative ρ A hρ hA hρrad hreg
  have hpointPositive : 0 < S (spacePart
      (R.criticalSaddlePositiveBoundaryEnd p hp b .negative ρ A)) := by
    change 0 < Cinstalled (cobSpaceTime (spacePart
      (R.criticalSaddlePositiveBoundaryEnd p hp b .negative ρ A))
        (G.localSeparatedTime p p.2 + A ^ 2))
    rw [← R.criticalSaddlePositiveBoundaryEnd_time p hp hindex
      b .negative hρ hA hρrad, spaceTime_spacePart]
    exact hboundaryPositive
  have hmem : V.orbitPoint O ∈ V.orbit (spacePart
      (R.criticalSaddlePositiveBoundaryEnd p hp b .negative ρ A)) := by
    change V.orbitPoint O ∈ (O : Set (EuclideanSpace ℝ (Fin (n + 1))))
    rw [V.orbitPoint_orbit O]
    exact V.mem_orbit_self _
  exact (S.pos_iff_of_mem_orbit V hpointFiber hmem).mp hpointPositive


-- @@ L462-541 verbatim
/-- Positivity at the critical center propagates to either distinguished
negative-side branch orbit. -/
theorem negativeBranch_mem_positiveOrbitCollection
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (hcenterPositive :
      0 < (R.amplitude.toVerticalAmplitude.pullbackSigned C₀)
        (R.criticalCenter p))
    (b : SaddleBranch) (ρ A : ℝ)
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism).G
      (G.localSeparatedTime p p.2 - A ^ 2))
    (V : TamedField (R.criticalSaddleNegativeSlice p hp A hreg)) :
    ((R.criticalSaddleNegativeBranchOrbitIndex p hp hindex b ρ A
      hρ hA hρrad hreg V : V.OrbitIndex) :
        Set (EuclideanSpace ℝ (Fin (n + 1)))) ∈
      ((R.amplitude.toVerticalAmplitude.pullbackSigned C₀).sliceSign
        (G.localSeparatedTime p p.2 - A ^ 2) hreg).positiveOrbitCollection V := by
  let Cinstalled := R.amplitude.toVerticalAmplitude.pullbackSigned C₀
  change 0 < Cinstalled (R.criticalCenter p) at hcenterPositive
  let u₀ := saddleNegativeBoundaryEndParam b .negative ρ 0
  have hzeroLevel : (0 : ℝ) ^ 2 < ρ ^ 2 := by nlinarith
  have hu₀ : ‖u₀‖ < (R.criticalModelShrink p hp).radius := by
    rw [norm_saddleNegativeBoundaryEndParam b .negative hρ hzeroLevel]
    exact hρrad
  let γcenter := R.criticalSurfaceRadialPath p hp u₀ hu₀
  have hcenterPathFiber : ∀ q,
      Cinstalled.cobordism.G (γcenter q) = 0 := by
    intro q
    exact R.criticalSurfaceRadialPath_fiber p hp u₀ hu₀ q
  have hcriticalPositive :
      0 < Cinstalled (R.criticalSurfaceParam p hp u₀) := by
    have hsign := Cinstalled.pos_iff_of_zeroFiber_path
      γcenter hcenterPathFiber
    have hstart : 0 < Cinstalled (γcenter 0) := by
      simpa [γcenter] using hcenterPositive
    have hend := hsign.mp hstart
    simpa [γcenter] using hend
  let γtrack := R.criticalSaddleNegativeBoundaryTrack p hp
    b .negative ρ A hρ hA hρrad
  have htrackFiber : ∀ q, Cinstalled.cobordism.G (γtrack q) = 0 := by
    intro q
    exact R.criticalSaddleNegativeBoundaryTrack_fiber p hp
      b .negative ρ A hρ hA hρrad q
  have hboundaryPositive :
      0 < Cinstalled
        (R.criticalSaddleNegativeBoundaryEnd p hp b .negative ρ A) := by
    have hsign := Cinstalled.pos_iff_of_zeroFiber_path γtrack htrackFiber
    have hstart : 0 < Cinstalled (γtrack 0) := by
      simpa [γtrack, u₀, criticalSaddleNegativeBoundaryEnd] using
        hcriticalPositive
    have hend := hsign.mp hstart
    simpa [γtrack] using hend
  let O := R.criticalSaddleNegativeBranchOrbitIndex p hp hindex b ρ A
    hρ hA hρrad hreg V
  let S := Cinstalled.sliceSign
    (G.localSeparatedTime p p.2 - A ^ 2) hreg
  apply (S.mem_positiveOrbitCollection_iff V O).2
  have hpointFiber : spacePart
      (R.criticalSaddleNegativeBoundaryEnd p hp b .negative ρ A) ∈
      (R.criticalSaddleNegativeSlice p hp A hreg).fiber :=
    R.criticalSaddleNegativeBoundaryEnd_mem_slice_fiber p hp hindex
      b .negative ρ A hρ hA hρrad hreg
  have hpointPositive : 0 < S (spacePart
      (R.criticalSaddleNegativeBoundaryEnd p hp b .negative ρ A)) := by
    change 0 < Cinstalled (cobSpaceTime (spacePart
      (R.criticalSaddleNegativeBoundaryEnd p hp b .negative ρ A))
        (G.localSeparatedTime p p.2 - A ^ 2))
    rw [← R.criticalSaddleNegativeBoundaryEnd_time p hp hindex
      b .negative hρ hA hρrad, spaceTime_spacePart]
    exact hboundaryPositive
  have hmem : V.orbitPoint O ∈ V.orbit (spacePart
      (R.criticalSaddleNegativeBoundaryEnd p hp b .negative ρ A)) := by
    change V.orbitPoint O ∈ (O : Set (EuclideanSpace ℝ (Fin (n + 1))))
    rw [V.orbitPoint_orbit O]
    exact V.mem_orbit_self _
  exact (S.pos_iff_of_mem_orbit V hpointFiber hmem).mp hpointPositive


-- @@ L543-568 verbatim
theorem positiveSliceSign_heq_eventAfter
    (R : ExactFiniteMorseJetInstallation G)
    (P : MorsePosition
      (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism))
    (t : ℝ) (ht : t ∈ P.eventTimes)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (A : ℝ)
    (hafter : (P.eventBracket t ht).after =
      G.localSeparatedTime p p.2 + A ^ 2) :
    HEq
      ((R.amplitude.toVerticalAmplitude.pullbackSigned C₀).sliceSign
        (G.localSeparatedTime p p.2 + A ^ 2) (by
          rw [← hafter]
          exact (P.eventBracket t ht).after_regular))
      ((R.amplitude.toVerticalAmplitude.pullbackSigned C₀).sliceSign
        (P.eventBracket t ht).after
        (P.eventBracket t ht).after_regular) := by
  apply FiberSign.heq_of_eq_toFun
    (R.criticalSaddlePositiveSlice_eq_eventAfter P t ht p hp A hafter)
  apply heq_of_eq
  funext x
  change (R.amplitude.toVerticalAmplitude.pullbackSigned C₀)
      (cobSpaceTime x (G.localSeparatedTime p p.2 + A ^ 2)) =
    (R.amplitude.toVerticalAmplitude.pullbackSigned C₀)
      (cobSpaceTime x (P.eventBracket t ht).after)
  rw [hafter]


-- @@ L570-595 verbatim
theorem negativeSliceSign_heq_eventBefore
    (R : ExactFiniteMorseJetInstallation G)
    (P : MorsePosition
      (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism))
    (t : ℝ) (ht : t ∈ P.eventTimes)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (A : ℝ)
    (hbefore : (P.eventBracket t ht).before =
      G.localSeparatedTime p p.2 - A ^ 2) :
    HEq
      ((R.amplitude.toVerticalAmplitude.pullbackSigned C₀).sliceSign
        (G.localSeparatedTime p p.2 - A ^ 2) (by
          rw [← hbefore]
          exact (P.eventBracket t ht).before_regular))
      ((R.amplitude.toVerticalAmplitude.pullbackSigned C₀).sliceSign
        (P.eventBracket t ht).before
        (P.eventBracket t ht).before_regular) := by
  apply FiberSign.heq_of_eq_toFun
    (R.criticalSaddleNegativeSlice_eq_eventBefore P t ht p hp A hbefore)
  apply heq_of_eq
  funext x
  change (R.amplitude.toVerticalAmplitude.pullbackSigned C₀)
      (cobSpaceTime x (G.localSeparatedTime p p.2 - A ^ 2)) =
    (R.amplitude.toVerticalAmplitude.pullbackSigned C₀)
      (cobSpaceTime x (P.eventBracket t ht).before)
  rw [hbefore]


-- @@ L597-638 verbatim
/-- Event-bracket form of positive-side distinguished-orbit membership. -/
theorem positiveBranch_mem_eventAfter_positiveOrbitCollection
    (R : ExactFiniteMorseJetInstallation G)
    (P : MorsePosition
      (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism))
    (t : ℝ) (ht : t ∈ P.eventTimes)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (hcenterPositive :
      0 < (R.amplitude.toVerticalAmplitude.pullbackSigned C₀)
        (R.criticalCenter p))
    (b : SaddleBranch) (ρ A : ℝ)
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hafter : (P.eventBracket t ht).after =
      G.localSeparatedTime p p.2 + A ^ 2)
    (V : TamedField
      (R.criticalSaddlePositiveSlice p hp A (by
        rw [← hafter]
        exact (P.eventBracket t ht).after_regular))) :
    ((R.criticalSaddlePositiveBranchOrbitIndex p hp hindex b ρ A
      hρ hA hρrad _ V : V.OrbitIndex) :
        Set (EuclideanSpace ℝ (Fin (n + 1)))) ∈
      ((R.amplitude.toVerticalAmplitude.pullbackSigned C₀).sliceSign
        (P.eventBracket t ht).after
        (P.eventBracket t ht).after_regular).positiveOrbitCollection
          (R.criticalSaddlePositiveSlice_eq_eventAfter P t ht p hp A hafter ▸ V) := by
  let hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism).G
      (G.localSeparatedTime p p.2 + A ^ 2) := by
    rw [← hafter]
    exact (P.eventBracket t ht).after_regular
  let hX := R.criticalSaddlePositiveSlice_eq_eventAfter
    P t ht p hp A hafter
  let Slocal := (R.amplitude.toVerticalAmplitude.pullbackSigned C₀).sliceSign
    (G.localSeparatedTime p p.2 + A ^ 2) hreg
  let Sevent := (R.amplitude.toVerticalAmplitude.pullbackSigned C₀).sliceSign
    (P.eventBracket t ht).after (P.eventBracket t ht).after_regular
  apply positiveOrbitCollection_mem_of_slice_transport hX Slocal Sevent
    (R.positiveSliceSign_heq_eventAfter P t ht p hp A hafter)
  exact R.positiveBranch_mem_positiveOrbitCollection p hp hindex
    hcenterPositive b ρ A hρ hA hρrad hreg V


-- @@ L640-681 verbatim
/-- Event-bracket form of negative-side distinguished-orbit membership. -/
theorem negativeBranch_mem_eventBefore_positiveOrbitCollection
    (R : ExactFiniteMorseJetInstallation G)
    (P : MorsePosition
      (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism))
    (t : ℝ) (ht : t ∈ P.eventTimes)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (hcenterPositive :
      0 < (R.amplitude.toVerticalAmplitude.pullbackSigned C₀)
        (R.criticalCenter p))
    (b : SaddleBranch) (ρ A : ℝ)
    (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hbefore : (P.eventBracket t ht).before =
      G.localSeparatedTime p p.2 - A ^ 2)
    (V : TamedField
      (R.criticalSaddleNegativeSlice p hp A (by
        rw [← hbefore]
        exact (P.eventBracket t ht).before_regular))) :
    ((R.criticalSaddleNegativeBranchOrbitIndex p hp hindex b ρ A
      hρ hA hρrad _ V : V.OrbitIndex) :
        Set (EuclideanSpace ℝ (Fin (n + 1)))) ∈
      ((R.amplitude.toVerticalAmplitude.pullbackSigned C₀).sliceSign
        (P.eventBracket t ht).before
        (P.eventBracket t ht).before_regular).positiveOrbitCollection
          (R.criticalSaddleNegativeSlice_eq_eventBefore P t ht p hp A hbefore ▸ V) := by
  let hreg : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism).G
      (G.localSeparatedTime p p.2 - A ^ 2) := by
    rw [← hbefore]
    exact (P.eventBracket t ht).before_regular
  let hX := R.criticalSaddleNegativeSlice_eq_eventBefore
    P t ht p hp A hbefore
  let Slocal := (R.amplitude.toVerticalAmplitude.pullbackSigned C₀).sliceSign
    (G.localSeparatedTime p p.2 - A ^ 2) hreg
  let Sevent := (R.amplitude.toVerticalAmplitude.pullbackSigned C₀).sliceSign
    (P.eventBracket t ht).before (P.eventBracket t ht).before_regular
  apply positiveOrbitCollection_mem_of_slice_transport hX Slocal Sevent
    (R.negativeSliceSign_heq_eventBefore P t ht p hp A hbefore)
  exact R.negativeBranch_mem_positiveOrbitCollection p hp hindex
    hcenterPositive b ρ A hρ hA hρrad hreg V


-- @@ L683-698 verbatim
/-- A critical center identified with a positively labelled event center has
positive installed sign. -/
theorem criticalCenter_positive_of_positive_event
    (R : ExactFiniteMorseJetInstallation G)
    (P : MorsePosition
      (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism))
    (t : ℝ) (ht : t ∈ P.eventTimes)
    (p : Σ _ : ι, E₂)
    (hcenter : R.criticalCenter p = P.eventCenter t ht)
    (hpositive : P.eventCenter t ht ∈
      ((R.amplitude.toVerticalAmplitude.pullbackSigned C₀).labelMorsePosition P).positiveCenters) :
    0 < (R.amplitude.toVerticalAmplitude.pullbackSigned C₀)
      (R.criticalCenter p) := by
  rw [hcenter]
  let L := (R.amplitude.toVerticalAmplitude.pullbackSigned C₀).labelMorsePosition P
  exact (L.mem_positiveCenters_iff.mp hpositive).2


-- @@ L700-760 verbatim
/-- The merge-frame equation follows from the exterior-relative saddle
contract.  Unlike comparison with three complete Cassini circles, this form
retains the two arbitrary exterior frame factors of the actual orbits. -/
theorem negativeTwo_orbitFrameClass_splice_of_relativeContractHomotopies
    (hn : 3 ≤ n + 1)
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (ρ A : ℝ) (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hregNegative : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism).G
      (G.localSeparatedTime p p.2 - A ^ 2))
    (Vnegative : TamedField
      (R.criticalSaddleNegativeSlice p hp A hregNegative))
    (hregPositive : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism).G
      (G.localSeparatedTime p p.2 + A ^ 2))
    (Vpositive : TamedField
      (R.criticalSaddlePositiveSlice p hp A hregPositive))
    (exterior₁ exterior₂ : C(I, SOGroup (n + 1)))
    (hext₁ : exterior₁ 0 = exterior₁ 1)
    (hext₂ : exterior₂ 0 = exterior₂ 1)
    (S : SaddleModelContract)
    (H₁ : ContinuousMap.Homotopy
      (Vnegative.orbitFrameLoop
        (R.criticalSaddleNegativeBranchOrbitIndex p hp hindex .negative ρ A
          hρ hA hρrad hregNegative Vnegative))
      (exterior₁ * S.incoming₁.frame (n + 1)))
    (H₂ : ContinuousMap.Homotopy
      (Vnegative.orbitFrameLoop
        (R.criticalSaddleNegativeBranchOrbitIndex p hp hindex .positive ρ A
          hρ hA hρrad hregNegative Vnegative))
      (exterior₂ * S.incoming₂.frame (n + 1)))
    (Hhat : ContinuousMap.Homotopy
      (Vpositive.orbitFrameLoop
        (R.criticalSaddlePositiveBranchOrbitIndex p hp hindex .negative ρ A
          hρ hA hρrad hregPositive Vpositive))
      ((exterior₁ * exterior₂) * S.outgoing.frame (n + 1)))
    (H₁_closed : ∀ s : I, H₁ (s, 0) = H₁ (s, 1))
    (H₂_closed : ∀ s : I, H₂ (s, 0) = H₂ (s, 1))
    (Hhat_closed : ∀ s : I, Hhat (s, 0) = Hhat (s, 1)) :
    Vpositive.orbitFrameClass
        (R.criticalSaddlePositiveBranchOrbitIndex p hp hindex .negative ρ A
          hρ hA hρrad hregPositive Vpositive) =
      Vnegative.orbitFrameClass
          (R.criticalSaddleNegativeBranchOrbitIndex p hp hindex .negative ρ A
            hρ hA hρrad hregNegative Vnegative) +
        Vnegative.orbitFrameClass
          (R.criticalSaddleNegativeBranchOrbitIndex p hp hindex .positive ρ A
            hρ hA hρrad hregNegative Vnegative) + 1 := by
  exact TamedField.orbitFrameClass_relative_saddle_splice hn
    Vnegative Vpositive
    (R.criticalSaddleNegativeBranchOrbitIndex p hp hindex .negative ρ A
      hρ hA hρrad hregNegative Vnegative)
    (R.criticalSaddleNegativeBranchOrbitIndex p hp hindex .positive ρ A
      hρ hA hρrad hregNegative Vnegative)
    (R.criticalSaddlePositiveBranchOrbitIndex p hp hindex .negative ρ A
      hρ hA hρrad hregPositive Vpositive)
    exterior₁ exterior₂ hext₁ hext₂ S
    H₁ H₂ Hhat H₁_closed H₂_closed Hhat_closed


-- @@ L762-821 verbatim
/-- Reverse-orientation form of the exterior-relative saddle contract for a
chronological split. -/
theorem positiveTwo_orbitFrameClass_splice_of_relativeContractHomotopies
    (hn : 3 ≤ n + 1)
    (R : ExactFiniteMorseJetInstallation G)
    (p : Σ _ : ι, E₂) (hp : p ∈ G.criticalPoints)
    (hindex : (G.localMorseNormalForm p hp).index = .saddle)
    (ρ A : ℝ) (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hregNegative : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism).G
      (G.localSeparatedTime p p.2 - A ^ 2))
    (Vnegative : TamedField
      (R.criticalSaddleNegativeSlice p hp A hregNegative))
    (hregPositive : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C₀.cobordism).G
      (G.localSeparatedTime p p.2 + A ^ 2))
    (Vpositive : TamedField
      (R.criticalSaddlePositiveSlice p hp A hregPositive))
    (exterior₁ exterior₂ : C(I, SOGroup (n + 1)))
    (hext₁ : exterior₁ 0 = exterior₁ 1)
    (hext₂ : exterior₂ 0 = exterior₂ 1)
    (S : SaddleModelContract)
    (H₁ : ContinuousMap.Homotopy
      (Vpositive.orbitFrameLoop
        (R.criticalSaddlePositiveBranchOrbitIndex p hp hindex .negative ρ A
          hρ hA hρrad hregPositive Vpositive))
      (exterior₁ * S.incoming₁.frame (n + 1)))
    (H₂ : ContinuousMap.Homotopy
      (Vpositive.orbitFrameLoop
        (R.criticalSaddlePositiveBranchOrbitIndex p hp hindex .positive ρ A
          hρ hA hρrad hregPositive Vpositive))
      (exterior₂ * S.incoming₂.frame (n + 1)))
    (Hhat : ContinuousMap.Homotopy
      (Vnegative.orbitFrameLoop
        (R.criticalSaddleNegativeBranchOrbitIndex p hp hindex .negative ρ A
          hρ hA hρrad hregNegative Vnegative))
      ((exterior₁ * exterior₂) * S.outgoing.frame (n + 1)))
    (H₁_closed : ∀ s : I, H₁ (s, 0) = H₁ (s, 1))
    (H₂_closed : ∀ s : I, H₂ (s, 0) = H₂ (s, 1))
    (Hhat_closed : ∀ s : I, Hhat (s, 0) = Hhat (s, 1)) :
    Vnegative.orbitFrameClass
        (R.criticalSaddleNegativeBranchOrbitIndex p hp hindex .negative ρ A
          hρ hA hρrad hregNegative Vnegative) =
      Vpositive.orbitFrameClass
          (R.criticalSaddlePositiveBranchOrbitIndex p hp hindex .negative ρ A
            hρ hA hρrad hregPositive Vpositive) +
        Vpositive.orbitFrameClass
          (R.criticalSaddlePositiveBranchOrbitIndex p hp hindex .positive ρ A
            hρ hA hρrad hregPositive Vpositive) + 1 := by
  exact TamedField.orbitFrameClass_relative_saddle_splice hn
    Vpositive Vnegative
    (R.criticalSaddlePositiveBranchOrbitIndex p hp hindex .negative ρ A
      hρ hA hρrad hregPositive Vpositive)
    (R.criticalSaddlePositiveBranchOrbitIndex p hp hindex .positive ρ A
      hρ hA hρrad hregPositive Vpositive)
    (R.criticalSaddleNegativeBranchOrbitIndex p hp hindex .negative ρ A
      hρ hA hρrad hregNegative Vnegative)
    exterior₁ exterior₂ hext₁ hext₂ S
    H₁ H₂ Hhat H₁_closed H₂_closed Hhat_closed


-- @@ L823-885 verbatim
/-- The required merge-frame equation follows from three closed homotopies
to the literal Cassini source and target loops. -/
theorem negativeTwo_orbitFrameClass_splice_of_cassiniHomotopies
    {m : ℕ}
    {Y₀ Y₁ : FramedLevelSet (m + 2)}
    {Q₀ : FiberSign Y₀} {Q₁ : FiberSign Y₁}
    {C₁ : SignedFramedLevelCobordism Q₀ Q₁}
    {κ : Type*} [Fintype κ]
    {B₁ : FiniteIFTSurfaceCover C₁.cobordism κ}
    {G₁ : GenericFiniteIFTSurfaceAtlas B₁.toSurfaceChartFamily}
    (R : ExactFiniteMorseJetInstallation G₁)
    (p : Σ _ : κ, E₂) (hp : p ∈ G₁.criticalPoints)
    (hindex : (G₁.localMorseNormalForm p hp).index = .saddle)
    (ρ A : ℝ) (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hregNegative : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C₁.cobordism).G
      (G₁.localSeparatedTime p p.2 - A ^ 2))
    (Vnegative : TamedField
      (R.criticalSaddleNegativeSlice p hp A hregNegative))
    (hregPositive : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C₁.cobordism).G
      (G₁.localSeparatedTime p p.2 + A ^ 2))
    (Vpositive : TamedField
      (R.criticalSaddlePositiveSlice p hp A hregPositive))
    (Vsource : TamedField (StandardSaddle.sourceFLS m))
    (Vtarget : TamedField (StandardSaddle.targetFLS m))
    (H₁ : ContinuousMap.Homotopy
      (Vnegative.orbitFrameLoop
        (R.criticalSaddleNegativeBranchOrbitIndex p hp hindex .negative ρ A
          hρ hA hρrad hregNegative Vnegative))
      (StandardSaddle.sourceRightSimpleClosedOrbitParam m Vsource).paramFrameLoop)
    (H₂ : ContinuousMap.Homotopy
      (Vnegative.orbitFrameLoop
        (R.criticalSaddleNegativeBranchOrbitIndex p hp hindex .positive ρ A
          hρ hA hρrad hregNegative Vnegative))
      (StandardSaddle.sourceLeftSimpleClosedOrbitParam m Vsource).paramFrameLoop)
    (Hhat : ContinuousMap.Homotopy
      (Vpositive.orbitFrameLoop
        (R.criticalSaddlePositiveBranchOrbitIndex p hp hindex .negative ρ A
          hρ hA hρrad hregPositive Vpositive))
      (StandardSaddle.targetSimpleClosedOrbitParam m Vtarget).paramFrameLoop)
    (H₁_closed : ∀ s : I, H₁ (s, 0) = H₁ (s, 1))
    (H₂_closed : ∀ s : I, H₂ (s, 0) = H₂ (s, 1))
    (Hhat_closed : ∀ s : I, Hhat (s, 0) = Hhat (s, 1)) :
    Vpositive.orbitFrameClass
        (R.criticalSaddlePositiveBranchOrbitIndex p hp hindex .negative ρ A
          hρ hA hρrad hregPositive Vpositive) =
      Vnegative.orbitFrameClass
          (R.criticalSaddleNegativeBranchOrbitIndex p hp hindex .negative ρ A
            hρ hA hρrad hregNegative Vnegative) +
        Vnegative.orbitFrameClass
          (R.criticalSaddleNegativeBranchOrbitIndex p hp hindex .positive ρ A
            hρ hA hρrad hregNegative Vnegative) + 1 := by
  exact StandardSaddle.actual_orbitFrameClass_splice
    Vnegative Vpositive
    (R.criticalSaddleNegativeBranchOrbitIndex p hp hindex .negative ρ A
      hρ hA hρrad hregNegative Vnegative)
    (R.criticalSaddleNegativeBranchOrbitIndex p hp hindex .positive ρ A
      hρ hA hρrad hregNegative Vnegative)
    (R.criticalSaddlePositiveBranchOrbitIndex p hp hindex .negative ρ A
      hρ hA hρrad hregPositive Vpositive)
    Vsource Vtarget H₁ H₂ Hhat H₁_closed H₂_closed Hhat_closed


-- @@ L887-949 verbatim
/-- The required split-frame equation follows from the same Cassini splice
with the positive and negative installed slices interchanged. -/
theorem positiveTwo_orbitFrameClass_splice_of_cassiniHomotopies
    {m : ℕ}
    {Y₀ Y₁ : FramedLevelSet (m + 2)}
    {Q₀ : FiberSign Y₀} {Q₁ : FiberSign Y₁}
    {C₁ : SignedFramedLevelCobordism Q₀ Q₁}
    {κ : Type*} [Fintype κ]
    {B₁ : FiniteIFTSurfaceCover C₁.cobordism κ}
    {G₁ : GenericFiniteIFTSurfaceAtlas B₁.toSurfaceChartFamily}
    (R : ExactFiniteMorseJetInstallation G₁)
    (p : Σ _ : κ, E₂) (hp : p ∈ G₁.criticalPoints)
    (hindex : (G₁.localMorseNormalForm p hp).index = .saddle)
    (ρ A : ℝ) (hρ : 0 < ρ) (hA : A ^ 2 < ρ ^ 2)
    (hρrad : ρ < (R.criticalModelShrink p hp).radius)
    (hregNegative : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C₁.cobordism).G
      (G₁.localSeparatedTime p p.2 - A ^ 2))
    (Vnegative : TamedField
      (R.criticalSaddleNegativeSlice p hp A hregNegative))
    (hregPositive : sliceRegular
      (R.amplitude.toVerticalAmplitude.pullback C₁.cobordism).G
      (G₁.localSeparatedTime p p.2 + A ^ 2))
    (Vpositive : TamedField
      (R.criticalSaddlePositiveSlice p hp A hregPositive))
    (Vsource : TamedField (StandardSaddle.sourceFLS m))
    (Vtarget : TamedField (StandardSaddle.targetFLS m))
    (H₁ : ContinuousMap.Homotopy
      (Vpositive.orbitFrameLoop
        (R.criticalSaddlePositiveBranchOrbitIndex p hp hindex .negative ρ A
          hρ hA hρrad hregPositive Vpositive))
      (StandardSaddle.sourceRightSimpleClosedOrbitParam m Vsource).paramFrameLoop)
    (H₂ : ContinuousMap.Homotopy
      (Vpositive.orbitFrameLoop
        (R.criticalSaddlePositiveBranchOrbitIndex p hp hindex .positive ρ A
          hρ hA hρrad hregPositive Vpositive))
      (StandardSaddle.sourceLeftSimpleClosedOrbitParam m Vsource).paramFrameLoop)
    (Hhat : ContinuousMap.Homotopy
      (Vnegative.orbitFrameLoop
        (R.criticalSaddleNegativeBranchOrbitIndex p hp hindex .negative ρ A
          hρ hA hρrad hregNegative Vnegative))
      (StandardSaddle.targetSimpleClosedOrbitParam m Vtarget).paramFrameLoop)
    (H₁_closed : ∀ s : I, H₁ (s, 0) = H₁ (s, 1))
    (H₂_closed : ∀ s : I, H₂ (s, 0) = H₂ (s, 1))
    (Hhat_closed : ∀ s : I, Hhat (s, 0) = Hhat (s, 1)) :
    Vnegative.orbitFrameClass
        (R.criticalSaddleNegativeBranchOrbitIndex p hp hindex .negative ρ A
          hρ hA hρrad hregNegative Vnegative) =
      Vpositive.orbitFrameClass
          (R.criticalSaddlePositiveBranchOrbitIndex p hp hindex .negative ρ A
            hρ hA hρrad hregPositive Vpositive) +
        Vpositive.orbitFrameClass
          (R.criticalSaddlePositiveBranchOrbitIndex p hp hindex .positive ρ A
            hρ hA hρrad hregPositive Vpositive) + 1 := by
  exact StandardSaddle.actual_orbitFrameClass_splice
    Vpositive Vnegative
    (R.criticalSaddlePositiveBranchOrbitIndex p hp hindex .negative ρ A
      hρ hA hρrad hregPositive Vpositive)
    (R.criticalSaddlePositiveBranchOrbitIndex p hp hindex .positive ρ A
      hρ hA hρrad hregPositive Vpositive)
    (R.criticalSaddleNegativeBranchOrbitIndex p hp hindex .negative ρ A
      hρ hA hρrad hregNegative Vnegative)
    Vsource Vtarget H₁ H₂ Hhat H₁_closed H₂_closed Hhat_closed


-- @@ L951-951 verbatim
end ExactFiniteMorseJetInstallation

-- @@ L952-952 verbatim
end Submission
