import Singularity.ProjectiveWalkProjection
import Singularity.GeometricHittingMeasure
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable


-- @@ L5-12 verbatim
/-!
# The hitting measure of the original projective random walk

Use the measurable limit selector of the actual PSL₂ orbit trajectory and
retract from the sphere to its real boundary. Under the lifted spectral-gap
hypothesis this selector is the almost-sure geometric limit. Its law equals
the already constructed SL₂ hitting law, not merely a stationary measure.
-/


-- @@ L14-14 verbatim
noncomputable section

-- @@ L15-15 verbatim
open MeasureTheory Filter Set OnePoint TopologicalSpace

-- @@ L16-16 verbatim
open scoped MatrixGroups UpperHalfPlane Topology


-- @@ L18-18 verbatim
namespace Singularity


-- @@ L20-21 verbatim
variable (Γ : Subgroup PSL(2, ℝ)) [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  (s : Finset Γ) (z : ℍ)


-- @@ L23-25 verbatim
/-- A canonical measurable boundary limit selector for the original projective paths. -/
def projectiveBoundaryMap (ω : ℕ → s) : OnePoint ℝ :=
  compactBoundaryRetraction (walkPathLimit s (fun g : Γ => hyperbolicCompactEmbedding (g • z)) ω)


-- @@ L27-31 verbatim
theorem measurable_projectiveBoundaryMap : Measurable (projectiveBoundaryMap Γ s z) := by
  let := TopologicalSpace.metrizableSpaceMetric (OnePoint ℂ)
  apply measurable_compactBoundaryRetraction.comp
  exact (StronglyMeasurable.limUnder (fun n =>
    (measurable_walkOrbitPosition s (fun g : Γ => hyperbolicCompactEmbedding (g • z)) n).stronglyMeasurable)).measurable


-- @@ L33-33 verbatim
variable (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g) (hmass : ∑ g ∈ s, μ g = 1)


-- @@ L35-38 verbatim
/-- The distribution of the projective orbit limit selector. Its identification as
an actual hitting law is proved by the convergence theorem below. -/
def projectiveHittingMeasure : Measure (OnePoint ℝ) :=
  walkBoundaryLaw s μ (fun g hg => (hpos g hg).le) hmass (projectiveBoundaryMap Γ s z)


-- @@ L40-43 verbatim
theorem projectiveHittingMeasure_probability :
    IsProbabilityMeasure (projectiveHittingMeasure Γ s z μ hpos hmass) :=
  walkBoundaryLaw_probability s μ (fun g hg => (hpos g hg).le) hmass _
    (measurable_projectiveBoundaryMap Γ s z)


-- @@ L45-49 verbatim
variable [DiscreteTopology Γ]
  [MeasurableSpace (projectiveSubgroupLift Γ)] [MeasurableSingletonClass (projectiveSubgroupLift Γ)]
  [MeasurableMul (projectiveSubgroupLift Γ)]
  (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov (projectiveLiftSupport Γ s) (projectiveLiftWeight Γ μ)) < 1)


-- @@ L51-51 verbatim
attribute [local instance] projectiveSubgroupLift_discrete


-- @@ L53-53 verbatim
local notation "sL" => projectiveLiftSupport Γ s

-- @@ L54-54 verbatim
local notation "μL" => projectiveLiftWeight Γ μ

-- @@ L55-55 verbatim
local notation "hpL" => projectiveLiftWeight_positive Γ s μ hpos

-- @@ L56-56 verbatim
local notation "hmL" => projectiveLiftWeight_mass Γ s μ hmass

-- @@ L57-57 verbatim
local notation "hgL" => projectiveLiftSupport_generates_of_mass Γ s μ hmass hgen


-- @@ L59-71 verbatim
omit [MeasurableSpace Γ] [MeasurableSingletonClass Γ] in
/-- Almost every coupled path has the same boundary limit in both models. -/
theorem projectiveBoundaryMap_lift_ae :
    (fun ω => projectiveBoundaryMap Γ s z (projectiveWalkProjection Γ s ω)) =ᵐ[
      infiniteWalkLaw sL μL (fun g hg => (hpL g hg).le) hmL]
      geometricBoundaryMap (projectiveSubgroupLift Γ) sL μL hpL hmL hgL hgap z := by
  filter_upwards [geometricBoundaryMap_tendsto (projectiveSubgroupLift Γ) sL μL hpL hmL hgL hgap z] with ω hω
  have ht : Tendsto (fun n => hyperbolicCompactEmbedding
      (walkPosition s 1 n (projectiveWalkProjection Γ s ω) • z)) atTop
      (𝓝 (compactBoundaryEmbedding (geometricBoundaryMap (projectiveSubgroupLift Γ) sL μL hpL hmL hgL hgap z ω))) := by
    simpa only [projective_walk_hyperbolic_trajectory] using hω
  change compactBoundaryRetraction (limUnder atTop _) = _
  rw [ht.limUnder_eq, compactBoundaryRetraction_embedding]


-- @@ L73-89 verbatim
include hgen hgap in
/-- The original projective orbit converges almost surely to the named boundary map. -/
theorem projectiveBoundaryMap_tendsto :
    ∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
      Tendsto (fun n => hyperbolicCompactEmbedding (walkPosition s 1 n ω • z)) atTop
        (𝓝 (compactBoundaryEmbedding (projectiveBoundaryMap Γ s z ω))) := by
  have hP : MeasurableSet {ω : ℕ → s | Tendsto
      (fun n => hyperbolicCompactEmbedding (walkPosition s 1 n ω • z)) atTop
      (𝓝 (compactBoundaryEmbedding (projectiveBoundaryMap Γ s z ω)))} :=
    measurableSet_tendsto_fun
      (fun n => measurable_walkOrbitPosition s (fun g : Γ => hyperbolicCompactEmbedding (g • z)) n)
      (continuous_compactBoundaryEmbedding.measurable.comp (measurable_projectiveBoundaryMap Γ s z))
  rw [← infiniteWalkLaw_projective_projection Γ s μ hpos hmass]
  apply (ae_map_iff (measurable_projectiveWalkProjection Γ s).aemeasurable hP).mpr
  filter_upwards [projectiveBoundaryMap_lift_ae Γ s z μ hpos hmass hgen hgap,
    geometricBoundaryMap_tendsto (projectiveSubgroupLift Γ) sL μL hpL hmL hgL hgap z] with ω he hω
  simpa only [he, projective_walk_hyperbolic_trajectory] using hω


-- @@ L91-98 verbatim
/-- The hitting probability is unchanged by introducing the two central signs. -/
theorem projectiveHittingMeasure_eq_lift :
    projectiveHittingMeasure Γ s z μ hpos hmass =
      geometricHittingMeasure (projectiveSubgroupLift Γ) sL μL hpL hmL hgL hgap z := by
  unfold projectiveHittingMeasure walkBoundaryLaw
  rw [← infiniteWalkLaw_projective_projection Γ s μ hpos hmass,
    Measure.map_map (measurable_projectiveBoundaryMap Γ s z) (measurable_projectiveWalkProjection Γ s)]
  exact Measure.map_congr (projectiveBoundaryMap_lift_ae Γ s z μ hpos hmass hgen hgap)


-- @@ L100-109 verbatim
include hgen hgap in
/-- Any measurable version of the original projective path limit gives this same law. -/
theorem projectiveHittingMeasure_unique (b : (ℕ → s) → OnePoint ℝ)
    (hb : ∀ᵐ ω ∂infiniteWalkLaw s μ (fun g hg => (hpos g hg).le) hmass,
      Tendsto (fun n => hyperbolicCompactEmbedding (walkPosition s 1 n ω • z)) atTop
        (𝓝 (compactBoundaryEmbedding (b ω)))) :
    walkBoundaryLaw s μ (fun g hg => (hpos g hg).le) hmass b = projectiveHittingMeasure Γ s z μ hpos hmass := by
  apply Measure.map_congr
  filter_upwards [hb, projectiveBoundaryMap_tendsto Γ s z μ hpos hmass hgen hgap] with ω h₁ h₂
  exact compactBoundaryEmbedding_injective (tendsto_nhds_unique h₁ h₂)


-- @@ L111-111 verbatim
end Singularity
