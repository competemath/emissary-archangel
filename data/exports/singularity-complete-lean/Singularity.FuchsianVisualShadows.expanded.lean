import Singularity.AbsolutelyContinuousVisualShadows
import Singularity.VisualShadowCocycle
import Singularity.FuchsianDensityCocycle


-- @@ L5-12 verbatim
/-!
# Visual shadow estimates for a nonsingular hitting measure

The actual hitting measure inherits uniform inverse-shadow fullness and
vanishing mass of escaping shadows. On inverse shadows, its cocycle differs
from displacement by a bounded visual error and the exact density coboundary.
The latter error has not been shown uniformly bounded.
-/


-- @@ L14-14 verbatim
noncomputable section

-- @@ L15-15 verbatim
open MeasureTheory Set Filter

-- @@ L16-16 verbatim
open scoped MatrixGroups UpperHalfPlane ENNReal Topology


-- @@ L18-18 verbatim
namespace Singularity


-- @@ L20-24 verbatim
variable (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  (hne : ProjectiveNonelementary Γ)
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤) (z : ℍ)


-- @@ L26-26 verbatim
local notation "ν" => projectiveHittingMeasure Γ s z μ hpos hmass

-- @@ L27-27 verbatim
local notation "m" => compactPoissonMeasure z


-- @@ L29-29 verbatim
include hne hgen


-- @@ L31-40 verbatim
/-- Under nonsingularity, inverse visual shadows have uniformly almost full
hitting mass, including for groups with noncompact quotient. -/
theorem fuchsian_hittingMeasure_inverse_shadow_full_mass (hns : ¬ ν ⟂ₘ m)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ g : Γ,
      ν (((fun ξ : OnePoint ℝ => g • ξ) ⁻¹' visualShadow z (g • z) r)ᶜ) < ε := by
  let := projectiveHittingMeasure_probability Γ s z μ hpos hmass
  obtain ⟨r, hr, hfull⟩ := absolutelyContinuous_visualShadow_uniform_full_mass z ν
    (fuchsian_hittingMeasure_absolutelyContinuous_of_not_singular Γ hne s μ hpos hmass hgen z hns) hε
  exact ⟨r, hr, fun g => hfull (g : PSL(2, ℝ))⟩


-- @@ L42-50 verbatim
/-- Escaping shadows have vanishing hitting mass under nonsingularity. -/
theorem fuchsian_hittingMeasure_shadow_mass_tendsto_zero (hns : ¬ ν ⟂ₘ m)
    (w : ℕ → ℍ) {r : ℝ} (hr : 0 < r)
    (hescape : Tendsto (fun n => dist z (w n)) atTop atTop) :
    Tendsto (fun n => ν (visualShadow z (w n) r)) atTop (𝓝 0) := by
  let := projectiveHittingMeasure_probability Γ s z μ hpos hmass
  exact absolutelyContinuous_visualShadow_mass_tendsto_zero z ν
    (fuchsian_hittingMeasure_absolutelyContinuous_of_not_singular Γ hne s μ hpos hmass hgen z hns)
    w hr hescape


-- @@ L52-75 verbatim
/-- The density-corrected hitting cocycle differs from displacement by the
explicit cap error on every inverse shadow, simultaneously for all elements. -/
theorem fuchsian_logCocycle_shadow_density_error (hns : ¬ ν ⟂ₘ m)
    {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ξ ∂ν, ∀ g : Γ,
      ξ ∈ (fun η : OnePoint ℝ => g • η) ⁻¹' visualShadow z (g • z) r →
      |stationaryLogCocycle ν g ξ - dist z (g • z) -
        Real.log (((ν).rnDeriv m ξ).toReal) +
        Real.log (((ν).rnDeriv m (g • ξ)).toReal)| ≤ Real.log (verticalShadowFactor r) := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  have hac := fuchsian_hittingMeasure_absolutelyContinuous_of_not_singular Γ hne s μ hpos hmass hgen z hns
  have hvis : ∀ᵐ ξ ∂ν, ∀ g : Γ,
      ξ ∈ (fun η : OnePoint ℝ => g • η) ⁻¹' visualShadow z (g • z) r →
      |stationaryLogCocycle m g ξ - dist z (g • z)| ≤ Real.log (verticalShadowFactor r) := by
    apply ae_all_iff.mpr
    intro g
    exact hac.ae_le (projective_visual_logCocycle_shadow_error (g : PSL(2, ℝ)) z hr)
  filter_upwards [fuchsian_logCocycle_visual_coboundary Γ hne s μ hpos hmass hgen z hns,
    hvis] with ξ hc hv
  intro g hmem
  rw [hc g]
  convert hv g hmem using 1
  congr 1
  ring


-- @@ L77-77 verbatim
end Singularity
