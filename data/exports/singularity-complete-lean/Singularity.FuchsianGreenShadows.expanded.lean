import Singularity.StationaryGreenMeasure
import Singularity.FuchsianVisualShadows
import Singularity.ShadowMagnitudeComparison
import Singularity.FuchsianGreenRigidityReduction


-- @@ L6-13 verbatim
/-!
# What the Green estimates give for actual visual shadows

The lower hitting-mass estimate is proved under nonsingularity. The reverse
estimate, which would bound the mass by exp(-Green distance), is not inferred
from it. The last theorems isolate how that upper shadow estimate and a
one-sided density lower bound would imply the remaining Green comparison.
-/


-- @@ L15-15 verbatim
noncomputable section

-- @@ L16-16 verbatim
open MeasureTheory Set Filter

-- @@ L17-17 verbatim
open scoped MatrixGroups UpperHalfPlane ENNReal


-- @@ L19-19 verbatim
namespace Singularity


-- @@ L21-25 verbatim
variable (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  (hne : ProjectiveNonelementary Γ)
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤) (z : ℍ)


-- @@ L27-27 verbatim
local notation "ν" => projectiveHittingMeasure Γ s z μ hpos hmass

-- @@ L28-28 verbatim
local notation "m" => compactPoissonMeasure z


-- @@ L30-30 verbatim
include hne hgen


-- @@ L32-46 verbatim
/-- Actual visual shadow masses satisfy the directed Green bounds with their
inverse-shadow mass retained. This uses no nonsingularity assumption. -/
theorem fuchsian_visualShadow_green_mass_bounds (g : Γ) (r : ℝ) :
    ENNReal.ofReal (Real.exp (-greenDistance s μ 1 g)) *
      ν ((fun ξ : OnePoint ℝ => g • ξ) ⁻¹' visualShadow z (g • z) r) ≤
        ν (visualShadow z (g • z) r) ∧
    ν (visualShadow z (g • z) r) ≤ ENNReal.ofReal (Real.exp (greenDistance s μ g 1)) *
      ν ((fun ξ : OnePoint ℝ => g • ξ) ⁻¹' visualShadow z (g • z) r) := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  let : MeasurableMul Γ := ⟨fun _ => measurable_of_countable _, fun _ => measurable_of_countable _⟩
  let := projectiveHittingMeasure_probability Γ s z μ hpos hmass
  exact stationary_set_green_bounds s μ hpos hmass hgen
    (projectiveNonelementary_rightMarkov_gap Γ hne s μ hpos hmass hgen) ν
    (fuchsian_hittingMeasure_stationary Γ hne s μ hpos hmass hgen z) g
    (isOpen_visualShadow _ _ _).measurableSet


-- @@ L48-67 verbatim
/-- Under nonsingularity the inverse-shadow mass can be made uniformly close
to one, giving a genuine lower Green shadow estimate for the hitting law. -/
theorem fuchsian_visualShadow_green_lower (hns : ¬ ν ⟂ₘ m)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ g : Γ,
      ENNReal.ofReal (Real.exp (-greenDistance s μ 1 g)) * (1 - ε) ≤
        ν (visualShadow z (g • z) r) := by
  let := projectiveHittingMeasure_probability Γ s z μ hpos hmass
  obtain ⟨r, hr, hfull⟩ := fuchsian_hittingMeasure_inverse_shadow_full_mass Γ hne s μ hpos hmass hgen z hns hε
  refine ⟨r, hr, fun g => ?_⟩
  let T := (fun ξ : OnePoint ℝ => g • ξ) ⁻¹' visualShadow z (g • z) r
  have hT : MeasurableSet T := (isOpen_visualShadow _ _ _).measurableSet.preimage (measurable_const_smul g)
  have hl : 1 - ε ≤ ν T := by
    calc
      1 - ε ≤ 1 - ν Tᶜ := tsub_le_tsub_left (hfull g).le _
      _ = ν T := by
        rw [← measure_univ (μ := ν), ← measure_compl hT.compl (measure_ne_top _ _)]
        simp
  apply le_trans ?_ (fuchsian_visualShadow_green_mass_bounds Γ hne s μ hpos hmass hgen z g r).1
  gcongr


-- @@ L69-89 verbatim
omit hne hgen [DiscreteTopology Γ] [MeasurableSingletonClass Γ] in
/-- An upper Green shadow estimate together with visual domination by the
hitting law gives the required radial upper Green-distance bound. Both
analytic estimates here are explicit hypotheses, not proved consequences of
nonsingularity. -/
theorem fuchsian_green_upper_of_shadow_and_density_bounds {r : ℝ} (hr : 0 < r)
    (K C : ℝ) (hdom : m ≤ ENNReal.ofReal (Real.exp K) • ν)
    (hupper : ∀ g : Γ, ν (visualShadow z (g • z) r) ≤
      ENNReal.ofReal (Real.exp (C - greenDistance s μ 1 g))) :
    ∀ g : Γ, greenDistance s μ 1 g ≤ dist z (g • z) + K + C -
      Real.log (verticalShadowMass r).toReal := by
  intro g
  have hfinite : verticalShadowMass r ≠ ⊤ := ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ⊤)
    (verticalShadowMass_le_one r)
  have ha : 0 < (verticalShadowMass r).toReal :=
    ENNReal.toReal_pos (verticalShadowMass_pos r).ne' hfinite
  apply shadow_magnitude_upper_of_one_sided_comparison ν m (visualShadow z (g • z) r)
    (greenDistance s μ 1 g) (dist z (g • z)) C K (verticalShadowMass r).toReal ha
    ?_ (hupper g) hdom
  rw [ENNReal.ofReal_toReal hfinite]
  exact (visualShadow_mass_bounds z (g • z) hr).1


-- @@ L91-104 verbatim
/-- A sufficient analytic interface for the full theorem. The preceding
lower shadow estimate does not discharge either of these upper/density
hypotheses. -/
theorem fuchsian_singularity_of_shadow_density_rigidity
    (hrig : ¬ ν ⟂ₘ m → ∃ r K C : ℝ, 0 < r ∧
      m ≤ ENNReal.ofReal (Real.exp K) • ν ∧
      ∀ g : Γ, ν (visualShadow z (g • z) r) ≤
        ENNReal.ofReal (Real.exp (C - greenDistance s μ 1 g))) : ν ⟂ₘ m := by
  apply fuchsian_singularity_of_green_upper_rigidity Γ hne s μ hpos hmass hgen z
  intro hns
  obtain ⟨r, K, C, hr, hd, hu⟩ := hrig hns
  refine ⟨1, K + C - Real.log (verticalShadowMass r).toReal, by norm_num, fun g => ?_⟩
  have h := fuchsian_green_upper_of_shadow_and_density_bounds Γ s μ hpos hmass z hr K C hd hu g
  simpa only [one_mul, add_assoc, sub_eq_add_neg] using h


-- @@ L106-106 verbatim
end Singularity
