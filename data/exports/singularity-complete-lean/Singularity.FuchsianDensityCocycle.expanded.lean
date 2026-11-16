import Singularity.FuchsianLogCocycle
import Singularity.VisualLogCocycle
import Singularity.InvariantDensityCarrier


-- @@ L5-12 verbatim
/-!
# The density comparison available under nonsingularity

Nonsingularity supplies an invariant carrier and an exact measurable
coboundary. Hyperbolic displacement controls the visual term. A uniform bound
on the density is not inferred from these facts; the last theorem explicitly
states that additional hypothesis when illustrating its cocycle consequence.
-/


-- @@ L14-14 verbatim
noncomputable section

-- @@ L15-15 verbatim
open MeasureTheory Set Filter OnePoint

-- @@ L16-16 verbatim
open scoped MatrixGroups UpperHalfPlane ENNReal


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


-- @@ L31-43 verbatim
/-- Nonsingularity gives equivalence with visual measure restricted to an
invariant hitting-conull carrier, not necessarily with the whole visual measure. -/
theorem fuchsian_hittingMeasure_invariant_visual_carrier (hns : ¬ ν ⟂ₘ m) :
    ∃ E : Set (OnePoint ℝ), MeasurableSet E ∧ (∀ᵐ ξ ∂ν, ξ ∈ E) ∧
      (∀ g : Γ, (fun ξ : OnePoint ℝ => g • ξ) ⁻¹' E = E) ∧
      (ν ≪ (m).restrict E) ∧ ((m).restrict E ≪ ν) ∧
      ∀ ξ ∈ E, 0 < (ν).rnDeriv m ξ ∧ (ν).rnDeriv m ξ < (⊤ : ℝ≥0∞) := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  let := projectiveHittingMeasure_probability Γ s z μ hpos hmass
  let := compactPoissonMeasure_probability z
  exact exists_invariant_equivalent_restriction ν m
    (fuchsian_hittingMeasure_absolutelyContinuous_of_not_singular Γ hne s μ hpos hmass hgen z hns)
    (fun g => (fuchsian_hittingMeasure_translate_equivalent Γ hne s μ hpos hmass hgen z g).1)


-- @@ L45-67 verbatim
/-- The geometric bound has two explicit density-error terms. Absolute
continuity alone does not make those error terms uniformly bounded. -/
theorem fuchsian_logCocycle_bound_with_density_error (hns : ¬ ν ⟂ₘ m) :
    ∀ᵐ ξ ∂ν, ∀ g : Γ, |stationaryLogCocycle ν g ξ| ≤ dist z (g • z) +
      |Real.log (((ν).rnDeriv m ξ).toReal)| +
      |Real.log (((ν).rnDeriv m (g • ξ)).toReal)| := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  have hac := fuchsian_hittingMeasure_absolutelyContinuous_of_not_singular Γ hne s μ hpos hmass hgen z hns
  have hvis : ∀ᵐ ξ ∂ν, ∀ g : Γ,
      |stationaryLogCocycle m g ξ| ≤ dist z (g • z) := by
    apply ae_all_iff.mpr
    intro g
    exact hac.ae_le (projective_visual_logCocycle_bound z (g : PSL(2, ℝ)))
  filter_upwards [fuchsian_logCocycle_visual_coboundary Γ hne s μ hpos hmass hgen z hns,
    hvis] with ξ hc hv
  intro g
  rw [hc g]
  calc
    _ ≤ |stationaryLogCocycle m g ξ + Real.log (((ν).rnDeriv m ξ).toReal)| +
        |Real.log (((ν).rnDeriv m (g • ξ)).toReal)| := abs_sub _ _
    _ ≤ (|stationaryLogCocycle m g ξ| + |Real.log (((ν).rnDeriv m ξ).toReal)|) +
        |Real.log (((ν).rnDeriv m (g • ξ)).toReal)| := add_le_add (abs_add_le _ _) le_rfl
    _ ≤ _ := by linarith [hv g]


-- @@ L69-85 verbatim
/-- If the log density is essentially bounded, the hitting cocycle is bounded
by hyperbolic displacement plus a uniform constant. This is conditional and
does not assert the missing density-rigidity theorem. -/
theorem fuchsian_logCocycle_geometric_bound_of_logDensity_bound (hns : ¬ ν ⟂ₘ m)
    (C : ℝ) (hC : ∀ᵐ ξ ∂ν, |Real.log (((ν).rnDeriv m ξ).toReal)| ≤ C) :
    ∀ᵐ ξ ∂ν, ∀ g : Γ, |stationaryLogCocycle ν g ξ| ≤ dist z (g • z) + 2 * C := by
  let : Countable Γ := countable_of_finite_jump_generation s hgen
  have htrans : ∀ᵐ ξ ∂ν, ∀ g : Γ, |Real.log (((ν).rnDeriv m (g • ξ)).toReal)| ≤ C := by
    apply ae_all_iff.mpr
    intro g
    exact (show Measure.QuasiMeasurePreserving (fun ξ : OnePoint ℝ => g • ξ) ν ν from
      ⟨measurable_const_smul g,
        (fuchsian_hittingMeasure_translate_equivalent Γ hne s μ hpos hmass hgen z g).1⟩).ae hC
  filter_upwards [fuchsian_logCocycle_bound_with_density_error Γ hne s μ hpos hmass hgen z hns,
    hC, htrans] with ξ hb h0 hg
  intro g
  linarith [hb g, hg g]


-- @@ L87-87 verbatim
end Singularity
