import Singularity.BoundaryCurrentBounds
import Singularity.CocompactCurrentComparison


-- @@ L4-13 verbatim
/-!
# Hitting-density bounds from the cocompact current construction

The proved cocompact ergodicity and scalar current comparison, followed by
compact off-diagonal density reconstruction, give uniform two-sided visual
measure bounds. The positive continuous kernel and its covariance remain
explicit inputs. Nonsingularity of both the forward and reflected laws suffices
for the marginal absolute-continuity inputs; nonsingularity of one is not
silently assumed to imply nonsingularity of the other.
-/


-- @@ L15-15 verbatim
noncomputable section

-- @@ L16-16 verbatim
open MeasureTheory Filter Set OnePoint

-- @@ L17-17 verbatim
open scoped Classical Topology MatrixGroups UpperHalfPlane ENNReal


-- @@ L19-19 verbatim
namespace Singularity


-- @@ L21-28 verbatim
variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  (s : Finset Γ) (μ : Γ → ℝ)
  (hpos : ∀ g ∈ s, 0 < μ g) (hmass : ∑ g ∈ s, μ g = 1)
  (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (z : ℍ)
  (horbit : ∀ p : OnePoint ℝ, (MulAction.orbit Γ p).Infinite)


-- @@ L30-30 verbatim
local notation "νm" => reflectedGeometricHittingMeasure Γ s μ hpos hmass hgen hgap z

-- @@ L31-31 verbatim
local notation "νp" => geometricHittingMeasure Γ s μ hpos hmass hgen hgap z

-- @@ L32-32 verbatim
local notation "m" => compactPoissonMeasure UpperHalfPlane.I


-- @@ L34-34 verbatim
include horbit


-- @@ L36-57 verbatim
/-- A positive continuous covariant kernel upgrades marginal absolute continuity to uniform two-sided bounds. -/
theorem geometricHittingMeasure_bounds_of_continuous_current
    (hback : νm ≪ m) (hforward : νp ≪ m)
    (K : BoundaryPair → ℝ) (hK : Continuous K) (hp : ∀ p, 0 < K p)
    (hcov : ∀ g : Γ, ∀ᵐ p ∂geometricBoundaryPairMeasure Γ s μ hpos hmass hgen hgap z,
      K (g⁻¹ • p) = K p /
        (stationaryRealDensity νm g p.val.1 * stationaryRealDensity νp g p.val.2)) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      (ENNReal.ofReal a • m ≤ νm ∧ νm ≤ ENNReal.ofReal b • m) ∧
      (ENNReal.ofReal a • m ≤ νp ∧ νp ≤ ENNReal.ofReal b • m) := by
  have := reflectedGeometricHittingMeasure_probability Γ s μ hpos hmass hgen hgap z
  have := geometricHittingMeasure_probability Γ s μ hpos hmass hgen hgap z
  have := compactPoissonMeasure_probability UpperHalfPlane.I
  have := compactPoissonMeasure_nullSingleton UpperHalfPlane.I
  obtain ⟨c, hc, hct, heq⟩ := geometricKernelCurrent_eq_liouville_cocompact
    Γ s μ hpos hmass hgen hgap z horbit hback hforward K hK.measurable hp hcov
  obtain ⟨a,b,ha,hb,hab⟩ := boundaryPairCurrent_uniform_density_bounds νm νp m hback hforward
    K liouvilleBoundaryKernel hK continuous_liouvilleBoundaryKernel hp liouvilleBoundaryKernel_pos
    c hc hct heq
  exact ⟨a,b,ha,hb,
    real_rnDeriv_measure_bounds νm m hback a b (hab.mono (fun _ hx => hx.1)),
    real_rnDeriv_measure_bounds νp m hforward a b (hab.mono (fun _ hx => hx.2))⟩


-- @@ L59-76 verbatim
/-- Nonsingularity of both actual hitting laws plus the continuous current kernel supplies the uniform bounds. -/
theorem geometricHittingMeasure_bounds_of_nonsingular_continuous_current
    (hback : ¬ νm ⟂ₘ compactPoissonMeasure z)
    (hforward : ¬ νp ⟂ₘ compactPoissonMeasure z)
    (K : BoundaryPair → ℝ) (hK : Continuous K) (hp : ∀ p, 0 < K p)
    (hcov : ∀ g : Γ, ∀ᵐ p ∂geometricBoundaryPairMeasure Γ s μ hpos hmass hgen hgap z,
      K (g⁻¹ • p) = K p /
        (stationaryRealDensity νm g p.val.1 * stationaryRealDensity νp g p.val.2)) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      (ENNReal.ofReal a • m ≤ νm ∧ νm ≤ ENNReal.ofReal b • m) ∧
      (ENNReal.ofReal a • m ≤ νp ∧ νp ≤ ENNReal.ofReal b • m) := by
  have hbz : νm ≪ compactPoissonMeasure z :=
    geometricHittingMeasure_absolutelyContinuous_of_not_singular Γ _ _ _ _ _ _ z hback
  have hfz := geometricHittingMeasure_absolutelyContinuous_of_not_singular
    Γ s μ hpos hmass hgen hgap z hforward
  exact geometricHittingMeasure_bounds_of_continuous_current Γ s μ hpos hmass hgen hgap z horbit
    (hbz.trans (compactPoissonMeasure_absolutelyContinuous _ _))
    (hfz.trans (compactPoissonMeasure_absolutelyContinuous _ _)) K hK hp hcov


-- @@ L78-78 verbatim
end Singularity
