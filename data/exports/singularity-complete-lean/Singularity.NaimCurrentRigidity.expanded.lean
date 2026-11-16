import Singularity.GeometricNaimCurrent
import Singularity.CocompactGreenComparison


-- @@ L4-10 verbatim
/-!
# Rigidity using the constructed Naïm current

The global Naïm kernel, its continuity, positivity, and derivative covariance
are now conclusions, not inputs. The remaining marginal assumption is explicit:
both forward and reflected hitting laws are nonsingular against visual measure.
-/


-- @@ L12-12 verbatim
noncomputable section

-- @@ L13-13 verbatim
open MeasureTheory Filter Set OnePoint

-- @@ L14-14 verbatim
open scoped Classical Topology MatrixGroups UpperHalfPlane ENNReal

-- @@ L15-15 verbatim
namespace Singularity


-- @@ L17-23 verbatim
variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] [Countable Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (horbit : ∀ p : OnePoint ℝ, (MulAction.orbit Γ p).Infinite) (z : ℍ)


-- @@ L25-25 verbatim
local notation "νm" => reflectedGeometricHittingMeasure Γ s μ hpos hmass hgen hgap z

-- @@ L26-26 verbatim
local notation "νp" => geometricHittingMeasure Γ s μ hpos hmass hgen hgap z

-- @@ L27-27 verbatim
local notation "Θ" => geometricNaimKernel Γ s μ hpos hmass hgen hgap (horbit ∞)

-- @@ L28-28 verbatim
local notation "m" => compactPoissonMeasure UpperHalfPlane.I


-- @@ L30-30 verbatim
include horbit


-- @@ L32-40 verbatim
/-- Absolute continuity of both marginals makes the actual Naïm current a
positive finite scalar multiple of Liouville current. -/
theorem geometricNaimCurrent_eq_liouville (hback : νm ≪ m) (hforward : νp ≪ m) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧
      geometricNaimCurrent Γ s μ hpos hmass hgen hgap horbit z = c • compactLiouvilleCurrent :=
  geometricKernelCurrent_eq_liouville_cocompact Γ s μ hpos hmass hgen hgap z horbit
    hback hforward Θ (continuous_geometricNaimKernel Γ s μ hpos hmass hgen hgap (horbit ∞)).measurable
    (geometricNaimKernel_pos Γ s μ hpos hmass hgen hgap (horbit ∞))
    (geometricNaimKernel_density_covariance Γ s μ hpos hmass hgen hgap horbit z)


-- @@ L42-52 verbatim
/-- Nonsingularity of both marginals supplies uniform two-sided visual bounds,
with no kernel or current hypothesis. -/
theorem geometricHittingMeasure_bounds_of_both_nonsingular
    (hback : ¬ νm ⟂ₘ compactPoissonMeasure z) (hforward : ¬ νp ⟂ₘ compactPoissonMeasure z) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      (ENNReal.ofReal a • m ≤ νm ∧ νm ≤ ENNReal.ofReal b • m) ∧
      (ENNReal.ofReal a • m ≤ νp ∧ νp ≤ ENNReal.ofReal b • m) :=
  geometricHittingMeasure_bounds_of_nonsingular_continuous_current Γ s μ hpos hmass hgen hgap z horbit
    hback hforward Θ (continuous_geometricNaimKernel Γ s μ hpos hmass hgen hgap (horbit ∞))
    (geometricNaimKernel_pos Γ s μ hpos hmass hgen hgap (horbit ∞))
    (geometricNaimKernel_density_covariance Γ s μ hpos hmass hgen hgap horbit z)


-- @@ L54-63 verbatim
/-- Both nonsingularity assumptions yield sharp Green-distance comparison for
both laws; the Naïm construction is fully discharged. -/
theorem GreenDistanceComparison_of_both_nonsingular
    (hback : ¬ νm ⟂ₘ compactPoissonMeasure z) (hforward : ¬ νp ⟂ₘ compactPoissonMeasure z) :
    ∃ C : ℝ, 1 ≤ C ∧ GreenDistanceComparison Γ s μ C ∧
      GreenDistanceComparison Γ (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹) C :=
  cocompact_current_Green_comparison Γ s μ hpos hmass hgen hgap z horbit hback hforward Θ
    (continuous_geometricNaimKernel Γ s μ hpos hmass hgen hgap (horbit ∞))
    (geometricNaimKernel_pos Γ s μ hpos hmass hgen hgap (horbit ∞))
    (geometricNaimKernel_density_covariance Γ s μ hpos hmass hgen hgap horbit z)


-- @@ L65-65 verbatim
end Singularity
