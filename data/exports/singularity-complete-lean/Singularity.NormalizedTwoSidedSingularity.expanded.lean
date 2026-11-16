import Singularity.HittingDensityPairing
import Singularity.NaimCurrentRigidity
import Singularity.CurrentFactorization


-- @@ L5-12 verbatim
/-!
# Singularity of at least one hitting law in normalized cocompact coordinates

The actual Naïm current and the actual strip-density pairing now feed the
proved Fourier contradiction. Both hitting laws cannot be nonsingular against
visual measure. A positive diagonal element is supplied in the subgroup;
transporting the conclusion through normalization is a separate step.
-/


-- @@ L14-14 verbatim
noncomputable section

-- @@ L15-15 verbatim
open MeasureTheory Filter Set OnePoint

-- @@ L16-16 verbatim
open scoped Classical Topology MatrixGroups UpperHalfPlane ENNReal

-- @@ L17-17 verbatim
namespace Singularity


-- @@ L19-26 verbatim
variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] [Countable Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (horbit : ∀ p : OnePoint ℝ, (MulAction.orbit Γ p).Infinite) (z : ℍ)
  (a : Γ) {τ : ℝ} (ha : (a : SL(2, ℝ)) = dilationMatrix τ) (hτ : 0 < τ)


-- @@ L28-28 verbatim
local notation "νm" => reflectedGeometricHittingMeasure Γ s μ hpos hmass hgen hgap z

-- @@ L29-29 verbatim
local notation "νp" => geometricHittingMeasure Γ s μ hpos hmass hgen hgap z

-- @@ L30-30 verbatim
local notation "Θ" => geometricNaimKernel Γ s μ hpos hmass hgen hgap (horbit ∞)


-- @@ L32-94 verbatim
include horbit ha hτ in
/-- Both actual hitting laws cannot be nonsingular in the normalized cocompact case. -/
theorem normalized_hitting_not_both_nonsingular
    (hback : ¬ νm ⟂ₘ compactPoissonMeasure z) (hforward : ¬ νp ⟂ₘ compactPoissonMeasure z) : False := by
  obtain ⟨d, B, hd, hB, hbm, hbp⟩ := geometricHittingMeasure_bounds_of_both_nonsingular
    Γ s μ hpos hmass hgen hgap horbit z hback hforward
  have hmac : νm ≪ compactPoissonMeasure UpperHalfPlane.I := Measure.absolutelyContinuous_of_le_smul hbm.2
  have hpac : νp ≪ compactPoissonMeasure UpperHalfPlane.I := Measure.absolutelyContinuous_of_le_smul hbp.2
  obtain ⟨c, hc, hct, hcurrent⟩ := geometricNaimCurrent_eq_liouville Γ s μ hpos hmass hgen hgap
    horbit z hmac hpac
  let : IsProbabilityMeasure νm := reflectedGeometricHittingMeasure_probability Γ s μ hpos hmass hgen hgap z
  let : IsProbabilityMeasure νp := geometricHittingMeasure_probability Γ s μ hpos hmass hgen hgap z
  let : NullSingletonClass νp := geometricHittingMeasure_nullSingleton Γ s μ hpos hmass hgen hgap z horbit
  let : IsProbabilityMeasure (finiteBoundaryMeasure νm) := finiteBoundaryMeasure_probability νm
  let : IsProbabilityMeasure (finiteBoundaryMeasure νp) := finiteBoundaryMeasure_probability νp
  let q := poissonCappedDensity (finiteBoundaryMeasure νm) 0 1 B
  let r := poissonCappedDensity (finiteBoundaryMeasure νp) 0 1 B
  have hq : Measurable q := measurable_poissonCappedDensity _ _ _ _
  have hr : Measurable r := measurable_poissonCappedDensity _ _ _ _
  have hpq : ∀ u, 0 ≤ q u := poissonCappedDensity_nonneg _ _ zero_lt_one hB.le
  have hpr : ∀ u, 0 ≤ r u := poissonCappedDensity_nonneg _ _ zero_lt_one hB.le
  have hqm : volume.withDensity (fun u => ENNReal.ofReal (q u)) = finiteBoundaryMeasure νm :=
    poissonCappedDensity_measure _ (finiteBoundaryMeasure_absolutelyContinuous νm UpperHalfPlane.I hmac)
      0 1 B (finiteBoundaryMeasure_density_bound νm UpperHalfPlane.I hB.le hbm.2)
  have hrm : volume.withDensity (fun u => ENNReal.ofReal (r u)) = finiteBoundaryMeasure νp :=
    poissonCappedDensity_measure _ (finiteBoundaryMeasure_absolutelyContinuous νp UpperHalfPlane.I hpac)
      0 1 B (finiteBoundaryMeasure_density_bound νp UpperHalfPlane.I hB.le hbp.2)
  have hqmc : compactRealMeasure (volume.withDensity (fun u => ENNReal.ofReal (q u))) = νm := by
    rw [hqm]
    exact finiteBoundaryMeasure_reconstruct νm (compactPoisson_ac_infty νm UpperHalfPlane.I hmac)
  have hrmc : compactRealMeasure (volume.withDensity (fun u => ENNReal.ofReal (r u))) = νp := by
    rw [hrm]
    exact finiteBoundaryMeasure_reconstruct νp (compactPoisson_ac_infty νp UpperHalfPlane.I hpac)
  let F := realBoundaryCurrentDensity q r Θ
  have hF : Measurable F := measurable_realBoundaryCurrentDensity q r Θ hq hr
    (continuous_geometricNaimKernel Γ s μ hpos hmass hgen hgap (horbit ∞)).measurable
  have hpF : ∀ t, 0 ≤ F t := realBoundaryCurrentDensity_nonneg q r Θ hpq hpr
    (fun p => (geometricNaimKernel_pos Γ s μ hpos hmass hgen hgap (horbit ∞) p).le)
  have hreal := boundaryPairCurrent_real_eq_liouville νm νp q r Θ hq hr
    (continuous_geometricNaimKernel Γ s μ hpos hmass hgen hgap (horbit ∞)).measurable
    hpq hpr hqmc hrmc c hcurrent
  have hrestriction := realCurrent_eq_liouville_opposite F c hreal
  let R := jumpStripRadius (finiteJumpLengthBound Γ UpperHalfPlane.I s)
  let J := stripRepresentatives Γ UpperHalfPlane.I R τ
  let : Fintype J := (finite_stripRepresentatives Γ UpperHalfPlane.I
    (jumpStripRadius_pos (finiteJumpLengthBound_nonneg Γ UpperHalfPlane.I s)).le τ).fintype
  let b : J → Γ := Subtype.val
  let e : (ℤ × J) ≃ finiteJumpStrip Γ UpperHalfPlane.I s :=
    stripOrbitEquiv Γ a ha hτ UpperHalfPlane.I R
  have he (p : ℤ × J) : (e p : Γ) = a ^ p.1 * b p.2 := rfl
  let Hm := geometricHittingDensityFamily Γ (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹)
    (reflected_jump_pos s μ hpos) ((reflected_jump_mass s μ).trans hmass)
    (reflected_support_generates s hgen) (reflectedMarkov_spectral_gap s μ hgap) z
    (-1) (Or.inr rfl) hτ B hB.le hbm.2 b
  let Hp := geometricHittingDensityFamily Γ s μ hpos hmass hgen hgap z 1 (Or.inl rfl) hτ B hB.le hbp.2 b
  let M := orbitGreenInverse s μ (fun g hg => (hpos g hg).le) hmass hgap e
  have hpair := geometricHittingDensityFamily_pairing Γ s μ hpos hmass hgen hgap (horbit ∞) z hτ
    a ha b e he B B hB.le hB.le hbm.2 hbp.2 q r hq hr hpq hpr hqm hrm
  have hfactor := liouville_factorization_of_current_identity Hm Hp M F hF hpF c hrestriction hpair
  exact impossible_factorization (liouvilleConvolution c.toReal) Hp.analysis M Hm.analysis.adjoint
    hfactor (liouvilleConvolution_injective (ENNReal.toReal_pos hc.ne' hct.ne))
    (geometricHittingDensityFamily_has_kernel Γ s μ hpos hmass hgen hgap z
      1 (Or.inl rfl) hτ B hB.le hbp.2 b)


-- @@ L96-102 verbatim
include horbit ha hτ in
/-- At least one of the actual forward and reflected laws is singular against visual measure. -/
theorem normalized_forward_or_reflected_singular :
    νp ⟂ₘ compactPoissonMeasure z ∨ νm ⟂ₘ compactPoissonMeasure z := by
  by_contra h
  push Not at h
  exact normalized_hitting_not_both_nonsingular Γ s μ hpos hmass hgen hgap horbit z a ha hτ h.2 h.1


-- @@ L104-104 verbatim
end Singularity
