import Singularity.CocompactRayApproximation
import Singularity.GeometricBoundaryLimit
import Singularity.NaimSubsequence


-- @@ L5-12 verbatim
/-!
# The geometric Green boundary limit for a compact orbit quotient

Ray approximations, eventual sides, the finite periodic separator, and summable
Green envelopes are all supplied by proved constructions. The initial rigidity
comparison, spectral gap, normalized diagonal element, and pointwise boundary
coordinates remain explicit inputs.
-/


-- @@ L14-14 verbatim
noncomputable section

-- @@ L15-15 verbatim
open MeasureTheory Filter Set

-- @@ L16-16 verbatim
open scoped MatrixGroups UpperHalfPlane Topology


-- @@ L18-18 verbatim
namespace Singularity


-- @@ L20-26 verbatim
variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] [Countable Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (a : Γ) {τ : ℝ} (ha : (a : SL(2, ℝ)) = dilationMatrix τ) (hτ : 0 < τ)
  {ξ η : ℝ}


-- @@ L28-29 verbatim
local notation "Rep" => stripRepresentatives Γ UpperHalfPlane.I
  (jumpStripRadius (finiteJumpLengthBound Γ UpperHalfPlane.I s)) τ

-- @@ L30-31 verbatim
local notation "E" => stripOrbitEquiv Γ a ha hτ UpperHalfPlane.I
  (jumpStripRadius (finiteJumpLengthBound Γ UpperHalfPlane.I s))

-- @@ L32-32 verbatim
local notation "X" => cocompactRaySequence Γ ξ

-- @@ L33-33 verbatim
local notation "Y" => cocompactRaySequence Γ η


-- @@ L35-56 verbatim
/-- The actual cocompact ray sequences satisfy the normalized Green pairing
limit whenever their pointwise boundary coordinates converge. -/
theorem cocompactStrip_boundary_limit {C : ℝ} (hC : 0 < C)
    (hcmp : GreenDistanceComparison Γ s μ C) (hξ : ξ < 0) (hη : 0 < η)
    (u₀ v₀ : (ℤ × Rep) → ℂ)
    (hup : ∀ p, Tendsto (fun n => (walkGreen s μ (X n) (a ^ p.1 * (p.2 : Γ)) : ℂ) /
      (walkGreen s μ (X n) 1 : ℂ)) atTop (𝓝 (u₀ p)))
    (hvp : ∀ p, Tendsto (fun n => (walkGreen s μ (a ^ p.1 * (p.2 : Γ)) (Y n) : ℂ) /
      (walkGreen s μ 1 (Y n) : ℂ)) atTop (𝓝 (v₀ p))) :
    ∃ u v : SequenceL2 (ℤ × Rep),
      (∀ p, u p = u₀ p) ∧ (∀ p, v p = v₀ p) ∧
      Tendsto (fun n => orbitGreenRow s μ E (X n) (walkGreen s μ (X n) 1)) atTop (𝓝 u) ∧
      Tendsto (fun n => orbitGreenColumn s μ E (Y n) (walkGreen s μ 1 (Y n))) atTop (𝓝 v) ∧
      Tendsto (fun n => (walkGreen s μ (X n) (Y n) : ℂ) /
        ((walkGreen s μ (X n) 1 : ℂ) * (walkGreen s μ 1 (Y n) : ℂ)))
        atTop (𝓝 (inner ℂ u (orbitGreenInverse s μ hμ hmass hgap E v))) := by
  exact geometricStrip_boundary_limit Γ s μ hμ hmass hgap a ha hτ hC hcmp X Y
    (fun n : ℕ => (n : ℝ)) (fun n : ℕ => (n : ℝ)) hξ.ne hη.ne'
    (cocompactOrbitRadius Γ) (cocompactOrbitRadius Γ)
    (fun n => Nat.cast_nonneg n) (fun n => Nat.cast_nonneg n)
    (cocompactRaySequence_bound Γ ξ) (cocompactRaySequence_bound Γ η)
    (cocompactRaySequence_eventually_opposite Γ hξ hη) u₀ v₀ hup hvp


-- @@ L58-90 verbatim
/-- Without assuming pointwise coordinates, Martin compactness supplies a
subsequence whose normalized Green quotient converges to the strip pairing.
This does not assert uniqueness or existence of the full Naïm limit. -/
theorem cocompactStrip_naim_subsequence
    (hpos : ∀ g ∈ s, 0 < μ g) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
    {C : ℝ} (hC : 0 < C) (hcmp : GreenDistanceComparison Γ s μ C)
    (hξ : ξ < 0) (hη : 0 < η) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u v : SequenceL2 (ℤ × Rep),
      Tendsto (fun n => orbitGreenRow s μ E (X (φ n)) (walkGreen s μ (X (φ n)) 1)) atTop (𝓝 u) ∧
      Tendsto (fun n => orbitGreenColumn s μ E (Y (φ n)) (walkGreen s μ 1 (Y (φ n)))) atTop (𝓝 v) ∧
      Tendsto (fun n => (finiteNaimQuotient s μ 1 (X (φ n)) (Y (φ n)) : ℂ)) atTop
        (𝓝 (inner ℂ u (orbitGreenInverse s μ hμ hmass hgap E v))) := by
  let : Fintype Rep := (finite_stripRepresentatives Γ UpperHalfPlane.I
    (jumpStripRadius_pos (finiteJumpLengthBound_nonneg Γ UpperHalfPlane.I s)).le τ).fintype
  apply finiteNaim_pairing_subsequence s μ hμ hmass hgap E hpos hgen 1 X Y hτ hτ
    (fun j => (C ^ 2 * Real.exp (2 * cocompactOrbitRadius Γ)) *
      visualPoissonEnvelope ((j : Γ) • UpperHalfPlane.I) ξ)
    (fun j => (C ^ 2 * Real.exp (2 * cocompactOrbitRadius Γ)) *
      visualPoissonEnvelope ((j : Γ) • UpperHalfPlane.I) η)
  · filter_upwards [cocompactRaySequence_eventually_opposite Γ hξ hη] with n hn
    exact finiteJumpStrip_separates Γ UpperHalfPlane.I s (X n) (Y n) hn.1 hn.2
  · apply Filter.Eventually.of_forall
    intro n p
    rw [reverseMartinQuotient, Complex.ofReal_div, stripOrbitEquiv_apply,
      greenDistance_complex_quotient_norm Γ s μ hC hcmp]
    exact greenDistance_row_orbit_bound Γ s μ hC hcmp a (p.2 : Γ) ha hτ hξ.ne
      (Nat.cast_nonneg n) (X n) (cocompactRaySequence_bound Γ ξ n) p.1
  · apply Filter.Eventually.of_forall
    intro n p
    rw [martinQuotient, Complex.ofReal_div, stripOrbitEquiv_apply,
      greenDistance_complex_quotient_norm Γ s μ hC hcmp]
    exact greenDistance_column_orbit_bound Γ s μ hC hcmp a (p.2 : Γ) ha hτ hη.ne'
      (Nat.cast_nonneg n) (Y n) (cocompactRaySequence_bound Γ η n) p.1


-- @@ L92-92 verbatim
end Singularity
