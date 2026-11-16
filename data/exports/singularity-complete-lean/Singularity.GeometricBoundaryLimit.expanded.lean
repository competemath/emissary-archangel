import Singularity.GreenPoissonBounds


-- @@ L3-12 verbatim
/-!
# Dominated Green boundary limits on the actual geometric strip

The geometric distance comparison and bounded-distance ray approaches now
supply the exponential ℓ² domination, while the constructed strip supplies
separation and its finite cyclic enumeration. The spectral gap, geometric
comparison, ray approximations, eventual opposite sides, and coordinate limits
remain explicit inputs. Separation and summable domination are derived, so the
infinite sum is not interchanged with a limit without norm control.
-/


-- @@ L14-14 verbatim
noncomputable section

-- @@ L15-15 verbatim
open MeasureTheory Filter Set

-- @@ L16-16 verbatim
open scoped MatrixGroups UpperHalfPlane Topology


-- @@ L18-18 verbatim
namespace Singularity


-- @@ L20-24 verbatim
variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] [Countable Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (a : Γ) {τ : ℝ} (ha : (a : SL(2, ℝ)) = dilationMatrix τ) (hτ : 0 < τ)


-- @@ L26-27 verbatim
local notation "Rep" => stripRepresentatives Γ UpperHalfPlane.I
  (jumpStripRadius (finiteJumpLengthBound Γ UpperHalfPlane.I s)) τ

-- @@ L28-29 verbatim
local notation "E" => stripOrbitEquiv Γ a ha hτ UpperHalfPlane.I
  (jumpStripRadius (finiteJumpLengthBound Γ UpperHalfPlane.I s))


-- @@ L31-73 verbatim
/-- The normalized geometric Green pairing converges from pointwise Martin
coordinates, with both separation and square-summable bounds derived. -/
theorem geometricStrip_boundary_limit {α : Type*} {l : Filter α} [l.NeBot]
    {C : ℝ} (hC : 0 < C) (hcmp : GreenDistanceComparison Γ s μ C)
    (x y : α → Γ) (tx ty : α → ℝ) {ξ η : ℝ} (hξ : ξ ≠ 0) (hη : η ≠ 0)
    (Dx Dy : ℝ) (hxt : ∀ n, 0 ≤ tx n) (hyt : ∀ n, 0 ≤ ty n)
    (hxr : ∀ n, dist (x n • UpperHalfPlane.I) (finiteBoundaryRay ξ (tx n)) ≤ Dx)
    (hyr : ∀ n, dist (y n • UpperHalfPlane.I) (finiteBoundaryRay η (ty n)) ≤ Dy)
    (hsides : ∀ᶠ n in l, (x n • UpperHalfPlane.I).re < 0 ∧ 0 ≤ (y n • UpperHalfPlane.I).re)
    (u₀ v₀ : (ℤ × Rep) → ℂ)
    (hup : ∀ p, Tendsto (fun n => (walkGreen s μ (x n) (a ^ p.1 * (p.2 : Γ)) : ℂ) /
      (walkGreen s μ (x n) 1 : ℂ)) l (𝓝 (u₀ p)))
    (hvp : ∀ p, Tendsto (fun n => (walkGreen s μ (a ^ p.1 * (p.2 : Γ)) (y n) : ℂ) /
      (walkGreen s μ 1 (y n) : ℂ)) l (𝓝 (v₀ p))) :
    ∃ u v : SequenceL2 (ℤ × Rep),
      (∀ p, u p = u₀ p) ∧ (∀ p, v p = v₀ p) ∧
      Tendsto (fun n => orbitGreenRow s μ E (x n) (walkGreen s μ (x n) 1)) l (𝓝 u) ∧
      Tendsto (fun n => orbitGreenColumn s μ E (y n) (walkGreen s μ 1 (y n))) l (𝓝 v) ∧
      Tendsto (fun n => (walkGreen s μ (x n) (y n) : ℂ) /
        ((walkGreen s μ (x n) 1 : ℂ) * (walkGreen s μ 1 (y n) : ℂ)))
        l (𝓝 (inner ℂ u (orbitGreenInverse s μ hμ hmass hgap E v))) := by
  let : Fintype Rep := (finite_stripRepresentatives Γ UpperHalfPlane.I
    (jumpStripRadius_pos (finiteJumpLengthBound_nonneg Γ UpperHalfPlane.I s)).le τ).fintype
  apply orbitGreen_boundary_limit s μ hμ hmass hgap E x y
    (fun n => walkGreen s μ (x n) 1) (fun n => walkGreen s μ 1 (y n)) u₀ v₀ hτ hτ
    (fun j => (C ^ 2 * Real.exp (2 * Dx)) * visualPoissonEnvelope ((j : Γ) • UpperHalfPlane.I) ξ)
    (fun j => (C ^ 2 * Real.exp (2 * Dy)) * visualPoissonEnvelope ((j : Γ) • UpperHalfPlane.I) η)
  · filter_upwards [hsides] with n hn
    exact finiteJumpStrip_separates Γ UpperHalfPlane.I s (x n) (y n) hn.1 hn.2
  · apply Filter.Eventually.of_forall
    intro n p
    rw [stripOrbitEquiv_apply, greenDistance_complex_quotient_norm Γ s μ hC hcmp]
    exact greenDistance_row_orbit_bound Γ s μ hC hcmp a (p.2 : Γ) ha hτ hξ
      (hxt n) (x n) (hxr n) p.1
  · apply Filter.Eventually.of_forall
    intro n p
    rw [stripOrbitEquiv_apply, greenDistance_complex_quotient_norm Γ s μ hC hcmp]
    exact greenDistance_column_orbit_bound Γ s μ hC hcmp a (p.2 : Γ) ha hτ hη
      (hyt n) (y n) (hyr n) p.1
  · intro p
    simpa only [stripOrbitEquiv_apply] using hup p
  · intro p
    simpa only [stripOrbitEquiv_apply] using hvp p


-- @@ L75-75 verbatim
end Singularity
