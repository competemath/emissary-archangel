import Singularity.GeometricNaimContinuity
import Singularity.NaimCovariance


-- @@ L4-9 verbatim
/-!
# Exact covariance of the global Naïm kernel

The finite Green quotient identity passes to the proved full boundary limit.
The two cocycle factors are the actual reflected and forward Martin kernels.
-/


-- @@ L11-11 verbatim
noncomputable section

-- @@ L12-12 verbatim
open Filter Set OnePoint

-- @@ L13-13 verbatim
open scoped Classical Topology MatrixGroups UpperHalfPlane

-- @@ L14-14 verbatim
namespace Singularity


-- @@ L16-29 verbatim
/-- Left translation of orbit approaches agrees with the genuine boundary action. -/
theorem compact_orbit_approach_smul (Γ : Subgroup SL(2, ℝ))
    {ι : Type*} {l : Filter ι} (g : Γ) (p : OnePoint ℝ) (x : ι → Γ)
    (hx : Tendsto (fun n => hyperbolicCompactEmbedding (x n • UpperHalfPlane.I)) l
      (𝓝 (compactBoundaryEmbedding p))) :
    Tendsto (fun n => hyperbolicCompactEmbedding ((g * x n) • UpperHalfPlane.I)) l
      (𝓝 (compactBoundaryEmbedding (g • p))) := by
  have ht := (continuous_const_smul (g : SL(2, ℝ))).continuousAt.tendsto.comp hx
  rw [← compactBoundaryEmbedding_smul] at ht
  convert ht using 1
  · funext n
    rw [mul_smul]
    exact hyperbolicCompactEmbedding_smul g _
  · rfl


-- @@ L31-37 verbatim
variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] [Countable Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (horbit : (MulAction.orbit Γ (∞ : OnePoint ℝ)).Infinite)


-- @@ L39-41 verbatim
local notation "Km" => compactMartinPoint Γ (s.map (Function.Embedding.mk Inv.inv inv_injective))
  (fun g => μ g⁻¹) (reflected_jump_pos s μ hpos) (reflected_support_generates s hgen)
  (reflectedMarkov_spectral_gap s μ hgap) horbit

-- @@ L42-42 verbatim
local notation "Kp" => compactMartinPoint Γ s μ hpos hgen hgap horbit

-- @@ L43-43 verbatim
local notation "Θ" => geometricNaimKernel Γ s μ hpos hmass hgen hgap horbit


-- @@ L45-69 verbatim
/-- The global Naïm kernel obeys the exact forward/reflected covariance law. -/
theorem geometricNaimKernel_smul (g : Γ) (p : BoundaryPair) :
    Θ ((g : SL(2, ℝ)) • p) = Θ p / ((Km p.val.1).val g⁻¹ * (Kp p.val.2).val g⁻¹) := by
  obtain ⟨x, hx⟩ := exists_compact_boundary_orbit_approach Γ horbit p.val.1
  obtain ⟨y, hy⟩ := exists_compact_boundary_orbit_approach Γ horbit p.val.2
  have hθ := geometricNaimKernel_tendsto Γ s μ hpos hmass hgen hgap horbit p x y hx hy
  have hm := compactMartinPoint_tendsto Γ (s.map ⟨Inv.inv, inv_injective⟩) (fun a => μ a⁻¹)
    (reflected_jump_pos s μ hpos) ((reflected_jump_mass s μ).trans hmass)
    (reflected_support_generates s hgen) (reflectedMarkov_spectral_gap s μ hgap)
    horbit p.val.1 x hx g⁻¹
  have hp := compactMartinPoint_tendsto Γ s μ hpos hmass hgen hgap horbit p.val.2 y hy g⁻¹
  have hmp := martinClosure_pos (s.map ⟨Inv.inv, inv_injective⟩) (fun a => μ a⁻¹)
    (reflected_jump_pos s μ hpos) (reflected_support_generates s hgen)
    (reflectedMarkov_spectral_gap s μ hgap) 1 (Km p.val.1).property.1 g⁻¹
  have hpp := martinClosure_pos s μ hpos hgen hgap 1 (Kp p.val.2).property.1 g⁻¹
  have ht := hθ.div (hm.mul hp) (ne_of_gt (mul_pos hmp hpp))
  have he (n : ℕ) : finiteNaimQuotient s μ 1 (x n) (y n) /
      (martinQuotient (s.map ⟨Inv.inv, inv_injective⟩) (fun a => μ a⁻¹) 1 g⁻¹ (x n) *
        martinQuotient s μ 1 g⁻¹ (y n)) = finiteNaimQuotient s μ 1 (g * x n) (g * y n) := by
    rw [finiteNaimQuotient_translate s μ hpos hgen hgap 1 g (x n) (y n)]
    simp only [martinQuotient, reverseMartinQuotient, reflected_walkGreen s μ hgap, mul_one]
  have hgθ := geometricNaimKernel_tendsto Γ s μ hpos hmass hgen hgap horbit ((g : SL(2, ℝ)) • p)
    (fun n => g * x n) (fun n => g * y n)
    (compact_orbit_approach_smul Γ g p.val.1 x hx) (compact_orbit_approach_smul Γ g p.val.2 y hy)
  exact tendsto_nhds_unique hgθ (ht.congr' (Eventually.of_forall he))


-- @@ L71-71 verbatim
end Singularity
