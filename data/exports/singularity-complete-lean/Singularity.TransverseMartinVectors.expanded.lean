import Singularity.TransverseStrip
import Singularity.GeometricMartinConvergence
import Singularity.RayMartinConvergence
import Singularity.GreenBoundary


-- @@ L6-12 verbatim
/-!
# Strong Martin limits on a strip in any boundary chart

Ordinary Ancona supplies square-summable Green envelopes for every transverse
approach. Dominated convergence gives strong limits of the normalized restricted
Green row and column, with the actual reflected/forward Martin coordinates.
-/


-- @@ L14-14 verbatim
noncomputable section

-- @@ L15-15 verbatim
open MeasureTheory Filter Set OnePoint

-- @@ L16-16 verbatim
open scoped Classical Topology MatrixGroups UpperHalfPlane

-- @@ L17-17 verbatim
namespace Singularity


-- @@ L19-26 verbatim
variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] [Countable Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (horbit : (MulAction.orbit Γ (∞ : OnePoint ℝ)).Infinite)
  (B : SL(2, ℝ))


-- @@ L28-28 verbatim
local notation "A" => transverseJumpStrip Γ s B

-- @@ L29-31 verbatim
local notation "Km" => compactMartinPoint Γ (s.map (Function.Embedding.mk Inv.inv inv_injective))
  (fun g => μ g⁻¹) (reflected_jump_pos s μ hpos) (reflected_support_generates s hgen)
  (reflectedMarkov_spectral_gap s μ hgap) horbit

-- @@ L32-32 verbatim
local notation "Kp" => compactMartinPoint Γ s μ hpos hgen hgap horbit


-- @@ L34-106 verbatim
include hmass in
/-- Both restricted Green vectors converge strongly along every approach to a
finite nonzero endpoint. Their coordinates are actual Martin kernels. -/
theorem transverseMartinVectors_limit (p : OnePoint ℝ) (ξ : ℝ) (hξ : ξ ≠ 0)
    (hB : B • p = (ξ : OnePoint ℝ)) (x : ℕ → Γ)
    (hx : Tendsto (fun n => hyperbolicCompactEmbedding (x n • UpperHalfPlane.I)) atTop
      (𝓝 (compactBoundaryEmbedding p))) :
    ∃ u v : supportedL2 A,
      (∀ g ∈ A, (u : GroupL2 Γ) g = ((Km p).val g : ℂ)) ∧
      (∀ g ∈ A, (v : GroupL2 Γ) g = ((Kp p).val g : ℂ)) ∧
      Tendsto (fun n => normalizedGreenRow s μ A (x n) (walkGreen s μ (x n) 1)) atTop (𝓝 u) ∧
      Tendsto (fun n => normalizedGreenColumn s μ A (x n) (walkGreen s μ 1 (x n))) atTop (𝓝 v) := by
  obtain ⟨C, hC, hb⟩ := transverse_strip_green_domination Γ s μ hpos hmass hgen hgap B x ξ hξ
    (compact_approach_in_chart B p ξ hB (fun n => x n • UpperHalfPlane.I) hx)
  have hs := green_envelopes_square_summable s μ hgap C C
  have hμ : ∀ g ∈ s, 0 ≤ μ g := fun g hg => (hpos g hg).le
  let R := fun n => normalizedGreenRow s μ A (x n) (walkGreen s μ (x n) 1)
  let S := fun n => normalizedGreenColumn s μ A (x n) (walkGreen s μ 1 (x n))
  have hR : ∀ᶠ n in atTop, ∀ g, ‖(R n : GroupL2 Γ) g‖ ≤ C * walkGreen s μ 1 g := by
    filter_upwards [hb] with n hn
    intro g
    by_cases hg : g ∈ A
    · have he := normalizedGreenRow_apply s μ hgap A (x n) (walkGreen s μ (x n) 1) ⟨g,hg⟩
      change (R n : GroupL2 Γ) g = _ at he
      rw [he, ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (walkGreen_nonneg s μ hμ _ _) (walkGreen_nonneg s μ hμ _ _))]
      exact (hn g hg).1
    · rw [(R n).property g hg, norm_zero]
      exact mul_nonneg hC.le (walkGreen_nonneg s μ hμ _ _)
  have hS : ∀ᶠ n in atTop, ∀ g, ‖(S n : GroupL2 Γ) g‖ ≤ C * walkGreen s μ g 1 := by
    filter_upwards [hb] with n hn
    intro g
    by_cases hg : g ∈ A
    · have he := normalizedGreenColumn_apply s μ hgap A (x n) (walkGreen s μ 1 (x n)) ⟨g,hg⟩
      change (S n : GroupL2 Γ) g = _ at he
      rw [he, ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (walkGreen_nonneg s μ hμ _ _) (walkGreen_nonneg s μ hμ _ _))]
      exact (hn g hg).2
    · rw [(S n).property g hg, norm_zero]
      exact mul_nonneg hC.le (walkGreen_nonneg s μ hμ _ _)
  have hRp (g : Γ) : Tendsto (fun n => (R n : GroupL2 Γ) g) atTop
      (𝓝 (if g ∈ A then ((Km p).val g : ℂ) else 0)) := by
    by_cases hg : g ∈ A
    · rw [ite_eq_left hg]
      have ht := compactMartinPoint_tendsto Γ (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹)
        (reflected_jump_pos s μ hpos) ((reflected_jump_mass s μ).trans hmass)
        (reflected_support_generates s hgen) (reflectedMarkov_spectral_gap s μ hgap) horbit p x hx g
      have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp ht
      have he (n : ℕ) := normalizedGreenRow_apply s μ hgap A (x n) (walkGreen s μ (x n) 1) ⟨g,hg⟩
      simp only [Function.comp_def, martinQuotient, reflected_walkGreen s μ hgap, Complex.ofReal_div] at hc
      exact hc.congr' (Filter.Eventually.of_forall (fun n => (he n).symm))
    · simp only [ite_eq_right hg]
      have he : (fun n => (R n : GroupL2 Γ) g) = fun _ => 0 := funext (fun n => (R n).property g hg)
      rw [he]
      exact tendsto_const_nhds
  have hSp (g : Γ) : Tendsto (fun n => (S n : GroupL2 Γ) g) atTop
      (𝓝 (if g ∈ A then ((Kp p).val g : ℂ) else 0)) := by
    by_cases hg : g ∈ A
    · rw [ite_eq_left hg]
      have ht := compactMartinPoint_tendsto Γ s μ hpos hmass hgen hgap horbit p x hx g
      have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp ht
      have he (n : ℕ) := normalizedGreenColumn_apply s μ hgap A (x n) (walkGreen s μ 1 (x n)) ⟨g,hg⟩
      simp only [Function.comp_def, martinQuotient, Complex.ofReal_div] at hc
      exact hc.congr' (Filter.Eventually.of_forall (fun n => (he n).symm))
    · simp only [ite_eq_right hg]
      have he : (fun n => (S n : GroupL2 Γ) g) = fun _ => 0 := funext (fun n => (S n).property g hg)
      rw [he]
      exact tendsto_const_nhds
  obtain ⟨u, hu, hut⟩ := supportedL2_limit_exists A hs.1 hR hRp
  obtain ⟨v, hv, hvt⟩ := supportedL2_limit_exists A hs.2 hS hSp
  refine ⟨u, v, fun g hg => ?_, fun g hg => ?_, hut, hvt⟩
  · simpa only [ite_eq_left hg] using hu g
  · simpa only [ite_eq_left hg] using hv g


-- @@ L108-108 verbatim
end Singularity
