import Singularity.StripMartinVectors
import Singularity.NaimAnconaBounds


-- @@ L4-11 verbatim
/-!
# A positive Naïm kernel on opposite finite boundary sides

The normalized restricted Green vectors have unique strong limits determined by
their Martin coordinates. Their compressed-inverse pairing defines a real kernel.
Every pair of approaches to a negative and a positive endpoint converges to it.
No visual-density, Green-distance-comparison, or current hypothesis is used.
-/


-- @@ L13-13 verbatim
noncomputable section

-- @@ L14-14 verbatim
open MeasureTheory Filter Set

-- @@ L15-15 verbatim
open scoped Classical Topology MatrixGroups UpperHalfPlane

-- @@ L16-16 verbatim
namespace Singularity


-- @@ L18-28 verbatim
/-- Supported counting-L² vectors are determined by their coordinates on the support. -/
theorem supportedL2_ext_on {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (A : Set X) (u v : supportedL2 A)
    (h : ∀ g ∈ A, (u : GroupL2 X) g = (v : GroupL2 X) g) : u = v := by
  apply Subtype.ext
  apply Lp.ext
  apply Filter.Eventually.of_forall
  intro g
  by_cases hg : g ∈ A
  · exact h g hg
  · rw [u.property g hg, v.property g hg]


-- @@ L30-35 verbatim
variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] [Countable Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)


-- @@ L37-37 verbatim
local notation "A" => finiteJumpStrip Γ UpperHalfPlane.I s

-- @@ L38-40 verbatim
local notation "Km" => rayMartinPoint Γ (s.map (Function.Embedding.mk Inv.inv inv_injective))
  (fun g => μ g⁻¹) (reflected_jump_pos s μ hpos) (reflected_support_generates s hgen)
  (reflectedMarkov_spectral_gap s μ hgap)

-- @@ L41-41 verbatim
local notation "Kp" => rayMartinPoint Γ s μ hpos hgen hgap

-- @@ L42-43 verbatim
local notation "M" => ContinuousLinearEquiv.symm
  (walkGreenCompression s μ (fun g hg => le_of_lt (hpos g hg)) hmass hgap A)


-- @@ L45-48 verbatim
/-- The unique reflected Martin vector on the actual strip. -/
def stripMartinRow (ξ : ℝ) (hξ : ξ ≠ 0) : supportedL2 A :=
  (stripMartinVectors_limit Γ s μ hpos hmass hgen hgap ξ hξ
    (cocompactRaySequence Γ ξ) (cocompactRaySequence_tendsto Γ ξ)).choose


-- @@ L50-53 verbatim
/-- The unique forward Martin vector on the actual strip. -/
def stripMartinColumn (ξ : ℝ) (hξ : ξ ≠ 0) : supportedL2 A :=
  (stripMartinVectors_limit Γ s μ hpos hmass hgen hgap ξ hξ
    (cocompactRaySequence Γ ξ) (cocompactRaySequence_tendsto Γ ξ)).choose_spec.choose


-- @@ L55-58 verbatim
theorem stripMartinRow_apply (ξ : ℝ) (hξ : ξ ≠ 0) (g : Γ) (hg : g ∈ A) :
    (stripMartinRow Γ s μ hpos hmass hgen hgap ξ hξ : GroupL2 Γ) g = ((Km ξ).val g : ℂ) :=
  (stripMartinVectors_limit Γ s μ hpos hmass hgen hgap ξ hξ
    (cocompactRaySequence Γ ξ) (cocompactRaySequence_tendsto Γ ξ)).choose_spec.choose_spec.1 g hg


-- @@ L60-63 verbatim
theorem stripMartinColumn_apply (ξ : ℝ) (hξ : ξ ≠ 0) (g : Γ) (hg : g ∈ A) :
    (stripMartinColumn Γ s μ hpos hmass hgen hgap ξ hξ : GroupL2 Γ) g = ((Kp ξ).val g : ℂ) :=
  (stripMartinVectors_limit Γ s μ hpos hmass hgen hgap ξ hξ
    (cocompactRaySequence Γ ξ) (cocompactRaySequence_tendsto Γ ξ)).choose_spec.choose_spec.2.1 g hg


-- @@ L65-81 verbatim
/-- The same named vectors are the strong limits for every approach to the endpoint. -/
theorem stripMartinVectors_tendsto (ξ : ℝ) (hξ : ξ ≠ 0) (x : ℕ → Γ)
    (hx : Tendsto (fun n => ((x n • UpperHalfPlane.I : ℍ) : ℂ)) atTop (𝓝 (ξ : ℂ))) :
    Tendsto (fun n => normalizedGreenRow s μ A (x n) (walkGreen s μ (x n) 1)) atTop
      (𝓝 (stripMartinRow Γ s μ hpos hmass hgen hgap ξ hξ)) ∧
    Tendsto (fun n => normalizedGreenColumn s μ A (x n) (walkGreen s μ 1 (x n))) atTop
      (𝓝 (stripMartinColumn Γ s μ hpos hmass hgen hgap ξ hξ)) := by
  obtain ⟨u, v, hu, hv, hut, hvt⟩ := stripMartinVectors_limit Γ s μ hpos hmass hgen hgap ξ hξ x hx
  have he : u = stripMartinRow Γ s μ hpos hmass hgen hgap ξ hξ := by
    apply supportedL2_ext_on
    intro g hg
    rw [hu g hg, stripMartinRow_apply Γ s μ hpos hmass hgen hgap ξ hξ g hg]
  have he' : v = stripMartinColumn Γ s μ hpos hmass hgen hgap ξ hξ := by
    apply supportedL2_ext_on
    intro g hg
    rw [hv g hg, stripMartinColumn_apply Γ s μ hpos hmass hgen hgap ξ hξ g hg]
  exact ⟨he ▸ hut, he' ▸ hvt⟩


-- @@ L83-86 verbatim
/-- The real compressed-inverse pairing of the actual limiting Martin vectors. -/
def stripNaimKernel (ξ η : ℝ) (hξ : ξ ≠ 0) (hη : η ≠ 0) : ℝ :=
  (inner ℂ (stripMartinRow Γ s μ hpos hmass hgen hgap ξ hξ)
    (M (stripMartinColumn Γ s μ hpos hmass hgen hgap η hη))).re


-- @@ L88-112 verbatim
/-- The complex Naïm quotients converge to the actual compressed-inverse pairing. -/
theorem stripNaimKernel_complex_tendsto {ξ η : ℝ} (hξ : ξ < 0) (hη : 0 < η)
    (x y : ℕ → Γ)
    (hx : Tendsto (fun n => ((x n • UpperHalfPlane.I : ℍ) : ℂ)) atTop (𝓝 (ξ : ℂ)))
    (hy : Tendsto (fun n => ((y n • UpperHalfPlane.I : ℍ) : ℂ)) atTop (𝓝 (η : ℂ))) :
    Tendsto (fun n => (finiteNaimQuotient s μ 1 (x n) (y n) : ℂ)) atTop
      (𝓝 (inner ℂ (stripMartinRow Γ s μ hpos hmass hgen hgap ξ hξ.ne)
        (M (stripMartinColumn Γ s μ hpos hmass hgen hgap η hη.ne')))) := by
  have hu := (stripMartinVectors_tendsto Γ s μ hpos hmass hgen hgap ξ hξ.ne x hx).1
  have hv := (stripMartinVectors_tendsto Γ s μ hpos hmass hgen hgap η hη.ne' y hy).2
  have hp := pairing_tendsto (M).toContinuousLinearMap hu hv
  have hxr : Tendsto (fun n => (x n • UpperHalfPlane.I).re) atTop (𝓝 ξ) :=
    Complex.continuous_re.continuousAt.tendsto.comp hx
  have hyr : Tendsto (fun n => (y n • UpperHalfPlane.I).re) atTop (𝓝 η) :=
    Complex.continuous_re.continuousAt.tendsto.comp hy
  have he : ∀ᶠ n in atTop,
      inner ℂ (normalizedGreenRow s μ A (x n) (walkGreen s μ (x n) 1))
        (M (normalizedGreenColumn s μ A (y n) (walkGreen s μ 1 (y n)))) =
        (finiteNaimQuotient s μ 1 (x n) (y n) : ℂ) := by
    filter_upwards [hxr.eventually (gt_mem_nhds hξ), hyr.eventually (lt_mem_nhds hη)] with n hn hm
    have h := normalizedGreen_separator_pairing s μ (fun g hg => (hpos g hg).le) hmass hgap A
      (x n) (y n) (walkGreen s μ (x n) 1) (walkGreen s μ 1 (y n))
      (finiteJumpStrip_separates Γ UpperHalfPlane.I s (x n) (y n) hn hm.le)
    simpa only [finiteNaimQuotient, Complex.ofReal_div, Complex.ofReal_mul] using h.symm
  simpa only [ContinuousLinearEquiv.coe_coe] using hp.congr' he


-- @@ L114-124 verbatim
/-- Every two sequences approaching opposite finite endpoints have the same
Naïm quotient limit. This is the full sequence, without selecting a subsequence. -/
theorem stripNaimKernel_tendsto {ξ η : ℝ} (hξ : ξ < 0) (hη : 0 < η)
    (x y : ℕ → Γ)
    (hx : Tendsto (fun n => ((x n • UpperHalfPlane.I : ℍ) : ℂ)) atTop (𝓝 (ξ : ℂ)))
    (hy : Tendsto (fun n => ((y n • UpperHalfPlane.I : ℍ) : ℂ)) atTop (𝓝 (η : ℂ))) :
    Tendsto (fun n => finiteNaimQuotient s μ 1 (x n) (y n)) atTop
      (𝓝 (stripNaimKernel Γ s μ hpos hmass hgen hgap ξ η hξ.ne hη.ne')) := by
  have ht := Complex.continuous_re.continuousAt.tendsto.comp
    (stripNaimKernel_complex_tendsto Γ s μ hpos hmass hgen hgap hξ hη x y hx hy)
  simpa only [Function.comp_def, Complex.ofReal_re, stripNaimKernel] using ht


-- @@ L126-137 verbatim
/-- The limiting compressed-inverse pairing is real and equals the named kernel. -/
theorem stripNaimKernel_pairing {ξ η : ℝ} (hξ : ξ < 0) (hη : 0 < η) :
    (stripNaimKernel Γ s μ hpos hmass hgen hgap ξ η hξ.ne hη.ne' : ℂ) =
      inner ℂ (stripMartinRow Γ s μ hpos hmass hgen hgap ξ hξ.ne)
        (M (stripMartinColumn Γ s μ hpos hmass hgen hgap η hη.ne')) := by
  have hc := stripNaimKernel_complex_tendsto Γ s μ hpos hmass hgen hgap hξ hη
    (cocompactRaySequence Γ ξ) (cocompactRaySequence Γ η)
    (cocompactRaySequence_tendsto Γ ξ) (cocompactRaySequence_tendsto Γ η)
  have hr := stripNaimKernel_tendsto Γ s μ hpos hmass hgen hgap hξ hη
    (cocompactRaySequence Γ ξ) (cocompactRaySequence Γ η)
    (cocompactRaySequence_tendsto Γ ξ) (cocompactRaySequence_tendsto Γ η)
  exact tendsto_nhds_unique (Complex.continuous_ofReal.continuousAt.tendsto.comp hr) hc


-- @@ L139-145 verbatim
/-- The local Naïm kernel is positive and has the universal Green lower bound. -/
theorem stripNaimKernel_lower {ξ η : ℝ} (hξ : ξ < 0) (hη : 0 < η) :
    (walkGreen s μ 1 1)⁻¹ ≤ stripNaimKernel Γ s μ hpos hmass hgen hgap ξ η hξ.ne hη.ne' := by
  apply ge_of_tendsto (stripNaimKernel_tendsto Γ s μ hpos hmass hgen hgap hξ hη
    (cocompactRaySequence Γ ξ) (cocompactRaySequence Γ η)
    (cocompactRaySequence_tendsto Γ ξ) (cocompactRaySequence_tendsto Γ η))
  exact Filter.Eventually.of_forall (fun n => finiteNaimQuotient_lower s μ hpos hmass hgen hgap 1 _ _)


-- @@ L147-150 verbatim
theorem stripNaimKernel_pos {ξ η : ℝ} (hξ : ξ < 0) (hη : 0 < η) :
    0 < stripNaimKernel Γ s μ hpos hmass hgen hgap ξ η hξ.ne hη.ne' :=
  (inv_pos.mpr (walkGreen_pos s μ hpos hgen hgap 1 1)).trans_le
    (stripNaimKernel_lower Γ s μ hpos hmass hgen hgap hξ hη)


-- @@ L152-152 verbatim
end Singularity
