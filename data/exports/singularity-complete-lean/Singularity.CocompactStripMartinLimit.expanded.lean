import Singularity.CocompactBoundaryLimit
import Singularity.CocompactGreenComparison


-- @@ L4-11 verbatim
/-!
# Full strip-pairing limits with the actual Martin coordinates

The geometric Martin convergence discharges the pointwise-coordinate hypotheses
of the dominated separator argument. Both ray times may tend independently to
infinity. Visual bounds can now supply its Green comparison hypothesis.
This is a ray-limit result; it does not construct a global continuous Naïm kernel.
-/


-- @@ L13-13 verbatim
noncomputable section

-- @@ L14-14 verbatim
open MeasureTheory Filter Set OnePoint

-- @@ L15-15 verbatim
open scoped Classical Topology MatrixGroups UpperHalfPlane

-- @@ L16-16 verbatim
namespace Singularity


-- @@ L18-24 verbatim
variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] [Countable Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (a : Γ) {τ : ℝ} (ha : (a : SL(2, ℝ)) = dilationMatrix τ) (hτ : 0 < τ)


-- @@ L26-27 verbatim
local notation "Rep" => stripRepresentatives Γ UpperHalfPlane.I
  (jumpStripRadius (finiteJumpLengthBound Γ UpperHalfPlane.I s)) τ

-- @@ L28-29 verbatim
local notation "E" => stripOrbitEquiv Γ a ha hτ UpperHalfPlane.I
  (jumpStripRadius (finiteJumpLengthBound Γ UpperHalfPlane.I s))

-- @@ L30-31 verbatim
local notation "Km" => rayMartinPoint Γ (s.map (Function.Embedding.mk Inv.inv inv_injective)) (fun g => μ g⁻¹)
  (reflected_jump_pos s μ hpos) (reflected_support_generates s hgen) (reflectedMarkov_spectral_gap s μ hgap)

-- @@ L32-32 verbatim
local notation "Kp" => rayMartinPoint Γ s μ hpos hgen hgap


-- @@ L34-71 verbatim
/-- Full strong row/column convergence and the normalized Green pairing limit,
with the actual forward/reflected Martin coordinates and independently diverging ray times. -/
theorem cocompactStrip_martin_limit {ι : Type*} {l : Filter ι} [l.NeBot]
    {C : ℝ} (hC : 0 < C) (hcmp : GreenDistanceComparison Γ s μ C)
    {ξ η : ℝ} (hξ : ξ < 0) (hη : 0 < η)
    (m n : ι → ℕ) (hm : Tendsto m l atTop) (hn : Tendsto n l atTop) :
    ∃ u v : SequenceL2 (ℤ × Rep),
      (∀ p, u p = ((Km ξ).val (a ^ p.1 * (p.2 : Γ)) : ℂ)) ∧
      (∀ p, v p = ((Kp η).val (a ^ p.1 * (p.2 : Γ)) : ℂ)) ∧
      Tendsto (fun k => orbitGreenRow s μ E (cocompactRaySequence Γ ξ (m k))
        (walkGreen s μ (cocompactRaySequence Γ ξ (m k)) 1)) l (𝓝 u) ∧
      Tendsto (fun k => orbitGreenColumn s μ E (cocompactRaySequence Γ η (n k))
        (walkGreen s μ 1 (cocompactRaySequence Γ η (n k)))) l (𝓝 v) ∧
      Tendsto (fun k => (walkGreen s μ (cocompactRaySequence Γ ξ (m k)) (cocompactRaySequence Γ η (n k)) : ℂ) /
        ((walkGreen s μ (cocompactRaySequence Γ ξ (m k)) 1 : ℂ) *
          (walkGreen s μ 1 (cocompactRaySequence Γ η (n k)) : ℂ))) l
        (𝓝 (inner ℂ u (orbitGreenInverse s μ (fun g hg => (hpos g hg).le) hmass hgap E v))) := by
  apply geometricStrip_boundary_limit Γ s μ (fun g hg => (hpos g hg).le) hmass hgap a ha hτ hC hcmp
    (fun k => cocompactRaySequence Γ ξ (m k)) (fun k => cocompactRaySequence Γ η (n k))
    (fun k => (m k : ℝ)) (fun k => (n k : ℝ)) hξ.ne hη.ne'
    (cocompactOrbitRadius Γ) (cocompactOrbitRadius Γ)
    (fun k => Nat.cast_nonneg _) (fun k => Nat.cast_nonneg _)
    (fun k => cocompactRaySequence_bound Γ ξ (m k)) (fun k => cocompactRaySequence_bound Γ η (n k))
  · have hs := cocompactRaySequence_eventually_opposite Γ hξ hη
    filter_upwards [hm.eventually hs, hn.eventually hs] with k hk hk'
    exact ⟨hk.1, hk'.2⟩
  · intro p
    have ht := (rayMartinPoint_tendsto Γ (s.map (Function.Embedding.mk Inv.inv inv_injective)) (fun g => μ g⁻¹)
      (reflected_jump_pos s μ hpos) ((reflected_jump_mass s μ).trans hmass)
      (reflected_support_generates s hgen) (reflectedMarkov_spectral_gap s μ hgap)
      ξ (a ^ p.1 * (p.2 : Γ))).comp hm
    have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp ht
    simpa only [Function.comp_def, martinQuotient, reflected_walkGreen s μ hgap,
      Complex.ofReal_div] using hc
  · intro p
    have ht := (rayMartinPoint_tendsto Γ s μ hpos hmass hgen hgap η (a ^ p.1 * (p.2 : Γ))).comp hn
    have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp ht
    simpa only [Function.comp_def, martinQuotient, Complex.ofReal_div] using hc


-- @@ L73-98 verbatim
/-- Two-sided visual bounds for the actual forward hitting measure suffice
for the full dominated strip-pairing limit; no coordinate-limit or separate
Green comparison hypothesis remains. -/
theorem cocompactStrip_martin_limit_of_visual_bounds
    (horbit : (MulAction.orbit Γ (∞ : OnePoint ℝ)).Infinite) (z : ℍ)
    (b d : ℝ) (hb : 0 < b) (hd : 0 < d)
    (hlow : ENNReal.ofReal b • compactPoissonMeasure UpperHalfPlane.I ≤
      geometricHittingMeasure Γ s μ hpos hmass hgen hgap z)
    (hupp : geometricHittingMeasure Γ s μ hpos hmass hgen hgap z ≤
      ENNReal.ofReal d • compactPoissonMeasure UpperHalfPlane.I)
    {ξ η : ℝ} (hξ : ξ < 0) (hη : 0 < η) :
    ∃ u v : SequenceL2 (ℤ × Rep),
      (∀ p, u p = ((Km ξ).val (a ^ p.1 * (p.2 : Γ)) : ℂ)) ∧
      (∀ p, v p = ((Kp η).val (a ^ p.1 * (p.2 : Γ)) : ℂ)) ∧
      Tendsto (fun n => orbitGreenRow s μ E (cocompactRaySequence Γ ξ n)
        (walkGreen s μ (cocompactRaySequence Γ ξ n) 1)) atTop (𝓝 u) ∧
      Tendsto (fun n => orbitGreenColumn s μ E (cocompactRaySequence Γ η n)
        (walkGreen s μ 1 (cocompactRaySequence Γ η n))) atTop (𝓝 v) ∧
      Tendsto (fun n => (walkGreen s μ (cocompactRaySequence Γ ξ n) (cocompactRaySequence Γ η n) : ℂ) /
        ((walkGreen s μ (cocompactRaySequence Γ ξ n) 1 : ℂ) *
          (walkGreen s μ 1 (cocompactRaySequence Γ η n) : ℂ))) atTop
        (𝓝 (inner ℂ u (orbitGreenInverse s μ (fun g hg => (hpos g hg).le) hmass hgap E v))) := by
  obtain ⟨C, hC, hcmp, _⟩ := geometricHittingMeasure_GreenDistanceComparison Γ s μ hpos hmass hgen hgap
    horbit z b d hb hd hlow hupp
  exact cocompactStrip_martin_limit Γ s μ hpos hmass hgen hgap a ha hτ
    (lt_of_lt_of_le zero_lt_one hC) hcmp hξ hη id id tendsto_id tendsto_id


-- @@ L100-100 verbatim
end Singularity
