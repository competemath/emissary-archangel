import Singularity.HittingOrbitColumns
import Singularity.NaimOrbitPairing
import Singularity.RealCurrentChart
import Singularity.KernelFactorization
import Singularity.GeometricKernelCurrent


-- @@ L7-13 verbatim
/-!
# The actual logarithmic hitting-density pairing

The analysis columns are identified with real scalar multiples of the strip
Martin vectors. Their pairing through the actual compressed Green inverse is
therefore exactly the real Naïm-current density with the exponential Jacobian.
-/


-- @@ L15-15 verbatim
noncomputable section

-- @@ L16-16 verbatim
open MeasureTheory Filter Set OnePoint

-- @@ L17-17 verbatim
open scoped Classical Topology MatrixGroups UpperHalfPlane ENNReal

-- @@ L18-18 verbatim
namespace Singularity


-- @@ L20-35 verbatim
variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] [Countable Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (horbit : (MulAction.orbit Γ (∞ : OnePoint ℝ)).Infinite) (z : ℍ)
  {J : Type*} [Fintype J] {τ : ℝ} (hτ : 0 < τ)
  (a : Γ) (ha : (a : SL(2, ℝ)) = dilationMatrix τ) (b : J → Γ)
  (e : (ℤ × J) ≃ finiteJumpStrip Γ UpperHalfPlane.I s)
  (he : ∀ p : ℤ × J, (e p : Γ) = a ^ p.1 * b p.2)
  (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
  (hb : reflectedGeometricHittingMeasure Γ s μ hpos hmass hgen hgap z ≤
    ENNReal.ofReal B • compactPoissonMeasure UpperHalfPlane.I)
  (hd : geometricHittingMeasure Γ s μ hpos hmass hgen hgap z ≤
    ENNReal.ofReal D • compactPoissonMeasure UpperHalfPlane.I)


-- @@ L37-37 verbatim
local notation "νm" => reflectedGeometricHittingMeasure Γ s μ hpos hmass hgen hgap z

-- @@ L38-38 verbatim
local notation "νp" => geometricHittingMeasure Γ s μ hpos hmass hgen hgap z

-- @@ L39-39 verbatim
local notation "Θ" => geometricNaimKernel Γ s μ hpos hmass hgen hgap horbit

-- @@ L40-43 verbatim
local notation "Hm" => geometricHittingDensityFamily Γ (s.map (Function.Embedding.mk Inv.inv inv_injective))
  (fun g => μ g⁻¹) (reflected_jump_pos s μ hpos) (Eq.trans (reflected_jump_mass s μ) hmass)
  (reflected_support_generates s hgen) (reflectedMarkov_spectral_gap s μ hgap) z
  (-1) (Or.inr rfl) hτ B hB hb b

-- @@ L44-45 verbatim
local notation "Hp" => geometricHittingDensityFamily Γ s μ hpos hmass hgen hgap z
  1 (Or.inl rfl) hτ D hD hd b

-- @@ L46-46 verbatim
local notation "M" => orbitGreenInverse s μ (fun g hg => le_of_lt (hpos g hg)) hmass hgap e


-- @@ L48-91 verbatim
include ha he in
/-- The scalar pairing identity needed by Fourier factorization, now derived
from the actual hitting measures and actual strip Green inverse. -/
theorem geometricHittingDensityFamily_pairing
    (q r : ℝ → ℝ) (hq : Measurable q) (hr : Measurable r)
    (hpq : ∀ u, 0 ≤ q u) (hpr : ∀ u, 0 ≤ r u)
    (hqm : volume.withDensity (fun u => ENNReal.ofReal (q u)) = finiteBoundaryMeasure νm)
    (hrm : volume.withDensity (fun u => ENNReal.ofReal (r u)) = finiteBoundaryMeasure νp) :
    ∀ᵐ t : ℝ × ℝ ∂volume.prod volume,
      densityPairingKernel Hm Hp M t.1 t.2 =
        ((Real.exp t.1 * Real.exp t.2 * realBoundaryCurrentDensity q r Θ (logBoundaryPair t) : ℝ) : ℂ) := by
  have hm := geometricHittingDensityFamily_column_ae Γ (s.map ⟨Inv.inv, inv_injective⟩)
    (fun g => μ g⁻¹) (reflected_jump_pos s μ hpos) (Eq.trans (reflected_jump_mass s μ) hmass)
    (reflected_support_generates s hgen) (reflectedMarkov_spectral_gap s μ hgap) z
    (-1) (Or.inr rfl) hτ B hB hb b horbit a ha q hq hpq hqm
  have hp := geometricHittingDensityFamily_column_ae Γ s μ hpos hmass hgen hgap z
    1 (Or.inl rfl) hτ D hD hd b horbit a ha r hr hpr hrm
  have hm' : ∀ᵐ t : ℝ × ℝ ∂volume.prod volume, ∀ p : ℤ × J,
      (Hm).column t.1 p = ((Real.exp t.1 * q (-Real.exp t.1) *
        (rayMartinPoint Γ (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹)
          (reflected_jump_pos s μ hpos) (reflected_support_generates s hgen)
          (reflectedMarkov_spectral_gap s μ hgap) (-Real.exp t.1)).val (e p) : ℝ) : ℂ) := by
    simpa only [neg_one_mul, he] using Measure.quasiMeasurePreserving_fst.ae hm
  have hp' : ∀ᵐ t : ℝ × ℝ ∂volume.prod volume, ∀ p : ℤ × J,
      (Hp).column t.2 p = ((Real.exp t.2 * r (Real.exp t.2) *
        (rayMartinPoint Γ s μ hpos hgen hgap (Real.exp t.2)).val (e p) : ℝ) : ℂ) := by
    simpa only [one_mul, he] using Measure.quasiMeasurePreserving_snd.ae hp
  filter_upwards [hm', hp'] with t hmt hpt
  have hξ : -Real.exp t.1 < 0 := neg_neg_of_pos (Real.exp_pos _)
  have hη : 0 < Real.exp t.2 := Real.exp_pos _
  let p : BoundaryPair := ⟨(((-Real.exp t.1 : ℝ) : OnePoint ℝ), ((Real.exp t.2 : ℝ) : OnePoint ℝ)),
    fun h => (ne_of_lt (hξ.trans hη)) (OnePoint.coe_injective h)⟩
  have hpair := geometricNaimKernel_weighted_orbit_pairing Γ s μ hpos hmass hgen hgap e horbit hξ hη
    (Real.exp t.1 * q (-Real.exp t.1)) (Real.exp t.2 * r (Real.exp t.2))
    ((Hm).column t.1) ((Hp).column t.2) hmt hpt
  change inner ℂ ((Hm).column t.1) (M ((Hp).column t.2)) = _
  rw [hpair]
  have hext : extendBoundaryPairKernel Θ (realBoundaryPairChart (logBoundaryPair t)) = Θ p :=
    extendBoundaryPairKernel_apply Θ p
  simp only [realBoundaryCurrentDensity]
  rw [hext]
  congr 1
  dsimp only [logBoundaryPair, p]
  ring


-- @@ L93-93 verbatim
end Singularity
