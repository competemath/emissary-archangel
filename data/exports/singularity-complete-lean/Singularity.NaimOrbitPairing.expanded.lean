import Singularity.GeometricNaimKernel
import Singularity.OrbitGreenBoundary


-- @@ L4-11 verbatim
/-!
# The global Naïm kernel in actual strip sequence coordinates

Any enumeration of the strip transports the strong Martin vectors and the
compressed Green inverse isometrically. The exact kernel identity is retained.
Multiplication by real boundary densities yields the weighted pairing used by
the logarithmic analysis operators.
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
  {J : Type*} (e : (ℤ × J) ≃ finiteJumpStrip Γ UpperHalfPlane.I s)


-- @@ L26-28 verbatim
local notation "Km" => rayMartinPoint Γ (s.map (Function.Embedding.mk Inv.inv inv_injective))
  (fun g => μ g⁻¹) (reflected_jump_pos s μ hpos) (reflected_support_generates s hgen)
  (reflectedMarkov_spectral_gap s μ hgap)

-- @@ L29-29 verbatim
local notation "Kp" => rayMartinPoint Γ s μ hpos hgen hgap

-- @@ L30-30 verbatim
local notation "M" => orbitGreenInverse s μ (fun g hg => le_of_lt (hpos g hg)) hmass hgap e


-- @@ L32-34 verbatim
/-- Reflected Martin vector in the enumerated strip coordinates. -/
def stripOrbitMartinRow (ξ : ℝ) (hξ : ξ ≠ 0) : SequenceL2 (ℤ × J) :=
  supportedCoordinatesEquiv e (stripMartinRow Γ s μ hpos hmass hgen hgap ξ hξ)


-- @@ L36-38 verbatim
/-- Forward Martin vector in the same coordinates. -/
def stripOrbitMartinColumn (η : ℝ) (hη : η ≠ 0) : SequenceL2 (ℤ × J) :=
  supportedCoordinatesEquiv e (stripMartinColumn Γ s μ hpos hmass hgen hgap η hη)


-- @@ L40-42 verbatim
theorem stripOrbitMartinRow_apply (ξ : ℝ) (hξ : ξ ≠ 0) (p : ℤ × J) :
    stripOrbitMartinRow Γ s μ hpos hmass hgen hgap e ξ hξ p = ((Km ξ).val (e p) : ℂ) :=
  stripMartinRow_apply Γ s μ hpos hmass hgen hgap ξ hξ (e p) (e p).property


-- @@ L44-46 verbatim
theorem stripOrbitMartinColumn_apply (η : ℝ) (hη : η ≠ 0) (p : ℤ × J) :
    stripOrbitMartinColumn Γ s μ hpos hmass hgen hgap e η hη p = ((Kp η).val (e p) : ℂ) :=
  stripMartinColumn_apply Γ s μ hpos hmass hgen hgap η hη (e p) (e p).property


-- @@ L48-60 verbatim
/-- The actual strip inverse gives the exact global Naïm kernel pairing. -/
theorem geometricNaimKernel_orbit_pairing
    (horbit : (MulAction.orbit Γ (∞ : OnePoint ℝ)).Infinite)
    {ξ η : ℝ} (hξ : ξ < 0) (hη : 0 < η) :
    inner ℂ (stripOrbitMartinRow Γ s μ hpos hmass hgen hgap e ξ hξ.ne)
      (M (stripOrbitMartinColumn Γ s μ hpos hmass hgen hgap e η hη.ne')) =
    (geometricNaimKernel Γ s μ hpos hmass hgen hgap horbit
      ⟨((ξ : OnePoint ℝ), (η : OnePoint ℝ)),
        fun h => (ne_of_lt (hξ.trans hη)) (OnePoint.coe_injective h)⟩ : ℂ) := by
  rw [geometricNaimKernel_eq_strip Γ s μ hpos hmass hgen hgap horbit hξ hη]
  unfold stripOrbitMartinRow stripOrbitMartinColumn orbitGreenInverse
  rw [coordinateOperator_pairing]
  exact (stripNaimKernel_pairing Γ s μ hpos hmass hgen hgap hξ hη).symm


-- @@ L62-85 verbatim
/-- Coordinatewise density identification suffices for the weighted global
Naïm pairing; no operator factorization is assumed. -/
theorem geometricNaimKernel_weighted_orbit_pairing
    (horbit : (MulAction.orbit Γ (∞ : OnePoint ℝ)).Infinite)
    {ξ η : ℝ} (hξ : ξ < 0) (hη : 0 < η)
    (r t : ℝ) (u v : SequenceL2 (ℤ × J))
    (hu : ∀ p, u p = ((r * (Km ξ).val (e p) : ℝ) : ℂ))
    (hv : ∀ p, v p = ((t * (Kp η).val (e p) : ℝ) : ℂ)) :
    inner ℂ u (M v) =
      ((r * t * geometricNaimKernel Γ s μ hpos hmass hgen hgap horbit
        ⟨((ξ : OnePoint ℝ), (η : OnePoint ℝ)),
          fun h => (ne_of_lt (hξ.trans hη)) (OnePoint.coe_injective h)⟩ : ℝ) : ℂ) := by
  have hue : u = (r : ℂ) • stripOrbitMartinRow Γ s μ hpos hmass hgen hgap e ξ hξ.ne := by
    ext p
    simp only [hu, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      stripOrbitMartinRow_apply, Complex.ofReal_mul]
  have hve : v = (t : ℂ) • stripOrbitMartinColumn Γ s μ hpos hmass hgen hgap e η hη.ne' := by
    ext p
    simp only [hv, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      stripOrbitMartinColumn_apply, Complex.ofReal_mul]
  rw [hue, hve, _root_.map_smul, inner_smul_left, inner_smul_right,
    geometricNaimKernel_orbit_pairing Γ s μ hpos hmass hgen hgap e horbit hξ hη]
  simp only [Complex.conj_ofReal, Complex.ofReal_mul]
  ring


-- @@ L87-87 verbatim
end Singularity
