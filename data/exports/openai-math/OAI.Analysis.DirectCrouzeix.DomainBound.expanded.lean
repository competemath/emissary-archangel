import OAI.Analysis.DirectCrouzeix.OuterApproximation


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u_144 u_145


-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
open scoped Matrix Matrix.Norms.L2Operator Kronecker


-- @@ L11-11 verbatim
noncomputable section


-- @@ L13-13 verbatim
open MeasureTheory Set Filter Metric


-- @@ L15-15 verbatim
open scoped Topology Interval ENNReal NNReal ComplexConjugate


-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
open Filter Metric Set


-- @@ L21-21 verbatim
open scoped Topology ComplexConjugate


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
open Set Filter Metric


-- @@ L27-27 verbatim
open scoped Topology ComplexConjugate


-- @@ L29-29 verbatim
noncomputable section


-- @@ L31-31 verbatim
open Set Filter Metric


-- @@ L33-33 verbatim
open scoped Topology ComplexConjugate


-- @@ L35-35 verbatim
noncomputable section


-- @@ L37-37 verbatim
open Set Filter Metric


-- @@ L39-39 verbatim
open scoped Topology ComplexConjugate


-- @@ L41-41 verbatim
noncomputable section


-- @@ L43-43 verbatim
open Set Filter Metric


-- @@ L45-45 verbatim
open scoped Topology ComplexConjugate


-- @@ L47-47 verbatim
noncomputable section


-- @@ L49-49 verbatim
open Set Filter Metric


-- @@ L51-51 verbatim
open scoped Topology ComplexConjugate


-- @@ L53-53 verbatim
noncomputable section


-- @@ L55-55 verbatim
open Set


-- @@ L57-57 verbatim
open scoped ComplexConjugate Matrix


-- @@ L59-59 verbatim
namespace DirectCrouzeix


-- @@ L61-61 verbatim
open Set Filter Metric


-- @@ L63-97 verbatim
theorem expLevel_domain_bound {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (A : Matrix (Fin n) (Fin n) ℂ) {ι : Type u_144} [Fintype ι]
    (v : ι → ℂ) (b : ι → ℝ) (hc : IsCompact {z | Geometry.expLevel v b z ≤ 1})
    (hW : ∀ z ∈ numericalRange A, Geometry.expLevel v b z < 1)
    (F : MatrixPolynomial m)
    (hF : ∀ z, Geometry.expLevel v b z ≤ 1 → ‖matrixPolynomialValue z F‖ ≤ 1) :
    ‖tensorPolynomial A F‖ ≤ 2 := by
  obtain ⟨a,ha⟩ := numericalRange_nonempty hn A
  obtain ⟨R,hR,c,g,hc0,hg,hinj,hder,hcircle,hout⟩ :=
    Geometry.exists_expLevel_exterior v b hc (hW a ha)
  have hge (ζ : ℂ) (hζ : 1 ≤ ‖ζ‖) : 1 ≤ Geometry.expLevel v b (Faber.exterior c g ζ) := by
    rcases eq_or_lt_of_le hζ with he|hl
    · exact le_of_eq (hcircle ζ he.symm).symm
    · exact le_of_lt (hout ζ hl)
  have hs (t : Faber.Angle) (w : ℂ) (hw : Geometry.expLevel v b w ≤ 1) :
      0 ≤ (conj (Faber.boundaryNormal c g t)*(Faber.boundary c g t-w)).re := by
    have hdt := Faber.hasDerivAt_exterior hg c (Faber.unitPoint_ne_zero t) (Faber.unitPoint_inv_mem hR t)
    have hh := Geometry.expLevel_holomorphic_support v b (hW a ha) (Faber.unitPoint_norm t)
      hdt.differentiableAt.hasDerivAt (hder _ (Faber.unitPoint_ne_zero t) (Faber.unitPoint_inv_mem hR t)) hcircle hge hw
    have he : Faber.unitPoint t*deriv (Faber.exterior c g) (Faber.unitPoint t) = Faber.boundaryNormal c g t := by
      rw [hdt.deriv]; rfl
    rw [he,real_inner_eq_re_inner ℂ,RCLike.inner_apply] at hh
    change 0 ≤ ((Faber.exterior c g (Faber.unitPoint t)-w)*conj (Faber.boundaryNormal c g t)).re at hh
    simpa only [Faber.boundary,mul_comm] using hh
  apply exterior_collar_bound hn hm A hR hg hc0 hinj hder
  · intro t s
    exact hs t _ (le_of_eq (hcircle _ (Faber.unitPoint_norm s)))
  · intro ζ hζ hz
    have h1 := hge ζ hζ
    have h2 := hW _ hz
    linarith
  · intro t w hw
    exact hs t w (le_of_lt (hW w hw))
  · intro t
    exact hF _ (le_of_eq (hcircle _ (Faber.unitPoint_norm t)))


-- @@ L99-113 verbatim
theorem expLevel_domain_bound_scaled {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (A : Matrix (Fin n) (Fin n) ℂ) {ι : Type u_145} [Fintype ι]
    (v : ι → ℂ) (b : ι → ℝ) (hc : IsCompact {z | Geometry.expLevel v b z ≤ 1})
    (hW : ∀ z ∈ numericalRange A, Geometry.expLevel v b z < 1)
    (F : MatrixPolynomial m) {ρ : ℝ} (hρ : 0 < ρ)
    (hF : ∀ z, Geometry.expLevel v b z ≤ 1 → ‖matrixPolynomialValue z F‖ ≤ ρ) :
    ‖tensorPolynomial A F‖ ≤ 2*ρ := by
  have hb := expLevel_domain_bound hn hm A v b hc hW (((ρ⁻¹:ℝ):ℂ) • F) (by
    intro z hz
    rw [matrixPolynomialValue_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hρ)]
    exact (mul_le_mul_of_nonneg_left (hF z hz) (le_of_lt (inv_pos.mpr hρ))).trans_eq (inv_mul_cancel₀ (ne_of_gt hρ)))
  rw [tensorPolynomial_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hρ)] at hb
  have hh := mul_le_mul_of_nonneg_left hb (le_of_lt hρ)
  rw [← mul_assoc,mul_inv_cancel₀ (ne_of_gt hρ),one_mul] at hh
  simpa only [mul_comm] using hh


-- @@ L115-115 verbatim
end DirectCrouzeix


-- @@ L117-117 verbatim
namespace DirectCrouzeix


-- @@ L119-119 verbatim
open Set Metric


-- @@ L121-121 verbatim
end DirectCrouzeix


-- @@ L123-123 verbatim
end


-- @@ L125-125 verbatim
end


-- @@ L127-127 verbatim
end


-- @@ L129-129 verbatim
end


-- @@ L131-131 verbatim
end


-- @@ L133-133 verbatim
end


-- @@ L135-135 verbatim
end


-- @@ L137-137 verbatim
end


-- @@ L139-139 verbatim
end


-- @@ L141-141 verbatim
end OAI
