import OAI.Analysis.DirectCrouzeix.DomainBound


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open scoped Matrix Matrix.Norms.L2Operator Kronecker


-- @@ L9-9 verbatim
noncomputable section


-- @@ L11-11 verbatim
open MeasureTheory Set Filter Metric


-- @@ L13-13 verbatim
open scoped Topology Interval ENNReal NNReal ComplexConjugate


-- @@ L15-15 verbatim
noncomputable section


-- @@ L17-17 verbatim
open Filter Metric Set


-- @@ L19-19 verbatim
open scoped Topology ComplexConjugate


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
open Set Filter Metric


-- @@ L25-25 verbatim
open scoped Topology ComplexConjugate


-- @@ L27-27 verbatim
noncomputable section


-- @@ L29-29 verbatim
open Set Filter Metric


-- @@ L31-31 verbatim
open scoped Topology ComplexConjugate


-- @@ L33-33 verbatim
noncomputable section


-- @@ L35-35 verbatim
open Set Filter Metric


-- @@ L37-37 verbatim
open scoped Topology ComplexConjugate


-- @@ L39-39 verbatim
noncomputable section


-- @@ L41-41 verbatim
open Set Filter Metric


-- @@ L43-43 verbatim
open scoped Topology ComplexConjugate


-- @@ L45-45 verbatim
noncomputable section


-- @@ L47-47 verbatim
open Set Filter Metric


-- @@ L49-49 verbatim
open scoped Topology ComplexConjugate


-- @@ L51-51 verbatim
noncomputable section


-- @@ L53-53 verbatim
open Set


-- @@ L55-55 verbatim
open scoped ComplexConjugate Matrix


-- @@ L57-57 verbatim
namespace DirectCrouzeix


-- @@ L59-59 verbatim
open Set Metric


-- @@ L61-63 verbatim
theorem convex_numericalRange {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Convex ℝ (numericalRange A) :=
  Geometry.convex_quadratic_range (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A).toLinearMap


-- @@ L65-97 verbatim
theorem complete_crouzeix : UniversalBound 2 := by
  intro n m d hn hm A B
  let M := rangeMaximum A B
  have hM : 0 ≤ M := by
    obtain ⟨z,hz,he⟩ := rangeMaximum_attained hn A B
    rw [show M = ‖polynomialValue B z‖ from he.symm]
    exact norm_nonneg _
  apply le_of_forall_pos_le_add
  intro ε hε
  let ρ := M+ε/2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hMρ : M < ρ := by dsimp [ρ]; linarith
  let V := {z : ℂ | ‖polynomialValue B z‖ < ρ}
  have hV : IsOpen V := isOpen_lt (continuous_polynomialValue B).norm continuous_const
  have hWV : numericalRange A ⊆ V := by
    intro z hz
    exact lt_of_le_of_lt (norm_polynomialValue_le_rangeMaximum A B hz) hMρ
  obtain ⟨δ,hδ,hδV⟩ := (isCompact_numericalRange A).exists_thickening_subset_open hV hWV
  obtain ⟨D,v,b,hW,hc,hnear⟩ := Geometry.exists_exponential_outer (isCompact_numericalRange A)
    (numericalRange_nonempty hn A) (convex_numericalRange A) hδ
  have hbound : ∀ z, Geometry.expLevel v b z ≤ 1 →
      ‖matrixPolynomialValue z (coefficientPolynomial B)‖ ≤ ρ := by
    intro z hz
    rw [matrixPolynomialValue_coefficientPolynomial]
    apply le_of_lt
    apply hδV
    obtain ⟨w,hw,hzw⟩ := hnear z hz
    exact mem_thickening_iff.mpr ⟨w,hw,by simpa only [dist_eq_norm] using hzw⟩
  have hh := expLevel_domain_bound_scaled hn hm A v b hc hW (coefficientPolynomial B) hρ hbound
  rw [tensorPolynomial_coefficientPolynomial] at hh
  calc
    ‖tensorEvaluation A B‖ ≤ 2*ρ := hh
    _ = 2*rangeMaximum A B+ε := by dsimp [ρ,M]; ring


-- @@ L99-99 verbatim
end DirectCrouzeix


-- @@ L101-101 verbatim
end


-- @@ L103-103 verbatim
end


-- @@ L105-105 verbatim
end


-- @@ L107-107 verbatim
end


-- @@ L109-109 verbatim
end


-- @@ L111-111 verbatim
end


-- @@ L113-113 verbatim
end


-- @@ L115-115 verbatim
end


-- @@ L117-117 verbatim
end


-- @@ L119-119 verbatim
end OAI
