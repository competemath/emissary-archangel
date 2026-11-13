import NLAlib.Probability.Free.WordNativeDysonResolvent
import NLAlib.Matrix.Functions.CoefficientSandwichSum
import NLAlib.ForMathlib.Analysis.Normed.Algebra.DysonStability


-- @@ L5-13 verbatim
/-!
# A residual bound relative to the actual native free model

The genuine compressed free resolvent solves the coefficient Dyson equation.
Consequently an arbitrary matrix is close to that specific resolvent when
its actual polynomial residual is small and the native norms contract.
This derives the endpoint estimate from the concrete model without an
assumed Dyson solution or approximation certificate.
-/


-- @@ L15-15 verbatim
noncomputable section

-- @@ L16-16 verbatim
set_option autoImplicit false

-- @@ L17-17 verbatim
set_option backward.isDefEq.respectTransparency false

-- @@ L18-18 verbatim
open scoped Classical

-- @@ L19-19 verbatim
namespace NLAlib

-- @@ L20-20 verbatim
variable {D ι : Type*} [Fintype D] [DecidableEq D] [Fintype ι]

-- @@ L21-21 verbatim
local notation "M" => Matrix D D ℂ


-- @@ L23-49 verbatim
open scoped Matrix.Norms.L2Operator in
/-- The spectral distance to the actual compressed free resolvent is controlled
by the literal coefficient Dyson residual under the native contraction bound.
This is an endpoint prerequisite for arXiv:2108.06312v2, Theorem 6.2.
atlas: gaussian-free-spectrum-two-sided (partial). -/
theorem specNorm_sub_wordNativeDysonResolvent_le_residual
    {A₀ : M} (hA₀ : A₀.IsHermitian)
    {A : ι → M} (hA : ∀ i, (A i).IsHermitian)
    {z : ℂ} (hz : z.im≠0) (y : M)
    (hc : ((Fintype.card D : ℝ)*|z.im|⁻¹)*‖coefficientSandwichSum A‖*specNorm y≤1/2) :
    specNorm (y-wordNativeDysonResolvent A₀ A z)≤
      2*((Fintype.card D : ℝ)*|z.im|⁻¹)*
        specNorm ((z•(1 : M)-A₀-coefficientSandwichSum A y)*y-1) := by
  have hm : wordNativeDysonResolvent A₀ A z*
      (z•(1 : M)-A₀-coefficientSandwichSum A (wordNativeDysonResolvent A₀ A z))=1 := by
    rw [coefficientSandwichSum_apply_of_isHermitian A hA]
    exact mul_eq_one_comm.mp (wordNativeDysonResolvent_dyson hA₀ hA hz)
  have hn := specNorm_wordNativeDysonResolvent_le hA₀ hA hz
  have hh : ‖wordNativeDysonResolvent A₀ A z‖*‖coefficientSandwichSum A‖*‖y‖≤1/2 := by
    calc
      _ ≤ ((Fintype.card D : ℝ)*|z.im|⁻¹)*‖coefficientSandwichSum A‖*‖y‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hn (norm_nonneg _)) (norm_nonneg _)
      _ ≤ _ := hc
  exact (norm_sub_le_two_mul_norm_mul_norm_dyson_residual
    (coefficientSandwichSum A) A₀ (z•(1 : M)) _ y hm hh).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by norm_num)) (norm_nonneg _))


-- @@ L51-51 verbatim
end NLAlib
