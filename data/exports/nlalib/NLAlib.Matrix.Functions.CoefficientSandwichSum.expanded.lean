import NLAlib.Matrix.Structured.CoefficientBlock
import Mathlib.Analysis.Normed.Operator.Mul


-- @@ L4-10 verbatim
/-!
# The native coefficient sandwich map

Finite coefficient matrices define the actual continuous positive map
`x ↦ ∑ i, A i * x * (A i)ᴴ` for Euclidean operator norm. For Hermitian
coefficients this is precisely the covariance map in the Dyson equation.
-/


-- @@ L12-12 verbatim
noncomputable section

-- @@ L13-13 verbatim
set_option autoImplicit false

-- @@ L14-14 verbatim
open scoped Classical Matrix

-- @@ L15-15 verbatim
namespace NLAlib

-- @@ L16-16 verbatim
variable {D ι : Type*} [Fintype D] [DecidableEq D] [Fintype ι]

-- @@ L17-17 verbatim
local notation "M" => Matrix D D ℂ


-- @@ L19-22 verbatim
open scoped Matrix.Norms.L2Operator in
/-- The actual continuous coefficient sandwich map, using native matrix operator norms. -/
def coefficientSandwichSum (A : ι → M) : M →L[ℂ] M :=
  ∑ i, ContinuousLinearMap.mulLeftRight ℂ M (A i) (A i)ᴴ


-- @@ L24-28 verbatim
open scoped Matrix.Norms.L2Operator in
/-- Evaluating the map gives its literal finite coefficient sandwich sum. -/
theorem coefficientSandwichSum_apply (A : ι → M) (x : M) :
    coefficientSandwichSum A x=∑ i, A i*x*(A i)ᴴ := by
  simp [coefficientSandwichSum]


-- @@ L30-38 verbatim
open scoped Matrix.Norms.L2Operator in
/-- The spectral-to-spectral map norm is bounded by the sum of squared coefficient spectral norms. -/
theorem norm_coefficientSandwichSum_le (A : ι → M) :
    ‖coefficientSandwichSum A‖≤∑ i, specNorm (A i)^2 := by
  calc
    _ ≤ ∑ i, ‖ContinuousLinearMap.mulLeftRight ℂ M (A i) (A i)ᴴ‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖A i‖*‖(A i)ᴴ‖ := Finset.sum_le_sum fun i _ =>
      ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le ℂ M _ _
    _ = _ := by simp only [Matrix.l2_opNorm_conjTranspose, pow_two]; rfl


-- @@ L40-46 verbatim
open scoped Matrix.Norms.L2Operator in
/-- Hermitian coefficients give the precise unstarred covariance map in the Dyson equation. -/
theorem coefficientSandwichSum_apply_of_isHermitian
    (A : ι → M) (hA : ∀ i, (A i).IsHermitian) (x : M) :
    coefficientSandwichSum A x=∑ i, A i*x*A i := by
  rw [coefficientSandwichSum_apply]
  simp only [fun i => (hA i).eq]


-- @@ L48-54 verbatim
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder in
/-- The native coefficient sandwich map preserves positive semidefinite matrices. -/
theorem coefficientSandwichSum_nonneg (A : ι → M) {x : M} (hx : 0≤x) :
    0≤coefficientSandwichSum A x := by
  rw [coefficientSandwichSum_apply]
  exact Finset.sum_nonneg fun i _ =>
    ((Matrix.nonneg_iff_posSemidef.mp hx).mul_mul_conjTranspose_same (A i)).nonneg


-- @@ L56-56 verbatim
end NLAlib
