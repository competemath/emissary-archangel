import NLAlib.Matrix.Basic.RealCoordinates
import Mathlib.Algebra.Star.Module
import Mathlib.LinearAlgebra.Matrix.Hermitian


-- @@ L5-12 verbatim
/-!
# Hermitian reconstruction from full real coordinates

The inverse real-coordinate map followed by the native self-adjoint-part
projection is globally defined and linear over the reals. It reconstructs
every Hermitian matrix exactly, while arbitrary real inputs stay Hermitian.
This permits globally bounded resolvent test functions in Gaussian calculus.
-/


-- @@ L14-14 verbatim
noncomputable section

-- @@ L15-15 verbatim
open scoped Matrix Matrix.Norms.L2Operator

-- @@ L16-16 verbatim
namespace NLAlib

-- @@ L17-17 verbatim
variable {n : Type*} [Fintype n] [DecidableEq n]

-- @@ L18-18 verbatim
local notation "M" => Matrix n n ℂ

-- @@ L19-19 verbatim
local notation "J" => (n×n) ⊕ (n×n)


-- @@ L21-25 verbatim
/-- Reconstruct a complex matrix from real entry coordinates and retain its
native self-adjoint part, as a continuous real linear map. -/
def hermitianMatrixFromRealCoordinates : (J → ℝ) →L[ℝ] M :=
  ((selfAdjoint.submodule ℝ M).subtype.comp
    ((selfAdjointPart ℝ).comp matrixRealCoordinates.symm.toLinearMap)).toContinuousLinearMap


-- @@ L27-33 verbatim
/-- Every real coordinate vector reconstructs to a Hermitian matrix. -/
theorem isHermitian_hermitianMatrixFromRealCoordinates (x : J → ℝ) :
    (hermitianMatrixFromRealCoordinates x).IsHermitian := by
  change ((selfAdjointPart ℝ (matrixRealCoordinates.symm x) : selfAdjoint M) : M).IsHermitian
  have h : IsSelfAdjoint ((selfAdjointPart ℝ (matrixRealCoordinates.symm x) : selfAdjoint M) : M) :=
    (selfAdjointPart ℝ (matrixRealCoordinates.symm x)).property
  exact h.isHermitian


-- @@ L35-41 verbatim
/-- Full real coordinates reconstruct any Hermitian matrix exactly. -/
theorem hermitianMatrixFromRealCoordinates_matrixRealCoordinates
    {A : M} (hA : A.IsHermitian) :
    hermitianMatrixFromRealCoordinates (matrixRealCoordinates A) = A := by
  change (selfAdjointPart ℝ (matrixRealCoordinates.symm (matrixRealCoordinates A)) : M) = A
  rw [LinearEquiv.symm_apply_apply]
  exact hA.isSelfAdjoint.coe_selfAdjointPart_apply ℝ


-- @@ L43-56 verbatim
/-- A Hermitian matrix is the finite sum of its actual real entry coordinates
against the corresponding Hermitian reconstruction directions. -/
theorem sum_matrixRealCoordinates_smul_hermitianMatrixFromRealCoordinates
    {A : M} (hA : A.IsHermitian) :
    (∑ j : J, matrixRealCoordinates A j •
      hermitianMatrixFromRealCoordinates (Pi.single j 1)) = A := by
  simp_rw [← map_smul]
  rw [← map_sum]
  have he : (∑ j : J, matrixRealCoordinates A j • Pi.single j (1 : ℝ)) =
      matrixRealCoordinates A := by
    ext k
    simp [Pi.single_apply]
  rw [he]
  exact hermitianMatrixFromRealCoordinates_matrixRealCoordinates hA


-- @@ L58-58 verbatim
end NLAlib
