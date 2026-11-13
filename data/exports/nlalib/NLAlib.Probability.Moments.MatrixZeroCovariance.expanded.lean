import NLAlib.Matrix.Basic.RealCoordinates
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap


-- @@ L6-13 verbatim
/-! # Matrix laws with zero coordinate covariance

Square-integrable full real and imaginary coordinates with zero diagonal
covariances force an actual matrix law to be the Dirac law at its mean.
No Gaussian, Hermitian, invertibility or positive-dimension hypothesis is
needed. This supplies the honest empty-family endpoint for the atlas result
`matrix-resolvent-gaussian-universality`.
-/


-- @@ L15-15 verbatim
noncomputable section

-- @@ L16-16 verbatim
set_option autoImplicit false

-- @@ L17-17 verbatim
open MeasureTheory ProbabilityTheory

-- @@ L18-18 verbatim
namespace NLAlib

-- @@ L19-19 verbatim
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

-- @@ L20-20 verbatim
local notation "M" => Matrix m n ℂ

-- @@ L21-21 verbatim
local notation "J" => (m × n) ⊕ (m × n)

-- @@ L22-22 verbatim
local notation "E" => J → ℝ


-- @@ L24-52 verbatim
open scoped Matrix.Norms.L2Operator in
/-- A square-integrable matrix law with zero diagonal full-coordinate
covariances is almost surely equal to its specified actual matrix mean.
Empty row or column index types are included. -/
theorem ae_eq_of_matrix_mean_eq_of_zero_coordinate_covariance
    (ρ : Measure M) [IsProbabilityMeasure ρ]
    (hL2 : MemLp (matrixRealCoordinates : M → E) 2 ρ)
    (A₀ : M) (hmean : (∫ A : M, A ∂ρ) = A₀)
    (hcov : ∀ j : J, cov[(fun A : M => matrixRealCoordinates A j),
      (fun A : M => matrixRealCoordinates A j); ρ] = 0) :
    ∀ᵐ A ∂ρ, A = A₀ := by
  have hm : (∫ A : M, matrixRealCoordinates A ∂ρ) = matrixRealCoordinates A₀ := by
    have h := (matrixRealCoordinatesContinuousLinearEquiv (m := m) (n := n)).integral_comp_comm
      (μ := ρ) (fun A : M => A)
    change (∫ A : M, matrixRealCoordinates A ∂ρ) =
      matrixRealCoordinates (∫ A : M, A ∂ρ) at h
    exact h.trans (congrArg matrixRealCoordinates hmean)
  have hcoords (j : J) : ∀ᵐ A ∂ρ, matrixRealCoordinates A j = matrixRealCoordinates A₀ j := by
    let P : E →L[ℝ] ℝ := ContinuousLinearMap.proj j
    have hj : MemLp (fun A : M => matrixRealCoordinates A j) 2 ρ := P.comp_memLp' hL2
    have hvar : Var[(fun A : M => matrixRealCoordinates A j); ρ] = 0 :=
      (covariance_self hj.aemeasurable).symm.trans (hcov j)
    have hmj := P.integral_comp_comm (hL2.integrable one_le_two)
    change (∫ A : M, matrixRealCoordinates A j ∂ρ) =
      (∫ A : M, matrixRealCoordinates A ∂ρ) j at hmj
    rw [hm] at hmj
    exact (ae_eq_integral_of_variance_eq_zero hj hvar).mono fun A hA => hA.trans hmj
  filter_upwards [ae_all_iff.mpr hcoords] with A hA
  exact (matrixRealCoordinates : M ≃ₗ[ℝ] E).injective (funext hA)


-- @@ L54-69 verbatim
open scoped Matrix.Norms.L2Operator in
/-- A square-integrable matrix probability law with zero diagonal full-coordinate
covariances is exactly the Dirac law at its actual matrix mean. This applies
in particular to singular Gaussian coordinate laws with zero covariance. -/
theorem eq_dirac_of_matrix_mean_eq_of_zero_coordinate_covariance
    (ρ : Measure M) [IsProbabilityMeasure ρ]
    (hL2 : MemLp (matrixRealCoordinates : M → E) 2 ρ)
    (A₀ : M) (hmean : (∫ A : M, A ∂ρ) = A₀)
    (hcov : ∀ j : J, cov[(fun A : M => matrixRealCoordinates A j),
      (fun A : M => matrixRealCoordinates A j); ρ] = 0) :
    ρ = Measure.dirac A₀ := by
  have hAE := ae_eq_of_matrix_mean_eq_of_zero_coordinate_covariance ρ hL2 A₀ hmean hcov
  calc
    ρ = ρ.map id := (Measure.map_id).symm
    _ = ρ.map (fun _ : M => A₀) := Measure.map_congr hAE
    _ = Measure.dirac A₀ := by simp only [Measure.map_const, measure_univ, one_smul]


-- @@ L71-71 verbatim
end NLAlib
