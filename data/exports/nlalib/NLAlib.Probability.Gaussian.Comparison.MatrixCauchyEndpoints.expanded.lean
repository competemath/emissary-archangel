import NLAlib.Probability.Gaussian.Comparison.CenteredMatrixLaw
import NLAlib.Probability.Gaussian.Comparison.ResamplingInterpolation
import NLAlib.Matrix.Functions.ResolventCoordinateBounds


-- @@ L5-10 verbatim
/-! # Matrix-law endpoints of the actual Cauchy interpolation

The full-coordinate interpolation endpoints are the genuine independent
matrix-sum and matching Gaussian matrix resolvent expectations. The only
support restriction is almost-everywhere Hermitian support of the laws.
-/


-- @@ L12-12 verbatim
noncomputable section

-- @@ L13-13 verbatim
set_option backward.isDefEq.respectTransparency false

-- @@ L14-14 verbatim
open MeasureTheory ProbabilityTheory

-- @@ L15-15 verbatim
namespace NLAlib

-- @@ L16-18 verbatim
variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [Fintype n] [DecidableEq n] [Nonempty n]

-- @@ L19-19 verbatim
local notation "M" => Matrix n n ℂ

-- @@ L20-20 verbatim
local notation "J" => (n × n) ⊕ (n × n)

-- @@ L21-21 verbatim
local notation "E" => J → ℝ


-- @@ L23-45 verbatim
open scoped Matrix.Norms.L2Operator in
/-- The actual time-one coordinate interpolation is the original independent
Hermitian matrix-sum resolvent expectation. -/
theorem resamplingInterpolation_one_matrix_law
    (ν : ι → Measure M) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, ∀ᵐ A ∂ν i, A.IsHermitian)
    (γ : Measure E) [IsProbabilityMeasure γ] (ζ : ℂ) (hζ : ζ.im ≠ 0) :
    resamplingInterpolation (fun i => (ν i).map matrixRealCoordinates) γ
      (hermitianCoordinateTraceResolvent ζ) 1 =
      ∫ x : ι → M, normalizedTrace (resolvent (∑ i, x i) ζ) ∂Measure.pi ν := by
  haveI (i : ι) : IsProbabilityMeasure ((ν i).map matrixRealCoordinates) :=
    (ν i).isProbabilityMeasure_map measurable_matrixRealCoordinates.aemeasurable
  have hΦ : Continuous (hermitianCoordinateTraceResolvent (n := n) ζ) :=
    continuous_iff_continuousAt.mpr (fun x =>
      (hasFDerivAt_hermitianCoordinateTraceResolvent ζ hζ x).continuousAt)
  rw [resamplingInterpolation_one _ γ _ hΦ]
  calc
    _ = ∫ x : ι → M,
        hermitianCoordinateTraceResolvent ζ (matrixRealCoordinates (∑ i, x i)) ∂Measure.pi ν :=
      ((identDistrib_resamplingTripleOriginal_matrixRealCoordinates_sum ν).comp hΦ.measurable).integral_eq
    _ = _ := integral_congr_ae ((ae_isHermitian_sum_pi ν hν).mono fun x hx => by
      dsimp only [hermitianCoordinateTraceResolvent]
      rw [hermitianMatrixFromRealCoordinates_matrixRealCoordinates hx])


-- @@ L47-89 verbatim
open scoped Matrix.Norms.L2Operator in
/-- The actual time-zero coordinate interpolation is the Gaussian matrix
resolvent expectation when the actual matrix means agree. -/
theorem resamplingInterpolation_zero_matrix_law
    (ν : ι → Measure M) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, MemLp (id : M → M) 3 (ν i))
    (ρ : Measure M) (hρ : HasGaussianLaw (matrixRealCoordinates : M → E) ρ)
    (hHerm : ∀ᵐ A ∂ρ, A.IsHermitian)
    (hmean : (∫ A : M, A ∂ρ) = ∫ x : ι → M, ∑ i, x i ∂Measure.pi ν)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) :
    resamplingInterpolation (fun i => (ν i).map matrixRealCoordinates)
      (centeredMatrixCoordinateLaw ρ) (hermitianCoordinateTraceResolvent ζ) 0 =
      ∫ A : M, normalizedTrace (resolvent A ζ) ∂ρ := by
  haveI (i : ι) : IsProbabilityMeasure ((ν i).map matrixRealCoordinates) :=
    (ν i).isProbabilityMeasure_map measurable_matrixRealCoordinates.aemeasurable
  haveI := hρ.isProbabilityMeasure
  have hγ := hasGaussianLaw_id_centeredMatrixCoordinateLaw ρ hρ
  haveI := hγ.isProbabilityMeasure
  have hΦ : Continuous (hermitianCoordinateTraceResolvent (n := n) ζ) :=
    continuous_iff_continuousAt.mpr (fun x =>
      (hasFDerivAt_hermitianCoordinateTraceResolvent ζ hζ x).continuousAt)
  let m : E := ∫ p, resamplingTripleOriginal p ∂resamplingTripleMeasure
    (fun i => (ν i).map matrixRealCoordinates)
  have hm : m = ∫ A : M, matrixRealCoordinates A ∂ρ := by
    dsimp [m]
    rw [integral_resamplingTripleOriginal_matrixRealCoordinates ν hν, ← hmean]
    exact ((matrixRealCoordinatesContinuousLinearEquiv (m := n) (n := n)).toContinuousLinearMap.integral_comp_comm
      (integrable_id_of_hasGaussianLaw_matrixRealCoordinates ρ hρ)).symm
  rw [resamplingInterpolation_zero _ _ _ hΦ]
  change (∫ z : E, hermitianCoordinateTraceResolvent ζ (m + z)
    ∂centeredMatrixCoordinateLaw ρ) = _
  have hshift : Continuous (fun z : E => hermitianCoordinateTraceResolvent ζ (m + z)) :=
    hΦ.comp (by fun_prop)
  have ht := (hasLaw_centeredMatrixCoordinates ρ).integral_comp hshift.aestronglyMeasurable
  rw [← ht]
  apply integral_congr_ae (hHerm.mono fun A hA => ?_)
  change hermitianCoordinateTraceResolvent ζ
    (m + (matrixRealCoordinates A - ∫ B : M, matrixRealCoordinates B ∂ρ)) = _
  have he : m + (matrixRealCoordinates A - ∫ B : M, matrixRealCoordinates B ∂ρ) =
      matrixRealCoordinates A := by rw [hm]; abel
  rw [he]
  dsimp only [hermitianCoordinateTraceResolvent]
  rw [hermitianMatrixFromRealCoordinates_matrixRealCoordinates hA]


-- @@ L91-91 verbatim
end NLAlib
