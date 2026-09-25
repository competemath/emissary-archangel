module
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.AdditionTheorem.ZonalPolynomial24
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.Kernel


-- @@ L5-16 verbatim
/-!
# Gegenbauer recurrence for the harmonic zonal kernel (dimension 24)

This file completes the addition-theorem bridge: the zonal polynomial `harmPoly24` extracted from
harmonic projection agrees with the normalized Gegenbauer polynomial `Gegenbauer24`. As a result,
the harmonic Gram kernel `harmKernel24` is a scalar multiple of
`(Gegenbauer24 k).eval (⟪u, v⟫ : ℝ)`.

## Main statements
* `harmKernel24_eq_gegenbauer_eval`
* `zonalKernel24_eq_inv_harmKernelScalar24_mul_harmKernel24`
-/



-- @@ L19-19 verbatim
namespace SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.AdditionTheorem

-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
open scoped RealInnerProductSpace


-- @@ L24-24 verbatim
open Polynomial


-- @@ L26-26 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L28-35 verbatim
/-- Express `harmKernel24` as a scalar multiple of the normalized Gegenbauer kernel. -/
public theorem harmKernel24_eq_gegenbauer_eval
    (k : ℕ) {u v : ℝ²⁴} (hu : ‖u‖ = (1 : ℝ)) (hv : ‖v‖ = (1 : ℝ)) :
    PSD.ZonalKernel.harmKernel24 k u v =
      (harmKernelScalar24 k) *
        (Gegenbauer24 k).eval (⟪u, v⟫ : ℝ) := by
  simpa [harmPoly24, mul_assoc, mul_left_comm, mul_comm] using
    (harmKernel24_eq_harmPoly24_eval (k := k) (u := u) (v := v) hu hv)


-- @@ L37-43 verbatim
theorem harmKernel24_eq_zonalKernel24
    (k : ℕ) {u v : ℝ²⁴} (hu : ‖u‖ = (1 : ℝ)) (hv : ‖v‖ = (1 : ℝ)) :
    PSD.ZonalKernel.harmKernel24 k u v =
      (harmKernelScalar24 k) *
        zonalKernel24 k u v := by
  simpa [zonalKernel24, mul_assoc] using
    (harmKernel24_eq_gegenbauer_eval (k := k) (u := u) (v := v) hu hv)


-- @@ L45-54 verbatim
/-- Solve for `zonalKernel24` in terms of `harmKernel24` and `harmKernelScalar24`. -/
public theorem zonalKernel24_eq_inv_harmKernelScalar24_mul_harmKernel24
    (k : ℕ) {u v : ℝ²⁴} (hu : ‖u‖ = (1 : ℝ)) (hv : ‖v‖ = (1 : ℝ)) :
    zonalKernel24 k u v =
      (harmKernelScalar24 k)⁻¹ *
        PSD.ZonalKernel.harmKernel24 k u v := by
  have hs : harmKernelScalar24 k ≠ 0 := harmKernelScalar24_ne_zero (k := k)
  have h :=
    (harmKernel24_eq_zonalKernel24 (k := k) (u := u) (v := v) hu hv)
  exact (eq_inv_mul_iff_mul_eq₀ hs).mpr (id (Eq.symm h))


-- @@ L56-56 verbatim
end


-- @@ L58-58 verbatim
end SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.AdditionTheorem
