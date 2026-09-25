module
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.Kernel
public import
  SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.AdditionTheorem.HarmPolyRecurrence24


-- @@ L6-15 verbatim
/-!
# Positivity of the Gegenbauer zonal kernels on `Ω₂₄`

This file isolates the LP-layer theorem `zonalKernel24_psd`. It is proved by:
* building the harmonic Gram kernel `harmKernel24` (PSD by Gram form), and
* using the addition theorem bridge `harmKernel24 = zonalKernel24` on the unit sphere.

## Main statements
* `zonalKernel24_psd`
-/



-- @@ L18-18 verbatim
namespace SpherePacking.Dim24.Uniqueness.BS81.LP

-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
open scoped BigOperators RealInnerProductSpace


-- @@ L23-23 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L25-25 verbatim
open Uniqueness.BS81.LP.Gegenbauer24.AdditionTheorem

-- @@ L26-26 verbatim
open Uniqueness.BS81.LP.Gegenbauer24.PSD.ZonalKernel


-- @@ L28-66 verbatim
/-- The normalized Gegenbauer zonal kernel `zonalKernel24 k` is PSD on `Ω₂₄`. -/
public lemma zonalKernel24_psd (k : ℕ) : IsPSDKernel24 (zonalKernel24 k) := by
  intro C hC
  -- Rewrite the Gegenbauer kernel as a positive scalar multiple of the harmonic Gram kernel on
  -- `Ω₂₄`.
  set s := harmKernelScalar24 k
  have hspos : 0 < s := by
    simpa [s] using
      harmKernelScalar24_pos (k := k)
  have hsinv : 0 ≤ s⁻¹ := le_of_lt (inv_pos.2 hspos)
  have hEq :
      C.sum (fun u => C.sum (fun v => zonalKernel24 k u v)) =
        s⁻¹ * C.sum (fun u => C.sum (fun v => harmKernel24 k u v)) := by
    -- Rewrite each kernel term using the addition theorem bridge on the unit sphere, then pull out
    -- the scalar.
    calc
      C.sum (fun u => C.sum (fun v => zonalKernel24 k u v)) =
          C.sum (fun u => s⁻¹ * C.sum (fun v => harmKernel24 k u v)) := by
            refine Finset.sum_congr rfl ?_
            intro u hu
            have hu1 : ‖u‖ = (1 : ℝ) := hC u hu
            calc
              C.sum (fun v => zonalKernel24 k u v) =
                  C.sum (fun v => s⁻¹ * harmKernel24 k u v) := by
                    refine Finset.sum_congr rfl ?_
                    exact fun x a =>
                     zonalKernel24_eq_inv_harmKernelScalar24_mul_harmKernel24 k (hC u hu) (hC x a)
              _ = s⁻¹ * C.sum (fun v => harmKernel24 k u v) := by
                    simpa [mul_assoc] using
                      (Finset.mul_sum (s := C) (f := fun v => harmKernel24 k u v) (a := s⁻¹)).symm
      _ = s⁻¹ * C.sum (fun u => C.sum (fun v => harmKernel24 k u v)) :=
            Eq.symm (Finset.mul_sum C (fun i => ∑ v ∈ C, harmKernel24 k i v) s⁻¹)
  -- Nonnegativity is immediate for the Gram kernel; multiply by the nonnegative scalar.
  have hnonneg :
      0 ≤ C.sum (fun u => C.sum (fun v => harmKernel24 k u v)) :=
    Uniqueness.BS81.LP.Gegenbauer24.PSD.ZonalKernel.sum_sum_harmKernel24_nonneg (k := k) (C := C)
  have hmul : 0 ≤ s⁻¹ * C.sum (fun u => C.sum (fun v => harmKernel24 k u v)) :=
    mul_nonneg hsinv hnonneg
  simpa [hEq] using hmul


-- @@ L68-68 verbatim
end


-- @@ L70-70 verbatim
end SpherePacking.Dim24.Uniqueness.BS81.LP
