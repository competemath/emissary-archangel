module
public import SpherePacking.Dim24.MagicFunction.F.Defs
import SpherePacking.Dim24.MagicFunction.F.Fourier
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Radial
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Basic
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Final
public import SpherePacking.Dim24.MagicFunction.A.Eigen.Eigenfunction
public import SpherePacking.Dim24.MagicFunction.B.Eigen.PermJ5



-- @@ L11-20 verbatim
/-!
# Normalization at the origin

This file records the normalization `f 0 = 1` and the corresponding value of the Fourier
transform at the origin.

## Main statements
* `f_zero`
* `fourier_f_zero`
-/


-- @@ L22-22 verbatim
namespace SpherePacking.Dim24


-- @@ L24-24 verbatim
open scoped FourierTransform SchwartzMap

-- @@ L25-25 verbatim
open SchwartzMap Complex Real


-- @@ L27-27 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

-- @@ L28-28 verbatim
local notation "FT" => FourierTransform.fourierCLE ℂ (SchwartzMap ℝ²⁴ ℂ)


-- @@ L30-31 verbatim
private lemma a_zero : a (0 : ℝ²⁴) = (113218560 : ℂ) * Complex.I / (π : ℂ) := by
  simpa [aRadial, axisVec_zero] using (aRadial_zero : aRadial (0 : ℝ) = _)


-- @@ L33-34 verbatim
private lemma b_zero : b (0 : ℝ²⁴) = 0 := by
  simpa [bRadial, axisVec_zero] using (bRadial_zero : bRadial (0 : ℝ) = 0)


-- @@ L36-43 verbatim
/-- Normalization of the auxiliary function `f` at the origin. -/
public theorem f_zero : f 0 = 1 := by
  /- Proof sketch:
  Use the explicit special values of `a(0)` and `b(0)` coming from the analytic continuation
  formulas in Sections 2-3, and simplify the scalar linear combination defining `f`. -/
  -- Evaluate the defining linear combination at `0`.
  simp [f, a_zero, b_zero, SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul,
    div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]


-- @@ L45-60 verbatim
/-- Normalization of the Fourier transform of `f` at the origin. -/
public theorem fourier_f_zero : (FT f) 0 = 1 := by
  /- Proof sketch:
  By linearity and `eig_a`/`eig_b`, compute `𝓕 f` from `f` and reduce to `f_zero`. -/
  have hF0 :
      (FT f) 0 =
        ((- (π * Complex.I) / (113218560 : ℂ)) • a +
            (Complex.I / ((262080 : ℂ) * π)) • b) 0 := by
    simpa using congrArg (fun g => g 0)
      (fourier_f :
        FT f =
          (- (π * Complex.I) / (113218560 : ℂ)) • a +
            (Complex.I / ((262080 : ℂ) * π)) • b)
  -- Evaluate at `0` and use the special values.
  simp [-FourierTransform.fourierCLE_apply, hF0, a_zero, b_zero, SchwartzMap.add_apply,
    SchwartzMap.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]


-- @@ L62-62 verbatim
end SpherePacking.Dim24
