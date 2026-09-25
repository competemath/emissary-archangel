module
public import SpherePacking.Dim24.MagicFunction.F.Defs
import SpherePacking.Dim24.MagicFunction.A.Eigen.Eigenfunction
import SpherePacking.Dim24.MagicFunction.B.Eigen.PermJ5


-- @@ L6-14 verbatim
/-!
# Fourier transform of `f`

We compute the Fourier transform of the auxiliary function `f` using the eigenfunction relations
`𝓕 a = a` and `𝓕 b = -b`.

## Main statement
* `fourier_f`
-/


-- @@ L16-16 verbatim
open scoped FourierTransform


-- @@ L18-18 verbatim
namespace SpherePacking.Dim24


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

-- @@ L23-23 verbatim
local notation "FT" => FourierTransform.fourierCLE ℂ (SchwartzMap ℝ²⁴ ℂ)


-- @@ L25-34 verbatim
/--
Fourier transform of `f`, obtained by linearity and the eigenfunction identities
`𝓕 a = a` and `𝓕 b = -b`.
-/
public theorem fourier_f :
    FT f =
      (-((Real.pi : ℂ) * Complex.I) / (113218560 : ℂ)) • a +
        (Complex.I / ((262080 : ℂ) * (Real.pi : ℂ))) • b := by
  -- `𝓕 a = a` and `𝓕 b = -b`, so the `b` coefficient flips sign.
  simp [-FourierTransform.fourierCLE_apply, Dim24.f, eig_a, eig_b]


-- @@ L36-36 verbatim
end


-- @@ L38-38 verbatim
end SpherePacking.Dim24
