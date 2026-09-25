module
public import SpherePacking.Dim8.MagicFunction.a.Eigenfunction.PermI12Prelude
public import SpherePacking.Dim8.MagicFunction.a.Basic
import SpherePacking.Dim8.MagicFunction.a.Eigenfunction.PermI12ContourAux
import SpherePacking.Contour.MobiusInv.WedgeSetContour



-- @@ L8-16 verbatim
/-!
# Contour permutation for `I₁` and `I₂`

We apply the general wedge-domain contour permutation lemma to the integrands defining `I₁` and
`I₂`, reducing the identity to the hypotheses verified in `PermI12ContourAux`.

## Main statements
* `perm_I12_contour`
-/


-- @@ L18-18 verbatim
namespace MagicFunction.a.Fourier


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
open scoped FourierTransform RealInnerProductSpace Topology

-- @@ L23-23 verbatim
open Filter SpherePacking


-- @@ L25-25 verbatim
section Integral_Permutations


-- @@ L27-27 verbatim
local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)


-- @@ L29-29 verbatim
open MeasureTheory Set Complex Real

-- @@ L30-30 verbatim
open scoped Interval


-- @@ L32-49 verbatim
/-- The contour permutation identity underlying the Fourier invariance of the `I₁`/`I₂` part. -/
public lemma perm_I12_contour (r : ℝ) :
    (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + I),
          scalarOneForm (Φ₁_fourier r) z) +
        ∫ᶜ z in Path.segment ((-1 : ℂ) + I) I,
          scalarOneForm (Φ₁_fourier r) z =
      (∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I),
            scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₃' r) z) +
          ∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I,
            scalarOneForm (MagicFunction.a.ComplexIntegrands.Φ₃' r) z := by
  simpa using
    (SpherePacking.perm_I12_contour_mobiusInv_wedgeSet
      (Ψ₁_fourier := Φ₁_fourier)
      (Ψ₁' := MagicFunction.a.ComplexIntegrands.Φ₃')
      (Ψ₁_fourier_eq_deriv_mul := Φ₁_fourier_eq_deriv_mobiusInv_mul_Φ₃')
      (closed_ω_wedgeSet := fun r =>
        ⟨diffContOnCl_ω_wedgeSet (r := r), fderivWithin_ω_wedgeSet_symm (r := r)⟩)
      (r := r))



-- @@ L52-52 verbatim
end Integral_Permutations


-- @@ L54-54 verbatim
end

-- @@ L55-55 verbatim
end MagicFunction.a.Fourier
