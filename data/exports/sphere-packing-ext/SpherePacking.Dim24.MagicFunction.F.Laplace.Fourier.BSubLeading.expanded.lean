module
public import SpherePacking.Dim24.MagicFunction.F.Defs
public import SpherePacking.Dim24.MagicFunction.A.LaplaceZerosTail.HolomorphyHelpers
public import SpherePacking.Dim24.MagicFunction.A.LaplaceZerosTail.TailBounds
public import SpherePacking.Dim24.MagicFunction.A.LaplaceZerosTail.TailDeform
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.EvenU.BProfileZeros
public import SpherePacking.Dim24.MagicFunction.F.BKernelAsymptotics
public import SpherePacking.Dim24.MagicFunction.F.Laplace.KernelTools
public import SpherePacking.Dim24.MagicFunction.F.Laplace.B.LeadingCorrection
public import SpherePacking.Dim24.MagicFunction.F.Laplace.B.SubLeadingBounds.BKernelSubLeadingBound
public import SpherePacking.Dim24.MagicFunction.F.ProfileComplex.B
public import SpherePacking.Dim24.MagicFunction.F.Laplace.TopologyDomains
public import SpherePacking.Dim24.Inequalities.Defs
import SpherePacking.Tactic.NormNumI
public import SpherePacking.ForMathlib.CauchyGoursat.OpenRectangular
public import SpherePacking.Dim24.MagicFunction.Radial
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import SpherePacking.Dim24.MagicFunction.F.Laplace.B.SubLeadingContinuation.Agreement
public import SpherePacking.Dim24.MagicFunction.F.Laplace.Fourier.Basic


-- @@ L27-35 verbatim
/-!
# Subtract-leading continuation on `0 < ‖y‖ < √2`

This file applies the subtract-leading continuation `rhsBSubLeading` to rewrite `𝓕 f` as a
convergent Laplace expression on the range `0 < ‖y‖ < Real.sqrt 2`.

## Main statement
* `fourier_f_eq_laplace_B_subtract_leading`
-/

-- @@ L36-36 verbatim
namespace SpherePacking.Dim24.LaplaceTmp


-- @@ L38-38 verbatim
noncomputable section


-- @@ L40-40 verbatim
open scoped FourierTransform SchwartzMap


-- @@ L42-42 verbatim
open Complex MeasureTheory Real SchwartzMap Set

-- @@ L43-43 verbatim
open UpperHalfPlane


-- @@ L45-45 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

-- @@ L46-46 verbatim
local notation "FT" => FourierTransform.fourierCLE ℂ (SchwartzMap ℝ²⁴ ℂ)


-- @@ L48-48 verbatim
namespace LaplaceBSubLeadingCont.Private


-- @@ L50-50 verbatim
open LaplaceFourierCont.PrivateDefs


-- @@ L52-61 verbatim
/-- Specialize `rhsBSubLeading` to a real parameter and expand the definition. -/
public lemma rhsBSubLeading_ofReal (u : ℝ) :
    rhsBSubLeading (u : ℂ) =
      (((Real.sin (Real.pi * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ) *
        ((∫ t in Set.Ioc (0 : ℝ) 1, BKernel0 t * Real.exp (-Real.pi * u * t)) +
          (∫ t in Set.Ioi (1 : ℝ),
              (BKernel0 t - (BleadingTermR t : ℂ)) * Real.exp (-Real.pi * u * t)) +
          BleadingCorrection u) := by
  simp [rhsBSubLeading, LaplaceFourierCont.sinSqC_ofReal, laplaceBKernelSubLeading,
    BleadingCorrectionC_ofReal]


-- @@ L63-63 verbatim
end LaplaceBSubLeadingCont.Private


-- @@ L65-122 verbatim
/-- Analytically continued convergent integral expression for `𝓕 f` on `0 < ‖y‖ < Real.sqrt 2`.

Paper reference: `dim_24.tex`, around (4.4)-(4.6). -/
public theorem fourier_f_eq_laplace_B_subtract_leading (y : ℝ²⁴)
    (hy0 : 0 < ‖y‖) (hy : ‖y‖ < Real.sqrt 2) :
    FT f y =
      (((Real.sin (Real.pi * (‖y‖ ^ 2) / 2)) ^ (2 : ℕ) : ℝ) : ℂ) *
        ((∫ t in Set.Ioc (0 : ℝ) 1, BKernel0 t * Real.exp (-Real.pi * (‖y‖ ^ 2) * t)) +
          (∫ t in Set.Ioi (1 : ℝ),
              (BKernel0 t -
                  ((1 / 39 : ℝ) * t * Real.exp (2 * Real.pi * t)
                    - (10 / (117 * Real.pi) : ℝ) * Real.exp (2 * Real.pi * t) : ℝ)) *
                Real.exp (-Real.pi * (‖y‖ ^ 2) * t)) +
          BleadingCorrection (‖y‖ ^ 2)) := by
  -- Set `u = ‖y‖^2` and place it in the continuation domain.
  set u : ℝ := ‖y‖ ^ (2 : ℕ)
  have hu2 : u < 2 := by
    have hs0 : 0 ≤ ‖y‖ := norm_nonneg y
    exact (lt_sqrt hs0).mp hy
  have huDom : (u : ℂ) ∈ LaplaceDomains.domainPosNeTwo := by
    refine ⟨?_, ?_⟩
    · have : 0 < u := by simpa [u] using pow_pos hy0 2
      simpa using this
    · have : (u : ℂ) ≠ (2 : ℂ) := by
        intro hEq
        have : u = (2 : ℝ) := by exact_mod_cast hEq
        exact (ne_of_lt hu2) this
      simpa [LaplaceDomains.domainPosNeTwo] using this
  have heq :
      LaplaceFourierCont.PrivateDefs.fhatProfileC (u : ℂ) =
        LaplaceBSubLeadingCont.Private.rhsBSubLeading (u : ℂ) :=
    LaplaceBSubLeadingCont.Private.eqOn_domainPosNeTwo_fhatProfileC_rhsBSubLeading (x := (u : ℂ))
      huDom
  -- Finish by rewriting `u = ‖y‖^2` and expanding the explicit leading term.
  calc
    FT f y = LaplaceFourier.fhatProfile u := by
      simpa [u] using LaplaceFourier.fourier_f_apply (y := y)
    _ = LaplaceFourierCont.PrivateDefs.fhatProfileC (u : ℂ) := by
      simpa using (LaplaceFourierCont.fhatProfileC_ofReal (u := u)).symm
    _ = LaplaceBSubLeadingCont.Private.rhsBSubLeading (u : ℂ) := heq
    _ =
        (((Real.sin (Real.pi * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ) *
          ((∫ t in Set.Ioc (0 : ℝ) 1, BKernel0 t * Real.exp (-Real.pi * u * t)) +
            (∫ t in Set.Ioi (1 : ℝ),
                (BKernel0 t - (BleadingTermR t : ℂ)) * Real.exp (-Real.pi * u * t)) +
            BleadingCorrection u) := by
      simpa using LaplaceBSubLeadingCont.Private.rhsBSubLeading_ofReal (u := u)
    _ =
        (((Real.sin (Real.pi * (‖y‖ ^ 2) / 2)) ^ (2 : ℕ) : ℝ) : ℂ) *
          ((∫ t in Set.Ioc (0 : ℝ) 1, BKernel0 t * Real.exp (-Real.pi * (‖y‖ ^ 2) * t)) +
            (∫ t in Set.Ioi (1 : ℝ),
                (BKernel0 t -
                    ((1 / 39 : ℝ) * t * Real.exp (2 * Real.pi * t) -
                        (10 / (117 * Real.pi) : ℝ) * Real.exp (2 * Real.pi * t) : ℝ)) *
                  Real.exp (-Real.pi * (‖y‖ ^ 2) * t)) +
            BleadingCorrection (‖y‖ ^ 2)) := by
          subst u
          simp [BleadingTermR, mul_assoc, add_assoc]



-- @@ L125-125 verbatim
end


-- @@ L127-127 verbatim
end SpherePacking.Dim24.LaplaceTmp
