/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonFourierSetup
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.RieszSymbolRegularity
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma


-- @@ L15-20 verbatim
/-!
# Linearity and decay of Riesz test operators

The integrable Fourier multipliers defining the test operators respect complex
linear combinations. Their inverse Fourier integrals vanish at spatial infinity.
-/


-- @@ L22-22 verbatim
@[expose] public section




-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-28 verbatim
open MeasureTheory Filter

-- @@ L29-29 verbatim
open scoped Topology BigOperators RealInnerProductSpace


-- @@ L31-31 verbatim
namespace NavierStokesR3.RieszTestOperators


-- @@ L33-33 verbatim
open ProblemStatement Comparison


-- @@ L35-55 verbatim
theorem rieszTest_add (i j : Fin 3) (ψ φ : ComplexTest) :
    rieszTest i j (ψ + φ) = rieszTest i j ψ + rieszTest i j φ := by
  have hmul :
      (fun ξ : Space => (rieszSymbol i j ξ : ℂ) *
        (EulerSobolev.schwartzFourier (ψ + φ)) ξ) =
      (fun ξ : Space => (rieszSymbol i j ξ : ℂ) *
        (EulerSobolev.schwartzFourier ψ) ξ) +
      (fun ξ : Space => (rieszSymbol i j ξ : ℂ) *
        (EulerSobolev.schwartzFourier φ) ξ) := by
    have hadd : EulerSobolev.schwartzFourier (ψ + φ) =
        EulerSobolev.schwartzFourier ψ + EulerSobolev.schwartzFourier φ :=
      (EulerSobolev.schwartzFourierCLM (V := Space) (E := ℂ)).map_add ψ φ
    funext ξ
    simp only [hadd, add_apply, Pi.add_apply, mul_add]
  have hcont : Continuous (fun p : Space × Space => (-innerₗ Space) p.1 p.2) := by
    change Continuous (fun p : Space × Space => -⟪p.1, p.2⟫)
    exact (continuous_fst.inner continuous_snd).neg
  unfold rieszTest
  rw [hmul]
  exact VectorFourier.fourierIntegral_add Real.continuous_fourierChar hcont
    (integrable_rieszMultiplier i j ψ) (integrable_rieszMultiplier i j φ)


-- @@ L57-71 verbatim
theorem rieszTest_smul (i j : Fin 3) (c : ℂ) (ψ : ComplexTest) :
    rieszTest i j (c • ψ) = c • rieszTest i j ψ := by
  have hmul :
      (fun ξ : Space => (rieszSymbol i j ξ : ℂ) *
        (EulerSobolev.schwartzFourier (c • ψ)) ξ) =
      c • (fun ξ : Space => (rieszSymbol i j ξ : ℂ) *
        (EulerSobolev.schwartzFourier ψ) ξ) := by
    have hsmul : EulerSobolev.schwartzFourier (c • ψ) =
        c • EulerSobolev.schwartzFourier ψ :=
      (EulerSobolev.schwartzFourierCLM (V := Space) (E := ℂ)).map_smul c ψ
    funext ξ
    simp only [hsmul, smul_apply, Pi.smul_apply, smul_eq_mul, mul_left_comm]
  unfold rieszTest
  rw [hmul]
  exact VectorFourier.fourierIntegral_const_smul _ _ _ _ c


-- @@ L73-77 verbatim
/-- The Riesz test operator as a complex linear map into ordinary functions. -/
def rieszTestLinear (i j : Fin 3) : ComplexTest →ₗ[ℂ] (Space → ℂ) where
  toFun := rieszTest i j
  map_add' := rieszTest_add i j
  map_smul' := rieszTest_smul i j


-- @@ L79-80 verbatim
@[simp] theorem rieszTestLinear_apply (i j : Fin 3) (ψ : ComplexTest) :
    rieszTestLinear i j ψ = rieszTest i j ψ := rfl


-- @@ L82-83 verbatim
@[simp] theorem rieszTest_zero (i j : Fin 3) : rieszTest i j 0 = 0 :=
  map_zero (rieszTestLinear i j)


-- @@ L85-87 verbatim
theorem rieszTest_neg (i j : Fin 3) (ψ : ComplexTest) :
    rieszTest i j (-ψ) = -rieszTest i j ψ :=
  map_neg (rieszTestLinear i j) ψ


-- @@ L89-91 verbatim
theorem rieszTest_sub (i j : Fin 3) (ψ φ : ComplexTest) :
    rieszTest i j (ψ - φ) = rieszTest i j ψ - rieszTest i j φ :=
  map_sub (rieszTestLinear i j) ψ φ


-- @@ L93-95 verbatim
theorem rieszTest_sum (i j : Fin 3) {ι : Type*} (s : Finset ι) (ψ : ι → ComplexTest) :
    rieszTest i j (∑ a ∈ s, ψ a) = ∑ a ∈ s, rieszTest i j (ψ a) :=
  map_sum (rieszTestLinear i j) ψ s


-- @@ L97-101 verbatim
theorem rieszTest_tendsto_zero (i j : Fin 3) (ψ : ComplexTest) :
    Tendsto (rieszTest i j ψ) (cocompact Space) (𝓝 0) := by
  unfold rieszTest
  rw [Real.fourierInv_eq_fourier_comp_neg]
  exact tendsto_integral_exp_inner_smul_cocompact _


-- @@ L103-103 verbatim
end NavierStokesR3.RieszTestOperators
