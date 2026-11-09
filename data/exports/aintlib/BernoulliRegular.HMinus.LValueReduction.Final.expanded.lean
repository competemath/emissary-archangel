/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.HMinus.LValueReduction.Assembly
public import BernoulliRegular.HMinus.LValueReduction.GaussProduct


-- @@ L11-16 verbatim
/-!
# Final `hMinus` formulas

This file combines the residue, `hPlus`, and Gauss-product packages into
Diekmann Theorem 43 for `hMinus`.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
open NumberField

-- @@ L23-23 verbatim
open scoped BigOperators


-- @@ L25-25 verbatim
namespace BernoulliRegular


-- @@ L27-27 verbatim
section Final


-- @@ L29-30 verbatim
variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K]


-- @@ L32-62 verbatim
theorem hMinus_formula_of_residue_and_hPlus_cyclotomic_and_gauss
    (hp_odd' : p ≠ 2)
    (hres :
      ((NumberField.dedekindZeta_residue K : ℝ) : ℂ) =
        Finset.prod (evenNontrivialCharacters (p := p)) (fun χ ↦ evenLValueRhs p χ) *
          Finset.prod (oddCharacters (p := p)) (fun χ ↦ DirichletCharacter.LFunction χ 1))
    (hplus :
      ((hPlus K : ℕ) : ℂ) =
        cyclotomicHPlusFactor (K := K) *
          Finset.prod (evenNontrivialCharacters (p := p)) (fun χ ↦ evenLValueRhs p χ))
    (hgauss : cyclotomicHGaussGoal (p := p) K) :
    ((hMinus K : ℕ) : ℂ) =
      (2 * p : ℂ) *
        Finset.prod (oddCharacters (p := p)) (fun χ ↦
          (-(1 / 2 : ℂ)) * BernoulliGen χ⁻¹ 1) := by
  apply hMinus_formula_of_residue_and_hPlus_and_gauss (p := p) (K := K) hp_odd'
    (coefficient := cyclotomicRelativeLValueCoefficient (p := p) (K := K))
    (plusFactor := cyclotomicHPlusFactor (K := K))
  · calc
      ((h K : ℕ) : ℂ) =
          ((NumberField.dedekindZeta_residue K : ℝ) : ℂ) *
            cyclotomicClassNumberFactor (p := p) (K := K) :=
            h_formula_cyclotomic_complex (p := p) (K := K) hp_odd'
      _ = ((NumberField.dedekindZeta_residue K : ℝ) : ℂ) *
            (cyclotomicRelativeLValueCoefficient (p := p) (K := K) *
              cyclotomicHPlusFactor (K := K)) := by
            rw [cyclotomicClassNumberFactor_eq_relative_coefficient_mul_hPlusFactor
              (p := p) (K := K)]
  · exact hres
  · exact hplus
  · exact hgauss


-- @@ L64-91 verbatim
/-- Diekmann Theorem 43: the relative class number of a cyclotomic field of
prime conductor is the odd-character Bernoulli product.

This is the explicit statement ultimately obtained by combining the cyclotomic
class-number formula with the odd and even `L(1, χ)` evaluations. -/
theorem hMinus_formula (hp_odd' : p ≠ 2) :
    ((hMinus K : ℕ) : ℂ) =
      (2 * p : ℂ) *
        Finset.prod (oddCharacters (p := p)) fun χ ↦
          (-(1 / 2 : ℂ)) * BernoulliGen χ⁻¹ 1 := by
  apply hMinus_formula_of_residue_and_hPlus_cyclotomic_and_gauss
    (p := p) (K := K) hp_odd'
  · calc
      ((NumberField.dedekindZeta_residue K : ℝ) : ℂ) =
          nontrivialLProduct p (1 : ℂ) :=
            tendsto_nhds_unique
              (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K)
              (tendsto_sub_one_mul_dedekindZeta_via_LProducts p K)
      _ = evenLProduct p (1 : ℂ) * oddLProduct p (1 : ℂ) := by
            rw [nontrivialLProduct_eq_even_mul_odd]
      _ =
          Finset.prod (evenNontrivialCharacters (p := p)) (fun χ ↦ evenLValueRhs p χ) *
            Finset.prod (oddCharacters (p := p))
              (fun χ ↦ DirichletCharacter.LFunction χ 1) := by
            rw [evenLProduct_one_eq_prod_evenLValueRhs (p := p)]
            rfl
  · exact hPlus_formula_of_evenLValues (p := p) (K := K) hp_odd'
  · exact cyclotomicHGaussGoal_holds (p := p) (K := K) hp_odd'


-- @@ L93-93 verbatim
end Final


-- @@ L95-95 verbatim
end BernoulliRegular
