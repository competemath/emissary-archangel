/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.GaussSum
public import BernoulliRegular.GaussSumSign
public import BernoulliRegular.LFunctionPositive
public import BernoulliRegular.LValueAtOne
public import BernoulliRegular.ZetaFactorisation
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality


-- @@ L16-32 verbatim
/-!
# Product of Gauss sums over odd Dirichlet characters

For `p` a prime, we compute the square of the product of Gauss sums over
the set of odd Dirichlet characters modulo `p`:

`(∏_{χ∈X⁻} τ(χ))² = (-p)^n`

where `n = (p-1)/2 = |X⁻|`. This avoids the classical Gauss sum sign
theorem — we only use T026 (`τ(χ)·τ(χ⁻¹) = χ(-1)·p`) and the fact that
conjugation `χ ↦ χ⁻¹` is an involution preserving oddness.

## Main results

* `BernoulliRegular.gaussSum_oddCharacters_prod_sq`: the squared product
  identity. This is the Gauss-sign-free half of section9_detailed Prop 5.3.
-/


-- @@ L34-34 verbatim
@[expose] public section


-- @@ L36-36 verbatim
noncomputable section


-- @@ L38-38 verbatim
namespace BernoulliRegular


-- @@ L40-40 verbatim
open Complex


-- @@ L42-42 verbatim
section GaussProduct


-- @@ L44-44 verbatim
variable (p : ℕ) [hp : Fact p.Prime]


-- @@ L46-89 verbatim
/-- **G7 (squared form)**: `(∏_{χ odd} τ(χ))² = (-p)^|X⁻|`.

The squared version of section9_detailed Prop 5.3. Avoids the Gauss sum
sign theorem; uses only T026 and the involution `χ ↦ χ⁻¹` on the odd
characters. -/
theorem gaussSum_oddCharacters_prod_sq :
    (∏ χ ∈ oddCharacters p,
        gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ)) ^ 2 =
      (-(p : ℂ)) ^ (oddCharacters p).card := by
  classical
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  -- Step 1: reindex ∏ τ(χ⁻¹) = ∏ τ(χ) via the involution.
  have h_bij : ∏ χ ∈ oddCharacters p,
        gaussSum χ⁻¹ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) =
      ∏ χ ∈ oddCharacters p,
        gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) := by
    refine Finset.prod_bij (fun χ _ => χ⁻¹)
      (fun _ hχ => inv_mem_oddCharacters p hχ) ?_ ?_ ?_
    · intro χ₁ _ χ₂ _ hχ
      rw [show χ₁ = (χ₁⁻¹)⁻¹ from (inv_inv _).symm, hχ, inv_inv]
    · intro χ hχ
      exact ⟨χ⁻¹, inv_mem_oddCharacters p hχ, inv_inv _⟩
    · intro χ _
      rfl
  -- Step 2: `(∏ τ(χ))² = ∏ τ(χ) · ∏ τ(χ⁻¹) = ∏ (τ(χ)·τ(χ⁻¹))`.
  rw [sq]
  nth_rw 2 [← h_bij]
  rw [← Finset.prod_mul_distrib]
  -- Step 3: each factor `τ(χ)·τ(χ⁻¹) = χ(-1)·p = -p` for odd `χ`.
  have h_term : ∀ χ ∈ oddCharacters p,
      gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) *
        gaussSum χ⁻¹ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) = -(p : ℂ) := by
    intro χ hχ
    have hχ_odd : χ.Odd := (Finset.mem_filter.mp hχ).2
    have hχ_neg_one : χ (-1) = -1 := hχ_odd
    -- Odd characters are nontrivial: `1` is even, so `χ ≠ 1`.
    have hχ_ne_one : χ ≠ 1 := by
      rintro rfl
      have h_one_even : (1 : DirichletCharacter ℂ p).Even :=
        MulChar.one_apply isUnit_one.neg
      exact DirichletCharacter.Odd.not_even _ hχ_odd h_one_even
    rw [gaussSum_mul_gaussSum_inv_stdAddChar p hχ_ne_one, hχ_neg_one]
    ring
  rw [Finset.prod_congr rfl h_term, Finset.prod_const]


-- @@ L91-91 verbatim
end GaussProduct


-- @@ L93-93 verbatim
end BernoulliRegular
