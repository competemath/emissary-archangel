/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic


-- @@ L11-17 verbatim
/-!
# Basic definitions for classical complex Weierstrass preparation

This module will contain the ordinary finite-dimensional spaces and local analytic
definitions used by the proof development. The independently audited public
statement remains in `Challenge.lean`.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
open scoped BigOperators Topology



-- @@ L24-24 verbatim
namespace ClassicalComplexWPT


-- @@ L26-27 verbatim
/-- The complex parameter space `ℂⁿ`. -/
abbrev Base (n : ℕ) := Fin n → ℂ


-- @@ L29-30 verbatim
/-- The parameter space together with the distinguished complex variable. -/
abbrev Ambient (n : ℕ) := Base n × ℂ


-- @@ L32-34 verbatim
/-- The additive zero in the ambient product is the pair of coordinate zeros. -/
theorem ambient_zero_eq (n : ℕ) : (0 : Ambient n) = ((0 : Base n), 0) := by
  ext <;> simp


-- @@ L36-38 verbatim
/-- Restriction of a function to the distinguished-variable axis. -/
def lastSlice {n : ℕ} (f : Ambient n → ℂ) : ℂ → ℂ :=
  fun w ↦ f (0, w)


-- @@ L40-42 verbatim
@[simp]
theorem lastSlice_zero {n : ℕ} (f : Ambient n → ℂ) : lastSlice f 0 = f 0 := by
  rw [lastSlice, ambient_zero_eq]


-- @@ L44-51 verbatim
/--
The distinguished-variable slice has a zero of exact order `d` at the origin:
all derivatives of order below `d` vanish and the derivative of order `d` does
not vanish.
-/
def ExactOrderInLastVariable {n : ℕ} (f : Ambient n → ℂ) (d : ℕ) : Prop :=
  (∀ k < d, iteratedDeriv k (lastSlice f) 0 = 0) ∧
    iteratedDeriv d (lastSlice f) 0 ≠ 0


-- @@ L53-56 verbatim
/-- The monic degree-`d` polynomial in the distinguished variable. -/
def preparedPolynomial {n : ℕ} (d : ℕ) (a : Fin d → Base n → ℂ)
    (x : Ambient n) : ℂ :=
  x.2 ^ d + ∑ i : Fin d, a i x.1 * x.2 ^ (i : ℕ)


-- @@ L58-69 verbatim
/--
`f` is locally the product of a nonvanishing analytic unit and a monic
distinguished-variable polynomial whose lower coefficients are analytic and
vanish at the base origin.
-/
def IsWeierstrassPreparation {n : ℕ} (f : Ambient n → ℂ) (d : ℕ)
    (a : Fin d → Base n → ℂ) (u : Ambient n → ℂ) : Prop :=
  (∀ i, AnalyticAt ℂ (a i) 0) ∧
    (∀ i, a i 0 = 0) ∧
    AnalyticAt ℂ u 0 ∧
    u 0 ≠ 0 ∧
    f =ᶠ[𝓝 0] fun x ↦ u x * preparedPolynomial d a x


-- @@ L71-71 verbatim
end ClassicalComplexWPT
