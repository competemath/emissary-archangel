/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ProblemStatement
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic


-- @@ L12-18 verbatim
/-!
# Compact smooth test functions as Schwartz functions

Compact support is preserved by iterated derivatives. Consequently each
polynomially weighted derivative norm is continuous with compact support and
is bounded, giving a Schwartz map with the original function as its coercion.
-/


-- @@ L20-20 verbatim
@[expose] public section




-- @@ L24-24 verbatim
noncomputable section


-- @@ L26-26 verbatim
open Set

-- @@ L27-27 verbatim
open scoped ContDiff


-- @@ L29-29 verbatim
namespace NavierStokesR3.CompactSchwartz


-- @@ L31-31 verbatim
open ProblemStatement


-- @@ L33-45 verbatim
/-- Polynomially weighted derivative norms of compact smooth functions are
bounded on all of space. -/
theorem weighted_derivative_bound (f : Space → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (k n : ℕ) :
    ∃ C : ℝ, ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
  have hcompact :
      HasCompactSupport (fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) :=
    (hc.iteratedFDeriv n).norm.mul_left
  have hcontinuous :
      Continuous (fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) :=
    (continuous_norm.pow k).mul (hf.continuous_iteratedFDeriv (mod_cast le_top)).norm
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuous hcontinuous
  exact ⟨C, fun x => (le_abs_self _).trans (hC x)⟩


-- @@ L47-52 verbatim
/-- A compactly supported smooth function defines a Schwartz function. -/
def ofCompactSupport (f : Space → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : SchwartzMap Space ℂ where
  toFun := f
  smooth' := hf
  decay' := weighted_derivative_bound f hf hc


-- @@ L54-56 verbatim
@[simp] theorem coe_ofCompactSupport (f : Space → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) :
    (ofCompactSupport f hf hc : Space → ℂ) = f := rfl


-- @@ L58-60 verbatim
@[simp] theorem ofCompactSupport_apply (f : Space → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (x : Space) :
    ofCompactSupport f hf hc x = f x := rfl


-- @@ L62-65 verbatim
/-- Passing to the Schwartz wrapper preserves topological support exactly. -/
@[simp] theorem tsupport_ofCompactSupport (f : Space → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) :
    tsupport (ofCompactSupport f hf hc) = tsupport f := rfl


-- @@ L67-70 verbatim
/-- Each iterated derivative remains supported inside the original support. -/
theorem tsupport_iteratedFDeriv_subset (f : Space → ℂ) (n : ℕ) :
    tsupport (iteratedFDeriv ℝ n f) ⊆ tsupport f :=
  _root_.tsupport_iteratedFDeriv_subset n


-- @@ L72-76 verbatim
/-- Each iterated derivative of a compactly supported test has compact support. -/
theorem hasCompactSupport_iteratedFDeriv (f : Space → ℂ)
    (hc : HasCompactSupport f) (n : ℕ) :
    HasCompactSupport (iteratedFDeriv ℝ n f) :=
  hc.iteratedFDeriv n


-- @@ L78-78 verbatim
end NavierStokesR3.CompactSchwartz
