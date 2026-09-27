/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.DerivNotation
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv


-- @@ L13-17 verbatim
/-!
Directional differentiation bundled with Schwartz regularity. The underlying functions
are explicit Fréchet derivatives, so their public formulas do not depend on integration
by parts or the analytic estimates used to prove rapid decay.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
namespace EulerSobolev


-- @@ L25-25 verbatim
open scoped SchwartzMap LineDeriv ContDiff


-- @@ L27-28 verbatim
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


-- @@ L30-40 verbatim
/-- The directional Fréchet derivative with its Schwartz smoothness and decay proofs. -/
def schwartzDerivative (m : E) (f : 𝓢(E, F)) : 𝓢(E, F) where
  toFun x := fderiv ℝ f x m
  smooth' := by
    have h : ContDiff ℝ ∞ (fun x => (∂_{m} f) x) := (∂_{m} f : 𝓢(E, F)).smooth'
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using h
  decay' := by
    have h : ∀ k n : ℕ, ∃ C : ℝ, ∀ x : E,
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => (∂_{m} f) y) x‖ ≤ C :=
      (∂_{m} f : 𝓢(E, F)).decay'
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using h


-- @@ L42-43 verbatim
private theorem schwartzDerivative_eq (m : E) (f : 𝓢(E, F)) :
    schwartzDerivative m f = ∂_{m} f := rfl


-- @@ L45-47 verbatim
/-- Iterated Schwartz differentiation in a finite ordered family of directions. -/
abbrev schwartzIteratedDerivative {n : ℕ} : (Fin n → E) → 𝓢(E, F) → 𝓢(E, F) :=
  @LineDeriv.iteratedLineDerivOp E 𝓢(E, F) ⟨schwartzDerivative⟩ n


-- @@ L49-50 verbatim
private theorem schwartzIteratedDerivative_eq {n : ℕ} (m : Fin n → E) (f : 𝓢(E, F)) :
    schwartzIteratedDerivative m f = ∂^{m} f := rfl


-- @@ L52-55 verbatim
/-- Iterated directional differentiation evaluates the actual Fréchet derivative tensor. -/
theorem schwartzIteratedDerivative_apply {n : ℕ} (m : Fin n → E) (f : 𝓢(E, F)) (x : E) :
    schwartzIteratedDerivative m f x = iteratedFDeriv ℝ n f x m :=
  SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv


-- @@ L57-57 verbatim
end EulerSobolev
