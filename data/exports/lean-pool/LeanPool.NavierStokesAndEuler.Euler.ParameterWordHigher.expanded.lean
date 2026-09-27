/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParameterWordGevrey
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import LeanPool.NavierStokesAndEuler.Euler.ParameterWordCalculus


-- @@ L13-13 verbatim
/-! Smoothness and exact concatenation of genuine directional word derivatives. -/


-- @@ L15-15 verbatim
@[expose] public section



-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-20 verbatim
namespace EulerParameterWordGevrey


-- @@ L22-22 verbatim
open ContinuousLinearMap Finset

-- @@ L23-23 verbatim
open scoped ContDiff


-- @@ L25-26 verbatim
variable {P E ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]


-- @@ L28-42 verbatim
theorem wordDerivative_contDiff (directions : ι → P) (f : P → E)
    (hf : ContDiff ℝ ∞ f) {n : ℕ} (w : Fin n → ι) :
    ContDiff ℝ ∞ (wordDerivative directions f w) := by
  induction n generalizing f with
  | zero =>
    have he : wordDerivative directions f w = f := funext (wordDerivative_zero directions f w)
    rwa [he]
  | succ n ih =>
    have he : wordDerivative directions f w =
        wordDerivative directions (directional directions f (w (Fin.last n))) (Fin.init w) := by
      funext x
      simpa only [Fin.snoc_init_self] using
        wordDerivative_snoc directions f hf (Fin.init w) (w (Fin.last n)) x
    rw [he]
    exact ih _ (directional_contDiff directions f hf (w (Fin.last n))) (Fin.init w)


-- @@ L44-50 verbatim
/-- The sum over all words can be decomposed for any scalar expression on words. -/
theorem sum_words_snoc [Fintype ι] (n : ℕ) (a : (Fin (n + 1) → ι) → ℝ) :
    (∑ w, a w) = ∑ i, ∑ w : Fin n → ι, a (Fin.snoc w i) := by
  calc
    _ = ∑ z : ι × (Fin n → ι), a (Fin.snoc z.2 z.1) :=
      ((Fin.snocEquiv (fun _ : Fin (n+1) => ι)).sum_comp a).symm
    _ = _ := Fintype.sum_prod_type _


-- @@ L52-52 verbatim
end EulerParameterWordGevrey
