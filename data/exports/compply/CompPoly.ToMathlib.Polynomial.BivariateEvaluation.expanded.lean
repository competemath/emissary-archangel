/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov, Aristotle (Harmonic)
-/
module

public import CompPoly.ToMathlib.Polynomial.BivariateDegree


-- @@ L10-15 verbatim
/-!
# Mathlib-Facing Bivariate Evaluation Helpers

This file collects evaluation-oriented helpers for Mathlib's
bivariate polynomial surface `R[X][Y]`.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
open Polynomial

-- @@ L20-20 verbatim
open scoped Polynomial.Bivariate


-- @@ L22-22 verbatim
namespace Polynomial.Bivariate


-- @@ L24-24 verbatim
noncomputable section


-- @@ L26-26 verbatim
variable {F : Type*}


-- @@ L28-28 verbatim
section CommSemiring


-- @@ L30-30 verbatim
variable [CommSemiring F]


-- @@ L32-42 verbatim
/-- Evaluation of a bivariate polynomial is commutative,
  i.e. evaluating in `X` and then in `Y` is the same as
  evaluating in `Y` first and then in `X`. -/
theorem eval_comm {f : Polynomial (Polynomial F)} {a x : F} :
    (f.eval (Polynomial.C a)).eval x =
    (Polynomial.map (evalRingHom x) f).eval a := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval_add, Polynomial.map_add, hp, hq]
  | monomial n c =>
      simp only [Polynomial.eval_monomial, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_C, Polynomial.map_monomial, Polynomial.coe_evalRingHom]


-- @@ L44-44 verbatim
end CommSemiring


-- @@ L46-46 verbatim
end

-- @@ L47-47 verbatim
end Polynomial.Bivariate
