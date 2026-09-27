/-
Copyright (c) 2026 Lazar Milikic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lazar Milikic
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset


-- @@ L17-21 verbatim
/-! # Basic definitions for Pythagorean polynomial parametrizations

This file contains the shared definitions used by the Frisch--Vaserstein
formalization setup.
-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
namespace LeanPool.PythagoreanPolynomialParametrization


-- @@ L27-27 verbatim
open MvPolynomial




-- @@ L31-32 verbatim
/-- A triple of integers (x,y,z) is a Pythagorean triple if x² + y² = z². -/
def IsPythagoreanTriple (x y z : ℤ) : Prop := x^2 + y^2 = z^2


-- @@ L34-35 verbatim
/-- The set of all Pythagorean triples. -/
def pythagoreanTriples : Set (ℤ × ℤ × ℤ) := {(x, y, z) | IsPythagoreanTriple x y z}


-- @@ L37-39 verbatim
/-- The set of all positive Pythagorean triples (x,y,z > 0). -/
def positivePythagoreanTriples : Set (ℤ × ℤ × ℤ) :=
  {(x, y, z) | 0 < x ∧ 0 < y ∧ 0 < z ∧ IsPythagoreanTriple x y z}


-- @@ L41-42 verbatim
/-- Multivariate polynomials with integer coefficients in n variables. -/
abbrev IntPoly (n : ℕ) := MvPolynomial (Fin n) ℤ


-- @@ L44-45 verbatim
/-- Multivariate polynomials with rational coefficients in n variables. -/
abbrev RatPoly (n : ℕ) := MvPolynomial (Fin n) ℚ


-- @@ L47-50 verbatim
/-- A rational-coefficient polynomial is integer-valued if it evaluates to an integer
at every integer tuple. -/
def IsIntValued {n : ℕ} (p : RatPoly n) : Prop :=
  ∀ a : Fin n → ℤ, ∃ k : ℤ, eval (fun i => (a i : ℚ)) p = (k : ℚ)


-- @@ L52-80 verbatim
/-- The paper's ring `Int(ℤⁿ)` of integer-valued rational polynomials, represented as
a subring of `ℚ[x₁, ..., xₙ]`. -/
def IntValuedSubring (n : ℕ) : Subring (RatPoly n) where
  carrier := {p | IsIntValued p}
  zero_mem' := by
    intro a
    use 0
    simp
  one_mem' := by
    intro a
    use 1
    simp
  add_mem' := by
    intro p q hp hq a
    rcases hp a with ⟨m, hm⟩
    rcases hq a with ⟨l, hl⟩
    use m + l
    simp [hm, hl]
  neg_mem' := by
    intro p hp a
    rcases hp a with ⟨m, hm⟩
    use -m
    simp [hm]
  mul_mem' := by
    intro p q hp hq a
    rcases hp a with ⟨m, hm⟩
    rcases hq a with ⟨l, hl⟩
    use m * l
    simp [hm, hl]


-- @@ L82-83 verbatim
/-- The type of integer-valued rational polynomials in `n` variables. -/
abbrev IntegerValuedPoly (n : ℕ) : Type := IntValuedSubring n


-- @@ L85-87 verbatim
/-- Evaluate an integer-coefficient polynomial at an integer tuple. -/
noncomputable def intPolyEval {n : ℕ} (p : IntPoly n) (a : Fin n → ℤ) : ℤ :=
  eval a p


-- @@ L89-91 verbatim
/-- Evaluate a rational-coefficient polynomial at an integer tuple. -/
noncomputable def ratPolyEval {n : ℕ} (p : RatPoly n) (a : Fin n → ℤ) : ℚ :=
  eval (fun i => (a i : ℚ)) p


-- @@ L93-97 verbatim
/-- General `k`-tuple version of parametrization by one tuple of integer-coefficient
polynomials, matching `pyth.tex` lines 104--116. -/
def IntPolyTupleParametrizes {n k : ℕ} (F : Fin k → IntPoly n)
    (S : Set (Fin k → ℤ)) : Prop :=
  S = {v | ∃ a : Fin n → ℤ, ∀ i : Fin k, intPolyEval (F i) a = v i}


-- @@ L99-104 verbatim
/-- General `k`-tuple version of parametrization by one tuple of integer-valued
polynomials, matching `pyth.tex` lines 104--116. -/
def IntValuedTupleParametrizes {n k : ℕ} (F : Fin k → RatPoly n)
    (S : Set (Fin k → ℤ)) : Prop :=
  (∀ i : Fin k, IsIntValued (F i)) ∧
    S = {v | ∃ a : Fin n → ℤ, ∀ i : Fin k, ratPolyEval (F i) a = (v i : ℚ)}


-- @@ L106-111 verbatim
/-- Parametrization by a finite number of `k`-tuples of integer-coefficient
polynomials, matching `pyth.tex` lines 118--125. -/
def FiniteIntPolyTupleParametrizes {m n k : ℕ} (F : Fin m → Fin k → IntPoly n)
    (S : Set (Fin k → ℤ)) : Prop :=
  S = {v | ∃ j : Fin m, ∃ a : Fin n → ℤ, ∀ i : Fin k,
    intPolyEval (F j i) a = v i}


-- @@ L113-119 verbatim
/-- Parametrization by a finite number of `k`-tuples of integer-valued polynomials,
matching `pyth.tex` lines 118--125. -/
def FiniteIntValuedTupleParametrizes {m n k : ℕ} (F : Fin m → Fin k → RatPoly n)
    (S : Set (Fin k → ℤ)) : Prop :=
  (∀ j : Fin m, ∀ i : Fin k, IsIntValued (F j i)) ∧
    S = {v | ∃ j : Fin m, ∃ a : Fin n → ℤ, ∀ i : Fin k,
      ratPolyEval (F j i) a = (v i : ℚ)}


-- @@ L121-125 verbatim
/-- A triple of integer-coefficient polynomials parametrizes a set S ⊆ ℤ³
if S equals the image of the polynomial map ℤⁿ → ℤ³. -/
def IntPolyParametrizes {n : ℕ} (f g h : IntPoly n) (S : Set (ℤ × ℤ × ℤ)) : Prop :=
  S = {(x, y, z) | ∃ a : Fin n → ℤ,
    intPolyEval f a = x ∧ intPolyEval g a = y ∧ intPolyEval h a = z}


-- @@ L127-132 verbatim
/-- A triple of rational-coefficient polynomials parametrizes a set S ⊆ ℤ³
if each is integer-valued and S equals the image of the polynomial map. -/
def IntValuedParametrizes {n : ℕ} (f g h : RatPoly n) (S : Set (ℤ × ℤ × ℤ)) : Prop :=
  IsIntValued f ∧ IsIntValued g ∧ IsIntValued h ∧
  S = {(x, y, z) | ∃ a : Fin n → ℤ,
    ratPolyEval f a = (x : ℚ) ∧ ratPolyEval g a = (y : ℚ) ∧ ratPolyEval h a = (z : ℚ)}


-- @@ L134-134 verbatim
end LeanPool.PythagoreanPolynomialParametrization
