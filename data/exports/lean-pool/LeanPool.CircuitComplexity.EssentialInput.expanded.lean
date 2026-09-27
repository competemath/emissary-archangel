/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import LeanPool.CircuitComplexity.Basic
public import Mathlib.Data.Fintype.Pi


-- @@ L11-20 verbatim
/-! # Essential Inputs

This module defines the notion of essential (non-redundant) input variables
for a Boolean function.

## Main definitions

* `IsEssentialInput` — a function depends on a particular input variable
* `EssentialInputs` — the set of essential input variables
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
namespace CircuitComplexity



-- @@ L27-30 verbatim
/-- A function `f` depends on input variable `i` if flipping that bit
    can change some output. -/
def IsEssentialInput {N M : Nat} (f : BitString N → BitString M) (i : Fin N) : Prop :=
  ∃ x : BitString N, f x ≠ f (Function.update x i (!x i))


-- @@ L32-34 verbatim
instance {N M : Nat} {f : BitString N → BitString M} {i : Fin N} :
    Decidable (IsEssentialInput f i) :=
  inferInstanceAs (Decidable (∃ x, f x ≠ f (Function.update x i (!x i))))


-- @@ L36-38 verbatim
/-- The set of input variables that `f` depends on. -/
def EssentialInputs {N M : Nat} (f : BitString N → BitString M) : Finset (Fin N) :=
  Finset.univ.filter (IsEssentialInput f)


-- @@ L40-40 verbatim
end CircuitComplexity
