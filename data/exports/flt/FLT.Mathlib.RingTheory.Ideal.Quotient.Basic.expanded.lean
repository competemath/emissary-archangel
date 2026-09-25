/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, Kevin Buzzard
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Defs


-- @@ L10-14 verbatim
/-!
# Basic

Material destined for Mathlib.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
variable {R : Type*} [Ring R] (I : Ideal R) [I.IsTwoSided]


-- @@ L20-21 verbatim
theorem Ideal.Quotient.out_sub (x : R) : (Ideal.Quotient.mk I x).out - x ∈ I := by
  rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]
