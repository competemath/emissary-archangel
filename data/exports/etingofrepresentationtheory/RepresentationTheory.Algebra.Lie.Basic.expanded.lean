/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.Algebra.Lie.Basic
import RepresentationTheory.Alignment.Attribute


-- @@ L10-10 verbatim
/-! # Lie ring auxiliaries -/


-- @@ L12-12 verbatim
namespace RepresentationTheory.Algebra.Lie.Basic


-- @@ L14-14 verbatim
namespace LieRing


-- @@ L16-19 verbatim
/-- An auxiliary type depending on a commutative ring and a Lie ring. -/
@[source_ref "Chapter2/Definition2.9.1" (role := supporting)]
abbrev AuxiliaryType (k : Type*) (L : Type*) [CommRing k] [LieRing L] :=
  LieAlgebra k L


-- @@ L21-21 verbatim
variable {k L : Type*} [Field k] [LieRing L] [LieAlgebra k L]


-- @@ L23-29 verbatim
/-- The cyclic sum of the three iterated brackets of elements of a Lie ring is zero. -/
@[source_ref "Chapter2/Definition2.9.1" (role := primary)]
theorem cyclic_iterated_bracket_sum_eq_zero (a b c : L) :
    ⁅⁅a, b⁆, c⁆ + ⁅⁅b, c⁆, a⁆ + ⁅⁅c, a⁆, b⁆ = 0 := by
  rw [← neg_eq_zero]
  simpa only [neg_add_rev, neg_neg, lie_skew, add_comm, add_left_comm, add_assoc] using
    lie_jacobi c a b


-- @@ L31-31 verbatim
end LieRing


-- @@ L33-33 verbatim
end RepresentationTheory.Algebra.Lie.Basic
