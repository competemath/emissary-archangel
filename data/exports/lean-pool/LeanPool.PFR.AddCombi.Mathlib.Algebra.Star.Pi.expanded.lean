/-
Copyright (c) 2026 AddCombi contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AddCombi contributors
-/

module

public import LeanPool.PFR.AddCombi.Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Star.Basic


-- @@ L12-14 verbatim
/-!
# Star operations on indicator functions
-/


-- @@ L16-16 verbatim
open scoped ComplexConjugate Indicator



-- @@ L19-19 verbatim
namespace Set

-- @@ L20-20 verbatim
variable {α R : Type*} [CommSemiring R] [StarRing R]


-- @@ L22-25 expanded
@[simp]
public lemma conj_indicator_one_apply (s : Set α) (a : α) :
    conj ((Set.indicator s fun _ ↦ (1 : R)) a) = (Set.indicator s fun _ ↦ (1 : _)) a := by
  classical simp [indicator_apply]


-- @@ L29-29 verbatim
end Set
