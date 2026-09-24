/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Conejero
-/
module

public import Mathlib.Algebra.Polynomial.RingDivision


-- @@ L10-19 verbatim
/-!
# Bridge lemmas for `Polynomial.divByMonic`

R-linearity of `divByMonic` in the dividend, dual to Mathlib's
`Polynomial.smul_modByMonic`.

Note, there's a PR to Mathlib that includes this result and this file
should be deleted if/when that PR is accepted:
https://github.com/leanprover-community/mathlib4/pull/39868
-/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
namespace Polynomial


-- @@ L25-33 verbatim
theorem smul_divByMonic {R : Type*} [CommRing R]
    (c : R) (p q : R[X]) : c • p /ₘ q = c • (p /ₘ q) := by
  by_cases hq : q.Monic
  · rcases subsingleton_or_nontrivial R with hR | hR
    · exact Subsingleton.elim _ _
    · exact (div_modByMonic_unique (c • (p /ₘ q)) (c • (p %ₘ q)) hq
        ⟨by rw [mul_smul_comm, ← smul_add, modByMonic_add_div],
         (degree_smul_le _ _).trans_lt (degree_modByMonic_lt _ hq)⟩).1
  · simp [divByMonic_eq_of_not_monic _ hq]


-- @@ L35-35 verbatim
end Polynomial
