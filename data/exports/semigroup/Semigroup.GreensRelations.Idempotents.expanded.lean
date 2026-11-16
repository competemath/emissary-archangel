/-
Copyright (c) 2026 Timothy Harvey and James Mitchell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timothy Harvey
-/
import Mathlib.Algebra.Group.Idempotent
import Semigroup.GreensRelations.Defs


-- @@ L9-39 verbatim
/-!
# Green's Divisibility at an Idempotent

This file proves the basic interaction between Green's divisibility preorders and
idempotents: an idempotent is a one-sided identity on everything it divides, and a
divisibility of an idempotent by an element can always be witnessed by a genuine
multiple (the "degenerate" equality case is absorbed using `e = e * e`).

These four lemmas eliminate the pervasive two-case `rcases` on the divisibility
disjunction in downstream files: the identity laws on H-classes
(`Semigroup.GreensTheorem.HClass.Basic`), the retraction and absorption lemmas of
the Rees machinery (`Semigroup.Rees.Basic`), and the linking-pair construction
(`Semigroup.GreensLemma.Basic`) are all corollaries.

## Main results

* `IsGreenLeftDvd.mul_idem_eq_self`: if `x ≤𝓛 e` with `e` idempotent, then `x * e = x`.
* `IsGreenRightDvd.idem_mul_eq_self`: if `x ≤𝓡 e` with `e` idempotent, then `e * x = x`.
* `IsGreenLeftDvd.exists_eq_mul_of_idem`: if `e ≤𝓛 x` with `e` idempotent, then
  `e = u * x` for some `u`.
* `IsGreenRightDvd.exists_eq_mul_of_idem`: if `e ≤𝓡 x` with `e` idempotent, then
  `e = x * v` for some `v`.

## References

The proofs formalized in this module closely follow the structure and logic
from lecture notes:

* J. D. Mitchell, *MT5863 Semigroup Theory* (lecture notes,
  University of St Andrews, 2026).
-/


-- @@ L41-41 verbatim
open scoped GreensRelations


-- @@ L43-43 verbatim
variable {S : Type*} [Semigroup S] {e x : S}


-- @@ L45-45 verbatim
namespace IsGreenLeftDvd


-- @@ L47-53 expanded
/-- An idempotent is a right identity on everything it left-divides:
if `x ≤𝓛 e` and `e * e = e`, then `x * e = x`. -/
theorem mul_idem_eq_self (he : IsIdempotentElem e) (h : IsGreenLeftDvd x e) : x * e = x :=
  by
  rcases h with rfl | ⟨z, rfl⟩
  · exact he.eq
  · rw [mul_assoc, he.eq]


-- @@ L55-62 expanded
/-- A left-divisibility of an idempotent is always witnessed by a genuine multiple:
if `e ≤𝓛 x` and `e * e = e`, then `e = u * x` for some `u` (in the degenerate case
`e = x`, the witness is `e` itself). -/
theorem exists_eq_mul_of_idem (he : IsIdempotentElem e) (h : IsGreenLeftDvd e x) : ∃ u, e = u * x :=
  by
  rcases h with h | ⟨u, hu⟩
  · exact ⟨e, by rw [← h]; exact he.eq.symm⟩
  · exact ⟨u, hu⟩


-- @@ L64-64 verbatim
end IsGreenLeftDvd


-- @@ L66-66 verbatim
namespace IsGreenRightDvd


-- @@ L68-74 expanded
/-- An idempotent is a left identity on everything it right-divides:
if `x ≤𝓡 e` and `e * e = e`, then `e * x = x`. -/
theorem idem_mul_eq_self (he : IsIdempotentElem e) (h : IsGreenRightDvd x e) : e * x = x :=
  by
  rcases h with rfl | ⟨c, rfl⟩
  · exact he.eq
  · rw [← mul_assoc, he.eq]


-- @@ L76-83 expanded
/-- A right-divisibility of an idempotent is always witnessed by a genuine multiple:
if `e ≤𝓡 x` and `e * e = e`, then `e = x * v` for some `v` (in the degenerate case
`e = x`, the witness is `e` itself). -/
theorem exists_eq_mul_of_idem (he : IsIdempotentElem e) (h : IsGreenRightDvd e x) :
    ∃ v, e = x * v := by
  rcases h with h | ⟨v, hv⟩
  · exact ⟨e, by rw [← h]; exact he.eq.symm⟩
  · exact ⟨v, hv⟩


-- @@ L85-85 verbatim
end IsGreenRightDvd
