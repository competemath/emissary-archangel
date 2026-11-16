/-
Copyright (c) 2026 Timothy Harvey and James Mitchell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timothy Harvey
-/
import Semigroup.GreensRelations.Classes
import Semigroup.GreensRelations.Idempotents


-- @@ L9-39 verbatim
/-!
# The H-Class of an Idempotent

This file develops the group-like structure of the H-class of an idempotent `e`
in a semigroup: `e` is a two-sided identity on its H-class, the H-class is closed
under multiplication, and every element has a two-sided inverse relative to `e`
inside the H-class.

The packaging of these facts as a subgroup (`IsSubgroupWith`) and Green's
theorem — that this subgroup is the *greatest* subgroup with identity `e` —
live in `Semigroup.GreensTheorem.Subgroups.Basic`.

## Main results

* `IsGreenH.mul_left_eq_self`, `IsGreenH.mul_right_eq_self`: an idempotent is a
  two-sided identity on its H-class.
* `IsGreenH.mul_mem`: the H-class of an idempotent is closed under multiplication.
* `IsGreenH.exists_inv`: every element of the H-class of an idempotent `e` has a
  two-sided inverse relative to `e` inside the H-class.
* `IsGreenH.eqvClass_eq_of_isGreenH`: H-related elements have the same H-class.

## References

* [J. M. Howie, *Fundamentals of Semigroup Theory*][howie1995]

The proofs formalized in this module closely follow the structure and logic
from lecture notes:

* J. D. Mitchell, *MT5863 Semigroup Theory* (lecture notes,
  University of St Andrews, 2026).
-/


-- @@ L41-41 verbatim
open scoped GreensRelations


-- @@ L43-43 verbatim
variable {S : Type*} [Semigroup S] {e x y : S}


-- @@ L45-45 verbatim
namespace IsGreenH


-- @@ L47-50 expanded
/-- An idempotent `e` is a left identity on its H-class: if `x H e`, then `e * x = x`. -/
theorem mul_left_eq_self (he : IsIdempotentElem e) (hx : IsGreenH x e) : e * x = x :=
  IsGreenRightDvd.idem_mul_eq_self he hx.2.1


-- @@ L52-55 expanded
/-- An idempotent `e` is a right identity on its H-class: if `x H e`, then `x * e = x`. -/
theorem mul_right_eq_self (he : IsIdempotentElem e) (hx : IsGreenH x e) : x * e = x :=
  IsGreenLeftDvd.mul_idem_eq_self he hx.1.1


-- @@ L57-66 expanded
/-- The H-class of an idempotent is closed under multiplication. -/
theorem mul_mem (he : IsIdempotentElem e) (hx : IsGreenH x e) (hy : IsGreenH y e) :
    IsGreenH (x * y) e := by
  constructor
  · have h1 : IsGreenL (x * y) (e * y) := IsGreenL.mul_right y hx.1
    rw [mul_left_eq_self he hy] at h1
    exact h1.trans hy.1
  · have h2 : IsGreenR (x * y) (x * e) := IsGreenR.mul_left x hy.2
    rw [mul_right_eq_self he hx] at h2
    exact h2.trans hx.2


-- @@ L68-94 expanded
/-- Every element `x` of the H-class of an idempotent `e` has a two-sided inverse
relative to `e` lying in the same H-class: there is `y` with `y H e`, `x * y = e`, and
`y * x = e`. -/
theorem exists_inv (he : IsIdempotentElem e) (hx : IsGreenH x e) :
    ∃ y, IsGreenH y e ∧ x * y = e ∧ y * x = e :=
  by
  have hex : e * x = x := mul_left_eq_self he hx
  have hxe : x * e = x := mul_right_eq_self he hx
  obtain ⟨u, hu⟩ := IsGreenLeftDvd.exists_eq_mul_of_idem he hx.1.2
  obtain ⟨v, hv⟩ := IsGreenRightDvd.exists_eq_mul_of_idem he hx.2.2
  have hyx : e * u * e * x = e := by rw [mul_assoc (e * u), hex, mul_assoc, ← hu, he.eq]
  have hxy' : x * (e * v * e) = e := by rw [← mul_assoc, ← mul_assoc, hxe, ← hv, he.eq]
  have h0 : e * u * e * e = e * u * e := by rw [mul_assoc (e * u), he.eq]
  have hyy' : e * u * e = e * v * e :=
    calc
      e * u * e = e * u * e * e := h0.symm
      _ = e * u * e * (x * (e * v * e)) := by rw [hxy']
      _ = e * u * e * x * (e * v * e) := (mul_assoc _ _ _).symm
      _ = e * (e * v * e) := by rw [hyx]
      _ = e * v * e := by rw [← mul_assoc, ← mul_assoc, he.eq]
  have hxy : x * (e * u * e) = e := by rw [hyy']; exact hxy'
  refine ⟨e * u * e, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, hxy, hyx⟩
  · exact Or.inr ⟨e * u, rfl⟩
  · exact Or.inr ⟨x, hxy.symm⟩
  · exact Or.inr ⟨u * e, by rw [mul_assoc]⟩
  · exact Or.inr ⟨x, hyx.symm⟩


-- @@ L96-99 expanded
/-- H-related elements have the same H-class. -/
theorem eqvClass_eq_of_isGreenH (h : IsGreenH x y) : IsGreenH.eqvClass x = IsGreenH.eqvClass y :=
  Set.ext fun _ => ⟨fun hz => hz.trans h, fun hz => hz.trans h.symm⟩


-- @@ L101-101 verbatim
end IsGreenH
