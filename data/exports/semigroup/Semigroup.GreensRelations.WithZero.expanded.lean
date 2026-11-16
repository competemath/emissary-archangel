/-
Copyright (c) 2026 Timothy Harvey and James Mitchell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timothy Harvey
-/
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.GroupWithZero.Defs
import Semigroup.GreensRelations.Defs


-- @@ L10-33 verbatim
/-!
# Green's Relations in a Semigroup with Zero

Nonvanishing lemmas for Green's relations in a `SemigroupWithZero`: elements
related to a nonzero element are nonzero, and the product of an L-related and an
R-related element of a nonzero idempotent is nonzero (the nonvanishing half of
the location lemma). These facts are general — no simplicity assumption — and are
consumed by the 0-simple theory in `Semigroup.ZeroSimple`.

## Main results

* `ne_zero_of_isGreenL`, `ne_zero_of_isGreenR`, `ne_zero_of_isGreenH`: elements
  Green-related to a nonzero element are nonzero.
* `mul_ne_zero_of_isGreenL_of_isGreenR`: if `x` is L-related and `y` is R-related
  to a nonzero idempotent `e`, then `x * y ≠ 0`.

## References

The proofs formalized in this module closely follow the structure and logic
from lecture notes:

* J. D. Mitchell, *MT5863 Semigroup Theory* (lecture notes,
  University of St Andrews, 2026).
-/


-- @@ L35-35 verbatim
open scoped GreensRelations


-- @@ L37-37 verbatim
variable {S : Type*} [SemigroupWithZero S]


-- @@ L39-44 expanded
/-- An element L-related to a nonzero element is nonzero. -/
theorem ne_zero_of_isGreenL {x e : S} (h : IsGreenL x e) (he : e ≠ 0) : x ≠ 0 :=
  by
  rintro rfl
  rcases h.2 with h0 | ⟨c, hc⟩
  · exact he h0
  · exact he (by rw [hc, mul_zero])


-- @@ L46-51 expanded
/-- An element R-related to a nonzero element is nonzero. -/
theorem ne_zero_of_isGreenR {x e : S} (h : IsGreenR x e) (he : e ≠ 0) : x ≠ 0 :=
  by
  rintro rfl
  rcases h.2 with h0 | ⟨c, hc⟩
  · exact he h0
  · exact he (by rw [hc, zero_mul])


-- @@ L53-55 expanded
/-- An element H-related to a nonzero element is nonzero. -/
theorem ne_zero_of_isGreenH {x e : S} (h : IsGreenH x e) (he : e ≠ 0) : x ≠ 0 :=
  ne_zero_of_isGreenL h.1 he


-- @@ L57-75 expanded
/-- **Location lemma (nonvanishing half)**: if `x` is L-related and `y` is
R-related to a nonzero idempotent `e`, then `x * y ≠ 0`. -/
theorem mul_ne_zero_of_isGreenL_of_isGreenR {e x y : S} (he : IsIdempotentElem e) (he0 : e ≠ 0)
    (hx : IsGreenL x e) (hy : IsGreenR y e) : x * y ≠ 0 :=
  by
  intro hxy
  rcases hx.2 with hex | ⟨c, hc⟩ <;> rcases hy.2 with hey | ⟨d, hd⟩
  · exact he0 (by rw [← hxy, ← hex, ← hey, he.eq])
  ·
    exact
      he0
        (by
          calc
            e = x * (y * d) := by rw [← hex, ← hd, he.eq]
            _ = x * y * d := (mul_assoc x y d).symm
            _ = 0 := by rw [hxy, zero_mul])
  ·
    exact
      he0
        (by
          calc
            e = c * x * y := by rw [← hc, ← hey, he.eq]
            _ = c * (x * y) := (mul_assoc c x y)
            _ = 0 := by rw [hxy, mul_zero])
  ·
    exact
      he0
        (by
          calc
            e = c * x * (y * d) := by rw [← hc, ← hd, he.eq]
            _ = c * (x * y) * d := by simp only [mul_assoc]
            _ = 0 := by rw [hxy, mul_zero, zero_mul])

