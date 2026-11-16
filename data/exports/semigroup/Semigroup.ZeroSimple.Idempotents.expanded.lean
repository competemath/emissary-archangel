/-
Copyright (c) 2026 Timothy Harvey and James Mitchell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timothy Harvey
-/
import Semigroup.GreensRelations.WithZero
import Semigroup.ZeroSimple.Basic


-- @@ L9-32 verbatim
/-!
# The Corner of a 0-Simple Semigroup at a Primitive Idempotent

This file proves that the corner `eSe` of a 0-simple semigroup at a primitive
idempotent `e` is a group with zero: every nonzero element of the corner has a
two-sided inverse relative to `e`, and hence is H-related to `e`.

## Main results

* `IsPrimitiveIdempotent.exists_corner_inv`: every nonzero element of the corner
  `eSe` has a two-sided inverse relative to the identity `e`.
* `IsPrimitiveIdempotent.isGreenH_of_corner`: every nonzero element of the corner
  `eSe` is H-related to `e`.

## References

* [J. M. Howie, *Fundamentals of Semigroup Theory*][howie1995]

The proofs formalized in this module closely follow the structure and logic
from lecture notes:

* J. D. Mitchell, *MT5863 Semigroup Theory* (lecture notes,
  University of St Andrews, 2026).
-/


-- @@ L34-34 verbatim
open scoped GreensRelations


-- @@ L36-36 verbatim
variable {S : Type*}


-- @@ L38-40 verbatim
/-! The nonvanishing helpers formerly here now live in
`Semigroup.GreensRelations.WithZero`; the retraction and factorization helpers
live in `Semigroup.Rees.Basic`. -/


-- @@ L42-42 verbatim
/-! ### The corner group -/


-- @@ L44-44 verbatim
section Corner


-- @@ L46-46 verbatim
variable [SemigroupWithZero S]


-- @@ L48-109 verbatim
/-- **The corner `eSe` is a group with zero**: in a 0-simple semigroup with
primitive idempotent `e`, every nonzero `a` with `e * a = a` and `a * e = a`
has a two-sided inverse `b` relative to the identity `e`, itself lying in the
corner. This is the crux where primitivity is used. -/
theorem IsPrimitiveIdempotent.exists_corner_inv (hS : IsZeroSimple S) {e : S}
    (he : IsPrimitiveIdempotent e) {a : S} (ha : a ≠ 0)
    (hea : e * a = a) (hae : a * e = a) :
    ∃ b : S, e * b = b ∧ b * e = b ∧ a * b = e ∧ b * a = e := by
  have hee := he.isIdempotentElem.eq
  -- decompose `e = u * a * v` and pad the factors into the corner
  obtain ⟨u, v, huv⟩ := hS.exists_eq_mul_mul ha e
  set p := e * u * e with hp
  set q := e * v * e with hq
  have hpaq : p * a * q = e := by
    calc p * a * q = e * (u * (e * a * e) * v) * e := by
          simp only [hp, hq, mul_assoc]
      _ = e * (u * a * v) * e := by rw [hea, hae]
      _ = e := by rw [← huv, hee, hee]
  have hep : e * p = p := by rw [hp, ← mul_assoc, ← mul_assoc, hee]
  have hpe : p * e = p := by rw [hp, mul_assoc, mul_assoc, hee, ← mul_assoc]
  have heq : e * q = q := by rw [hq, ← mul_assoc, ← mul_assoc, hee]
  have hqe : q * e = q := by rw [hq, mul_assoc, mul_assoc, hee, ← mul_assoc]
  -- first primitivity application: `a * q * p = e`
  have haqp : a * q * p = e := by
    set f := a * q * p with hf
    have hff : IsIdempotentElem f := by
      change f * f = f
      calc f * f = a * q * (p * a * q) * p := by simp only [hf, mul_assoc]
        _ = a * q * e * p := by rw [hpaq]
        _ = f := by rw [hf, mul_assoc a, mul_assoc a, hqe, ← mul_assoc a]
    have hf0 : f ≠ 0 := by
      intro h0
      apply he.ne_zero
      calc e = p * a * q * (p * a * q) := by rw [hpaq, hee]
        _ = p * f * (a * q) := by simp only [hf, mul_assoc]
        _ = 0 := by rw [h0, mul_zero, zero_mul]
    have hef : e * f = f := by rw [hf, ← mul_assoc, ← mul_assoc e a q, hea]
    have hfe : f * e = f := by rw [hf, mul_assoc, mul_assoc, hpe, ← mul_assoc]
    exact he.eq_of_le f hff hf0 hef hfe
  -- second primitivity application: `q * p * a = e`
  have hqpa : q * p * a = e := by
    set g := q * p * a with hg
    have hgg : IsIdempotentElem g := by
      change g * g = g
      calc g * g = q * (p * a * q) * (p * a) := by simp only [hg, mul_assoc]
        _ = q * e * (p * a) := by rw [hpaq]
        _ = g := by rw [hqe, hg, mul_assoc q p a]
    have hg0 : g ≠ 0 := by
      intro h0
      apply he.ne_zero
      calc e = p * a * q * (p * a * q) := by rw [hpaq, hee]
        _ = p * a * g * q := by simp only [hg, mul_assoc]
        _ = 0 := by rw [h0, mul_zero, zero_mul]
    have heg : e * g = g := by rw [hg, ← mul_assoc, ← mul_assoc, heq]
    have hge : g * e = g := by rw [hg, mul_assoc, hae]
    exact he.eq_of_le g hgg hg0 heg hge
  -- the inverse is `q * p`
  refine ⟨q * p, ?_, ?_, ?_, ?_⟩
  · rw [← mul_assoc, heq]
  · rw [mul_assoc, hpe]
  · rw [← mul_assoc]; exact haqp
  · rw [mul_assoc]; rw [mul_assoc] at hqpa; exact hqpa


-- @@ L111-117 expanded
/-- Every nonzero element of the corner `eSe` is H-related to `e`. -/
theorem IsPrimitiveIdempotent.isGreenH_of_corner (hS : IsZeroSimple S) {e : S}
    (he : IsPrimitiveIdempotent e) {a : S} (ha : a ≠ 0) (hea : e * a = a) (hae : a * e = a) :
    IsGreenH a e :=
  by
  obtain ⟨b, _, _, hab, hba⟩ := he.exists_corner_inv hS ha hea hae
  exact ⟨⟨Or.inr ⟨a, hae.symm⟩, Or.inr ⟨b, hba.symm⟩⟩, ⟨Or.inr ⟨a, hea.symm⟩, Or.inr ⟨b, hab.symm⟩⟩⟩


-- @@ L119-119 verbatim
end Corner
