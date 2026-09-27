/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/
module

public import Mathlib.Order.WithBotTop


-- @@ L10-17 verbatim
/-! # Belnap levels

## References

* [N. D. Belnap, *A Useful Four-Valued Logic*][Belnap1977]
* [Ghica, Kaye, and Sprunger, *A Complete Theory of Sequential Digital Circuits*][Ghica2025]

-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
namespace Circuit


-- @@ L23-25 verbatim
/-- The Belnap four-valued logic lattice on `Bool`, with a bottom (no information) and a
top (conflicting information) adjoined. -/
def BelnapLevel := WithBotTop Bool


-- @@ L27-27 verbatim
namespace BelnapLevel


-- @@ L29-30 verbatim
instance : Coe (WithBotTop Bool) (BelnapLevel) where
  coe l := l


-- @@ L32-33 verbatim
instance : Bot BelnapLevel where
  bot := .none


-- @@ L35-36 verbatim
instance : Top BelnapLevel where
  top := .some .none


-- @@ L38-45 verbatim
/-- The information ordering on Belnap levels: `⊥` is below everything, everything is below `⊤`,
and the two classical values are only related to themselves. -/
@[inline]
def le : BelnapLevel → BelnapLevel → Prop
  | ⊥, _ => true
  | _, ⊤ => true
  | .some (.some x), .some (.some y) => x == y
  | _, _ => false


-- @@ L47-48 verbatim
lemma le_refl : ∀ (a : BelnapLevel), a.le a := by
  rintro (_ | (_ | (_ | _))) <;> trivial


-- @@ L50-51 verbatim
lemma le_trans : ∀ (a b c : BelnapLevel), a.le b → b.le c → a.le c := by
  rintro (_ | (_ | a)) (_ | (_ | b)) (_ | (_ | c)) hab hbc <;> simp_all [le]


-- @@ L53-56 verbatim
instance : Preorder BelnapLevel where
  le
  le_refl
  le_trans


-- @@ L58-59 verbatim
lemma le_antisymm : ∀ (a b : BelnapLevel), a ≤ b → b ≤ a → a = b := by
  rintro (_ | (_ | a)) (_ | (_ | b)) hab hba <;> simp_all [LE.le, le] <;> rfl


-- @@ L61-67 verbatim
/-- The join (least upper bound) on Belnap levels in the information order. -/
def sup : BelnapLevel → BelnapLevel → BelnapLevel
  | .none, x => x
  | x, .none => x
  | .some .none, _ => .some .none
  | _, .some .none => .some .none
  | .some (.some x), .some (.some y) => if x == y then .some (.some x) else .some .none


-- @@ L69-70 verbatim
lemma le_sup_left : ∀ (a b : BelnapLevel), a ≤ a.sup b:= by
  rintro (_ | (_ | (_ | _))) (_ | (_ | (_ | _))) <;> trivial


-- @@ L72-73 verbatim
lemma le_sup_right : ∀ (a b : BelnapLevel), b ≤ a.sup b := by
  rintro (_ | (_ | (_ | _))) (_ | (_ | (_ | _))) <;> trivial


-- @@ L75-76 verbatim
lemma sup_le : ∀ (a b c : BelnapLevel), a ≤ c → b ≤ c → a.sup b ≤ c  := by
  rintro (_ | (_ | (_ | _))) (_ | (_ | (_ | _))) (_ | (_ | (_ | _))) hac hbc <;> trivial


-- @@ L78-83 verbatim
instance : SemilatticeSup BelnapLevel where
  le_antisymm
  sup
  le_sup_left
  le_sup_right
  sup_le


-- @@ L85-94 verbatim
/-- Logical AND. -/
@[inline]
def and (a b : BelnapLevel) : BelnapLevel := match a, b with
  | .some (.some false), _ => false
  | _, .some (.some false) => false
  | .some (.some true), x => x
  | x, .some (.some true) => x
  | ⊥, ⊥ => ⊥
  | ⊤, ⊤ => ⊤
  | _, _ => false


-- @@ L96-105 verbatim
/-- Logical OR. -/
@[inline]
def or (a b : BelnapLevel) : BelnapLevel := match a, b with
  | .some (.some true), _ => true
  | _, .some (.some true) => true
  | .some (.some false), x => x
  | x, .some (.some false) => x
  | ⊥, ⊥ => ⊥
  | ⊤, ⊤ => ⊤
  | _, _ => true


-- @@ L107-111 verbatim
/-- Logical NOT. -/
@[inline]
def not : BelnapLevel → BelnapLevel
  | .some (.some b) => !b
  | x => x


-- @@ L113-113 verbatim
end BelnapLevel


-- @@ L115-115 verbatim
end Circuit
