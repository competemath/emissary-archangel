/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/
module

public import LeanPool.Circuitlib.Circuit.Belnap.Level
public import LeanPool.Circuitlib.Circuit.Wires


-- @@ L11-18 verbatim
/-! # Belnap circuits

## References

* [N. D. Belnap, *A Useful Four-Valued Logic*][Belnap1977]
* [Ghica, Kaye, and Sprunger, *A Complete Theory of Sequential Digital Circuits*][Ghica2025]

-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
namespace Circuit


-- @@ L24-24 verbatim
namespace Belnap


-- @@ L26-28 verbatim
/-- The AND wire-function on a pair of Belnap-valued wires. -/
@[inline]
def and (w : Wires BelnapLevel 2) : Wires BelnapLevel 1 := #v[(w.get 0).and (w.get 1)]


-- @@ L30-38 verbatim
@[simp]
lemma and_leq
    {a₁ a₂ b₁ b₂ : BelnapLevel}
    (h0 : a₁ ≤ b₁)
    (h1 : a₂ ≤ b₂) :
    a₁.and a₂ ≤ b₁.and b₂ := by
  revert a₁ a₂ b₁ b₂
  rintro (_ | (_ | (_ | _))) (_ | (_ | (_ | _))) (_ | (_ | (_ | _))) (_ | (_ | (_ | _))) h0 h1 <;>
    first | exact h0 | exact h1 | rfl


-- @@ L40-44 verbatim
@[simp]
lemma and_monotonic : Monotone and := by
  intro a b hab i
  obtain rfl : i = 0 := by ext; omega
  exact and_leq (hab 0) (hab 1)


-- @@ L46-48 verbatim
/-- The OR wire-function on a pair of Belnap-valued wires. -/
@[inline]
def or (w : Wires BelnapLevel 2) : Wires BelnapLevel 1 := #v[(w.get 0).or (w.get 1)]


-- @@ L50-58 verbatim
@[simp]
lemma or_leq
    {a₁ a₂ b₁ b₂ : BelnapLevel}
    (h0 : a₁ ≤ b₁)
    (h1 : a₂ ≤ b₂) :
    a₁.or a₂ ≤ b₁.or b₂ := by
  revert a₁ a₂ b₁ b₂
  rintro (_ | (_ | (_ | _))) (_ | (_ | (_ | _))) (_ | (_ | (_ | _))) (_ | (_ | (_ | _))) h0 h1 <;>
    first | exact h0 | exact h1 | rfl


-- @@ L60-64 verbatim
@[simp]
lemma or_monotonic : Monotone or := by
  intro a b hab i
  obtain rfl : i = 0 := by ext; omega
  exact or_leq (hab 0) (hab 1)


-- @@ L66-68 verbatim
/-- The NOT wire-function on a single Belnap-valued wire. -/
@[inline]
def not (w : Wires BelnapLevel 1) : Wires BelnapLevel 1 := #v[ (w.get 0).not ]


-- @@ L70-73 verbatim
@[simp]
lemma not_leq {x y : BelnapLevel} (h : x ≤ y) : x.not ≤ y.not := by
  revert x y
  rintro (_ | (_ | (_ | _))) (_ | (_ | (_ | _))) h <;> exact h


-- @@ L75-79 verbatim
@[simp]
lemma not_monotonic : Monotone not := by
  intro a b hab i
  obtain rfl : i = 0 := by ext; omega
  exact not_leq (hab 0)


-- @@ L81-81 verbatim
end Belnap


-- @@ L83-83 verbatim
end Circuit
