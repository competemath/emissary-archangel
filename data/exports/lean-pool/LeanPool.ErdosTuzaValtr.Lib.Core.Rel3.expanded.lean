/-
Copyright (c) 2026 Jineon Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek
-/
module

public import Mathlib.Order.OrderDual


-- @@ L10-14 verbatim
/-!
# LeanPool.ErdosTuzaValtr.Lib.Core.Rel3

Imported Lean Pool material for `LeanPool.ErdosTuzaValtr.Lib.Core.Rel3`.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
universe u v


-- @@ L20-20 verbatim
open OrderDual


-- @@ L22-24 verbatim
/-- Mirror a binary relation/function to the order dual, swapping argument order. -/
def Mirror2 {α : Type u} {β : Sort v} (f : α → α → β) : αᵒᵈ → αᵒᵈ → β := fun a b =>
  f (ofDual b) (ofDual a)


-- @@ L26-28 verbatim
/-- Mirror a ternary relation/function to the order dual, reversing argument order. -/
def Mirror3 {α : Type u} {β : Sort v} (f : α → α → α → β) : αᵒᵈ → αᵒᵈ → αᵒᵈ → β :=
  fun a b c => f (ofDual c) (ofDual b) (ofDual a)


-- @@ L30-33 verbatim
/-- Decidability of a ternary relation: each instance is decidable. -/
@[reducible]
def DecidableRel3 {α : Sort u} (r : α → α → α → Prop) :=
  ∀ a b c : α, Decidable (r a b c)


-- @@ L35-38 verbatim
/-- Transport decidability of a binary relation to its mirror. -/
@[reducible]
def DecidableRel.Mirror2 {α : Type u} {r : α → α → Prop} (dec : DecidableRel r) :
    DecidableRel (Mirror2 r) := fun a b => dec (ofDual b) (ofDual a)


-- @@ L40-44 verbatim
/-- Transport decidability of a ternary relation to its mirror. -/
@[reducible]
def DecidableRel3.Mirror3 {α : Type u} {r : α → α → α → Prop}
    (dec : DecidableRel3 r) : DecidableRel3 (Mirror3 r) := fun a b c =>
  dec (ofDual c) (ofDual b) (ofDual a)
