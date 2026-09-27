/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import Mathlib.Order.OmegaCompletePartialOrder


-- @@ L10-14 verbatim
/-!
# LeanPool.QuasiBorelSpaces.OmegaCompletePartialOrder.Chain.Const

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.OmegaCompletePartialOrder.Chain.Const`.
-/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
namespace OmegaCompletePartialOrder.Chain


-- @@ L21-21 verbatim
variable {A : Type*} [Preorder A]


-- @@ L23-25 verbatim
/-- The chain that always returns the same value. -/
def const (x : A) : Chain A where
  toOrderHom := OrderHom.const ℕ x


-- @@ L27-29 verbatim
@[simp]
lemma const_apply (x : A) (n : ℕ) : const x n = x := by
  rfl


-- @@ L31-31 verbatim
end OmegaCompletePartialOrder.Chain
