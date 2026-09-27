/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Vorspiel.Vorspiel
import Mathlib.Algebra.Order.Ring.Nat


-- @@ L11-11 verbatim
/-! # Basic -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
namespace Fin


-- @@ L18-19 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
@[inline] def addCast (m) : Fin n → Fin (m + n) := castLE <| Nat.le_add_left n m


-- @@ L21-21 verbatim
@[simp] lemma addCast_val (i : Fin n) : (i.addCast m : ℕ) = i := rfl


-- @@ L23-23 verbatim
end Fin


-- @@ L25-25 verbatim
namespace Matrix


-- @@ L27-27 verbatim
variable {α : Type*}


-- @@ L29-30 verbatim
@[simp] lemma appeendr_addCast (u : Fin m → α) (v : Fin n → α) (i : Fin m) :
    appendr u v (i.addCast n) = u i := by simp [appendr, vecAppend_eq_ite]


-- @@ L32-33 verbatim
@[simp] lemma appeendr_addNat (u : Fin m → α) (v : Fin n → α) (i : Fin n) :
    appendr u v (i.addNat m) = v i := by simp [appendr, vecAppend_eq_ite]


-- @@ L35-35 verbatim
end Matrix
