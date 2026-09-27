/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic


-- @@ L10-14 verbatim
/-!
# LeanPool.BrauerGroupNew.Mathlib.Algebra.Algebra.Subalgebra.Basic

Imported Lean Pool material for `LeanPool.BrauerGroupNew.Mathlib.Algebra.Algebra.Subalgebra.Basic`.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
namespace Subalgebra

-- @@ L19-19 verbatim
variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] {L S T U : Subalgebra R A}


-- @@ L21-21 verbatim
lemma le_centralizer_self : L ≤ centralizer R L ↔ ∀ x ∈ L, ∀ y ∈ L, x * y = y * x := forall₂_comm

-- @@ L22-22 verbatim
variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] {S T U : Subalgebra R A}


-- @@ L24-25 verbatim
@[simp] lemma inclusion_comp_inclusion (hST : S ≤ T) (hTU : T ≤ U) :
    (inclusion hTU).comp (inclusion hST) = inclusion (hST.trans hTU) := rfl


-- @@ L27-27 verbatim
end Subalgebra
