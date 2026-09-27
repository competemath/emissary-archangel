/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/
module

public import Mathlib.RingTheory.TwoSidedIdeal.Lattice


-- @@ L10-14 verbatim
/-!
# LeanPool.BrauerGroupNew.Mathlib.RingTheory.TwoSidedIdeal.Lattice

Imported Lean Pool material for `LeanPool.BrauerGroupNew.Mathlib.RingTheory.TwoSidedIdeal.Lattice`.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
namespace TwoSidedIdeal

-- @@ L19-19 verbatim
variable {R : Type*} [NonUnitalNonAssocRing R] {I J : TwoSidedIdeal R} {x : R}


-- @@ L21-21 verbatim
@[simp] lemma ringCon_inj : I.ringCon = J.ringCon ↔ I = J := ringCon_injective.eq_iff


-- @@ L23-23 verbatim
@[simp] lemma ringCon_eq_top : I.ringCon = ⊤ ↔ I = ⊤ := by rw [← top_ringCon, ringCon_inj]


-- @@ L25-25 verbatim
end TwoSidedIdeal
