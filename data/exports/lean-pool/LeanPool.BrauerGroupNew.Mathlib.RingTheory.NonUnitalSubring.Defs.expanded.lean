/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/
module

public import Mathlib.RingTheory.NonUnitalSubring.Defs


-- @@ L10-14 verbatim
/-!
# LeanPool.BrauerGroupNew.Mathlib.RingTheory.NonUnitalSubring.Defs

Imported Lean Pool material for `LeanPool.BrauerGroupNew.Mathlib.RingTheory.NonUnitalSubring.Defs`.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
variable {R : Type*} [NonUnitalRing R]


-- @@ L20-20 verbatim
@[simp] lemma NonUnitalSubring.carrier_eq_coe (S : NonUnitalSubring R) : S.carrier = S := rfl
