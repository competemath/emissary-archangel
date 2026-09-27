/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/
module

public import Mathlib.RingTheory.NonUnitalSubsemiring.Defs


-- @@ L10-15 verbatim
/-!
# LeanPool.BrauerGroupNew.Mathlib.RingTheory.NonUnitalSubsemiring.Defs

Imported Lean Pool material for
`LeanPool.BrauerGroupNew.Mathlib.RingTheory.NonUnitalSubsemiring.Defs`.
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
variable {R : Type*} [NonUnitalSemiring R]


-- @@ L21-22 verbatim
@[simp]
lemma NonUnitalSubsemiring.carrier_eq_coe (S : NonUnitalSubsemiring R) : S.carrier = S := rfl
