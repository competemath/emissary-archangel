/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/
module

public import Mathlib.RingTheory.Congruence.Basic
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow


-- @@ L12-16 verbatim
/-!
# LeanPool.BrauerGroupNew.Mathlib.RingTheory.Congruence.Basic

Imported Lean Pool material for `LeanPool.BrauerGroupNew.Mathlib.RingTheory.Congruence.Basic`.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
open Function


-- @@ L22-26 verbatim
/-!
# Ring congruence quotient compatibility

This file restores the upstream quotient-map names used by the Brauer group port.
-/


-- @@ L28-28 verbatim
namespace RingCon


-- @@ L30-30 verbatim
variable {α R : Type*}


-- @@ L32-42 verbatim
instance instModuleQuotientOfIsScalarTowerLeanPool [Semiring α] [NonAssocSemiring R]
    [Module α R] [IsScalarTower α R R]
    (c : RingCon R) : Module α c.Quotient where
  zero_smul x := by
    induction x using Quotient.ind
    change ⟦_⟧ = ⟦_⟧
    simp
  add_smul r s x := by
    induction x using Quotient.ind
    change ⟦_⟧ = ⟦_⟧
    simp [add_smul]


-- @@ L44-49 verbatim
variable (α) in
/-- The quotient map as a linear map. -/
def mkL [Semiring α] [NonAssocSemiring R] [Module α R] [IsScalarTower α R R]
    (c : RingCon R) : R →ₗ[α] c.Quotient where
  __ := c.mk'
  map_smul' _ _ := rfl


-- @@ L51-52 verbatim
lemma algebraMap_def [CommSemiring α] [Semiring R] [Algebra α R] (c : RingCon R) :
    algebraMap α c.Quotient = c.mk'.comp (algebraMap α R) := rfl


-- @@ L54-57 verbatim
variable (α) in
/-- The quotient map as an algebra homomorphism. -/
def mkA [CommSemiring α] [Semiring R] [Algebra α R] (c : RingCon R) : R →ₐ[α] c.Quotient :=
  c.mkₐ (α := α)


-- @@ L59-59 verbatim
end RingCon
