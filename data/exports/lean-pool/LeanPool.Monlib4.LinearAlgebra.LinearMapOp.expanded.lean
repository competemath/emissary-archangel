/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Algebra.Opposite


-- @@ L10-14 verbatim
/-!
# LeanPool.Monlib4.LinearAlgebra.LinearMapOp

Imported Lean Pool material for `LeanPool.Monlib4.LinearAlgebra.LinearMapOp`.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-25 verbatim
/-- Push a semilinear map between modules through the multiplicative opposite. -/
@[simps]
def LinearMap.op {R S : Type*} [Semiring R] [Semiring S] {σ : R →+* S}
  {M M₂ : Type*} [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂]
  (f : M →ₛₗ[σ] M₂) : Mᵐᵒᵖ →ₛₗ[σ] M₂ᵐᵒᵖ where
    toFun x := MulOpposite.op (f (MulOpposite.unop x))
    map_add' _ _ := by simp only [MulOpposite.unop_add, map_add, MulOpposite.op_add]
    map_smul' _ _ := by simp only [MulOpposite.unop_smul, LinearMap.map_smulₛₗ, MulOpposite.op_smul]


-- @@ L27-34 verbatim
/-- Pull a semilinear map between opposite modules back through the multiplicative opposite. -/
@[simps]
def LinearMap.unop {R S : Type*} [Semiring R] [Semiring S] {σ : R →+* S}
  {M M₂ : Type*} [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂]
  (f : Mᵐᵒᵖ →ₛₗ[σ] M₂ᵐᵒᵖ) : M →ₛₗ[σ] M₂ where
    toFun x := MulOpposite.unop (f (MulOpposite.op x))
    map_add' _ _ := by simp only [MulOpposite.unop_add, map_add, MulOpposite.op_add]
    map_smul' _ _ := by simp only [MulOpposite.unop_smul, LinearMap.map_smulₛₗ, MulOpposite.op_smul]

-- @@ L35-40 verbatim
@[simp]
lemma LinearMap.unop_op {R S : Type*} [Semiring R] [Semiring S] {σ : R →+* S}
  {M M₂ : Type*} [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂]
  (f : Mᵐᵒᵖ →ₛₗ[σ] M₂ᵐᵒᵖ) :
  f.unop.op = f :=
rfl

-- @@ L41-46 verbatim
@[simp]
lemma LinearMap.op_unop {R S : Type*} [Semiring R] [Semiring S] {σ : R →+* S}
  {M M₂ : Type*} [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂]
  (f : M →ₛₗ[σ] M₂) :
  f.op.unop = f :=
rfl


-- @@ L48-53 verbatim
@[simp]
theorem AlgEquiv.op_toLinearMap
  {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A]
  [Algebra R B] (f : A ≃ₐ[R] B) :
  f.op.toLinearMap = f.toLinearMap.op :=
rfl
