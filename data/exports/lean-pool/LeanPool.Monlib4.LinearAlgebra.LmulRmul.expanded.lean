/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import LeanPool.Monlib4.LinearAlgebra.LinearMapOp
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Pow


-- @@ L13-19 verbatim
/-!
# lmul and rmul

The left and right multiplication maps, copied from `LinearMap.mulLeft` and
`LinearMap.mulRight` but defined as linear maps.

-/


-- @@ L21-21 verbatim
@[expose] public section



-- @@ L24-24 verbatim
section


-- @@ L26-28 verbatim
variable {R E F : Type _} [CommSemiring R] [NonUnitalNonAssocSemiring E]
  [NonUnitalNonAssocSemiring F] [Module R E] [Module R F] [SMulCommClass R E E]
  [SMulCommClass R F F] [IsScalarTower R E E] [IsScalarTower R F F]


-- @@ L30-35 verbatim
omit [IsScalarTower R E E] [IsScalarTower R F F] in
theorem LinearMap.mulLeft_conj_of_mulEquivClass_apply
  {Fn : Type*} [EquivLike Fn E F] [MulEquivClass Fn E F]
  (f : Fn) (x : E) (y : F) :
    f (LinearMap.mulLeft R x (EquivLike.inv f y))  = LinearMap.mulLeft R (f x) y := by
  simp_all


-- @@ L37-42 verbatim
omit [SMulCommClass R E E] [SMulCommClass R F F] in
theorem LinearMap.mulRight_conj_of_mulEquivClass_apply
  {Fn : Type*} [EquivLike Fn E F] [MulEquivClass Fn E F]
  (f : Fn) (x : E) (y : F) :
    f (LinearMap.mulRight R x (EquivLike.inv f y)) = LinearMap.mulRight R (f x) y := by
  simp_all


-- @@ L44-44 verbatim
end


-- @@ L46-46 verbatim
local notation "l(" x "," y ")" => y →ₗ[x] y


-- @@ L48-53 verbatim
variable {R H₁ H₂ : Type _} [CommSemiring R]
  -- [semiring H₁] [semiring H₂]
  -- [algebra R H₁] [algebra R H₂]
  [NonUnitalNonAssocSemiring H₁]
  [Module R H₁] [SMulCommClass R H₁ H₁] [IsScalarTower R H₁ H₁] [NonUnitalNonAssocSemiring H₂]
  [Module R H₂] [SMulCommClass R H₂ H₂] [IsScalarTower R H₂ H₂]


-- @@ L55-60 expanded
theorem left_module_map_iff {H₁ : Type _} [Semiring H₁] [Algebra R H₁] {x : H₁ →ₗ[R] H₁} :
    (∀ a b : H₁, x (a * b) = a * x b) ↔ x = LinearMap.mulRight R (x 1) :=
  by
  simp_rw [LinearMap.ext_iff, LinearMap.mulRight_apply]
  constructor <;> intro h <;> intros
  · rw [← h, mul_one]
  · rw [h, mul_assoc, ← h]


-- @@ L62-67 expanded
theorem right_module_map_iff {H₂ : Type _} [Semiring H₂] [Algebra R H₂] {x : H₂ →ₗ[R] H₂} :
    (∀ a b : H₂, x (a * b) = x a * b) ↔ x = LinearMap.mulLeft R (x 1) :=
  by
  simp_rw [LinearMap.ext_iff, LinearMap.mulLeft_apply]
  constructor <;> intro h <;> intros
  · rw [← h, one_mul]
  · rw [h, ← mul_assoc, ← h]


-- @@ L69-77 expanded
/-- The linear map sending an element to left multiplication by that element. -/
def lmul : H₁ →ₗ[R] H₁ →ₗ[R] H₁
    where
  toFun x := LinearMap.mulLeft R x
  map_add' x
    y := by
    ext1
    simp only [LinearMap.mulLeft_apply, add_mul, LinearMap.add_apply]
  map_smul' r
    x := by
    ext1
    simp only [LinearMap.mulLeft_apply, LinearMap.smul_apply, RingHom.id_apply, smul_mul_assoc]


-- @@ L79-80 expanded
theorem lmul_apply (x y : H₁) : (lmul x : H₁ →ₗ[R] H₁) y = x * y :=
  rfl


-- @@ L82-83 verbatim
theorem lmul_eq_mul (x : H₁) : lmul x = LinearMap.mulLeft R x :=
  rfl


-- @@ L85-87 expanded
theorem lmul_eq_alg_lmul {H₁ : Type _} [Semiring H₁] [Algebra R H₁] (x : H₁) :
    (lmul x : H₁ →ₗ[R] H₁) = Algebra.lmul R H₁ x :=
  rfl


-- @@ L89-92 expanded
theorem lmul_one {H₁ : Type _} [NonAssocSemiring H₁] [Module R H₁] [SMulCommClass R H₁ H₁]
    [IsScalarTower R H₁ H₁] : (lmul (1 : H₁) : H₁ →ₗ[R] H₁) = 1 :=
  by
  ext
  simp_rw [lmul_apply, Module.End.one_apply, one_mul]


-- @@ L94-102 expanded
/-- The linear map sending an element to right multiplication by that element. -/
def rmul : H₂ →ₗ[R] H₂ →ₗ[R] H₂
    where
  toFun x := LinearMap.mulRight R x
  map_add' x
    y := by
    ext1
    simp only [LinearMap.mulRight_apply, mul_add, LinearMap.add_apply]
  map_smul' r
    x := by
    ext1
    simp only [LinearMap.mulRight_apply, LinearMap.smul_apply, RingHom.id_apply, mul_smul_comm]


-- @@ L104-105 expanded
theorem rmul_apply (x y : H₂) : (rmul x : H₂ →ₗ[R] H₂) y = y * x :=
  rfl


-- @@ L107-108 verbatim
theorem rmul_eq_mul (x : H₂) : rmul x = LinearMap.mulRight R x :=
  rfl


-- @@ L110-113 expanded
theorem rmul_one {H₁ : Type _} [NonAssocSemiring H₁] [Module R H₁] [SMulCommClass R H₁ H₁]
    [IsScalarTower R H₁ H₁] : (rmul (1 : H₁) : H₁ →ₗ[R] H₁) = 1 :=
  by
  ext
  simp only [rmul_apply, mul_one, Module.End.one_apply]


-- @@ L115-115 verbatim
open scoped TensorProduct


-- @@ L117-117 verbatim
local notation x " ⊗ₘ " y => TensorProduct.map x y


-- @@ L119-124 verbatim
/-- Tensor right multiplication on the left factor with left multiplication on the right factor. -/
noncomputable def rmulMapLmul {R H₁ H₂ : Type*} [CommSemiring R]
  [NonUnitalNonAssocSemiring H₁] [Module R H₁] [SMulCommClass R H₁ H₁] [IsScalarTower R H₁ H₁]
  [NonUnitalNonAssocSemiring H₂] [Module R H₂] [SMulCommClass R H₂ H₂] [IsScalarTower R H₂ H₂] :
  H₁ ⊗[R] H₂ →ₗ[R] ((H₁ ⊗[R] H₂) →ₗ[R] (H₁ ⊗[R] H₂)) :=
(TensorProduct.homTensorHomMap (.id R) H₁ H₂ H₁ H₂) ∘ₗ (TensorProduct.map rmul lmul)


-- @@ L126-128 expanded
theorem rmulMapLmul_apply (x : H₁) (y : H₂) :
    rmulMapLmul (x ⊗ₜ[R] y) = TensorProduct.map (rmul x) (lmul y) := by
  rw [rmulMapLmul, LinearMap.comp_apply, TensorProduct.map_tmul,
    TensorProduct.homTensorHomMap_apply]


-- @@ L130-136 verbatim
theorem rmulMapLmul_one {H₁ : Type _} [NonAssocSemiring H₁] [Module R H₁] [SMulCommClass R H₁ H₁]
    [IsScalarTower R H₁ H₁] {H₂ : Type _} [NonAssocSemiring H₂] [Module R H₂]
    [SMulCommClass R H₂ H₂] [IsScalarTower R H₂ H₂] : rmulMapLmul (1 ⊗ₜ 1 : H₁ ⊗[R] H₂) = 1 := by
  apply TensorProduct.ext'
  intro a b
  simp_rw [rmulMapLmul_apply, TensorProduct.map_tmul, rmul_apply, lmul_apply, mul_one, one_mul,
    Module.End.one_apply]


-- @@ L138-138 verbatim
open scoped BigOperators


-- @@ L140-144 verbatim
theorem LinearMap.mulLeft_sum {R : Type _} {A : Type _} [CommSemiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
    {n : Type _} {s : Finset n} {x : n → A} :
    ∑ i ∈ s, LinearMap.mulLeft R (x i) = LinearMap.mulLeft R (∑ i ∈ s, x i) :=
by simp_rw [← lmul_eq_mul, map_sum]


-- @@ L146-150 verbatim
theorem LinearMap.mulRight_sum {R : Type _} {A : Type _} [CommSemiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
    {n : Type _} {s : Finset n} {x : n → A} :
    ∑ i ∈ s, LinearMap.mulRight R (x i) = LinearMap.mulRight R (∑ i ∈ s, x i) :=
by simp_rw [← rmul_eq_mul, map_sum]


-- @@ L152-154 expanded
theorem lmul_eq_zero_iff {H₁ : Type _} [Semiring H₁] [Algebra R H₁] (x : H₁) :
    (lmul x : H₁ →ₗ[R] H₁) = 0 ↔ x = 0 :=
  LinearMap.mulLeft_eq_zero_iff _ _ _


-- @@ L156-158 expanded
theorem rmul_eq_zero_iff {H₁ : Type _} [Semiring H₁] [Algebra R H₁] (x : H₁) :
    (rmul x : H₁ →ₗ[R] H₁) = 0 ↔ x = 0 :=
  LinearMap.mulRight_eq_zero_iff _ _ _


-- @@ L160-164 expanded
theorem lmul_eq_one_iff {H₁ : Type _} [NonAssocSemiring H₁] [Module R H₁] [SMulCommClass R H₁ H₁]
    [IsScalarTower R H₁ H₁] (x : H₁) : (lmul x : H₁ →ₗ[R] H₁) = 1 ↔ x = 1 :=
  by
  simp_rw [LinearMap.ext_iff, lmul_apply, Module.End.one_apply]
  refine ⟨fun h => ?_, fun h a => by rw [h, one_mul]⟩
  simpa using h 1


-- @@ L166-168 verbatim
theorem LinearMap.mulLeft_eq_one_iff {H₁ : Type _} [NonAssocSemiring H₁] [Module R H₁]
    [SMulCommClass R H₁ H₁] [IsScalarTower R H₁ H₁] (x : H₁) : LinearMap.mulLeft R x = 1 ↔ x = 1 :=
  lmul_eq_one_iff _


-- @@ L170-174 expanded
theorem rmul_eq_one_iff {H₁ : Type _} [NonAssocSemiring H₁] [Module R H₁] [SMulCommClass R H₁ H₁]
    [IsScalarTower R H₁ H₁] (x : H₁) : (rmul x : H₁ →ₗ[R] H₁) = 1 ↔ x = 1 :=
  by
  simp_rw [LinearMap.ext_iff, rmul_apply, Module.End.one_apply]
  refine ⟨fun h => ?_, fun h a => by rw [h, mul_one]⟩
  simpa using h 1


-- @@ L176-178 verbatim
theorem LinearMap.mulRight_eq_one_iff {H₁ : Type _} [NonAssocSemiring H₁] [Module R H₁]
    [SMulCommClass R H₁ H₁] [IsScalarTower R H₁ H₁] (x : H₁) : LinearMap.mulRight R x = 1 ↔ x = 1 :=
  rmul_eq_one_iff _


-- @@ L180-187 verbatim
theorem LinearMap.mulLeft_eq_one_or_zero_iff_mulRight_tfae {H₁ : Type _} [Semiring H₁]
    [Algebra R H₁] (x : H₁) (p : Prop) [Decidable p] :
    List.TFAE [LinearMap.mulLeft R x = ite p 1 0,
      LinearMap.mulRight R x = ite p 1 0, x = ite p 1 0] := by
  by_cases h : p
  · simp_rw [h, ite_true, LinearMap.mulLeft_eq_one_iff, LinearMap.mulRight_eq_one_iff]
    tfae_finish
  · simp_all


-- @@ L189-192 verbatim
theorem LinearMap.mulLeft_eq_one_or_zero_iff_mulRight {H₁ : Type _} [Semiring H₁] [Algebra R H₁]
    (x : H₁) (p : Prop) [Decidable p] :
    LinearMap.mulLeft R x = ite p 1 0 ↔ LinearMap.mulRight R x = ite p 1 0 :=
  List.TFAE.out (@LinearMap.mulLeft_eq_one_or_zero_iff_mulRight_tfae R _ H₁ _ _ x p _) 1 2


-- @@ L194-196 verbatim
theorem LinearMap.mulRight_smul (x : H₁) (α : R) :
    LinearMap.mulRight R (α • x) = α • LinearMap.mulRight R x :=
  rmul.map_smul _ _


-- @@ L198-200 verbatim
theorem LinearMap.mulLeft_smul (x : H₁) (α : R) :
    LinearMap.mulLeft R (α • x) = α • LinearMap.mulLeft R x :=
  lmul.map_smul _ _


-- @@ L202-209 verbatim
theorem LinearMap.mulLeft_comp_inj {H₁ H₂ : Type _} [Semiring H₁] [Module R H₁] [AddCommMonoid H₂]
    [Module R H₂] [SMulCommClass R H₁ H₁] (f g : H₁ →ₗ[R] H₂) (x : H₁)
    [Invertible x] : f ∘ₗ LinearMap.mulLeft R x = g ∘ₗ LinearMap.mulLeft R x ↔ f = g := by
  refine ⟨?_, fun h => by rw [h]⟩
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply, LinearMap.mulLeft_apply]
  intro h y
  specialize h (⅟ x * y)
  simp_all


-- @@ L211-215 verbatim
theorem LinearMap.mulLeft_apply_inj {H₁ : Type _} [Semiring H₁] [Module R H₁]
    [SMulCommClass R H₁ H₁]
    (x : H₁) [Invertible x] (y z : H₁) :
    LinearMap.mulLeft R x y = LinearMap.mulLeft R x z ↔ y = z :=
  IsUnit.mul_right_inj (isUnit_of_invertible x)


-- @@ L217-220 verbatim
theorem lmul_op {R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A] (x : Aᵐᵒᵖ) :
    lmul x = (rmul (x.unop) : A →ₗ[R] A).op :=
  rfl


-- @@ L222-225 verbatim
theorem lmul_op' {R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A] (x : A) :
    lmul (MulOpposite.op x) = (rmul x : A →ₗ[R] A).op :=
  rfl


-- @@ L227-230 verbatim
theorem rmul_op' {R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A] (x : A) :
    rmul (MulOpposite.op x) = (lmul x : A →ₗ[R] A).op :=
  rfl
