/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.RingTheory.Coalgebra.Basic
public import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.RingTheory.Coalgebra.CoassocSimps


-- @@ L12-16 verbatim
/-!
# LeanPool.Monlib4.LinearAlgebra.Coalgebra.Lemmas

Imported Lean Pool material for `LeanPool.Monlib4.LinearAlgebra.Coalgebra.Lemmas`.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-26 verbatim
theorem TensorProduct.map_left_up {R A B C D : Type*}
  [CommSemiring R]
  [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [Module R A] [Module R B] [Module R C] [Module R D]
  (f : A →ₗ[R] B) (g : C →ₗ[R] D) :
  map f g = (map f LinearMap.id) ∘ₗ (map LinearMap.id g) :=
ext rfl

-- @@ L27-27 verbatim
alias TensorProduct.map_right_down := TensorProduct.map_left_up


-- @@ L29-34 verbatim
theorem TensorProduct.map_right_up {R A B C D : Type*} [CommSemiring R]
  [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [Module R A] [Module R B] [Module R C] [Module R D]
  (f : A →ₗ[R] B) (g : C →ₗ[R] D) :
  map f g = (map LinearMap.id g) ∘ₗ (map f LinearMap.id) :=
ext rfl

-- @@ L35-35 verbatim
alias TensorProduct.map_left_down := TensorProduct.map_right_up


-- @@ L37-37 verbatim
open TensorProduct LinearMap

-- @@ L38-45 verbatim
theorem Algebra.linearMap_mul'_assoc {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] :
  (mul' R A) ∘ₗ (map (mul' R A) LinearMap.id)
  = (mul' R A) ∘ₗ (map LinearMap.id (mul' R A))
    ∘ₗ (_root_.TensorProduct.assoc R A A A) := by
  refine TensorProduct.ext_threefold ?_
  intro x y z
  simp only [coe_comp, Function.comp_apply, map_tmul, mul'_apply, id_coe, id_eq,
    LinearEquiv.coe_coe, assoc_tmul, mul_assoc]

-- @@ L46-46 verbatim
alias Algebra.assoc := Algebra.linearMap_mul'_assoc


-- @@ L48-51 verbatim
theorem Algebra.assoc' {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] :
  (mul' R A) ∘ₗ (rTensor A (mul' R A))
    = (mul' R A) ∘ₗ (lTensor A (mul' R A)) ∘ₗ (_root_.TensorProduct.assoc R A A A) :=
Algebra.assoc

-- @@ L52-52 verbatim
alias Algebra.mul_comp_rTensor_mul := Algebra.assoc'


-- @@ L54-54 verbatim
open scoped TensorProduct

-- @@ L55-63 verbatim
theorem Algebra.mul_comp_rTensor_unit {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] :
  (mul' R A) ∘ₗ (rTensor A (Algebra.linearMap R A))
  = _root_.TensorProduct.lid R A := by
  apply _root_.TensorProduct.ext'
  intro r a
  simp_rw [LinearMap.rTensor, LinearMap.comp_apply, map_tmul,
    LinearMap.id_apply, Algebra.linearMap_apply, LinearMap.mul'_apply,
    LinearEquiv.coe_coe, lid_tmul, algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul]

-- @@ L64-70 verbatim
theorem Algebra.mul_comp_rTensor_unit_comp_lid_symm
    {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] :
  (mul' R A) ∘ₗ (rTensor A (Algebra.linearMap R A))
    ∘ₗ (_root_.TensorProduct.lid R A).symm
  = LinearMap.id := by
  rw [← LinearMap.comp_assoc, Algebra.mul_comp_rTensor_unit]
  simp


-- @@ L72-80 verbatim
theorem Algebra.mul_comp_lTensor_unit {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] :
  (mul' R A) ∘ₗ (lTensor A (Algebra.linearMap R A))
  = _root_.TensorProduct.rid R A := by
  apply _root_.TensorProduct.ext'
  intro r a
  simp_rw [LinearMap.lTensor, LinearMap.comp_apply, map_tmul,
    LinearMap.id_apply, Algebra.linearMap_apply, LinearMap.mul'_apply,
    LinearEquiv.coe_coe, _root_.TensorProduct.rid_tmul, algebraMap_eq_smul_one,
    mul_smul_comm, mul_one]


-- @@ L82-87 verbatim
theorem Algebra.mul_comp_lTensor_unit_comp_rid_symm
  {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] :
  (mul' R A) ∘ₗ (lTensor A (Algebra.linearMap R A)) ∘ₗ (_root_.TensorProduct.rid R A).symm
  = LinearMap.id := by
  rw [← LinearMap.comp_assoc, Algebra.mul_comp_lTensor_unit]
  simp


-- @@ L89-89 verbatim
open Coalgebra

-- @@ L90-101 verbatim
theorem counit_comp_mul_comp_rTensor_unit {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  [Coalgebra R A] :
  counit ∘ₗ (LinearMap.mul' R _) ∘ₗ
    (LinearMap.rTensor A (Algebra.linearMap R A))
    ∘ₗ (TensorProduct.lid R A).symm.toLinearMap
  = counit :=
calc counit ∘ₗ (LinearMap.mul' R _) ∘ₗ
  (LinearMap.rTensor A (Algebra.linearMap R A))
      ∘ₗ ((TensorProduct.mk R _ _) 1)
    = counit ∘ₗ (TensorProduct.lid R _).toLinearMap ∘ₗ ((TensorProduct.mk R R A) 1) :=
      by simp_rw [← Algebra.mul_comp_rTensor_unit, LinearMap.comp_assoc]
  _ = counit := by aesop


-- @@ L103-113 verbatim
theorem counit_comp_mul_lTensor_unit {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  [Coalgebra R A] :
  counit ∘ₗ (mul' R _) ∘ₗ
    (lTensor A (Algebra.linearMap R A))
    ∘ₗ (TensorProduct.rid R A).symm.toLinearMap
  = counit :=
calc counit ∘ₗ (mul' R _) ∘ₗ (lTensor A (Algebra.linearMap R A))
      ∘ₗ ((TensorProduct.mk R A R).flip 1)
    = counit ∘ₗ (TensorProduct.rid R A).toLinearMap ∘ₗ ((TensorProduct.mk R A R).flip 1) :=
      by simp_rw [← Algebra.mul_comp_lTensor_unit, LinearMap.comp_assoc]
  _ = counit := by aesop


-- @@ L115-122 verbatim
theorem lTensor_counit_comp_comul_unit {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  [Coalgebra R A] :
  (lTensor A counit) ∘ₗ comul ∘ₗ (Algebra.linearMap R A)
  = (TensorProduct.rid R A).symm ∘ₗ (Algebra.linearMap R A) := by
  ext
  simp_all only [LinearMap.coe_comp, Function.comp_apply,
    Algebra.linearMap_apply, _root_.map_one, lTensor_counit_comul,
    LinearEquiv.coe_coe, TensorProduct.rid_symm_apply]


-- @@ L124-124 verbatim
variable {R : Type*} [CommSemiring R]


-- @@ L126-126 verbatim
local notation "lT" => LinearMap.lTensor

-- @@ L127-127 verbatim
local notation "rT" => LinearMap.rTensor

-- @@ L128-128 verbatim
local notation "m" => LinearMap.mul' R

-- @@ L129-129 verbatim
local notation "ϰ" => TensorProduct.assoc R

-- @@ L130-130 verbatim
local notation "τ" => TensorProduct.lid R

-- @@ L131-132 verbatim
local notation x " ⊗ₘ " y => TensorProduct.map x y
-- local notation "ϰ⁻¹" => LinearEquiv.symm ϰ


-- @@ L134-138 expanded
lemma Coalgebra.rTensor_counit_comp_comul' {A : Type*} [AddCommMonoid A] [Module R A]
    [Coalgebra R A] :
    ((LinearMap.rTensor _ counit) ∘ₗ comul) = (TensorProduct.lid R A).symm.toLinearMap :=
  by
  rw [rTensor_counit_comp_comul]
  rfl


-- @@ L140-147 expanded
lemma TensorProduct.assoc_symm_comp_rTensor {A B C D : Type*} [AddCommMonoid A] [AddCommMonoid B]
    [AddCommMonoid C] [AddCommMonoid D] [Module R A] [Module R B] [Module R C] [Module R D]
    (x : A →ₗ[R] D) :
    (LinearEquiv.symm ((TensorProduct.assoc R) D B C)) ∘ₗ (LinearMap.rTensor _ x) =
      (LinearMap.rTensor _ (LinearMap.rTensor _ x)) ∘ₗ
        (LinearEquiv.symm ((TensorProduct.assoc R) A B C)).toLinearMap :=
  by
  apply TensorProduct.ext_threefold'
  simp_all


-- @@ L148-154 expanded
lemma TensorProduct.assoc_symm_comp_lTensor_lTensor {A B C D : Type*} [AddCommMonoid A]
    [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D] [Module R A] [Module R B] [Module R C]
    [Module R D] (x : A →ₗ[R] D) :
    ((TensorProduct.assoc R) B C D).symm.toLinearMap ∘ₗ
        (LinearMap.lTensor _ (LinearMap.lTensor _ x)) =
      (LinearMap.lTensor _ x) ∘ₗ ((TensorProduct.assoc R) B C A).symm.toLinearMap :=
  by
  apply TensorProduct.ext_threefold'
  simp_all


-- @@ L156-161 expanded
lemma TensorProduct.rTensor_lTensor_comp_assoc_symm {A B C D : Type*} [AddCommMonoid A]
    [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D] [Module R A] [Module R B] [Module R C]
    [Module R D] (x : A →ₗ[R] D) :
    (LinearMap.rTensor _ (LinearMap.lTensor _ x)) ∘ₗ
        (LinearEquiv.symm ((TensorProduct.assoc R) _ _ _)).toLinearMap =
      (LinearEquiv.symm ((TensorProduct.assoc R) B D C)).toLinearMap ∘ₗ
        (LinearMap.lTensor _ (LinearMap.rTensor _ x)) :=
  by simp_rw [rTensor, lTensor, map_map_comp_assoc_symm_eq]


-- @@ L162-167 expanded
lemma TensorProduct.assoc_comp_rTensor_rTensor {A B C D : Type*} [AddCommMonoid A] [AddCommMonoid B]
    [AddCommMonoid C] [AddCommMonoid D] [Module R A] [Module R B] [Module R C] [Module R D]
    (x : A →ₗ[R] D) :
    ((TensorProduct.assoc R) D B C).toLinearMap ∘ₗ (LinearMap.rTensor _ (LinearMap.rTensor _ x)) =
      (LinearMap.rTensor _ x) ∘ₗ ((TensorProduct.assoc R) _ _ _).toLinearMap :=
  by
  apply TensorProduct.ext_threefold
  simp_all


-- @@ L169-177 verbatim
lemma TensorProduct.ext_fourfold_right {A B C D E : Type*}
  [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
  [AddCommMonoid E]
  [Module R A] [Module R B] [Module R C] [Module R D]
  [Module R E] {f g : (A ⊗[R] (B ⊗[R] (C ⊗[R] D))) →ₗ[R] E} :
  (∀ x y z w, f (x ⊗ₜ (y ⊗ₜ (z ⊗ₜ w))) = g (x ⊗ₜ (y ⊗ₜ (z ⊗ₜ w)))) → f = g := by
  intro h
  ext x y z w
  exact h x y z w


-- @@ L179-186 expanded
lemma TensorProduct.assoc_comp_rTensor_assoc_symm_comp_assoc_symm_comp_lTensor_assoc_symm
    {A B C D : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D]
    [Module R A] [Module R B] [Module R C] [Module R D] :
    ((TensorProduct.assoc R) _ _ _).toLinearMap ∘ₗ
        (LinearMap.rTensor _ ((TensorProduct.assoc R) _ _ _).symm.toLinearMap) ∘ₗ
          ((TensorProduct.assoc R) _ _ _).symm.toLinearMap ∘ₗ
            (LinearMap.lTensor _ ((TensorProduct.assoc R) _ _ _).symm.toLinearMap) =
      ((TensorProduct.assoc R) A B (C ⊗[R] D)).symm.toLinearMap :=
  by
  apply TensorProduct.ext_fourfold_right
  simp_all


-- @@ L188-193 expanded
lemma TensorProduct.rTensor_comp_rTensor {A B C D : Type*} [AddCommMonoid A] [AddCommMonoid B]
    [AddCommMonoid C] [AddCommMonoid D] [Module R A] [Module R B] [Module R C] [Module R D]
    (x : B →ₗ[R] C) (y : A →ₗ[R] B) :
    (LinearMap.rTensor D x) ∘ₗ (LinearMap.rTensor D y) = LinearMap.rTensor D (x ∘ₗ y) := by
  simp_rw [rTensor, ← map_comp, id_comp]


-- @@ L194-199 expanded
lemma TensorProduct.lTensor_comp_lTensor {A B C D : Type*} [AddCommMonoid A] [AddCommMonoid B]
    [AddCommMonoid C] [AddCommMonoid D] [Module R A] [Module R B] [Module R C] [Module R D]
    (x : B →ₗ[R] C) (y : A →ₗ[R] B) :
    (LinearMap.lTensor D x) ∘ₗ (LinearMap.lTensor D y) = LinearMap.lTensor D (x ∘ₗ y) := by
  simp_rw [lTensor, ← map_comp, id_comp]


-- @@ L201-206 expanded
lemma lid_tensor_toLinearMap {A B : Type*} [AddCommMonoid A] [Module R A] [AddCommMonoid B]
    [Module R B] :
    ((TensorProduct.lid R) (A ⊗[R] B)).toLinearMap =
      LinearMap.rTensor _ ((TensorProduct.lid R) _).toLinearMap ∘ₗ
        (LinearEquiv.symm ((TensorProduct.assoc R) _ _ _)).toLinearMap :=
  by
  simpa [LinearEquiv.coe_trans] using
    congrArg LinearEquiv.toLinearMap (TensorProduct.lid_tensor (R := R) (M := A) (N := B))


-- @@ L208-212 expanded
lemma lid_tensor {A B : Type*} [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B] :
    ((TensorProduct.lid R) (A ⊗[R] B)).toLinearMap =
      LinearMap.rTensor _ ((TensorProduct.lid R) _).toLinearMap ∘ₗ
        (LinearEquiv.symm ((TensorProduct.assoc R) _ _ _)).toLinearMap :=
  lid_tensor_toLinearMap


-- @@ L214-218 expanded
lemma rTensor_comp_lTensor' {A B C D : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]
    [AddCommMonoid D] [Module R A] [Module R B] [Module R C] [Module R D] (x : A →ₗ[R] B)
    (y : C →ₗ[R] D) :
    (LinearMap.rTensor _ x) ∘ₗ (LinearMap.lTensor _ y) =
      (LinearMap.lTensor _ y) ∘ₗ (LinearMap.rTensor _ x) :=
  by simp only [rTensor_comp_lTensor, lTensor_comp_rTensor]


-- @@ L220-221 verbatim
variable {A : Type*} [Semiring A] [Algebra R A]
  [Coalgebra R A]


-- @@ L223-223 verbatim
open TensorProduct


-- @@ L225-393 expanded
/-- if `(id ⊗ mul) (comul ⊗ id) = (mul ⊗ id) (id ⊗ comul)`,
  then `(id ⊗ mul) (comul ⊗ id) = comul ∘ mul`.

  This is sometimes referred to as the Frobenius equations. -/
theorem lTensor_mul_comp_rTensor_comul_of
    (h :
      (LinearMap.lTensor A ((LinearMap.mul' R) A)) ∘ₗ
          ((TensorProduct.assoc R) A A A) ∘ₗ (LinearMap.rTensor A comul) =
        (LinearMap.rTensor A ((LinearMap.mul' R) A)) ∘ₗ
          (LinearEquiv.symm ((TensorProduct.assoc R) A A A)) ∘ₗ (LinearMap.lTensor A comul)) :
    (LinearMap.lTensor A ((LinearMap.mul' R) A)) ∘ₗ
        ((TensorProduct.assoc R) A A A) ∘ₗ (LinearMap.rTensor A comul) =
      comul ∘ₗ ((LinearMap.mul' R) A) :=
  by
  calc
    (LinearMap.lTensor A ((LinearMap.mul' R) A)) ∘ₗ
          ((TensorProduct.assoc R) A A A) ∘ₗ (LinearMap.rTensor A comul) =
        (LinearMap.rTensor A ((LinearMap.mul' R) A)) ∘ₗ
          (LinearEquiv.symm ((TensorProduct.assoc R) A A A)) ∘ₗ (LinearMap.lTensor A comul) :=
      h
    _ =
        (LinearMap.rTensor _ ((LinearMap.mul' R) A)) ∘ₗ
          ((TensorProduct.assoc R) _ _ _).symm.toLinearMap ∘ₗ
            (TensorProduct.map
              ((((TensorProduct.lid R) _).toLinearMap ∘ₗ ((LinearMap.rTensor _ counit) ∘ₗ comul)))
              comul) :=
      by
      congr 2
      rw [rTensor_counit_comp_comul, lTensor]
      congr
      ext
      simp only [id_coe, id_eq, coe_comp, LinearEquiv.coe_coe, Function.comp_apply, mk_apply,
        lid_tmul, one_smul]
    _ =
        (LinearMap.rTensor _ ((LinearMap.mul' R) A)) ∘ₗ
          ((TensorProduct.assoc R) _ _ _).symm.toLinearMap ∘ₗ
            (LinearMap.rTensor _ ((TensorProduct.lid R) _).toLinearMap) ∘ₗ
              (LinearMap.rTensor _ (LinearMap.rTensor _ counit)) ∘ₗ
                (TensorProduct.map comul comul) :=
      by simp only [rTensor_comp_map]
    _ =
        (LinearMap.rTensor _
            (((LinearMap.mul' R) _) ∘ₗ
              ((TensorProduct.lid R) _).toLinearMap ∘ₗ
                (LinearMap.rTensor _ counit) ∘ₗ ((TensorProduct.assoc R) A A A).toLinearMap)) ∘ₗ
          ((TensorProduct.assoc R) _ _ _).symm.toLinearMap ∘ₗ (TensorProduct.map comul comul) :=
      by
      simp_rw [← LinearMap.comp_assoc]
      congr 1
      apply TensorProduct.ext_fourfold'
      simp_all
    _ =
        (LinearMap.rTensor _
            (((TensorProduct.lid R) _).toLinearMap ∘ₗ
              ((LinearMap.lTensor _ ((LinearMap.mul' R) A)) ∘ₗ (LinearMap.rTensor _ counit)) ∘ₗ
                ((TensorProduct.assoc R) _ _ _).toLinearMap)) ∘ₗ
          ((TensorProduct.assoc R) _ _ _).symm.toLinearMap ∘ₗ (TensorProduct.map comul comul) :=
      by
      simp_rw [← LinearMap.comp_assoc]
      congr 5
      apply TensorProduct.ext'
      simp_all
    _ =
        (LinearMap.rTensor _
            (((TensorProduct.lid R) _).toLinearMap ∘ₗ
              ((LinearMap.rTensor _ counit) ∘ₗ (LinearMap.lTensor _ ((LinearMap.mul' R) A))) ∘ₗ
                ((TensorProduct.assoc R) _ _ _).toLinearMap)) ∘ₗ
          ((TensorProduct.assoc R) _ _ _).symm.toLinearMap ∘ₗ (TensorProduct.map comul comul) :=
      by simp only [lTensor_comp_rTensor, rTensor_comp_lTensor]
    _ =
        (LinearMap.rTensor _
            (((TensorProduct.lid R) _).toLinearMap ∘ₗ
              ((LinearMap.rTensor _ counit) ∘ₗ (LinearMap.lTensor _ ((LinearMap.mul' R) A))) ∘ₗ
                ((TensorProduct.assoc R) _ _ _).toLinearMap)) ∘ₗ
          (((TensorProduct.assoc R) _ _ _).symm.toLinearMap ∘ₗ (LinearMap.rTensor _ comul)) ∘ₗ
            (LinearMap.lTensor _ comul) :=
      by simp only [comp_assoc, rTensor_comp_lTensor]
    _ =
        (LinearMap.rTensor _
            (((TensorProduct.lid R) _).toLinearMap ∘ₗ
              ((LinearMap.rTensor _ counit) ∘ₗ (LinearMap.lTensor _ ((LinearMap.mul' R) A))) ∘ₗ
                ((TensorProduct.assoc R) _ _ _).toLinearMap)) ∘ₗ
          (LinearMap.rTensor _ (LinearMap.rTensor _ comul)) ∘ₗ
            ((TensorProduct.assoc R) _ _ _).symm.toLinearMap ∘ₗ (LinearMap.lTensor _ comul) :=
      by simp only [TensorProduct.assoc_symm_comp_rTensor, comp_assoc]
    _ =
        (((TensorProduct.lid R) _).toLinearMap ∘ₗ (LinearMap.rTensor _ counit)) ∘ₗ
          ((TensorProduct.assoc R) _ _ _).toLinearMap ∘ₗ
            ((LinearMap.rTensor _
                  ((LinearMap.rTensor _ ((LinearMap.mul' R) A)) ∘ₗ
                    ((TensorProduct.assoc R) _ _ _).symm.toLinearMap ∘ₗ
                      (LinearMap.lTensor _ comul))) ∘ₗ
                ((TensorProduct.assoc R) _ _ _).symm.toLinearMap) ∘ₗ
              (LinearMap.lTensor A comul) :=
      by
      rw [← h]
      simp_rw [← comp_assoc]
      congr 2
      simp_rw [rTensor_comp_rTensor, lid_tensor_toLinearMap]
      symm
      nth_rw 3 [comp_assoc]
      rw [assoc_symm_comp_rTensor]
      simp_rw [← comp_assoc, rTensor_comp_rTensor]
      nth_rw 2 [comp_assoc]
      simp only [LinearEquiv.comp_coe, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap,
        comp_id]
      simp_rw [rTensor_comp_rTensor, comp_assoc]
    _ =
        ((TensorProduct.lid R) (A ⊗[R] A)).toLinearMap ∘ₗ
          (LinearMap.rTensor _ counit) ∘ₗ
            ((TensorProduct.assoc R) _ _ _).toLinearMap ∘ₗ
              (LinearMap.rTensor _ (LinearMap.rTensor _ ((LinearMap.mul' R) A))) ∘ₗ
                (LinearMap.rTensor A ((TensorProduct.assoc R) A A A).symm.toLinearMap) ∘ₗ
                  ((TensorProduct.assoc R) _ _ _).symm.toLinearMap ∘ₗ
                    (LinearMap.lTensor _ ((LinearMap.rTensor A comul) ∘ₗ comul)) :=
      by
      simp_rw [comp_assoc]
      congr 3
      simp_rw [← comp_assoc]
      rw [rTensor_comp_rTensor]
      nth_rw 1 [← rTensor_comp_rTensor]
      simp_rw [comp_assoc]
      congr 1
      rw [← comp_assoc, TensorProduct.rTensor_lTensor_comp_assoc_symm, comp_assoc,
        lTensor_comp_lTensor]
    _ =
        ((TensorProduct.lid R) (A ⊗[R] A)).toLinearMap ∘ₗ
          (LinearMap.rTensor _ counit) ∘ₗ
            ((TensorProduct.assoc R) _ _ _).toLinearMap ∘ₗ
              (LinearMap.rTensor _ (LinearMap.rTensor _ ((LinearMap.mul' R) A))) ∘ₗ
                (LinearMap.rTensor A ((TensorProduct.assoc R) A A A).symm.toLinearMap) ∘ₗ
                  ((TensorProduct.assoc R) _ _ _).symm.toLinearMap ∘ₗ
                    (LinearMap.lTensor _
                      (((TensorProduct.assoc R) _ _ _).symm.toLinearMap ∘ₗ
                        (LinearMap.lTensor A comul) ∘ₗ comul)) :=
      by rw [Coalgebra.coassoc_symm]
    _ =
        ((TensorProduct.lid R) (A ⊗[R] A)).toLinearMap ∘ₗ
          (LinearMap.rTensor _ counit) ∘ₗ
            ((TensorProduct.assoc R) _ _ _).toLinearMap ∘ₗ
              (LinearMap.rTensor _ (LinearMap.rTensor _ ((LinearMap.mul' R) A))) ∘ₗ
                (LinearMap.rTensor A ((TensorProduct.assoc R) A A A).symm.toLinearMap) ∘ₗ
                  ((TensorProduct.assoc R) _ _ _).symm.toLinearMap ∘ₗ
                    (LinearMap.lTensor _ ((TensorProduct.assoc R) _ _ _).symm.toLinearMap) ∘ₗ
                      (LinearMap.lTensor _ (LinearMap.lTensor A comul)) ∘ₗ
                        (LinearMap.lTensor _ comul) :=
      by simp_rw [lTensor_comp_lTensor]
    _ =
        ((TensorProduct.lid R) (A ⊗[R] A)).toLinearMap ∘ₗ
          (LinearMap.rTensor _ counit) ∘ₗ
            ((LinearMap.rTensor _ ((LinearMap.mul' R) A)) ∘ₗ
                ((TensorProduct.assoc R) _ _ _).toLinearMap) ∘ₗ
              (LinearMap.rTensor A ((TensorProduct.assoc R) A A A).symm.toLinearMap) ∘ₗ
                ((TensorProduct.assoc R) _ _ _).symm.toLinearMap ∘ₗ
                  (LinearMap.lTensor _ ((TensorProduct.assoc R) _ _ _).symm.toLinearMap) ∘ₗ
                    (LinearMap.lTensor _ (LinearMap.lTensor A comul)) ∘ₗ
                      (LinearMap.lTensor _ comul) :=
      by simp_rw [← assoc_comp_rTensor_rTensor, comp_assoc]
    _ =
        ((TensorProduct.lid R) (A ⊗[R] A)).toLinearMap ∘ₗ
          (LinearMap.rTensor _ counit) ∘ₗ
            (LinearMap.rTensor _ ((LinearMap.mul' R) A)) ∘ₗ
              (((TensorProduct.assoc R) _ _ _).symm.toLinearMap ∘ₗ
                  (LinearMap.lTensor _ (LinearMap.lTensor A comul))) ∘ₗ
                (LinearMap.lTensor _ comul) :=
      by
      symm
      rw [← assoc_comp_rTensor_assoc_symm_comp_assoc_symm_comp_lTensor_assoc_symm]
      simp_rw [comp_assoc]
    _ =
        ((TensorProduct.lid R) (A ⊗[R] A)).toLinearMap ∘ₗ
          (LinearMap.rTensor _ counit) ∘ₗ
            ((LinearMap.rTensor _ ((LinearMap.mul' R) A)) ∘ₗ (LinearMap.lTensor _ comul)) ∘ₗ
              ((TensorProduct.assoc R) _ _ _).symm.toLinearMap ∘ₗ (LinearMap.lTensor _ comul) :=
      by simp_rw [assoc_symm_comp_lTensor_lTensor, comp_assoc]
    _ =
        ((TensorProduct.lid R) (A ⊗[R] A)).toLinearMap ∘ₗ
          (LinearMap.rTensor _ counit) ∘ₗ
            (LinearMap.lTensor _ comul) ∘ₗ
              ((LinearMap.lTensor _ ((LinearMap.mul' R) A)) ∘ₗ
                ((TensorProduct.assoc R) _ _ _).toLinearMap ∘ₗ (LinearMap.rTensor _ comul)) :=
      by
      rw [rTensor_comp_lTensor', h]
      simp_rw [comp_assoc]
    _ =
        ((TensorProduct.lid R) (A ⊗[R] A)).toLinearMap ∘ₗ
          ((LinearMap.lTensor _ (comul ∘ₗ ((LinearMap.mul' R) A))) ∘ₗ
              (LinearMap.rTensor _ counit)) ∘ₗ
            ((TensorProduct.assoc R) _ _ _).toLinearMap ∘ₗ (LinearMap.rTensor _ comul) :=
      by
      rw [← rTensor_comp_lTensor', ← lTensor_comp_lTensor]
      simp_rw [comp_assoc]
    _ =
        ((TensorProduct.lid R) (A ⊗[R] A)).toLinearMap ∘ₗ
          (LinearMap.lTensor _ (comul ∘ₗ ((LinearMap.mul' R) A))) ∘ₗ
            ((LinearMap.rTensor _ counit) ∘ₗ ((TensorProduct.assoc R) _ _ _).toLinearMap) ∘ₗ
              (LinearMap.rTensor _ comul) :=
      by simp_rw [comp_assoc]
    _ =
        ((TensorProduct.lid R) (A ⊗[R] A)).toLinearMap ∘ₗ
          (LinearMap.lTensor _ (comul ∘ₗ ((LinearMap.mul' R) A))) ∘ₗ
            (((TensorProduct.assoc R) _ _ _).toLinearMap ∘ₗ
                (LinearMap.rTensor _ (LinearMap.rTensor _ counit))) ∘ₗ
              (LinearMap.rTensor _ comul) :=
      by simp_rw [assoc_comp_rTensor_rTensor]
    _ =
        ((TensorProduct.lid R) (A ⊗[R] A)).toLinearMap ∘ₗ
          (LinearMap.lTensor _ (comul ∘ₗ ((LinearMap.mul' R) A))) ∘ₗ
            ((TensorProduct.assoc R) _ _ _).toLinearMap ∘ₗ
              (LinearMap.rTensor _ ((TensorProduct.lid R) A).symm.toLinearMap) :=
      by
      rw [← rTensor_counit_comp_comul', ← rTensor_comp_rTensor]
      simp_rw [comp_assoc]
    _ = comul ∘ₗ ((LinearMap.mul' R) A) := by
      apply ext'
      simp_all


-- @@ L395-397 expanded
theorem counit_comp_mul_comp_rTensor_unit_eq_counit :
    counit ∘ₗ ((LinearMap.mul' R) A) ∘ₗ (LinearMap.rTensor _ (Algebra.linearMap R A)) =
      counit ∘ₗ ((TensorProduct.lid R) _).toLinearMap :=
  by rw [Algebra.mul_comp_rTensor_unit]


-- @@ L398-401 expanded
theorem counit_comp_mul_comp_lTensor_unit_eq_counit :
    counit ∘ₗ ((LinearMap.mul' R) A) ∘ₗ (LinearMap.lTensor _ (Algebra.linearMap R A)) =
      counit ∘ₗ (TensorProduct.rid _ _).toLinearMap :=
  by rw [Algebra.mul_comp_lTensor_unit]


-- @@ L402-406 expanded
theorem rTensor_counit_comp_comul_comp_unit_eq_unit :
    (LinearMap.rTensor _ counit) ∘ₗ comul ∘ₗ Algebra.linearMap R A =
      ((TensorProduct.lid R) _).symm.toLinearMap ∘ₗ Algebra.linearMap R A :=
  by
  rw [← LinearMap.comp_assoc, rTensor_counit_comp_comul]
  rfl


-- @@ L407-411 expanded
theorem lTensor_counit_comp_comul_comp_unit_eq_unit :
    (LinearMap.lTensor _ counit) ∘ₗ comul ∘ₗ Algebra.linearMap R A =
      (TensorProduct.rid _ _).symm.toLinearMap ∘ₗ Algebra.linearMap R A :=
  by
  rw [← LinearMap.comp_assoc, lTensor_counit_comp_comul]
  rfl


-- @@ L413-422 expanded
/-- An algebra and coalgebra with the Frobenius tensor compatibility law. -/
class FrobeniusAlgebra (R A : Type*) [CommSemiring R] [Semiring A] extends Algebra R A,
    Coalgebra R A where
  lTensor_mul_comp_rTensor_comul_commute :
    (LinearMap.lTensor A (LinearMap.mul' R A)) ∘ₗ
        (TensorProduct.assoc _ _ _ _).toLinearMap ∘ₗ (LinearMap.rTensor A comul) =
      (LinearMap.rTensor A (LinearMap.mul' R A)) ∘ₗ
        (TensorProduct.assoc _ _ _ _).symm.toLinearMap ∘ₗ (LinearMap.lTensor A comul)


-- @@ L424-424 verbatim
attribute [instance] FrobeniusAlgebra.toAlgebra

-- @@ L425-425 verbatim
attribute [instance] FrobeniusAlgebra.toCoalgebra


-- @@ L427-427 verbatim
variable {R A : Type*} [CommSemiring R] [Semiring A] [FrobeniusAlgebra R A]

-- @@ L428-432 expanded
theorem FrobeniusAlgebra.lTensor_mul_comp_rTensor_comul_eq_comul_comp_mul :
    (LinearMap.lTensor A (LinearMap.mul' R A)) ∘ₗ
        (TensorProduct.assoc _ _ _ _).toLinearMap ∘ₗ (LinearMap.rTensor A comul) =
      comul ∘ₗ LinearMap.mul' R A :=
  lTensor_mul_comp_rTensor_comul_of FrobeniusAlgebra.lTensor_mul_comp_rTensor_comul_commute


-- @@ L434-438 expanded
theorem FrobeniusAlgebra.rTensor_mul_comp_lTensor_comul_eq_comul_comp_mul :
    (LinearMap.rTensor A (LinearMap.mul' R A)) ∘ₗ
        (TensorProduct.assoc _ _ _ _).symm.toLinearMap ∘ₗ (LinearMap.lTensor A comul) =
      comul ∘ₗ LinearMap.mul' R A :=
  by rw [← lTensor_mul_comp_rTensor_comul_commute, lTensor_mul_comp_rTensor_comul_eq_comul_comp_mul]


-- @@ L440-447 expanded
theorem FrobeniusAlgebra.rTensor_mul_comp_lTensor_comul_unit_eq_comul :
    (LinearMap.rTensor A (LinearMap.mul' R A)) ∘ₗ
        (TensorProduct.assoc _ _ _ _).symm.toLinearMap ∘ₗ
          (LinearMap.lTensor A (comul ∘ₗ Algebra.linearMap R A)) =
      comul ∘ₗ (TensorProduct.rid R _).toLinearMap :=
  by
  simp_rw [← lTensor_comp_lTensor, ← LinearMap.comp_assoc]
  rw [LinearMap.comp_assoc (LinearMap.lTensor A comul),
    rTensor_mul_comp_lTensor_comul_eq_comul_comp_mul, LinearMap.comp_assoc,
    Algebra.mul_comp_lTensor_unit]


-- @@ L449-456 expanded
theorem FrobeniusAlgebra.lTensor_mul_comp_rTensor_comul_unit :
    (LinearMap.lTensor A (LinearMap.mul' R A)) ∘ₗ
        (TensorProduct.assoc R _ _ _).toLinearMap ∘ₗ
          (LinearMap.rTensor A (comul ∘ₗ Algebra.linearMap R A)) =
      comul ∘ₗ (TensorProduct.lid _ _).toLinearMap :=
  by
  simp_rw [← rTensor_comp_rTensor, ← LinearMap.comp_assoc]
  rw [LinearMap.comp_assoc (LinearMap.rTensor A comul),
    lTensor_mul_comp_rTensor_comul_eq_comul_comp_mul, LinearMap.comp_assoc,
    Algebra.mul_comp_rTensor_unit]


-- @@ L458-466 expanded
theorem FrobeniusAlgebra.rTensor_counit_mul_comp_lTensor_comul :
    (LinearMap.rTensor A (counit ∘ₗ LinearMap.mul' R A)) ∘ₗ
        (TensorProduct.assoc _ _ _ _).symm.toLinearMap ∘ₗ (LinearMap.lTensor A comul) =
      (TensorProduct.lid _ _).symm.toLinearMap ∘ₗ LinearMap.mul' R A :=
  by
  rw [← rTensor_comp_rTensor, LinearMap.comp_assoc,
    rTensor_mul_comp_lTensor_comul_eq_comul_comp_mul, ← LinearMap.comp_assoc,
    rTensor_counit_comp_comul]
  rfl


-- @@ L468-476 expanded
theorem FrobeniusAlgebra.lTensor_counit_mul_comp_rTensor_comul :
    (LinearMap.lTensor A (counit ∘ₗ LinearMap.mul' R A)) ∘ₗ
        (TensorProduct.assoc _ _ _ _).toLinearMap ∘ₗ (LinearMap.rTensor A comul) =
      (TensorProduct.rid _ _).symm.toLinearMap ∘ₗ LinearMap.mul' R A :=
  by
  rw [← lTensor_comp_lTensor, LinearMap.comp_assoc,
    lTensor_mul_comp_rTensor_comul_eq_comul_comp_mul, ← LinearMap.comp_assoc,
    lTensor_counit_comp_comul]
  rfl


-- @@ L478-492 expanded
/-- "snake equations" v1 -/
theorem FrobeniusAlgebra.rTensor_counit_mul_comp_lTensor_comul_unit :
    (LinearMap.rTensor A (counit ∘ₗ LinearMap.mul' R A)) ∘ₗ
        (TensorProduct.assoc _ _ _ _).symm.toLinearMap ∘ₗ
          (LinearMap.lTensor A (comul ∘ₗ Algebra.linearMap R A)) =
      (TensorProduct.comm _ _ _).toLinearMap :=
  by
  rw [← lTensor_comp_lTensor]
  simp_rw [← LinearMap.comp_assoc (LinearMap.lTensor A (Algebra.linearMap R A)),
    rTensor_counit_mul_comp_lTensor_comul, LinearMap.comp_assoc, Algebra.mul_comp_lTensor_unit]
  apply TensorProduct.ext'
  intro a b
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, TensorProduct.rid_tmul,
    TensorProduct.lid_symm_apply, TensorProduct.comm_tmul]
  simpa using (TensorProduct.smul_tmul (R := R) (R' := R) (M := R) (N := A) b (1 : R) a).symm


-- @@ L494-508 expanded
/-- "snake equations" v2 -/
theorem FrobeniusAlgebra.lTensor_counit_mul_comp_rTensor_comul_unit :
    (LinearMap.lTensor A (counit ∘ₗ LinearMap.mul' R A)) ∘ₗ
        (TensorProduct.assoc _ _ _ _).toLinearMap ∘ₗ
          (LinearMap.rTensor A (comul ∘ₗ Algebra.linearMap R A)) =
      (TensorProduct.comm _ _ _).toLinearMap :=
  by
  rw [← rTensor_comp_rTensor]
  simp_rw [← LinearMap.comp_assoc (LinearMap.rTensor A (Algebra.linearMap R A)),
    lTensor_counit_mul_comp_rTensor_comul, LinearMap.comp_assoc, Algebra.mul_comp_rTensor_unit]
  apply TensorProduct.ext'
  intro r a
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, TensorProduct.lid_tmul,
    TensorProduct.rid_symm_apply, TensorProduct.comm_tmul]
  simpa only [smul_eq_mul, mul_one] using
    TensorProduct.smul_tmul (R := R) (R' := R) (M := A) (N := R) r a (1 : R)

