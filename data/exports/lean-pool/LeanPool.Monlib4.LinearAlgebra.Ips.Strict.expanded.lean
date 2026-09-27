/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Associator


-- @@ L10-12 verbatim
/-!
# Strict tensor product (wip)
-/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-18 verbatim
variable {R E F G : Type _} [CommSemiring R] [AddCommGroup E] [AddCommGroup F] [AddCommGroup G]
  [Module R E] [Module R F] [Module R G]


-- @@ L20-20 verbatim
open scoped TensorProduct


-- @@ L22-25 verbatim
@[reducible, instance]
noncomputable def TensorProduct.assocHasCoe :
  CoeFun ((E ⊗[R] F) ⊗[R] G) (fun _ ↦ E ⊗[R] (F ⊗[R] G))
    where coe x := TensorProduct.assoc R E F G x


-- @@ L27-30 verbatim
@[reducible, instance]
noncomputable def TensorProduct.assocSymmHasCoe :
  CoeFun (E ⊗[R] (F ⊗[R] G)) (fun _ ↦ (E ⊗[R] F) ⊗[R] G)
    where coe x := (TensorProduct.assoc R E F G).symm x


-- @@ L32-34 verbatim
theorem TensorProduct.assoc_tmul_coe (a : E) (b : F) (c : G) :
    (a ⊗ₜ[R] b) ⊗ₜ[R] c = ↑(a ⊗ₜ[R] (b ⊗ₜ[R] c)) :=
  rfl


-- @@ L36-37 verbatim
theorem TensorProduct.assoc_coe_coe (a : (E ⊗[R] F) ⊗[R] G) :
    a = ↑(a : E ⊗[R] (F ⊗[R] G)) := by simp only [LinearEquiv.symm_apply_apply]


-- @@ L39-41 verbatim
theorem TensorProduct.tmul_assoc_coe (a : E) (b : F) (c : G) :
    a ⊗ₜ[R] (b ⊗ₜ[R] c) = ↑((a ⊗ₜ[R] b) ⊗ₜ[R] c) :=
  rfl


-- @@ L43-44 verbatim
theorem TensorProduct.coe_coe_assoc (a : E ⊗[R] (F ⊗[R] G)) :
    a = ↑(a : (E ⊗[R] F) ⊗[R] G) := by simp only [LinearEquiv.apply_symm_apply]


-- @@ L46-49 verbatim
@[reducible, instance]
noncomputable def TensorProduct.lidHasCoe :
    CoeFun (R ⊗[R] E) (fun _ => E) where
  coe x := TensorProduct.lid R E x


-- @@ L51-54 verbatim
@[reducible, instance]
noncomputable def TensorProduct.ridHasCoe :
    CoeFun (E ⊗[R] R) (fun _ => E) where
  coe x := TensorProduct.rid R E x


-- @@ L56-59 verbatim
@[reducible, instance]
noncomputable def TensorProduct.lidSymmHasCoe :
    Coe E (R ⊗[R] E) where
  coe x := (TensorProduct.lid R E).symm x


-- @@ L61-64 verbatim
@[reducible, instance]
noncomputable def TensorProduct.ridSymmHasCoe :
    Coe E (E ⊗[R] R) where
  coe x := (TensorProduct.rid R E).symm x


-- @@ L66-68 verbatim
theorem TensorProduct.lid_coe (x : E) (r : R) :
  (r ⊗ₜ[R] x : R ⊗[R] E) = r • x :=
  by simp only [lid_symm_apply, smul_tmul', smul_eq_mul, mul_one]


-- @@ L70-71 verbatim
theorem TensorProduct.rid_coe (x : E) (r : R) : (x ⊗ₜ[R] r) = r • x :=
  by simp only [rid_symm_apply, smul_tmul', smul_tmul, smul_eq_mul, mul_one]


-- @@ L73-74 verbatim
theorem TensorProduct.lid_symm_coe (x : E) : (x : R ⊗[R] E) = (1 : R) ⊗ₜ[R] x :=
  rfl


-- @@ L76-77 verbatim
theorem TensorProduct.rid_symm_coe (x : E) : (x : E ⊗[R] R) = x ⊗ₜ[R] (1 : R) :=
  rfl


-- @@ L79-80 verbatim
theorem TensorProduct.lid_coe' (x : E) (r : R) : r ⊗ₜ[R] x = r • x := by
  rw [TensorProduct.lid_symm_coe, TensorProduct.smul_tmul', smul_eq_mul, mul_one]


-- @@ L82-84 verbatim
theorem TensorProduct.rid_coe' (x : E) (r : R) : x ⊗ₜ[R] r = r • x := by
  rw [TensorProduct.rid_symm_coe, TensorProduct.smul_tmul', TensorProduct.smul_tmul, smul_eq_mul,
    mul_one]


-- @@ L86-87 verbatim
theorem TensorProduct.lid_coe_rid_coe (x : E) :
  (x : R ⊗[R] E) = (x : E ⊗[R] R) := by simp only [LinearEquiv.apply_symm_apply]


-- @@ L89-92 verbatim
@[reducible, instance]
noncomputable def funTensorProductAssocHasCoe {A : Type _} :
    CoeFun (((E ⊗[R] F) ⊗[R] G → A)) (fun _ => E ⊗[R] (F ⊗[R] G) → A)
    where coe f x := f x


-- @@ L94-101 verbatim
@[reducible, instance]
noncomputable def LinearMap.tensorProductAssocHasCoe {A : Type _} [AddCommMonoid A] [Module R A] :
    Coe ((E ⊗[R] F) ⊗[R] G →ₗ[R] A) (E ⊗[R] (F ⊗[R] G) →ₗ[R] A)
    where coe f :=
    f ∘ₗ
      (((TensorProduct.assoc R E F G).symm :
          E ⊗[R] (F ⊗[R] G) ≃ₗ[R] (E ⊗[R] F) ⊗[R] G) :
        E ⊗[R] (F ⊗[R] G) →ₗ[R] (E ⊗[R] F) ⊗[R] G)


-- @@ L103-106 verbatim
@[reducible, instance]
noncomputable def funTensorProductAssocHasCoe' {A : Type _} :
    Coe (E ⊗[R] (F ⊗[R] G) → A) ((E ⊗[R] F) ⊗[R] G → A)
    where coe f x := f x


-- @@ L108-115 verbatim
@[reducible, instance]
noncomputable def LinearMap.tensorProductAssocHasCoe' {A : Type _} [AddCommMonoid A] [Module R A] :
    Coe (E ⊗[R] (F ⊗[R] G) →ₗ[R] A) ((E ⊗[R] F) ⊗[R] G →ₗ[R] A)
    where coe f :=
    f ∘ₗ
      ((TensorProduct.assoc R E F G :
          (E ⊗[R] F) ⊗[R] G ≃ₗ[R] E ⊗[R] (F ⊗[R] G)) :
        (E ⊗[R] F) ⊗[R] G →ₗ[R] E ⊗[R] (F ⊗[R] G))


-- @@ L117-120 verbatim
@[reducible, instance]
noncomputable def funLidHasCoe {A : Type _} :
    CoeFun (R ⊗[R] E → A) (fun _ ↦ E → A) where
  coe f x := f x


-- @@ L122-125 verbatim
@[reducible, instance]
noncomputable def LinearMap.tensorProductLidHasCoe {A : Type _} [AddCommMonoid A] [Module R A] :
    Coe (R ⊗[R] E →ₗ[R] A) (E →ₗ[R] A) where
  coe f := f ∘ₗ ↑(TensorProduct.lid R E).symm


-- @@ L127-130 verbatim
@[reducible, instance]
noncomputable def funLidHasCoe' {A : Type _} :
    Coe (E → A) (R ⊗[R] E → A) where
  coe f x := f x


-- @@ L132-135 verbatim
@[reducible, instance]
noncomputable def LinearMap.tensorProductLidHasCoe' {A : Type _} [AddCommMonoid A] [Module R A] :
    Coe (E →ₗ[R] A) (R ⊗[R] E →ₗ[R] A) where
  coe f := f ∘ₗ ↑(TensorProduct.lid R E)


-- @@ L137-140 verbatim
@[reducible, instance]
noncomputable def funRidHasCoe {A : Type _} :
    CoeFun (E ⊗[R] R → A) (fun _ => E → A) where
  coe f x := f x


-- @@ L142-145 verbatim
@[reducible, instance]
noncomputable def LinearMap.tensorProductRidHasCoe {A : Type _} [AddCommMonoid A] [Module R A] :
    Coe (E ⊗[R] R →ₗ[R] A) (E →ₗ[R] A) where
  coe f := f ∘ₗ ↑(TensorProduct.rid R E).symm


-- @@ L147-150 verbatim
@[reducible, instance]
noncomputable def funRidHasCoe' {A : Type _} :
    Coe (E → A) (E ⊗[R] R → A) where
  coe f x := f x


-- @@ L152-155 verbatim
@[reducible, instance]
noncomputable def LinearMap.tensorProductRidHasCoe' {A : Type _} [AddCommMonoid A] [Module R A] :
    Coe (E →ₗ[R] A) (E ⊗[R] R →ₗ[R] A) where
  coe f := f ∘ₗ ↑(TensorProduct.rid R E)


-- @@ L157-160 verbatim
theorem LinearMap.lid_coe {A : Type _} [AddCommMonoid A] [Module R A] (f : E →ₗ[R] A) :
    f = (f : R ⊗[R] E →ₗ[R] A) := by
    simp only [LinearMap.comp_assoc, LinearEquiv.comp_coe,
      LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap, LinearMap.comp_id]


-- @@ L162-165 verbatim
theorem LinearMap.lid_symm_coe {A : Type _} [AddCommMonoid A] [Module R A] (f : R ⊗[R] E →ₗ[R] A) :
    f = (f : E →ₗ[R] A) := by
  simp only [LinearMap.comp_assoc, LinearEquiv.comp_coe,
    LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap, LinearMap.comp_id]


-- @@ L167-170 verbatim
theorem LinearMap.rid_coe {A : Type _} [AddCommMonoid A] [Module R A] (f : E →ₗ[R] A) :
    f = (f : E ⊗[R] R →ₗ[R] A) := by
  simp only [LinearMap.comp_assoc, LinearEquiv.comp_coe,
    LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap, LinearMap.comp_id]


-- @@ L172-175 verbatim
theorem LinearMap.rid_symm_coe {A : Type _} [AddCommMonoid A] [Module R A] (f : E ⊗[R] R →ₗ[R] A) :
    f = (f : E →ₗ[R] A) := by
  simp only [LinearMap.comp_assoc, LinearEquiv.comp_coe,
    LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap, LinearMap.comp_id]


-- @@ L177-178 verbatim
example {A : Type _} (f : E ⊗[R] (F ⊗[R] G) → A) :
    f = ↑(↑f : (E ⊗[R] F) ⊗[R] G → A) := by simp only [LinearEquiv.apply_symm_apply]
