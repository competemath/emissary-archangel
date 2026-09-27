/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import LeanPool.Monlib4.LinearAlgebra.QuantumSet.Basic
import LeanPool.Monlib4.LinearAlgebra.End
import LeanPool.Monlib4.LinearAlgebra.Ips.TensorHilbert
import LeanPool.Monlib4.LinearAlgebra.TensorProduct.BasicLemmas
import Mathlib.Tactic.Positivity.Finset


-- @@ L14-18 verbatim
/-!
# LeanPool.Monlib4.LinearAlgebra.QuantumSet.QIso

Imported Lean Pool material for `LeanPool.Monlib4.LinearAlgebra.QuantumSet.QIso`.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
local notation "lT" => LinearMap.lTensor

-- @@ L23-23 verbatim
local notation "rT" => LinearMap.rTensor


-- @@ L25-25 verbatim
open scoped InnerProductSpace TensorProduct


-- @@ L27-28 verbatim
variable {B₁ B₂ : Type*} [starAlgebra B₁] [starAlgebra B₂]
  [QuantumSet B₁] [QuantumSet B₂]


-- @@ L30-35 expanded
/-- The unit-preservation expression for a quantum function. -/
noncomputable abbrev QFun.mapUnit' {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)) :=
  P ∘ₗ (LinearMap.rTensor _ (Algebra.linearMap ℂ _)) ∘ₗ (TensorProduct.lid ℂ _).symm.toLinearMap


-- @@ L37-45 expanded
/-- The multiplication-preservation expression for a quantum function. -/
noncomputable abbrev QFun.mapMul' {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)) :=
  (LinearMap.lTensor _ (LinearMap.mul' ℂ B₂)) ∘ₗ
    (TensorProduct.assoc ℂ _ _ _).toLinearMap ∘ₗ
      (LinearMap.rTensor _ P) ∘ₗ
        (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap ∘ₗ (LinearMap.lTensor _ P)


-- @@ L47-59 expanded
/-- The reality condition expression for a quantum function. -/
noncomputable abbrev QFun.mapReal' {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)) :=
  (LinearMap.rTensor _
      ((TensorProduct.lid ℂ _).toLinearMap ∘ₗ
        (LinearMap.rTensor _ (Coalgebra.counit ∘ₗ LinearMap.mul' ℂ _)) ∘ₗ
          (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap)) ∘ₗ
    (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap ∘ₗ
      (LinearMap.lTensor B₁
          (((LinearMap.rTensor B₂ (LinearMap.adjoint P))) ∘ₗ
            (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap)) ∘ₗ
        (TensorProduct.assoc ℂ _ _ _).toLinearMap ∘ₗ
          (LinearMap.lTensor (B₁ ⊗[ℂ] H) ((Coalgebra.comul ∘ₗ Algebra.linearMap ℂ B₂))) ∘ₗ
            (TensorProduct.rid ℂ (B₁ ⊗[ℂ] H)).symm.toLinearMap


-- @@ L61-72 expanded
/-- A quantum function between quantum sets, encoded as a linear map with unit,
multiplication, and reality compatibility. -/
class QFun (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)) : Prop where
  map_unit :
    QFun.mapUnit' P =
      (LinearMap.lTensor _ (Algebra.linearMap ℂ _)) ∘ₗ (TensorProduct.rid ℂ _).symm.toLinearMap
  map_mul :
    QFun.mapMul' P =
      P ∘ₗ
        (LinearMap.rTensor _ (LinearMap.mul' ℂ B₁)) ∘ₗ
          (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap
  map_real : QFun.mapReal' P = P


-- @@ L74-78 verbatim
lemma TensorProduct.rid_symm_adjoint {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] :
    LinearMap.adjoint (TensorProduct.rid 𝕜 E).symm.toLinearMap =
      (TensorProduct.rid 𝕜 E).toLinearMap :=
by rw [← LinearMap.adjoint_adjoint (TensorProduct.rid 𝕜 E).toLinearMap, TensorProduct.rid_adjoint]


-- @@ L80-81 verbatim
variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]


-- @@ L83-119 expanded
lemma QFun.adjoint_eq {P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)} (hp : QFun H P) :
    LinearMap.adjoint P =
      (TensorProduct.rid ℂ _).toLinearMap ∘ₗ
        (LinearMap.lTensor _ (Coalgebra.counit ∘ₗ LinearMap.mul' ℂ _)) ∘ₗ
          (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap ∘ₗ
            (LinearMap.lTensor _
                (((TensorProduct.assoc ℂ _ _ _).toLinearMap ∘ₗ (LinearMap.rTensor _ P)))) ∘ₗ
              (TensorProduct.assoc ℂ _ _ _).toLinearMap ∘ₗ
                (LinearMap.rTensor _
                  ((TensorProduct.assoc ℂ _ _ _).toLinearMap ∘ₗ
                    (LinearMap.rTensor _ (Coalgebra.comul ∘ₗ Algebra.linearMap ℂ _)) ∘ₗ
                      (TensorProduct.lid ℂ _).symm.toLinearMap)) :=
  by
  simp_rw [Coalgebra.comul_eq_mul_adjoint, Coalgebra.counit_eq_unit_adjoint]
  nth_rw 1 [← LinearMap.adjoint_adjoint (LinearMap.mul' ℂ B₂)]
  nth_rw 1 [← LinearMap.adjoint_adjoint (Algebra.linearMap ℂ B₁)]
  simp_rw [← LinearMap.adjoint_comp, ← LinearMap.lTensor_adjoint, ← LinearMap.rTensor_adjoint, ←
    TensorProduct.lid_adjoint, ← TensorProduct.assoc_adjoint]
  nth_rw 4 [← TensorProduct.assoc_symm_adjoint]
  nth_rw 3 [← TensorProduct.assoc_symm_adjoint]
  simp_rw [← LinearMap.adjoint_comp, ← LinearMap.rTensor_adjoint]
  nth_rw 2 [← LinearMap.adjoint_adjoint P]
  rw [← LinearMap.rTensor_adjoint]
  nth_rw 2 [← TensorProduct.assoc_symm_adjoint]
  simp_rw [← LinearMap.adjoint_comp, ← LinearMap.lTensor_adjoint, ← LinearMap.adjoint_comp]
  rw [← TensorProduct.rid_symm_adjoint]
  simp only [← LinearMap.adjoint_comp]
  simp_rw [← Coalgebra.comul_eq_mul_adjoint, LinearMap.comp_assoc]
  nth_rw 1 [← hp.map_real]
  simp only [QFun.mapReal', Coalgebra.counit_eq_unit_adjoint]
  apply congrArg LinearMap.adjoint
  have hB₁ :
    (@Algebra.linearMap ℂ B₁ _ _ QuantumSet.isFrobeniusAlgebra.toAlgebra) =
      Algebra.linearMap ℂ B₁ :=
    LinearMap.ext fun r => by simp [Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]
  have hB₂ :
    (@Algebra.linearMap ℂ B₂ _ _ QuantumSet.isFrobeniusAlgebra.toAlgebra) =
      Algebra.linearMap ℂ B₂ :=
    LinearMap.ext fun r => by simp [Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]
  rw [hB₁, hB₂]


-- @@ L121-123 expanded
/-- The counit-preservation expression for a quantum function. -/
noncomputable abbrev QFun.mapCounit' (P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)) :=
  (TensorProduct.rid ℂ _).toLinearMap ∘ₗ (LinearMap.lTensor H Coalgebra.counit) ∘ₗ P


-- @@ L125-131 expanded
/-- The comultiplication-preservation expression for a quantum function. -/
noncomputable abbrev QFun.mapComul' (P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)) :=
  (LinearMap.rTensor B₂ P) ∘ₗ
    (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap ∘ₗ
      (LinearMap.lTensor B₁ P) ∘ₗ
        (TensorProduct.assoc ℂ _ _ _).toLinearMap ∘ₗ (LinearMap.rTensor H Coalgebra.comul)


-- @@ L133-140 expanded
/-- A quantum function is quantum-bijective when it also preserves counit and
comultiplication. -/
class QFun.qBijective {P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)} (hp : QFun H P) : Prop where
  map_counit :
    QFun.mapCounit' P =
      (TensorProduct.lid ℂ H).toLinearMap ∘ₗ (LinearMap.rTensor H Coalgebra.counit)
  map_comul :
    QFun.mapComul' P =
      (TensorProduct.assoc ℂ _ _ _).symm.toLinearMap ∘ₗ (LinearMap.lTensor H Coalgebra.comul) ∘ₗ P


-- @@ L143-143 verbatim
section

-- @@ L144-144 verbatim
variable {R : Type*} [CommSemiring R]


-- @@ L146-146 verbatim
local notation "m" => LinearMap.mul' R

-- @@ L147-147 verbatim
local notation "ϰ" => TensorProduct.assoc R

-- @@ L148-148 verbatim
local notation "τ" => TensorProduct.lid R

-- @@ L149-149 verbatim
local notation "τ'" => TensorProduct.rid R

-- @@ L150-150 verbatim
local notation x " ⊗ₘ " y => TensorProduct.map x y


-- @@ L152-155 expanded
theorem LinearMap.comp_rid_eq_rid_comp_rTensor {M M₂ : Type*} [AddCommMonoid M] [Module R M]
    [AddCommMonoid M₂] [Module R M₂] (f : M →ₗ[R] M₂) :
    f ∘ₗ (τ' M).toLinearMap = (τ' M₂).toLinearMap ∘ₗ (LinearMap.rTensor R f) := by ext; simp


-- @@ L157-166 expanded
theorem LinearMap.rTensor_lid_symm_comp_eq_assoc_symm_comp_lTensor_comp_lid_symm
    {M₁ M₂ M₃ M₄ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
    [AddCommMonoid M₄] [Module R M₁] [Module R M₂] [Module R M₃] [Module R M₄]
    (f : M₁ ⊗[R] M₂ →ₗ[R] M₃ ⊗[R] M₄) :
    (LinearMap.rTensor M₄ (τ _).symm.toLinearMap) ∘ₗ f =
      (ϰ _ _ _).symm.toLinearMap ∘ₗ (LinearMap.lTensor _ f) ∘ₗ (τ _).symm.toLinearMap :=
  by
  ext a b
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset (R := R) (f (a ⊗ₜ[R] b))
  simp [hS, TensorProduct.tmul_sum]


-- @@ L168-178 expanded
theorem LinearMap.rTensor_tensor_eq_assoc_comp_rTensor_rTensor_comp_assoc_symm {A B C D : Type*}
    [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D] [Module R A]
    [Module R B] [Module R C] [Module R D] (x : A →ₗ[R] D) :
    LinearMap.rTensor (B ⊗[R] C) x =
      (ϰ _ _ _).toLinearMap ∘ₗ
        LinearMap.rTensor C (LinearMap.rTensor B x) ∘ₗ (ϰ A B C).symm.toLinearMap :=
  by
  rw [← TensorProduct.assoc_symm_comp_rTensor, ← LinearMap.comp_assoc, LinearEquiv.comp_coe,
    LinearEquiv.symm_trans_self]
  rfl


-- @@ L179-186 expanded
theorem LinearMap.rTensor_rTensor_eq_assoc_symm_comp_rTensor_comp_assoc {A B C D : Type*}
    [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D] [Module R A]
    [Module R B] [Module R C] [Module R D] (x : A →ₗ[R] D) :
    LinearMap.rTensor C (LinearMap.rTensor B x) =
      (ϰ _ _ _).symm.toLinearMap ∘ₗ (LinearMap.rTensor _ x) ∘ₗ (ϰ _ _ _).toLinearMap :=
  by
  rw [rTensor_tensor_eq_assoc_comp_rTensor_rTensor_comp_assoc_symm]
  ext
  simp


-- @@ L188-192 expanded
theorem TensorProduct.lTensor_lTensor_comp_assoc {A B C D : Type*} [AddCommMonoid A]
    [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D] [Module R A] [Module R B] [Module R C]
    [Module R D] (x : A →ₗ[R] D) :
    LinearMap.lTensor B (LinearMap.lTensor C x) ∘ₗ (ϰ _ _ _).toLinearMap =
      (ϰ _ _ _).toLinearMap ∘ₗ LinearMap.lTensor _ x :=
  by ext; simp


-- @@ L194-200 expanded
theorem LinearMap.rTensor_assoc_symm_comp_assoc_symm {A B C D : Type*} [AddCommMonoid A]
    [AddCommMonoid B] [AddCommMonoid C] [AddCommMonoid D] [Module R A] [Module R B] [Module R C]
    [Module R D] :
    LinearMap.rTensor D (ϰ A B C).symm.toLinearMap ∘ₗ (ϰ A (B ⊗[R] C) D).symm.toLinearMap =
      (ϰ (A ⊗[R] B) C D).symm.toLinearMap ∘ₗ
        (ϰ A B (C ⊗[R] D)).symm.toLinearMap ∘ₗ (LinearMap.lTensor A (ϰ B C D).toLinearMap) :=
  by ext; simp


-- @@ L202-204 expanded
theorem rid_tensor {A B : Type*} [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B] :
    (τ' (TensorProduct R A B)).toLinearMap =
      LinearMap.lTensor A (τ' B).toLinearMap ∘ₗ (ϰ A B R).toLinearMap :=
  by ext; simp


-- @@ L206-216 expanded
theorem FrobeniusAlgebra.snake_equation_2 {A : Type*} [Semiring A] [FrobeniusAlgebra R A] :
    (τ' _).toLinearMap ∘ₗ
        (LinearMap.lTensor _ (Coalgebra.counit ∘ₗ LinearMap.mul' R _)) ∘ₗ
          (ϰ _ _ _).toLinearMap ∘ₗ
            (LinearMap.rTensor _ (Coalgebra.comul ∘ₗ Algebra.linearMap R _)) ∘ₗ
              (τ A).symm.toLinearMap =
      1 :=
  by
  nth_rw 2 [← LinearMap.comp_assoc]
  nth_rw 2 [← LinearMap.comp_assoc]
  nth_rw 2 [LinearMap.comp_assoc]
  rw [lTensor_counit_mul_comp_rTensor_comul_unit]
  ext
  simp


-- @@ L218-218 verbatim
end


-- @@ L220-220 verbatim
local notation "ϰ" => TensorProduct.assoc ℂ

-- @@ L221-221 verbatim
local notation "τ" => TensorProduct.lid ℂ

-- @@ L222-222 verbatim
local notation "τ'" => TensorProduct.rid ℂ

-- @@ L223-223 verbatim
local notation "η" => Algebra.linearMap ℂ


-- @@ L225-277 expanded
theorem QFun.self_comp_adjoint_eq_id_of_map_comul {P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)}
    (hp : QFun H P)
    (h :
      QFun.mapComul' P =
        ((TensorProduct.assoc ℂ) _ _ _).symm.toLinearMap ∘ₗ
          (LinearMap.lTensor H Coalgebra.comul) ∘ₗ P) :
    P ∘ₗ LinearMap.adjoint P = 1 := by
  rw [QFun.adjoint_eq hp]
  simp only [← LinearMap.comp_assoc]
  rw [LinearMap.comp_rid_eq_rid_comp_rTensor]
  simp only [LinearMap.comp_assoc, rTensor_comp_lTensor']
  rw [LinearMap.rTensor_tensor_eq_assoc_comp_rTensor_rTensor_comp_assoc_symm]
  simp only [LinearMap.rTensor_comp, LinearMap.lTensor_comp, LinearMap.comp_assoc]
  rw [← LinearMap.comp_assoc _ _ ((TensorProduct.assoc ℂ) (B₁ ⊗[ℂ] H) _ _).symm.toLinearMap]
  rw [← LinearMap.comp_assoc (LinearMap.lTensor B₁ (LinearMap.rTensor B₂ P) ∘ₗ _ ∘ₗ _ ∘ₗ _ ∘ₗ _),
    LinearMap.comp_assoc (LinearMap.lTensor _ _) _ _]
  rw [← LinearMap.rTensor_assoc_symm_comp_assoc_symm]
  rw [← LinearMap.comp_assoc _ _ (LinearMap.rTensor B₂ (LinearMap.rTensor _ _)), ←
    LinearMap.comp_assoc _ _ (LinearMap.rTensor B₂ (LinearMap.rTensor _ _)), ←
    LinearMap.rTensor_comp]
  rw [LinearMap.comp_assoc, ←
    LinearMap.comp_assoc _ _ ((TensorProduct.assoc ℂ) _ _ _).symm.toLinearMap]
  rw [← TensorProduct.rTensor_lTensor_comp_assoc_symm, LinearMap.comp_assoc, ←
    LinearMap.comp_assoc _ _ ((TensorProduct.assoc ℂ) _ _ _).symm.toLinearMap, LinearEquiv.comp_coe,
    LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap, LinearMap.id_comp]
  simp only [LinearMap.comp_assoc, ← LinearMap.rTensor_comp]
  simp only [← LinearMap.comp_assoc] at h ⊢
  rw [h]
  simp only [LinearMap.comp_assoc, hp.1]
  rw [← LinearMap.comp_assoc _ _ (LinearMap.lTensor (H ⊗[ℂ] B₂) _), ← LinearMap.lTensor_comp, ←
    LinearMap.comp_assoc _ _ (LinearMap.lTensor H _), ← LinearMap.lTensor_comp, ←
    LinearMap.comp_assoc _ _ (LinearMap.lTensor _ _)]
  ext a b
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_self,
    TensorProduct.curry_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.rTensor_tmul, TensorProduct.rid_symm_apply, LinearMap.lTensor_tmul,
    Algebra.linearMap_apply, map_one, Module.End.one_apply]
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset (R := ℂ) (Coalgebra.comul (1 : B₂))
  rw [hS]
  simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum, map_sum, LinearMap.comp_apply,
    TensorProduct.assoc_tmul, TensorProduct.assoc_symm_tmul, LinearMap.lTensor_tmul,
    LinearMap.mul'_apply, TensorProduct.rid_tmul]
  simp_rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, ← TensorProduct.tmul_sum]
  congr
  simp_rw [← TensorProduct.rid_tmul, ← LinearMap.mul'_apply (R := ℂ) (A := B₂), ←
    LinearMap.comp_apply, ← LinearMap.lTensor_tmul, ← TensorProduct.assoc_tmul, ←
    LinearEquiv.coe_toLinearMap, ← map_sum]
  rw [← TensorProduct.sum_tmul, ← hS]
  have :=
    @FrobeniusAlgebra.lTensor_counit_mul_comp_rTensor_comul_unit (R := ℂ) (A := B₂) _ _
      (QuantumSet.isFrobeniusAlgebra (A := B₂))
  simp only [TensorProduct.ext_iff', LinearMap.comp_apply, LinearMap.rTensor_tmul,
    LinearEquiv.coe_coe, TensorProduct.comm_tmul, Algebra.linearMap_apply,
    Algebra.algebraMap_eq_smul_one] at this
  specialize this 1
  simp_all


-- @@ L279-386 expanded
theorem QFun.adjoint_comp_self_eq_id_of_map_counit {P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)}
    (hp : QFun H P)
    (h :
      QFun.mapCounit' P =
        ((TensorProduct.lid ℂ) H).toLinearMap ∘ₗ (LinearMap.rTensor H Coalgebra.counit)) :
    LinearMap.adjoint P ∘ₗ P = 1 := by
  rw [QFun.adjoint_eq hp]
  simp only [LinearMap.rTensor_comp, LinearMap.lTensor_comp, LinearMap.comp_assoc]
  rw [LinearMap.rTensor_lid_symm_comp_eq_assoc_symm_comp_lTensor_comp_lid_symm, ←
    LinearMap.comp_assoc (_ ∘ₗ ((TensorProduct.lid ℂ) _).symm.toLinearMap) _
      (LinearMap.rTensor _ (LinearMap.rTensor _ _)),
    ← TensorProduct.assoc_symm_comp_rTensor]
  simp only [LinearMap.comp_assoc]
  rw [← LinearMap.comp_assoc _ ((TensorProduct.assoc ℂ) B₁ H B₂).symm.toLinearMap, ←
    TensorProduct.assoc_symm_comp_rTensor, ←
    LinearMap.comp_assoc _ _ (LinearMap.rTensor _ ((Algebra.linearMap ℂ) B₁)),
    LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor]
  simp only [LinearMap.comp_assoc]
  rw [← LinearMap.comp_assoc (_ ∘ₗ _) (LinearMap.lTensor B₁ P) (LinearMap.rTensor (H ⊗[ℂ] B₂) _),
    LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor]
  have :
    ((TensorProduct.assoc ℂ) B₁ (B₁ ⊗[ℂ] H) B₂).toLinearMap ∘ₗ
        LinearMap.rTensor B₂ ((TensorProduct.assoc ℂ) B₁ B₁ H).toLinearMap ∘ₗ
          ((TensorProduct.assoc ℂ) (B₁ ⊗[ℂ] B₁) H B₂).symm.toLinearMap =
      LinearMap.lTensor _ ((TensorProduct.assoc ℂ) _ _ _).symm.toLinearMap ∘ₗ
        ((TensorProduct.assoc ℂ) _ _ _).toLinearMap :=
    by
    apply TensorProduct.ext_fourfold'
    simp_all
  calc
    ((TensorProduct.rid ℂ) (B₁ ⊗[ℂ] H)).toLinearMap ∘ₗ
          LinearMap.lTensor (B₁ ⊗[ℂ] H) Coalgebra.counit ∘ₗ
            LinearMap.lTensor (B₁ ⊗[ℂ] H) (LinearMap.mul' ℂ B₂) ∘ₗ
              ((TensorProduct.assoc ℂ) B₁ H (B₂ ⊗[ℂ] B₂)).symm.toLinearMap ∘ₗ
                LinearMap.lTensor B₁ ((TensorProduct.assoc ℂ) H B₂ B₂).toLinearMap ∘ₗ
                  LinearMap.lTensor B₁ (LinearMap.rTensor B₂ P) ∘ₗ
                    ((TensorProduct.assoc ℂ) B₁ (B₁ ⊗[ℂ] H) B₂).toLinearMap ∘ₗ
                      LinearMap.rTensor B₂ ((TensorProduct.assoc ℂ) B₁ B₁ H).toLinearMap ∘ₗ
                        ((TensorProduct.assoc ℂ) (B₁ ⊗[ℂ] B₁) H B₂).symm.toLinearMap ∘ₗ
                          LinearMap.lTensor (B₁ ⊗[ℂ] B₁) P ∘ₗ
                            LinearMap.rTensor (B₁ ⊗[ℂ] H) Coalgebra.comul ∘ₗ
                              LinearMap.rTensor (B₁ ⊗[ℂ] H) ((Algebra.linearMap ℂ) B₁) ∘ₗ
                                ((TensorProduct.lid ℂ) (B₁ ⊗[ℂ] H)).symm.toLinearMap =
        ((TensorProduct.rid ℂ) (B₁ ⊗[ℂ] H)).toLinearMap ∘ₗ
          LinearMap.lTensor (B₁ ⊗[ℂ] H) Coalgebra.counit ∘ₗ
            (((TensorProduct.assoc ℂ) _ _ _).symm.toLinearMap ∘ₗ
                LinearMap.lTensor _ (LinearMap.lTensor _ (LinearMap.mul' ℂ B₂))) ∘ₗ
              (LinearMap.lTensor _
                  (((TensorProduct.assoc ℂ) H _ _).toLinearMap ∘ₗ LinearMap.rTensor B₂ P)) ∘ₗ
                (LinearMap.lTensor _ ((TensorProduct.assoc ℂ) _ _ _).symm.toLinearMap ∘ₗ
                    ((TensorProduct.assoc ℂ) _ _ _).toLinearMap) ∘ₗ
                  LinearMap.lTensor _ P ∘ₗ
                    LinearMap.rTensor (B₁ ⊗[ℂ] H) Coalgebra.comul ∘ₗ
                      LinearMap.rTensor (B₁ ⊗[ℂ] H) ((Algebra.linearMap ℂ) B₁) ∘ₗ
                        ((TensorProduct.lid ℂ) (B₁ ⊗[ℂ] H)).symm.toLinearMap :=
      by
      rw [TensorProduct.assoc_symm_comp_lTensor_lTensor, ← this]
      simp only [LinearMap.lTensor_comp, LinearMap.comp_assoc]
    _ =
        ((TensorProduct.rid ℂ) (B₁ ⊗[ℂ] H)).toLinearMap ∘ₗ
          LinearMap.lTensor (B₁ ⊗[ℂ] H) Coalgebra.counit ∘ₗ
            ((TensorProduct.assoc ℂ) _ _ _).symm.toLinearMap ∘ₗ
              LinearMap.lTensor _
                  (LinearMap.lTensor _ (LinearMap.mul' ℂ B₂) ∘ₗ
                    ((TensorProduct.assoc ℂ) _ _ _).toLinearMap ∘ₗ
                      LinearMap.rTensor _ P ∘ₗ ((TensorProduct.assoc ℂ) _ _ _).symm.toLinearMap) ∘ₗ
                (LinearMap.lTensor _ (LinearMap.lTensor _ P) ∘ₗ
                    ((TensorProduct.assoc ℂ) _ _ _).toLinearMap) ∘ₗ
                  LinearMap.rTensor (B₁ ⊗[ℂ] H) Coalgebra.comul ∘ₗ
                    LinearMap.rTensor (B₁ ⊗[ℂ] H) ((Algebra.linearMap ℂ) B₁) ∘ₗ
                      ((TensorProduct.lid ℂ) (B₁ ⊗[ℂ] H)).symm.toLinearMap :=
      by
      rw [TensorProduct.lTensor_lTensor_comp_assoc]
      simp only [LinearMap.lTensor_comp, LinearMap.comp_assoc]
    _ =
        ((TensorProduct.rid ℂ) (B₁ ⊗[ℂ] H)).toLinearMap ∘ₗ
          LinearMap.lTensor (B₁ ⊗[ℂ] H) Coalgebra.counit ∘ₗ
            ((TensorProduct.assoc ℂ) _ _ _).symm.toLinearMap ∘ₗ
              LinearMap.lTensor _
                  (LinearMap.lTensor _ (LinearMap.mul' ℂ B₂) ∘ₗ
                    ((TensorProduct.assoc ℂ) _ _ _).toLinearMap ∘ₗ
                      LinearMap.rTensor _ P ∘ₗ
                        ((TensorProduct.assoc ℂ) _ _ _).symm.toLinearMap ∘ₗ
                          LinearMap.lTensor _ P) ∘ₗ
                ((TensorProduct.assoc ℂ) _ _ _).toLinearMap ∘ₗ
                  LinearMap.rTensor (B₁ ⊗[ℂ] H) Coalgebra.comul ∘ₗ
                    LinearMap.rTensor (B₁ ⊗[ℂ] H) ((Algebra.linearMap ℂ) B₁) ∘ₗ
                      ((TensorProduct.lid ℂ) (B₁ ⊗[ℂ] H)).symm.toLinearMap :=
      by simp only [LinearMap.lTensor_comp, LinearMap.comp_assoc]
    _ =
        ((TensorProduct.rid ℂ) (B₁ ⊗[ℂ] H)).toLinearMap ∘ₗ
          (LinearMap.lTensor (B₁ ⊗[ℂ] H) Coalgebra.counit ∘ₗ
              ((TensorProduct.assoc ℂ) _ _ _).symm.toLinearMap) ∘ₗ
            LinearMap.lTensor _
                (P ∘ₗ
                  (LinearMap.rTensor _ (LinearMap.mul' ℂ B₁)) ∘ₗ
                    ((TensorProduct.assoc ℂ) _ _ _).symm.toLinearMap) ∘ₗ
              ((TensorProduct.assoc ℂ) _ _ _).toLinearMap ∘ₗ
                LinearMap.rTensor (B₁ ⊗[ℂ] H) Coalgebra.comul ∘ₗ
                  LinearMap.rTensor (B₁ ⊗[ℂ] H) ((Algebra.linearMap ℂ) B₁) ∘ₗ
                    ((TensorProduct.lid ℂ) (B₁ ⊗[ℂ] H)).symm.toLinearMap :=
      by simp only [hp.map_mul, LinearMap.comp_assoc]
    _ =
        LinearMap.lTensor _ ((TensorProduct.rid ℂ) _).toLinearMap ∘ₗ
          (((TensorProduct.assoc ℂ) _ _ _).toLinearMap ∘ₗ
              ((TensorProduct.assoc ℂ) _ _ _).symm.toLinearMap) ∘ₗ
            LinearMap.lTensor _
                (LinearMap.lTensor _ Coalgebra.counit ∘ₗ
                  P ∘ₗ
                    (LinearMap.rTensor _ (LinearMap.mul' ℂ B₁)) ∘ₗ
                      ((TensorProduct.assoc ℂ) _ _ _).symm.toLinearMap) ∘ₗ
              ((TensorProduct.assoc ℂ) _ _ _).toLinearMap ∘ₗ
                LinearMap.rTensor (B₁ ⊗[ℂ] H) (Coalgebra.comul ∘ₗ (Algebra.linearMap ℂ) B₁) ∘ₗ
                  ((TensorProduct.lid ℂ) (B₁ ⊗[ℂ] H)).symm.toLinearMap :=
      by
      simp only [← TensorProduct.assoc_symm_comp_lTensor_lTensor, rid_tensor,
        LinearMap.lTensor_comp, LinearMap.rTensor_comp, LinearMap.comp_assoc]
    _ =
        LinearMap.lTensor _
            ((((TensorProduct.rid ℂ) _).toLinearMap ∘ₗ LinearMap.lTensor _ Coalgebra.counit ∘ₗ P) ∘ₗ
              (LinearMap.rTensor _ (LinearMap.mul' ℂ B₁)) ∘ₗ
                ((TensorProduct.assoc ℂ) _ _ _).symm.toLinearMap) ∘ₗ
          ((TensorProduct.assoc ℂ) _ _ _).toLinearMap ∘ₗ
            LinearMap.rTensor (B₁ ⊗[ℂ] H) (Coalgebra.comul ∘ₗ (Algebra.linearMap ℂ) B₁) ∘ₗ
              ((TensorProduct.lid ℂ) (B₁ ⊗[ℂ] H)).symm.toLinearMap :=
      by
      simp only [LinearEquiv.comp_coe, LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap,
        LinearMap.id_comp, LinearMap.lTensor_comp, LinearMap.comp_assoc]
    _ =
        LinearMap.lTensor _
            ((((TensorProduct.lid ℂ) H).toLinearMap ∘ₗ (LinearMap.rTensor H Coalgebra.counit)) ∘ₗ
              (LinearMap.rTensor _ (LinearMap.mul' ℂ B₁)) ∘ₗ
                ((TensorProduct.assoc ℂ) _ _ _).symm.toLinearMap) ∘ₗ
          ((TensorProduct.assoc ℂ) _ _ _).toLinearMap ∘ₗ
            LinearMap.rTensor (B₁ ⊗[ℂ] H) (Coalgebra.comul ∘ₗ (Algebra.linearMap ℂ) B₁) ∘ₗ
              ((TensorProduct.lid ℂ) (B₁ ⊗[ℂ] H)).symm.toLinearMap :=
      by simp [h]
    _ =
        LinearMap.rTensor H
          (((TensorProduct.rid ℂ) _).toLinearMap ∘ₗ
            (LinearMap.lTensor _ (Coalgebra.counit ∘ₗ LinearMap.mul' ℂ _)) ∘ₗ
              ((TensorProduct.assoc ℂ) _ _ _).toLinearMap ∘ₗ
                (LinearMap.rTensor _ (Coalgebra.comul ∘ₗ (Algebra.linearMap ℂ) _)) ∘ₗ
                  ((TensorProduct.lid ℂ) _).symm.toLinearMap) :=
      by
      ext
      obtain ⟨S, hS⟩ := TensorProduct.exists_finset (R := ℂ) (Coalgebra.comul (1 : B₁))
      simp only [TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_self,
        TensorProduct.curry_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one]
      rw [hS]
      simp [TensorProduct.sum_tmul, map_sum, TensorProduct.smul_tmul]
    _ = LinearMap.rTensor H 1 :=
      by
      convert
        congrArg (LinearMap.rTensor H)
          (@FrobeniusAlgebra.snake_equation_2 ℂ _ B₁ _
            (QuantumSet.isFrobeniusAlgebra (A := B₁))) using
        2
      first
      | rfl
      | (congr 4; ext r; simp [Algebra.algebraMap_eq_smul_one])
    _ = 1 := by ext; simp


-- @@ L388-404 expanded
theorem QFun.map_counit_of_adjoint_comp_self_eq_id {P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)}
    (hp : QFun H P) (h : LinearMap.adjoint P ∘ₗ P = 1) :
    mapCounit' P =
      ((TensorProduct.lid ℂ) H).toLinearMap ∘ₗ (LinearMap.rTensor H Coalgebra.counit) :=
  by
  have :=
    calc
      LinearMap.adjoint P ∘ₗ
            (LinearMap.lTensor H ((Algebra.linearMap ℂ) B₂) ∘ₗ
              ((TensorProduct.rid ℂ) H).symm.toLinearMap) =
          LinearMap.adjoint P ∘ₗ
            (P ∘ₗ
              LinearMap.rTensor H ((Algebra.linearMap ℂ) _) ∘ₗ
                ((TensorProduct.lid ℂ) H).symm.toLinearMap) :=
        by rw [← hp.map_unit]
      _ =
          LinearMap.rTensor H ((Algebra.linearMap ℂ) _) ∘ₗ
            ((TensorProduct.lid ℂ) H).symm.toLinearMap :=
        by rw [← LinearMap.comp_assoc, h, LinearMap.one_comp]
  apply_fun LinearMap.adjoint at this
  simp only [LinearMap.adjoint_comp, LinearMap.lTensor_adjoint, LinearMap.rTensor_adjoint,
    ← TensorProduct.rid_adjoint, LinearMap.adjoint_adjoint, ← TensorProduct.lid_adjoint,
    LinearMap.comp_assoc] at this
  rw [← sub_eq_zero] at this ⊢
  simp only [mapCounit', Coalgebra.counit_eq_unit_adjoint]
  rw [← this]
  congr <;> ext <;> simp


-- @@ L406-409 expanded
lemma LinearMap.lTensor_one {R M₁ M₂ : Type*} [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂]
    [Module R M₁] [Module R M₂] : LinearMap.lTensor M₁ (1 : M₂ →ₗ[R] M₂) = 1 := by ext; simp


-- @@ L410-413 expanded
lemma LinearMap.rTensor_one {R M₁ M₂ : Type*} [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂]
    [Module R M₁] [Module R M₂] : LinearMap.rTensor M₁ (1 : M₂ →ₗ[R] M₂) = 1 := by ext; simp


-- @@ L415-441 expanded
theorem QFun.map_comul_of_inv_eq_adjoint {P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)} (hp : QFun H P)
    (h₁ : P ∘ₗ LinearMap.adjoint P = 1) (h₂ : LinearMap.adjoint P ∘ₗ P = 1) :
    mapComul' P =
      ((TensorProduct.assoc ℂ) _ _ _).symm.toLinearMap ∘ₗ
        (LinearMap.lTensor H Coalgebra.comul) ∘ₗ P :=
  by
  have :
    LinearMap.adjoint P ∘ₗ
        mapMul' P ∘ₗ
          (LinearMap.lTensor B₁ (LinearMap.adjoint P)) ∘ₗ
            ((TensorProduct.assoc ℂ) _ _ _).toLinearMap ∘ₗ
              (LinearMap.rTensor B₂ (LinearMap.adjoint P)) =
      LinearMap.adjoint (mapComul' P) :=
    by
    rw [hp.map_mul]
    simp_rw [← LinearMap.comp_assoc, h₂, LinearMap.one_comp, ← LinearMap.lTensor_adjoint, ←
      LinearMap.rTensor_adjoint, Coalgebra.comul_eq_mul_adjoint]
    rw [← TensorProduct.assoc_adjoint]
    nth_rw 2 [← TensorProduct.assoc_symm_adjoint]
    nth_rw 1 [← LinearMap.adjoint_adjoint (LinearMap.mul' ℂ B₁)]
    rw [← LinearMap.rTensor_adjoint]
    simp only [← LinearMap.adjoint_comp, LinearMap.comp_assoc]
  simp_all [mapMul', LinearMap.comp_assoc]
  rw [← LinearMap.comp_assoc _ _ (LinearMap.lTensor B₁ P), ← LinearMap.lTensor_comp, h₁,
    LinearMap.lTensor_one, LinearMap.one_comp, ←
    LinearMap.comp_assoc _ _ ((TensorProduct.assoc ℂ) _ _ _).symm.toLinearMap, LinearEquiv.comp_coe,
    LinearEquiv.self_trans_symm] at this
  simp only [LinearEquiv.refl_toLinearMap] at this
  rw [LinearMap.id_comp, ← LinearMap.rTensor_comp, h₁, LinearMap.rTensor_one,
    LinearMap.comp_one] at this
  apply_fun LinearMap.adjoint at this
  simp only [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint] at this
  simpa only [mapComul', TensorProduct.assoc_adjoint, TensorProduct.assoc_symm_adjoint,
    LinearMap.lTensor_adjoint, LinearMap.rTensor_adjoint, Coalgebra.comul_eq_mul_adjoint,
    LinearMap.adjoint_adjoint, LinearMap.comp_assoc] using this.symm


-- @@ L443-449 verbatim
theorem QFun.qBijective_iff_inv_eq_adjoint
  {P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)} (hp : QFun H P) :
  hp.qBijective ↔ P ∘ₗ LinearMap.adjoint P = 1 ∧ LinearMap.adjoint P ∘ₗ P = 1 :=
⟨fun h => ⟨hp.self_comp_adjoint_eq_id_of_map_comul h.2,
  hp.adjoint_comp_self_eq_id_of_map_counit h.1⟩,
  fun ⟨h1, h2⟩ => ⟨hp.map_counit_of_adjoint_comp_self_eq_id h2,
  hp.map_comul_of_inv_eq_adjoint h1 h2⟩⟩


-- @@ L451-463 verbatim
/-- The linear equivalence induced by a quantum-bijective quantum function. -/
noncomputable def QFun.qBijective.toLinearEquiv
  {P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)} [hp : QFun H P]
  (h : hp.qBijective) :
    (B₁ ⊗[ℂ] H) ≃ₗ[ℂ] (H ⊗[ℂ] B₂) where
  toLinearMap := P
  invFun := LinearMap.adjoint P
  left_inv _ := by
    simp only [LinearMap.toFun_eq_coe, ← LinearMap.comp_apply]
    rw [(hp.qBijective_iff_inv_eq_adjoint.mp h).2, Module.End.one_apply]
  right_inv _ := by
    simp only [LinearMap.toFun_eq_coe, ← LinearMap.comp_apply]
    rw [(hp.qBijective_iff_inv_eq_adjoint.mp h).1, Module.End.one_apply]


-- @@ L465-469 verbatim
lemma QFun.qBijective.toLinearEquiv_toLinearMap
  {P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)} [hp : QFun H P]
  (h : hp.qBijective) :
    h.toLinearEquiv.toLinearMap = P :=
rfl


-- @@ L471-475 verbatim
lemma QFun.qBijective.toLinearEquiv_symm_toLinearMap
  {P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)} [hp : QFun H P]
  (h : hp.qBijective) :
    h.toLinearEquiv.symm.toLinearMap = LinearMap.adjoint P :=
rfl


-- @@ L477-482 expanded
theorem QFun.qBijective_iso_id {P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)} [hp : QFun H P]
    (h : hp.qBijective) :
    h.toLinearEquiv.toLinearMap ∘ₗ (LinearMap.rTensor _ 1) ∘ₗ h.toLinearEquiv.symm.toLinearMap =
      LinearMap.lTensor _ 1 :=
  by
  ext
  simp [LinearMap.rTensor_one, LinearMap.lTensor_one]


-- @@ L484-488 expanded
theorem rankOne_one_one_eq :
    ContinuousLinearMap.toLinearMap (rankOne ℂ (1 : B₁) (1 : B₂)) =
      (Algebra.linearMap ℂ) B₁ ∘ₗ Coalgebra.counit :=
  by
  rw [Coalgebra.counit_eq_bra_one]
  ext
  simp [Algebra.algebraMap_eq_smul_one]


-- @@ L490-496 expanded
lemma QFun.mapUnit'' {P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)} (hp : QFun H P) :
    P ∘ₗ LinearMap.rTensor H ((Algebra.linearMap ℂ) B₁) =
      LinearMap.lTensor H ((Algebra.linearMap ℂ) B₂) ∘ₗ (TensorProduct.comm ℂ _ _).toLinearMap :=
  calc
    P ∘ₗ LinearMap.rTensor H ((Algebra.linearMap ℂ) B₁) =
        LinearMap.lTensor H ((Algebra.linearMap ℂ) B₂) ∘ₗ
          (((TensorProduct.rid ℂ) _).symm.toLinearMap ∘ₗ ((TensorProduct.lid ℂ) _).toLinearMap) :=
      by
      rw [← LinearMap.comp_assoc, ← hp.map_unit, mapUnit']
      simp only [LinearMap.comp_assoc, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm]
      rfl
    _ = LinearMap.lTensor H ((Algebra.linearMap ℂ) B₂) ∘ₗ (TensorProduct.comm ℂ _ _).toLinearMap :=
      by ext; simp


-- @@ L498-511 expanded
lemma QFun.counit_map_adjoint {P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)} (hp : QFun H P) :
    (LinearMap.rTensor _ Coalgebra.counit) ∘ₗ LinearMap.adjoint P =
      (TensorProduct.comm ℂ _ _).symm.toLinearMap ∘ₗ LinearMap.lTensor _ Coalgebra.counit :=
  calc
    (LinearMap.rTensor _ Coalgebra.counit) ∘ₗ LinearMap.adjoint P =
        LinearMap.adjoint (P ∘ₗ (LinearMap.rTensor _ ((Algebra.linearMap ℂ) B₁))) :=
      by
      rw [Coalgebra.counit_eq_unit_adjoint, ← LinearMap.rTensor_adjoint, LinearMap.adjoint_comp]
      congr; ext; rfl
    _ =
        LinearMap.adjoint
          (LinearMap.lTensor H ((Algebra.linearMap ℂ) B₂) ∘ₗ
            (TensorProduct.comm ℂ _ _).toLinearMap) :=
      by rw [hp.mapUnit'']
    _ = (TensorProduct.comm ℂ _ _).symm.toLinearMap ∘ₗ LinearMap.lTensor _ Coalgebra.counit :=
      by
      rw [LinearMap.adjoint_comp, LinearMap.lTensor_adjoint, Coalgebra.counit_eq_unit_adjoint,
        TensorProduct.comm_adjoint]
      congr; ext; rfl


-- @@ L513-526 expanded
/-- for any `qBijective` function `P`,
  we get `P ∘ (|1⟩⟨1| ⊗ id) ∘ adjoint P = (id ⊗ |1⟩⟨1|)`. -/
theorem QFun.qBijective_iso_rankOne_one_one {P : (B₁ ⊗[ℂ] H) →ₗ[ℂ] (H ⊗[ℂ] B₂)} [hp : QFun H P]
    (h : hp.qBijective) :
    h.toLinearEquiv.toLinearMap ∘ₗ
        (LinearMap.rTensor _ (rankOne ℂ (1 : B₁) (1 : B₁))) ∘ₗ h.toLinearEquiv.symm.toLinearMap =
      LinearMap.lTensor _ (rankOne ℂ (1 : B₂) (1 : B₂)) :=
  by
  rw [rankOne_one_one_eq, LinearMap.rTensor_comp, h.toLinearEquiv_toLinearMap,
    h.toLinearEquiv_symm_toLinearMap, LinearMap.comp_assoc, hp.counit_map_adjoint, ←
    LinearMap.comp_assoc, hp.mapUnit'']
  nth_rw 1 [LinearMap.comp_assoc]
  nth_rw 2 [← LinearMap.comp_assoc]
  rw [LinearEquiv.comp_coe, LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap,
    LinearMap.id_comp, ← LinearMap.lTensor_comp, rankOne_one_one_eq]

