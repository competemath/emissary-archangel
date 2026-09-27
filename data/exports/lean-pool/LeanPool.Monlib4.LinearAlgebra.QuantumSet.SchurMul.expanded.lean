/-
Copyright (c) 2024 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import LeanPool.Monlib4.LinearAlgebra.QuantumSet.Basic
public import Mathlib.RingTheory.Coalgebra.Hom
import LeanPool.Monlib4.LinearAlgebra.End
import LeanPool.Monlib4.LinearAlgebra.Ips.TensorHilbert
import LeanPool.Monlib4.LinearAlgebra.TensorProduct.BasicLemmas
import Mathlib.Tactic.Positivity.Finset


-- @@ L15-22 verbatim
/-!
# Schur Product Operator

This file ports the definition of the upstream `Monlib.LinearAlgebra.QuantumSet.SchurMul`
operator.  The deeper upstream Schur-product theorem stack depends on the finite-dimensional
Hilbert-algebra coalgebra instance and tensor-product infrastructure that are not yet recovered
in the current monlib4 slice.
-/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
open scoped TensorProduct BigOperators


-- @@ L28-28 verbatim
local notation "m" x => LinearMap.mul' ℂ x

-- @@ L29-29 verbatim
local notation x " ⊗ₘ " y => TensorProduct.map x y


-- @@ L31-31 verbatim
open Coalgebra


-- @@ L33-54 expanded
/-- Schur product `x •ₛ y := m ∘ (x ⊗ y) ∘ comul`. -/
@[simps]
noncomputable def schurMul {B C : Type*} [AddCommMonoid B] [NonUnitalNonAssocSemiring C]
    [Module ℂ B] [Module ℂ C] [CoalgebraStruct ℂ B] [SMulCommClass ℂ C C] [IsScalarTower ℂ C C] :
    (B →ₗ[ℂ] C) →ₗ[ℂ] (B →ₗ[ℂ] C) →ₗ[ℂ] (B →ₗ[ℂ] C)
    where
  toFun
    x :=
    { toFun := fun y => (LinearMap.mul' ℂ C) ∘ₗ (TensorProduct.map x y) ∘ₗ comul
      map_add' := fun _ _ => by
        simp only [TensorProduct.map_add_right, LinearMap.add_comp, LinearMap.comp_add]
      map_smul' := fun _ _ => by
        simp only [TensorProduct.map_smul_right, LinearMap.smul_comp, LinearMap.comp_smul,
          RingHom.id_apply] }
  map_add' x
    y :=
    by
    simp only [TensorProduct.map_add_left, LinearMap.add_comp, LinearMap.comp_add,
      LinearMap.ext_iff, LinearMap.add_apply, LinearMap.coe_mk]
    simp_all
  map_smul' r
    x :=
    by
    simp only [TensorProduct.map_smul_left, LinearMap.smul_comp, LinearMap.comp_smul,
      LinearMap.ext_iff, LinearMap.smul_apply, LinearMap.coe_mk, RingHom.id_apply]
    simp_all


-- @@ L56-57 verbatim
@[inherit_doc schurMul]
notation3:80 (name := schurMulNotation) x:81 " •ₛ " y:80 => schurMul x y


-- @@ L59-65 expanded
theorem nonUnitalAlgHom_comp_mul {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (f : A →ₙₐ[R] B) :
    (LinearMap.ofClass f) ∘ₗ LinearMap.mul' R A =
      (LinearMap.mul' R B) ∘ₗ (TensorProduct.map (LinearMap.ofClass f) (LinearMap.ofClass f)) :=
  by
  rw [TensorProduct.ext_iff']
  simp_all


-- @@ L67-75 expanded
theorem algHom_comp_mul {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A]
    [Algebra R B] (f : A →ₐ[R] B) :
    f.toLinearMap ∘ₗ LinearMap.mul' R A =
      (LinearMap.mul' R B) ∘ₗ (TensorProduct.map f.toLinearMap f.toLinearMap) :=
  by
  change
    (LinearMap.ofClass f.toNonUnitalAlgHom) ∘ₗ LinearMap.mul' R A =
      (LinearMap.mul' R B) ∘ₗ
        (TensorProduct.map (LinearMap.ofClass f.toNonUnitalAlgHom)
          (LinearMap.ofClass f.toNonUnitalAlgHom))
  exact nonUnitalAlgHom_comp_mul f.toNonUnitalAlgHom


-- @@ L77-77 verbatim
attribute [local instance] Algebra.ofIsScalarTowerSmulCommClass


-- @@ L79-84 verbatim
variable {A B : Type*}
  [NormedAddCommGroupOfRing A] [NormedAddCommGroupOfRing B]
  [InnerProductSpace ℂ A] [InnerProductSpace ℂ B]
  [SMulCommClass ℂ A A] [SMulCommClass ℂ B B]
  [IsScalarTower ℂ A A] [IsScalarTower ℂ B B]
  [FiniteDimensional ℂ A] [FiniteDimensional ℂ B]


-- @@ L86-102 expanded
omit [FiniteDimensional ℂ B] in
theorem schurMul.apply_rankOne (a c : B) (b d : A) :
    schurMul (rankOne ℂ a b).toLinearMap (rankOne ℂ c d).toLinearMap =
      (rankOne ℂ (a * c) (b * d) : A →L[ℂ] B).toLinearMap :=
  by
  rw [schurMul, LinearMap.ext_iff]
  intro x
  apply ext_inner_right ℂ
  intro u
  simp only [ContinuousLinearMap.coe_coe, LinearMap.coe_mk, AddHom.coe_mk, rankOne_apply,
    LinearMap.comp_apply]
  obtain ⟨α, β, h⟩ := TensorProduct.eq_span (Coalgebra.comul x : A ⊗[ℂ] A)
  rw [← h]
  simp_rw [map_sum, TensorProduct.map_tmul, ContinuousLinearMap.coe_coe, rankOne_apply,
    LinearMap.mul'_apply, smul_mul_smul_comm, ← TensorProduct.inner_tmul, ← Finset.sum_smul, ←
    inner_sum, h, Coalgebra.comul_eq_mul_adjoint, LinearMap.adjoint_inner_right,
    LinearMap.mul'_apply]


-- @@ L104-109 expanded
omit [FiniteDimensional ℂ B] in
theorem schurMul.apply_ket (a b : B) : schurMul (ket ℂ a) (ket ℂ b) = (ket ℂ (a * b)).toLinearMap :=
  by
  simp only [schurMul_apply_apply, QuantumSet.complex_comul]
  ext
  simp_all


-- @@ L111-111 verbatim
section TensorRankOne


-- @@ L113-115 verbatim
variable {𝕜 B C : Type*} [RCLike 𝕜] [NormedAddCommGroup B] [NormedAddCommGroup C]
  [InnerProductSpace 𝕜 B] [InnerProductSpace 𝕜 C]
  [FiniteDimensional 𝕜 B] [FiniteDimensional 𝕜 C]


-- @@ L117-123 verbatim
omit [FiniteDimensional 𝕜 B] [FiniteDimensional 𝕜 C] in
theorem bra_tmul (a : B) (b : C) :
    (bra 𝕜 (a ⊗ₜ[𝕜] b)).toLinearMap =
      (TensorProduct.lid 𝕜 _).toLinearMap ∘ₗ
        TensorProduct.map (bra 𝕜 a).toLinearMap (bra 𝕜 b).toLinearMap := by
  ext
  simp_all


-- @@ L125-131 verbatim
omit [FiniteDimensional 𝕜 B] [FiniteDimensional 𝕜 C] in
theorem bra_map_bra (a : B) (b : C) :
    TensorProduct.map (bra 𝕜 a).toLinearMap (bra 𝕜 b).toLinearMap =
      (TensorProduct.lid 𝕜 _).symm.toLinearMap ∘ₗ
        (bra 𝕜 (a ⊗ₜ[𝕜] b)).toLinearMap := by
  rw [bra_tmul, ← LinearMap.comp_assoc]
  simp_all


-- @@ L133-141 verbatim
omit [FiniteDimensional 𝕜 B] [FiniteDimensional 𝕜 C] in
theorem ket_tmul (a : B) (b : C) :
    (ket 𝕜 (a ⊗ₜ[𝕜] b)).toLinearMap =
      TensorProduct.map (ket 𝕜 a).toLinearMap (ket 𝕜 b).toLinearMap ∘ₗ
        (TensorProduct.lid 𝕜 _).symm.toLinearMap := by
  ext
  simp only [ContinuousLinearMap.coe_coe, ket_one_apply, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply, TensorProduct.lid_symm_apply,
    TensorProduct.map_tmul]


-- @@ L143-149 verbatim
omit [FiniteDimensional 𝕜 B] [FiniteDimensional 𝕜 C] in
theorem ket_map_ket (a : B) (b : C) :
    TensorProduct.map (ket 𝕜 a).toLinearMap (ket 𝕜 b).toLinearMap =
      (ket 𝕜 (a ⊗ₜ[𝕜] b)).toLinearMap ∘ₗ (TensorProduct.lid 𝕜 _).toLinearMap := by
  rw [ket_tmul, LinearMap.comp_assoc]
  simp only [LinearEquiv.comp_coe, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap,
    LinearMap.comp_id]


-- @@ L151-151 verbatim
end TensorRankOne


-- @@ L153-159 verbatim
theorem bra_comp_linearMap {𝕜 E₁ E₂ : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [NormedAddCommGroup E₂]
    [InnerProductSpace 𝕜 E₂] [FiniteDimensional 𝕜 E₁] [FiniteDimensional 𝕜 E₂]
    (x : E₂) (f : E₁ →ₗ[𝕜] E₂) :
    (bra 𝕜 x).toLinearMap.comp f = (bra 𝕜 (LinearMap.adjoint f x)).toLinearMap := by
  ext y
  exact (LinearMap.adjoint_inner_left f y x).symm


-- @@ L161-166 verbatim
theorem linearMap_comp_ket {𝕜 E₁ E₂ : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [NormedAddCommGroup E₂]
    [InnerProductSpace 𝕜 E₂] (x : E₁) (f : E₁ →ₗ[𝕜] E₂) :
    f ∘ₗ (ket 𝕜 x).toLinearMap = (ket 𝕜 (f x)).toLinearMap := by
  ext
  simp_all


-- @@ L168-170 verbatim
theorem mul_comp_lid_symm {R : Type*} [CommSemiring R] :
    LinearMap.mul' R R ∘ₗ (TensorProduct.lid R R).symm.toLinearMap = LinearMap.id := by
  aesop


-- @@ L172-177 expanded
theorem schurMul.apply_bra (a b : B) : schurMul (bra ℂ a) (bra ℂ b) = (bra ℂ (a * b)).toLinearMap :=
  by
  rw [schurMul_apply_apply, bra_map_bra, LinearMap.comp_assoc, bra_comp_linearMap,
    Coalgebra.comul_eq_mul_adjoint, LinearMap.adjoint_adjoint, LinearMap.mul'_apply, ←
    LinearMap.comp_assoc, mul_comp_lid_symm]
  rfl


-- @@ L179-196 expanded
omit [FiniteDimensional ℂ B] in
theorem schurMul.comp_apply_of {C : Type*} [NormedAddCommGroupOfRing C] [InnerProductSpace ℂ C]
    [SMulCommClass ℂ C C] [IsScalarTower ℂ C C] [FiniteDimensional ℂ C] (δ : ℂ)
    (hAδ : Coalgebra.comul ∘ₗ LinearMap.mul' ℂ A = δ • LinearMap.id) (a b : A →ₗ[ℂ] B)
    (c d : C →ₗ[ℂ] A) : (schurMul a b) ∘ₗ (schurMul c d) = δ • (schurMul (a ∘ₗ c) (b ∘ₗ d)) := by
  calc
    (schurMul a b) ∘ₗ (schurMul c d) =
        (LinearMap.mul' ℂ _) ∘ₗ
          (TensorProduct.map a b) ∘ₗ
            (Coalgebra.comul ∘ₗ (LinearMap.mul' ℂ A)) ∘ₗ
              (TensorProduct.map c d) ∘ₗ Coalgebra.comul :=
      by simp_rw [schurMul_apply_apply, LinearMap.comp_assoc]
    _ =
        δ •
          (LinearMap.mul' ℂ _) ∘ₗ
            ((TensorProduct.map a b) ∘ₗ (TensorProduct.map c d)) ∘ₗ Coalgebra.comul :=
      by
      simp_rw [hAδ, LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp,
        LinearMap.comp_assoc]
    _ = δ • schurMul (a ∘ₗ c) (b ∘ₗ d) :=
      by
      rw [← TensorProduct.map_comp]
      rfl


-- @@ L198-201 expanded
theorem schurMul_one_one_right (x : A →ₗ[ℂ] B) :
    schurMul x (rankOne ℂ (1 : B) (1 : A)).toLinearMap = x :=
  by
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne x
  simp_rw [map_sum, LinearMap.sum_apply, schurMul.apply_rankOne, mul_one]


-- @@ L203-206 expanded
theorem schurMul_one_one_left (x : A →ₗ[ℂ] B) :
    schurMul (rankOne ℂ (1 : B) (1 : A)).toLinearMap x = x :=
  by
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne x
  simp_rw [map_sum, schurMul.apply_rankOne, one_mul]


-- @@ L208-218 expanded
theorem schurMul_one_right_rankOne (a b : A) :
    schurMul (rankOne ℂ a b).toLinearMap (1 : A →ₗ[ℂ] A) = lmul a ∘ₗ LinearMap.adjoint (lmul b) :=
  by
  trans lmul a ∘ₗ ((1 : A →ₗ[ℂ] A) ∘ₗ LinearMap.adjoint (lmul b))
  · simp only [← rankOne.sum_orthonormalBasis_eq_id_lm (stdOrthonormalBasis ℂ A), map_sum,
      LinearMap.sum_comp, LinearMap.comp_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [schurMul.apply_rankOne, LinearMap.rankOne_comp', LinearMap.comp_rankOne]
    rfl
  · rfl


-- @@ L220-230 expanded
theorem schurMul_one_left_rankOne (a b : A) :
    schurMul (1 : A →ₗ[ℂ] A) (rankOne ℂ a b).toLinearMap = rmul a ∘ₗ LinearMap.adjoint (rmul b) :=
  by
  trans rmul a ∘ₗ ((1 : A →ₗ[ℂ] A) ∘ₗ LinearMap.adjoint (rmul b))
  · simp only [← rankOne.sum_orthonormalBasis_eq_id_lm (stdOrthonormalBasis ℂ A), map_sum,
      LinearMap.sum_apply, LinearMap.sum_comp, LinearMap.comp_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [schurMul.apply_rankOne, LinearMap.rankOne_comp', LinearMap.comp_rankOne]
    rfl
  · rfl


-- @@ L232-236 expanded
theorem schurMul_adjoint (x y : A →ₗ[ℂ] B) :
    LinearMap.adjoint (schurMul x y) = schurMul (LinearMap.adjoint x) (LinearMap.adjoint y) :=
  by
  simp_rw [schurMul, Coalgebra.comul_eq_mul_adjoint]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint,
    TensorProduct.map_adjoint, LinearMap.comp_assoc]


-- @@ L238-246 expanded
theorem schurMul_real {A B : Type*} [starAlgebra A] [starAlgebra B] [QuantumSet A] [QuantumSet B]
    (x y : A →ₗ[ℂ] B) :
    LinearMap.real (schurMul x y : A →ₗ[ℂ] B) = schurMul (LinearMap.real y) (LinearMap.real x) :=
  by
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne x
  obtain ⟨γ, ζ, rfl⟩ := LinearMap.exists_sum_rankOne y
  simp only [map_sum, LinearMap.real_sum, LinearMap.sum_apply, schurMul.apply_rankOne]
  simp_rw [rankOne_real, schurMul.apply_rankOne, ← map_mul, ← StarMul.star_mul]
  rw [Finset.sum_comm]


-- @@ L248-255 expanded
theorem Psi.schurMul {A B : Type*} [starAlgebra A] [starAlgebra B] [hA : QuantumSet A]
    [QuantumSet B] (r₁ r₂ : ℝ) (f g : A →ₗ[ℂ] B) :
    hA.Psi r₁ r₂ (schurMul f g) = hA.Psi r₁ r₂ f * hA.Psi r₁ r₂ g :=
  by
  obtain ⟨α, β, rfl⟩ := LinearMap.exists_sum_rankOne f
  obtain ⟨γ, δ, rfl⟩ := LinearMap.exists_sum_rankOne g
  simp only [map_sum, LinearMap.sum_apply, Finset.mul_sum, Finset.sum_mul]
  simp_rw [schurMul.apply_rankOne, QuantumSet.Psi_apply, QuantumSet.PsiToFun_apply, map_mul,
    StarMul.star_mul, MulOpposite.op_mul, Algebra.TensorProduct.tmul_mul_tmul]


-- @@ L257-261 expanded
theorem schurMul_assoc {A B : Type*} [starAlgebra A] [starAlgebra B] [hA : QuantumSet A]
    [QuantumSet B] (f g h : A →ₗ[ℂ] B) : schurMul (schurMul f g) h = schurMul f (schurMul g h) :=
  by
  apply_fun hA.Psi 0 0 using LinearEquiv.injective _
  simp_rw [Psi.schurMul, mul_assoc]


-- @@ L263-268 expanded
theorem comul_comp_nonUnitalAlgHom_adjoint (f : A →ₙₐ[ℂ] B) :
    Coalgebra.comul ∘ₗ LinearMap.adjoint (LinearMap.ofClass f) =
      (TensorProduct.map (LinearMap.adjoint (LinearMap.ofClass f))
          (LinearMap.adjoint (LinearMap.ofClass f))) ∘ₗ
        Coalgebra.comul :=
  by
  simp_rw [Coalgebra.comul_eq_mul_adjoint, ← TensorProduct.map_adjoint, ← LinearMap.adjoint_comp,
    nonUnitalAlgHom_comp_mul f]


-- @@ L270-279 expanded
theorem comul_comp_algHom_adjoint (f : A →ₐ[ℂ] B) :
    Coalgebra.comul ∘ₗ LinearMap.adjoint f.toLinearMap =
      (TensorProduct.map (LinearMap.adjoint f.toLinearMap) (LinearMap.adjoint f.toLinearMap)) ∘ₗ
        Coalgebra.comul :=
  by
  change
    Coalgebra.comul ∘ₗ LinearMap.adjoint (LinearMap.ofClass f.toNonUnitalAlgHom) =
      (TensorProduct.map (LinearMap.adjoint (LinearMap.ofClass f.toNonUnitalAlgHom))
          (LinearMap.adjoint (LinearMap.ofClass f.toNonUnitalAlgHom))) ∘ₗ
        Coalgebra.comul
  exact comul_comp_nonUnitalAlgHom_adjoint f.toNonUnitalAlgHom


-- @@ L281-295 expanded
theorem schurMul_nonUnitalAlgHom_comp_coalgHom {C D : Type*} [Semiring C] [Semiring D] [Module ℂ C]
    [Module ℂ D] [SMulCommClass ℂ C C] [SMulCommClass ℂ D D] [IsScalarTower ℂ C C]
    [IsScalarTower ℂ D D] (g : C →ₙₐ[ℂ] D) (f : A →ₗc[ℂ] B) (x y : B →ₗ[ℂ] C) :
    schurMul ((LinearMap.ofClass g) ∘ₗ x ∘ₗ f.toLinearMap)
        ((LinearMap.ofClass g) ∘ₗ y ∘ₗ f.toLinearMap) =
      (LinearMap.ofClass g) ∘ₗ (schurMul x y) ∘ₗ f.toLinearMap :=
  by
  simp_rw [schurMul_apply_apply, ← LinearMap.comp_assoc, nonUnitalAlgHom_comp_mul,
    LinearMap.comp_assoc, ← f.map_comp_comul]
  congr 1
  simp_rw [← LinearMap.comp_assoc]
  congr 1
  simp_rw [TensorProduct.map_comp]


-- @@ L297-308 expanded
theorem schurMul_algHom_comp_coalgHom {C D : Type*} [Semiring C] [Semiring D] [Module ℂ C]
    [Module ℂ D] [SMulCommClass ℂ C C] [SMulCommClass ℂ D D] [IsScalarTower ℂ C C]
    [IsScalarTower ℂ D D] (g : C →ₐ[ℂ] D) (f : A →ₗc[ℂ] B) (x y : B →ₗ[ℂ] C) :
    schurMul (g.toLinearMap ∘ₗ x ∘ₗ f.toLinearMap) (g.toLinearMap ∘ₗ y ∘ₗ f.toLinearMap) =
      g.toLinearMap ∘ₗ (schurMul x y) ∘ₗ f.toLinearMap :=
  by
  change
    schurMul ((LinearMap.ofClass g.toNonUnitalAlgHom) ∘ₗ x ∘ₗ f.toLinearMap)
        ((LinearMap.ofClass g.toNonUnitalAlgHom) ∘ₗ y ∘ₗ f.toLinearMap) =
      (LinearMap.ofClass g.toNonUnitalAlgHom) ∘ₗ (schurMul x y) ∘ₗ f.toLinearMap
  exact schurMul_nonUnitalAlgHom_comp_coalgHom g.toNonUnitalAlgHom f x y


-- @@ L310-327 expanded
theorem schurMul_nonUnitalAlgHom_comp_nonUnitalAlgHom_adjoint {C D : Type*} [Semiring C]
    [Semiring D] [Module ℂ C] [Module ℂ D] [SMulCommClass ℂ C C] [SMulCommClass ℂ D D]
    [IsScalarTower ℂ C C] [IsScalarTower ℂ D D] (g : C →ₙₐ[ℂ] D) (f : B →ₙₐ[ℂ] A)
    (x y : B →ₗ[ℂ] C) :
    schurMul ((LinearMap.ofClass g) ∘ₗ x ∘ₗ (LinearMap.adjoint (LinearMap.ofClass f)))
        ((LinearMap.ofClass g) ∘ₗ y ∘ₗ (LinearMap.adjoint (LinearMap.ofClass f))) =
      (LinearMap.ofClass g) ∘ₗ (schurMul x y) ∘ₗ LinearMap.adjoint (LinearMap.ofClass f) :=
  by
  simp_rw [schurMul_apply_apply, ← LinearMap.comp_assoc, nonUnitalAlgHom_comp_mul,
    LinearMap.comp_assoc, comul_comp_nonUnitalAlgHom_adjoint]
  congr 1
  simp_rw [← LinearMap.comp_assoc]
  congr 1
  simp_rw [TensorProduct.map_comp]


-- @@ L329-345 expanded
theorem schurMul_algHom_comp_algHom_adjoint {C D : Type*} [Semiring C] [Semiring D] [Module ℂ C]
    [Module ℂ D] [SMulCommClass ℂ C C] [SMulCommClass ℂ D D] [IsScalarTower ℂ C C]
    [IsScalarTower ℂ D D] (g : C →ₐ[ℂ] D) (f : B →ₐ[ℂ] A) (x y : B →ₗ[ℂ] C) :
    schurMul (g.toLinearMap ∘ₗ x ∘ₗ LinearMap.adjoint f.toLinearMap)
        (g.toLinearMap ∘ₗ y ∘ₗ LinearMap.adjoint f.toLinearMap) =
      g.toLinearMap ∘ₗ (schurMul x y) ∘ₗ LinearMap.adjoint f.toLinearMap :=
  by
  change
    schurMul
        ((LinearMap.ofClass g.toNonUnitalAlgHom) ∘ₗ
          x ∘ₗ LinearMap.adjoint (LinearMap.ofClass f.toNonUnitalAlgHom))
        ((LinearMap.ofClass g.toNonUnitalAlgHom) ∘ₗ
          y ∘ₗ LinearMap.adjoint (LinearMap.ofClass f.toNonUnitalAlgHom)) =
      (LinearMap.ofClass g.toNonUnitalAlgHom) ∘ₗ
        (schurMul x y) ∘ₗ LinearMap.adjoint (LinearMap.ofClass f.toNonUnitalAlgHom)
  exact
    schurMul_nonUnitalAlgHom_comp_nonUnitalAlgHom_adjoint g.toNonUnitalAlgHom f.toNonUnitalAlgHom x
      y


-- @@ L347-355 expanded
protected lemma QuantumSet.schurMul_algHom_comp_algHom_adjoint {A B C D : Type*} [starAlgebra A]
    [starAlgebra B] [QuantumSet A] [QuantumSet B] [starAlgebra C] [starAlgebra D] [QuantumSet C]
    [QuantumSet D] (g : C →ₐ[ℂ] D) (f : B →ₐ[ℂ] A) (x y : B →ₗ[ℂ] C) :
    schurMul (g.toLinearMap ∘ₗ x ∘ₗ LinearMap.adjoint f.toLinearMap)
        (g.toLinearMap ∘ₗ y ∘ₗ LinearMap.adjoint f.toLinearMap) =
      g.toLinearMap ∘ₗ (schurMul x y) ∘ₗ LinearMap.adjoint f.toLinearMap :=
  schurMul_nonUnitalAlgHom_comp_nonUnitalAlgHom_adjoint g.toNonUnitalAlgHom f.toNonUnitalAlgHom x y


-- @@ L357-363 expanded
theorem schurMul_one_iff_one_schurMul_of_isReal {A B : Type*} [starAlgebra A] [starAlgebra B]
    [QuantumSet A] [QuantumSet B] {x y z : A →ₗ[ℂ] B} (hx : LinearMap.IsReal x)
    (hy : LinearMap.IsReal y) (hz : LinearMap.IsReal z) : schurMul x y = z ↔ schurMul y x = z := by
  rw [LinearMap.real_inj_eq, schurMul_real, x.isReal_iff.mp hx, y.isReal_iff.mp hy,
    z.isReal_iff.mp hz]


-- @@ L365-368 expanded
theorem schurMul_reflexive_of_isReal {A : Type*} [starAlgebra A] [QuantumSet A] {x : A →ₗ[ℂ] A}
    (hx : LinearMap.IsReal x) : schurMul x 1 = 1 ↔ schurMul 1 x = 1 :=
  schurMul_one_iff_one_schurMul_of_isReal hx LinearMap.isRealOne LinearMap.isRealOne


-- @@ L370-373 expanded
theorem schurMul_irreflexive_of_isReal {A : Type*} [starAlgebra A] [QuantumSet A] {x : A →ₗ[ℂ] A}
    (hx : LinearMap.IsReal x) : schurMul x 1 = 0 ↔ schurMul 1 x = 0 :=
  schurMul_one_iff_one_schurMul_of_isReal hx LinearMap.isRealOne LinearMap.isRealZero


-- @@ L375-380 expanded
lemma schurIdempotent_iff_Psi_isIdempotentElem {A B : Type*} [starAlgebra A] [starAlgebra B]
    [hA : QuantumSet A] [QuantumSet B] (f : A →ₗ[ℂ] B) (t r : ℝ) :
    schurMul f f = f ↔ IsIdempotentElem (hA.Psi t r f) := by
  simp_rw [IsIdempotentElem, ← Psi.schurMul, Function.Injective.eq_iff (LinearEquiv.injective _)]

