/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import LeanPool.Monlib4.LinearAlgebra.QuantumSet.Instances
public import LeanPool.Monlib4.LinearAlgebra.QuantumSet.SchurMul
public import LeanPool.Monlib4.LinearAlgebra.QuantumSet.Symm
public import LeanPool.Monlib4.LinearAlgebra.QuantumSet.TensorProduct
import LeanPool.Monlib4.LinearAlgebra.Ips.Basic
import LeanPool.Monlib4.LinearAlgebra.Ips.TensorHilbert
import LeanPool.Monlib4.LinearAlgebra.MulPrimePrime
import LeanPool.Monlib4.LinearAlgebra.MySpec


-- @@ L17-21 verbatim
/-!
 # Isomorphisms between quantum graphs

 This file defines isomorphisms between quantum graphs.
-/


-- @@ L23-23 verbatim
@[expose] public section



-- @@ L26-26 verbatim
open TensorProduct Matrix


-- @@ L28-28 verbatim
open scoped TensorProduct BigOperators Kronecker Functional


-- @@ L30-30 verbatim
variable {p n : Type _} [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]


-- @@ L32-32 verbatim
local notation "⊗K" => Matrix (n × n) (n × n) ℂ


-- @@ L34-34 verbatim
local notation "l(" x ")" => x →ₗ[ℂ] x


-- @@ L36-36 verbatim
variable {φ : Module.Dual ℂ (Matrix n n ℂ)} {ψ : Module.Dual ℂ (Matrix p p ℂ)}


-- @@ L38-38 verbatim
local notation "|" x "⟩⟨" y "|" => @rankOne ℂ _ _ _ _ _ _ _ x y


-- @@ L40-40 verbatim
local notation "m" => LinearMap.mul' ℂ (Matrix n n ℂ)


-- @@ L42-42 verbatim
local notation "η" => Algebra.linearMap ℂ (Matrix n n ℂ)


-- @@ L44-44 verbatim
local notation x " ⊗ₘ " y => TensorProduct.map x y


-- @@ L46-49 verbatim
local notation "υ" =>
  (TensorProduct.assoc ℂ (Matrix n n ℂ) (Matrix n n ℂ) (Matrix n n ℂ) :
    (Matrix n n ℂ ⊗[ℂ] Matrix n n ℂ) ⊗[ℂ] Matrix n n ℂ →ₗ[ℂ]
      Matrix n n ℂ ⊗[ℂ] Matrix n n ℂ ⊗[ℂ] Matrix n n ℂ)


-- @@ L51-54 verbatim
local notation "υ⁻¹" =>
  (LinearEquiv.symm (TensorProduct.assoc ℂ (Matrix n n ℂ) (Matrix n n ℂ) (Matrix n n ℂ)) :
    Matrix n n ℂ ⊗[ℂ] Matrix n n ℂ ⊗[ℂ] Matrix n n ℂ →ₗ[ℂ]
      (Matrix n n ℂ ⊗[ℂ] Matrix n n ℂ) ⊗[ℂ] Matrix n n ℂ)


-- @@ L56-58 verbatim
local notation "ϰ" =>
  ((TensorProduct.comm ℂ (Matrix n n ℂ) ℂ) :
    Matrix n n ℂ ⊗[ℂ] ℂ →ₗ[ℂ] ℂ ⊗[ℂ] Matrix n n ℂ)


-- @@ L60-62 verbatim
local notation "ϰ⁻¹" =>
  (LinearEquiv.symm (TensorProduct.comm ℂ (Matrix n n ℂ) ℂ) :
    ℂ ⊗[ℂ] Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ ⊗[ℂ] ℂ)


-- @@ L64-66 verbatim
local notation "τ" =>
  (TensorProduct.lid ℂ (Matrix n n ℂ) :
    ℂ ⊗[ℂ] Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)


-- @@ L68-69 verbatim
local notation "τ⁻¹" =>
  (LinearEquiv.symm (TensorProduct.lid ℂ (Matrix n n ℂ)) : Matrix n n ℂ →ₗ[ℂ] ℂ ⊗[ℂ] Matrix n n ℂ)


-- @@ L71-71 verbatim
local notation "id" => (1 : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)


-- @@ L73-91 expanded
private theorem commutes_with_mul''_adjoint [hφ : φ.IsFaithfulPosMap]
    {f : (Matrix n n ℂ) ≃⋆ₐ[ℂ] (Matrix n n ℂ)} (hf : f φ.matrix = φ.matrix) :
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    (TensorProduct.map f.toLinearMap f.toLinearMap ∘ₗ Coalgebra.comul =
      Coalgebra.comul ∘ₗ f.toLinearMap) :=
  letI := Matrix.isStarAlgebra (φ := φ)
  letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
  letI := Module.Dual.NormedAddCommGroup φ
  letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
  letI := Module.Dual.InnerProductSpace (φ := φ)
  (by
    change
      TensorProduct.map f.toLinearMap f.toLinearMap ∘ₗ
          LinearMap.adjoint (LinearMap.mul' ℂ (Matrix n n ℂ)) =
        LinearMap.adjoint (LinearMap.mul' ℂ (Matrix n n ℂ)) ∘ₗ f.toLinearMap
    rw [LinearMap.commutes_with_mul_adjoint_iff f.toLinearMap]
    have :=
      (List.TFAE.out (@Module.Dual.IsFaithfulPosMap.starAlgEquiv_is_isometry_tFAE n _ _ φ _ f) 1
            2).mp
        hf
    simp_rw [this, StarAlgEquiv.toLinearMap_apply, _root_.map_mul, implies_true])


-- @@ L93-93 verbatim
open scoped Matrix


-- @@ L95-97 verbatim
private theorem innerAutStarAlg_symm_eq_star (U : unitaryGroup n ℂ) :
    (innerAutStarAlg U).symm = innerAutStarAlg (star U) := by
  simp_all


-- @@ L99-115 expanded
theorem innerAut_adjoint_eq_iff [hφ : φ.IsFaithfulPosMap] (U : unitaryGroup n ℂ) :
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    (LinearMap.adjoint (innerAut U) = innerAut (star U) ↔ Commute φ.matrix U) :=
  letI := Matrix.isStarAlgebra (φ := φ)
  letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
  letI := Module.Dual.NormedAddCommGroup φ
  letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
  letI := Module.Dual.InnerProductSpace (φ := φ)
  (by
    have hf : ∀ U : unitaryGroup n ℂ, innerAut U = (innerAutStarAlg U).toLinearMap := fun _ => rfl
    have hf' : innerAut (star U) = (innerAutStarAlg U).symm.toLinearMap := by
      rw [innerAutStarAlg_symm_eq_star, hf]
    have :=
      List.TFAE.out
        (@Module.Dual.IsFaithfulPosMap.starAlgEquiv_is_isometry_tFAE n _ _ φ hφ (innerAutStarAlg U))
        2 1
    rw [hf, hf', this, innerAutStarAlg_apply, unitaryGroup.injective_hMul U, Matrix.mul_assoc, ←
      unitaryGroup.star_coe_eq_coe_star, UnitaryGroup.star_mul_self, Matrix.mul_one]
    exact ⟨fun h => h.symm, fun h => h.symm⟩)


-- @@ L117-125 expanded
theorem Qam.mul'_adjoint_commutes_with_innerAut_lm [hφ : φ.IsFaithfulPosMap]
    {x : Matrix.unitaryGroup n ℂ} (hx : Commute φ.matrix x) :
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    (TensorProduct.map (innerAut x) (innerAut x) ∘ₗ Coalgebra.comul =
      Coalgebra.comul ∘ₗ innerAut x) :=
  by
  exact
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    (commutes_with_mul''_adjoint (f := innerAutStarAlg x)
      (by
        rw [innerAutStarAlg_apply, ← hx, mul_assoc, ← unitaryGroup.star_coe_eq_coe_star,
          unitaryGroup.star_coe_eq_coe_star, Unitary.coe_mul_star_self, mul_one]))


-- @@ L127-129 expanded
theorem Qam.unit_commutes_with_innerAut_lm (U : Matrix.unitaryGroup n ℂ) :
    innerAut U ∘ₗ Algebra.linearMap ℂ (Matrix n n ℂ) = Algebra.linearMap ℂ (Matrix n n ℂ) := by
  rw [commutes_with_unit_iff, innerAut_apply_one]


-- @@ L131-133 expanded
theorem Qam.mul'_commutes_with_innerAut_lm (x : Matrix.unitaryGroup n ℂ) :
    LinearMap.mul' ℂ (Matrix n n ℂ) ∘ₗ (TensorProduct.map (innerAut x) (innerAut x)) =
      innerAut x ∘ₗ LinearMap.mul' ℂ (Matrix n n ℂ) :=
  by simp_rw [commutes_with_mul'_iff, innerAut.map_mul, forall₂_true_iff]


-- @@ L135-146 expanded
theorem Qam.unit_adjoint_commutes_with_innerAut_lm [hφ : φ.IsFaithfulPosMap]
    {U : Matrix.unitaryGroup n ℂ} (hU : Commute φ.matrix U) :
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    (Coalgebra.counit ∘ₗ innerAut U = Coalgebra.counit) :=
  letI := Matrix.isStarAlgebra (φ := φ)
  letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
  letI := Module.Dual.NormedAddCommGroup φ
  letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
  letI := Module.Dual.InnerProductSpace (φ := φ)
  (by
    rw [← innerAut_adjoint_eq_iff] at hU
    apply_fun LinearMap.adjoint using LinearMap.adjoint.injective
    rw [LinearMap.adjoint_comp, Coalgebra.counit_eq_unit_adjoint, LinearMap.adjoint_adjoint, hU]
    ext1
    simp [LinearMap.comp_apply, Algebra.linearMap_apply])


-- @@ L148-148 verbatim
local notation "f_{" x "}" => innerAut x


-- @@ L150-151 verbatim
theorem innerAutIsReal (U : unitaryGroup n ℂ) : LinearMap.IsReal (innerAut U) := fun _ =>
  (innerAut.map_star _ _).symm


-- @@ L153-154 verbatim
@[reducible]
alias StarAlgEquiv.IsIsometry := Isometry


-- @@ L156-156 verbatim
open scoped InnerProductSpace


-- @@ L158-181 expanded
theorem InnerAut.toMatrix [hφ : φ.IsFaithfulPosMap] (U : unitaryGroup n ℂ) :
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    (hφ.toMatrix (innerAut U) = U ⊗ₖ Matrix.conj (modAut (-(1 / 2)) U)) :=
  letI := Matrix.isStarAlgebra (φ := φ)
  letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
  letI := Module.Dual.NormedAddCommGroup φ
  letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
  letI := Module.Dual.InnerProductSpace (φ := φ)
  (by
    ext
    simp only [Module.Dual.IsFaithfulPosMap.toMatrix, LinearMap.toMatrixAlgEquiv_apply, modAut,
      Module.Dual.IsFaithfulPosMap.inner_coord', Module.Dual.IsFaithfulPosMap.basis_repr_apply,
      Module.Dual.IsFaithfulPosMap.inner_coord']
    simp only [mul_apply, single, mul_ite, ite_mul, MulZeroClass.mul_zero, MulZeroClass.zero_mul,
      one_mul, Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.sum_const_zero, Finset.mem_univ,
      ite_true, ite_and, kroneckerMap, of_apply, conj_apply, sig_apply, star_sum, star_mul',
      neg_neg, Finset.mul_sum, Finset.sum_mul, mul_assoc, innerAut_apply',
      Module.Dual.IsFaithfulPosMap.basis_apply]
    simp_rw [← star_apply, star_eq_conjTranspose]
    repeat' apply Finset.sum_congr rfl; intros
    simp_rw [← star_eq_conjTranspose, ← unitaryGroup.star_coe_eq_coe_star]
    congr 1
    simp_rw [star_apply, ← conjTranspose_apply, (PosDef.rpow.isPosDef _ _).isHermitian.eq]
    nth_rw 1 [mul_rotate', ← mul_assoc]
    rw [mul_comm _ (PosDef.rpow _ (1 / 2) _ _), mul_assoc])


-- @@ L183-201 expanded
theorem unitary_commutes_with_hφ_matrix_iff_isIsometry (hφ : φ.IsFaithfulPosMap)
    (U : unitaryGroup n ℂ) :
    letI : φ.IsFaithfulPosMap := hφ
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    (Commute φ.matrix U ↔ StarAlgEquiv.IsIsometry (innerAutStarAlg U)) :=
  by
  let : φ.IsFaithfulPosMap := hφ
  exact
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    (by
      rw [← innerAut_adjoint_eq_iff, ← innerAutStarAlg_equiv_toLinearMap, ← innerAut_inv_eq_star, ←
        innerAutStarAlg_equiv_symm_toLinearMap]
      have :=
        List.TFAE.out
          (@Module.Dual.IsFaithfulPosMap.starAlgEquiv_is_isometry_tFAE n _ _ φ _
            (innerAutStarAlg U))
          2 5
      change
        LinearMap.adjoint (innerAutStarAlg U).toLinearMap = (innerAutStarAlg U).symm.toLinearMap ↔
          StarAlgEquiv.IsIsometry (innerAutStarAlg U)
      rw [this, StarAlgEquiv.IsIsometry, iff_comm]
      exact isometry_iff_norm _)


-- @@ L203-221 expanded
theorem Qam.symm_apply_starAlgEquiv_conj [hφ : φ.IsFaithfulPosMap]
    {f : (Matrix n n ℂ) ≃⋆ₐ[ℂ] (Matrix n n ℂ)} (hf : StarAlgEquiv.IsIsometry f)
    (A : (Matrix n n ℂ) →ₗ[ℂ] (Matrix n n ℂ)) :
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    (symmMap ℂ (Matrix n n ℂ) _ (f.toLinearMap ∘ₗ A ∘ₗ f.symm.toLinearMap) =
      f.toLinearMap ∘ₗ (symmMap ℂ (Matrix n n ℂ) _ A) ∘ₗ f.symm.toLinearMap) :=
  letI := Matrix.isStarAlgebra (φ := φ)
  letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
  letI := Module.Dual.NormedAddCommGroup φ
  letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
  letI := Module.Dual.InnerProductSpace (φ := φ)
  (by
    have :=
      List.TFAE.out (@Module.Dual.IsFaithfulPosMap.starAlgEquiv_is_isometry_tFAE n _ _ φ _ f) 5 2
    rw [StarAlgEquiv.IsIsometry, isometry_iff_norm, this] at hf
    change LinearMap.adjoint f.toAlgEquiv.toLinearMap = f.symm.toAlgEquiv.toLinearMap at hf
    change
      LinearMap.adjoint
          (LinearMap.real (f.toAlgEquiv.toLinearMap ∘ₗ A ∘ₗ f.symm.toAlgEquiv.toLinearMap)) =
        f.toAlgEquiv.toLinearMap ∘ₗ
          LinearMap.adjoint (LinearMap.real A) ∘ₗ f.symm.toAlgEquiv.toLinearMap
    rw [LinearMap.real_starAlgEquiv_conj, LinearMap.adjoint_comp, hf]
    nth_rw 1 [← hf]
    rw [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint, LinearMap.comp_assoc])


-- @@ L223-233 expanded
theorem InnerAut.symmetric_eq [hφ : φ.IsFaithfulPosMap] (A : (Matrix n n ℂ) →ₗ[ℂ] (Matrix n n ℂ))
    {U : Matrix.unitaryGroup n ℂ} (hU : Commute φ.matrix U) :
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    (symmMap ℂ (Matrix n n ℂ) _ (innerAut U ∘ₗ A ∘ₗ innerAut (star U)) =
      innerAut U ∘ₗ symmMap ℂ (Matrix n n ℂ) _ A ∘ₗ innerAut (star U)) :=
  letI := Matrix.isStarAlgebra (φ := φ)
  letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
  letI := Module.Dual.NormedAddCommGroup φ
  letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
  letI := Module.Dual.InnerProductSpace (φ := φ)
  (by
    rw [← innerAut_inv_eq_star, ← innerAutStarAlg_equiv_symm_toLinearMap, ←
      innerAutStarAlg_equiv_toLinearMap]
    exact
      Qam.symm_apply_starAlgEquiv_conj ((unitary_commutes_with_hφ_matrix_iff_isIsometry hφ U).mp hU)
        _)


-- @@ L235-243 expanded
open scoped Classical in
omit [DecidableEq n] in
theorem StarAlgEquiv.commutes_with_mul' (f : (Matrix n n ℂ) ≃⋆ₐ[ℂ] (Matrix n n ℂ)) :
    letI : DecidableEq n := Classical.decEq n
    (LinearMap.mul' ℂ (Matrix n n ℂ) ∘ₗ TensorProduct.map f.toLinearMap f.toLinearMap) =
      f.toLinearMap ∘ₗ LinearMap.mul' ℂ (Matrix n n ℂ) :=
  by
  classical
  rw [commutes_with_mul'_iff]
  simp_all


-- @@ L245-259 expanded
theorem StarAlgEquiv.IsIsometry.commutes_with_mul'_adjoint [hφ : φ.IsFaithfulPosMap]
    {f : (Matrix n n ℂ) ≃⋆ₐ[ℂ] (Matrix n n ℂ)} (hf : StarAlgEquiv.IsIsometry f) :
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    ((TensorProduct.map f.toLinearMap f.toLinearMap) ∘ₗ
        LinearMap.adjoint (LinearMap.mul' ℂ (Matrix n n ℂ)) =
      LinearMap.adjoint (LinearMap.mul' ℂ (Matrix n n ℂ)) ∘ₗ f.toLinearMap) :=
  letI := Matrix.isStarAlgebra (φ := φ)
  letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
  letI := Module.Dual.NormedAddCommGroup φ
  letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
  letI := Module.Dual.InnerProductSpace (φ := φ)
  (by
    have :=
      List.TFAE.out (@Module.Dual.IsFaithfulPosMap.starAlgEquiv_is_isometry_tFAE n _ _ φ _ f) 5 2
    rw [StarAlgEquiv.IsIsometry, isometry_iff_norm, this] at hf
    rw [← LinearMap.adjoint_adjoint (TensorProduct.map f.toLinearMap f.toLinearMap), ←
      LinearMap.adjoint_comp, TensorProduct.map_adjoint, hf, StarAlgEquiv.commutes_with_mul' f.symm,
      LinearMap.adjoint_comp, ← hf, LinearMap.adjoint_adjoint])


-- @@ L261-290 expanded
theorem Qam.reflIdempotent_starAlgEquiv_conj [hφ : φ.IsFaithfulPosMap]
    {f : (Matrix n n ℂ) ≃⋆ₐ[ℂ] (Matrix n n ℂ)} (hf : StarAlgEquiv.IsIsometry f)
    (A B : (Matrix n n ℂ) →ₗ[ℂ] (Matrix n n ℂ)) :
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    (schurMul (f.toLinearMap ∘ₗ A ∘ₗ f.symm.toLinearMap)
        (f.toLinearMap ∘ₗ B ∘ₗ f.symm.toLinearMap) =
      f.toLinearMap ∘ₗ (schurMul A B) ∘ₗ f.symm.toLinearMap) :=
  letI := Matrix.isStarAlgebra (φ := φ)
  letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
  letI := Module.Dual.NormedAddCommGroup φ
  letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
  letI := Module.Dual.InnerProductSpace (φ := φ)
  (by
    simp only [schurMul_apply_apply, TensorProduct.map_comp, ← LinearMap.comp_assoc,
      StarAlgEquiv.commutes_with_mul' f]
    have hsymm : StarAlgEquiv.IsIsometry f.symm :=
      by
      simp_rw [StarAlgEquiv.IsIsometry, isometry_iff_norm] at hf ⊢
      have :=
        List.TFAE.out (@Module.Dual.IsFaithfulPosMap.starAlgEquiv_is_isometry_tFAE n _ _ φ _ f.symm)
          5 2
      rw [this]
      have this' :=
        List.TFAE.out (@Module.Dual.IsFaithfulPosMap.starAlgEquiv_is_isometry_tFAE n _ _ φ _ f) 5 2
      rw [this'] at hf
      rw [StarAlgEquiv.symm_symm, ← hf, LinearMap.adjoint_adjoint]
    change
      (((f.toLinearMap ∘ₗ LinearMap.mul' ℂ (Matrix n n ℂ)) ∘ₗ TensorProduct.map A B) ∘ₗ
            TensorProduct.map f.symm.toLinearMap f.symm.toLinearMap) ∘ₗ
          LinearMap.adjoint (LinearMap.mul' ℂ (Matrix n n ℂ)) =
        (((f.toLinearMap ∘ₗ LinearMap.mul' ℂ (Matrix n n ℂ)) ∘ₗ TensorProduct.map A B) ∘ₗ
            LinearMap.adjoint (LinearMap.mul' ℂ (Matrix n n ℂ))) ∘ₗ
          f.symm.toLinearMap
    simp only [LinearMap.comp_assoc, StarAlgEquiv.IsIsometry.commutes_with_mul'_adjoint hsymm])


-- @@ L293-304 expanded
theorem InnerAut.reflIdempotent [hφ : φ.IsFaithfulPosMap] {U : unitaryGroup n ℂ}
    (hU : Commute φ.matrix U) (A B : (Matrix n n ℂ) →ₗ[ℂ] (Matrix n n ℂ)) :
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    (schurMul (innerAut U ∘ₗ A ∘ₗ innerAut (star U)) (innerAut U ∘ₗ B ∘ₗ innerAut (star U)) =
      innerAut U ∘ₗ (schurMul A B) ∘ₗ innerAut (star U)) :=
  letI := Matrix.isStarAlgebra (φ := φ)
  letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
  letI := Module.Dual.NormedAddCommGroup φ
  letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
  letI := Module.Dual.InnerProductSpace (φ := φ)
  (by
    rw [← innerAut_inv_eq_star, ← innerAutStarAlg_equiv_symm_toLinearMap, ←
      innerAutStarAlg_equiv_toLinearMap]
    rw [unitary_commutes_with_hφ_matrix_iff_isIsometry hφ U] at hU
    exact Qam.reflIdempotent_starAlgEquiv_conj hU _ _)


-- @@ L306-309 expanded
/-- Isomorphism relation between two matrix quantum adjacency maps. -/
def Qam.Iso (A B : (Matrix n n ℂ) →ₗ[ℂ] (Matrix n n ℂ)) : Prop :=
  ∃ f : (Matrix n n ℂ) ≃⋆ₐ[ℂ] (Matrix n n ℂ),
    A ∘ₗ f.toLinearMap = f.toLinearMap ∘ₗ B ∧ f φ.matrix = φ.matrix


-- @@ L311-329 expanded
theorem Qam.iso_iff [hφ : φ.IsFaithfulPosMap] {A B : (Matrix n n ℂ) →ₗ[ℂ] (Matrix n n ℂ)} :
    @Qam.Iso n _ _ φ A B ↔
      ∃ U : unitaryGroup n ℂ, A ∘ₗ innerAut U = innerAut U ∘ₗ B ∧ Commute φ.matrix U :=
  letI := Matrix.isStarAlgebra (φ := φ)
  letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
  letI := Module.Dual.NormedAddCommGroup φ
  letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
  letI := Module.Dual.InnerProductSpace (φ := φ)
  (by
    simp_rw [← innerAut_adjoint_eq_iff]
    have hf : ∀ U : unitaryGroup n ℂ, innerAut U = (innerAutStarAlg U).toLinearMap := fun _ => rfl
    have := fun U =>
      List.TFAE.out
        (@Module.Dual.IsFaithfulPosMap.starAlgEquiv_is_isometry_tFAE n _ _ φ _ (innerAutStarAlg U))
        2 1
    simp_rw [hf, ← innerAutStarAlg_symm_eq_star, this]
    constructor
    · rintro ⟨f, hf⟩
      obtain ⟨U, rfl⟩ := StarAlgEquiv.of_matrix_is_inner f
      exact ⟨U, hf⟩
    · rintro ⟨U, hU⟩
      exact ⟨innerAutStarAlg U, hU⟩)


-- @@ L331-346 expanded
theorem Qam.iso_preserves_spectrum (A B : (Matrix n n ℂ) →ₗ[ℂ] (Matrix n n ℂ))
    (h : @Qam.Iso n _ _ φ A B) : spectrum ℂ A = spectrum ℂ B :=
  by
  obtain ⟨f, ⟨hf, _⟩⟩ := h
  let f' := f.toLinearMap
  let f'' := f.symm.toLinearMap
  have hh' : f'' ∘ₗ f' = LinearMap.id := by
    ext x
    simp [f', f'', StarAlgEquiv.symm_apply_apply]
  have : B = f'' ∘ₗ A ∘ₗ f' := by rw [hf, ← LinearMap.comp_assoc, hh', LinearMap.id_comp]
  have hh'' : f' ∘ₗ f'' = LinearMap.id := by
    ext x
    simp [f', f'', StarAlgEquiv.apply_symm_apply]
  rw [this, spectrum.comm f'' (A ∘ₗ f'), LinearMap.comp_assoc, hh'', LinearMap.comp_id]
    -- MOVE:


-- @@ L347-357 expanded
theorem innerAut_lm_rankOne [hφ : φ.IsFaithfulPosMap] {U : Matrix.unitaryGroup n ℂ}
    (hU : Commute φ.matrix U) (x y : (Matrix n n ℂ)) :
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    (innerAut U ∘ₗ
        (@rankOne ℂ _ _ _ _ _ _ _ x y : (Matrix n n ℂ) →ₗ[ℂ] (Matrix n n ℂ)) ∘ₗ innerAut (star U) =
      @rankOne ℂ _ _ _ _ _ _ _ ((innerAut U) x) ((innerAut U) y)) :=
  letI := Matrix.isStarAlgebra (φ := φ)
  letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
  letI := Module.Dual.NormedAddCommGroup φ
  letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
  letI := Module.Dual.InnerProductSpace (φ := φ)
  (by
    rw [← innerAut_adjoint_eq_iff] at hU
    simp_rw [LinearMap.ext_iff, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, rankOne_apply,
      _root_.map_smul, ← hU, LinearMap.adjoint_inner_right, forall_true_iff])


-- @@ L359-361 verbatim
local notation "e_{" x "," y "}" => Matrix.stdBasisMatrix x y (1 : ℂ)

--MOVE:

-- @@ L362-368 expanded
theorem innerAut_lm_basis_apply (U : Matrix.unitaryGroup n ℂ) (i j k l : n) :
    ((innerAut U) (Matrix.stdBasisMatrix i j (1 : ℂ))) k l = (U ⊗ₖ star U) (k, j) (i, l) :=
  by
  simp_rw [Matrix.innerAut_apply, Matrix.mul_apply, Matrix.UnitaryGroup.inv_apply,
    Matrix.stdBasisMatrix, Matrix.single, of_apply, mul_boole, Finset.sum_mul, ite_mul,
    MulZeroClass.zero_mul, ite_and, Matrix.kroneckerMap, Matrix.of_apply]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]


-- @@ L370-377 expanded
lemma Module.Dual.IsFaithfulPosMap.basis_eq_onb_toBasis [hφ : φ.IsFaithfulPosMap] :
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    (hφ.basis = (hφ.orthonormalBasis).toBasis) :=
  letI := Matrix.isStarAlgebra (φ := φ)
  letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
  letI := Module.Dual.NormedAddCommGroup φ
  letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
  letI := Module.Dual.InnerProductSpace (φ := φ)
  (by
    ext
    simp only [OrthonormalBasis.coe_toBasis, Module.Dual.IsFaithfulPosMap.orthonormalBasis_apply,
      Module.Dual.IsFaithfulPosMap.basis_apply])


-- @@ L379-398 expanded
theorem Qam.rankOne_toMatrix_of_star_algEquiv_coord [hφ : φ.IsFaithfulPosMap] (x y : Matrix n n ℂ)
    (i j k l : n) :
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    (hφ.toMatrix (@rankOne ℂ _ _ _ _ _ _ _ x y) (i, j) (k, l) =
      ((x * hφ.matrixIsPosDef.rpow (1 / 2)) ⊗ₖ Matrix.conj (y * hφ.matrixIsPosDef.rpow (1 / 2)))
        (i, k) (j, l)) :=
  letI := Matrix.isStarAlgebra (φ := φ)
  letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
  letI := Module.Dual.NormedAddCommGroup φ
  letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
  letI := Module.Dual.InnerProductSpace (φ := φ)
  (by
    simp only [Module.Dual.IsFaithfulPosMap.toMatrix, LinearMap.toMatrixAlgEquiv,
      AlgEquiv.ofLinearEquiv_apply, Module.Dual.IsFaithfulPosMap.basis_eq_onb_toBasis,
      rankOne_toMatrix_of_onb]
    simp_rw [conjTranspose_replicateCol, Matrix.mul_apply, Matrix.replicateCol_apply,
      Matrix.replicateRow_apply, Pi.star_apply, kronecker_apply, conj_apply]
    simp only [Finset.sum_const, nsmul_eq_mul]
    simp only [OrthonormalBasis.repr_apply_apply, Module.Dual.IsFaithfulPosMap.inner_coord]
    simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.card_singleton,
      Nat.cast_one, one_div, RCLike.star_def, one_mul])

