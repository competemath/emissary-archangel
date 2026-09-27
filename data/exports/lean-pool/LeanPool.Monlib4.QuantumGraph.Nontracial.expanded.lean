/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import LeanPool.Monlib4.LinearAlgebra.QuantumSet.Symm
public import LeanPool.Monlib4.LinearAlgebra.QuantumSet.Instances


-- @@ L11-15 verbatim
/-!
 # Quantum graphs: quantum adjacency matrices

 This file defines the quantum adjacency matrix of a quantum graph.
-/


-- @@ L17-17 verbatim
@[expose] public section



-- @@ L20-20 verbatim
variable {n p : Type _} [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]


-- @@ L22-22 verbatim
open scoped TensorProduct BigOperators Kronecker


-- @@ L24-24 verbatim
local notation "ℍ" => Matrix n n ℂ

-- @@ L25-25 verbatim
local notation "ℍ₂" => Matrix p p ℂ


-- @@ L27-27 verbatim
local notation "⊗K" => Matrix (n × n) (n × n) ℂ


-- @@ L29-29 verbatim
local notation "l(" x ")" => x →ₗ[ℂ] x


-- @@ L31-31 verbatim
local notation "L(" x ")" => x →L[ℂ] x


-- @@ L33-33 verbatim
local notation "e_{" i "," j "}" => Matrix.stdBasisMatrix i j (1 : ℂ)


-- @@ L35-35 verbatim
variable {φ : Module.Dual ℂ (Matrix n n ℂ)} {ψ : Module.Dual ℂ (Matrix p p ℂ)}


-- @@ L37-37 verbatim
open scoped Matrix


-- @@ L39-39 verbatim
open Matrix


-- @@ L41-41 verbatim
local notation "|" x "⟩⟨" y "|" => @rankOne ℂ _ _ _ _ _ _ _ x y


-- @@ L43-43 expanded
local notation "m" => LinearMap.mul' ℂ (Matrix n n ℂ)


-- @@ L45-45 expanded
local notation "η" => Algebra.linearMap ℂ (Matrix n n ℂ)


-- @@ L47-47 verbatim
local notation x " ⊗ₘ " y => TensorProduct.map x y


-- @@ L49-50 verbatim
local notation "υ" =>
  LinearEquiv.toLinearMap (TensorProduct.assoc ℂ (Matrix n n ℂ) (Matrix n n ℂ) (Matrix n n ℂ))


-- @@ L52-54 verbatim
local notation "υ⁻¹" =>
  LinearEquiv.toLinearMap (LinearEquiv.symm (TensorProduct.assoc ℂ (Matrix n n ℂ) (Matrix n n
    ℂ) (Matrix n n ℂ)))


-- @@ L56-57 verbatim
local notation "ϰ" =>
  LinearEquiv.toLinearMap ((TensorProduct.comm ℂ (Matrix n n ℂ) ℂ))


-- @@ L59-60 verbatim
local notation "ϰ⁻¹" =>
  LinearEquiv.toLinearMap (LinearEquiv.symm (TensorProduct.comm ℂ (Matrix n n ℂ) ℂ))


-- @@ L62-63 verbatim
local notation "τ" =>
  LinearEquiv.toLinearMap (TensorProduct.lid ℂ (Matrix n n ℂ))


-- @@ L65-66 verbatim
local notation "τ⁻¹" =>
  LinearEquiv.toLinearMap (LinearEquiv.symm (TensorProduct.lid ℂ (Matrix n n ℂ)))


-- @@ L68-68 verbatim
local notation "id" => (1 : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)


-- @@ L70-70 verbatim
open TensorProduct


-- @@ L72-73 verbatim
theorem Finset.sum_fin_one {α : Type _} [AddCommMonoid α] (f : Fin 1 → α) : ∑ i, f i = f 0 :=
  Fin.sum_univ_one f


-- @@ L75-78 expanded
theorem sig_apply_posDef_matrix_hMul [hφ : φ.IsFaithfulPosMap] (t : ℝ) (x : Matrix n n ℂ) :
    hφ.sig t (hφ.matrixIsPosDef.rpow t * x) = x * hφ.matrixIsPosDef.rpow t := by
  simp_rw [Module.Dual.IsFaithfulPosMap.sig_apply, ← Matrix.mul_assoc, PosDef.rpow_mul_rpow,
    neg_add_cancel, PosDef.rpow_zero, Matrix.one_mul]


-- @@ L80-83 expanded
theorem sig_apply_posDef_matrix_mul' [hφ : φ.IsFaithfulPosMap] (x : Matrix n n ℂ) :
    hφ.sig 1 (φ.matrix * x) = x * φ.matrix :=
  by
  nth_rw 2 [← PosDef.rpow_one_eq_self hφ.matrixIsPosDef]
  rw [← sig_apply_posDef_matrix_hMul, PosDef.rpow_one_eq_self]


-- @@ L85-88 expanded
theorem sig_apply_matrix_hMul_posDef [hφ : φ.IsFaithfulPosMap] (t : ℝ) (x : Matrix n n ℂ) :
    hφ.sig t (x * hφ.matrixIsPosDef.rpow (-t)) = hφ.matrixIsPosDef.rpow (-t) * x := by
  simp_rw [Module.Dual.IsFaithfulPosMap.sig_apply, Matrix.mul_assoc, PosDef.rpow_mul_rpow,
    neg_add_cancel, PosDef.rpow_zero, Matrix.mul_one]


-- @@ L90-94 expanded
theorem sig_apply_matrix_hMul_posDef' [hφ : φ.IsFaithfulPosMap] (x : Matrix n n ℂ) :
    hφ.sig (-1) (x * φ.matrix) = φ.matrix * x :=
  by
  nth_rw 2 [← PosDef.rpow_one_eq_self hφ.matrixIsPosDef]
  nth_rw 2 [← neg_neg (1 : ℝ)]
  rw [← sig_apply_matrix_hMul_posDef, neg_neg, PosDef.rpow_one_eq_self]


-- @@ L96-99 expanded
theorem sig_apply_matrix_hMul_posDef'' [hφ : φ.IsFaithfulPosMap] (x : Matrix n n ℂ) :
    hφ.sig 1 (x * φ.matrix⁻¹) = φ.matrix⁻¹ * x :=
  by
  nth_rw 2 [← PosDef.rpow_neg_one_eq_inv_self hφ.matrixIsPosDef]
  rw [← sig_apply_matrix_hMul_posDef, PosDef.rpow_neg_one_eq_inv_self]


-- @@ L101-107 expanded
theorem sig_apply_basis [hφ : φ.IsFaithfulPosMap] (i : n × n) :
    hφ.sig 1 (hφ.basis i) =
      φ.matrix⁻¹ * Matrix.stdBasisMatrix i.1 i.2 (1 : ℂ) * hφ.matrixIsPosDef.rpow (1 / 2) :=
  by
  rw [Module.Dual.IsFaithfulPosMap.basis_apply]
  simp_rw [Module.Dual.IsFaithfulPosMap.sig_apply, Matrix.mul_assoc, PosDef.rpow_mul_rpow,
    PosDef.rpow_neg_one_eq_inv_self]
  norm_num


-- @@ L109-125 expanded
omit [DecidableEq n] in
theorem Qam.symm'_symm_real_apply_adjoint_tFAE [hφ : φ.IsFaithfulPosMap]
    (A : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) :
    letI : DecidableEq n := Classical.decEq n
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    (List.TFAE
      [symmMap ℂ (Matrix n n ℂ) _ A = A, (symmMap ℂ (Matrix n n ℂ) _).symm A = A,
        A.real = LinearMap.adjoint A, ∀ x y, φ (A x * y) = φ (x * A y)]) :=
  by
  classical
    exact
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    (by
      let : Coalgebra ℂ (Matrix n n ℂ) := Coalgebra.ofFiniteDimensionalHilbertAlgebra
      suffices φ = Coalgebra.counit by
        simp_rw [this]
        exact symmMap_eq_self_tfae _ rfl
      ext
      simp_rw [← Coalgebra.inner_eq_counit', Module.Dual.IsFaithfulPosMap.inner_eq,
        conjTranspose_one, one_mul])


-- @@ L127-129 expanded
theorem sig_comp_eq_iff [hφ : φ.IsFaithfulPosMap] (t : ℝ) (A B : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) :
    (hφ.sig t).toLinearMap.comp A = B ↔ A = (hφ.sig (-t)).toLinearMap.comp B := by
  rw [AlgEquiv.comp_linearMap_eq_iff, Module.Dual.IsFaithfulPosMap.sig_symm_eq]


-- @@ L131-133 expanded
theorem stdBasisMatrix_squash (i j k l : n) (x : Matrix n n ℂ) :
    Matrix.stdBasisMatrix i j (1 : ℂ) * x * Matrix.stdBasisMatrix k l (1 : ℂ) =
      x j k • Matrix.stdBasisMatrix i l (1 : ℂ) :=
  by simp_all


-- @@ L135-135 verbatim
open scoped ComplexOrder

-- @@ L136-160 expanded
theorem map_sig_mulLeft_injective [hφ : φ.IsFaithfulPosMap] (t s : ℝ) :
    Function.Injective
      (LinearMap.mulLeft ℂ
        (hφ.matrixIsPosDef.rpow t ⊗ₜ[ℂ]
          ((op ℂ (A := Matrix n n ℂ)).toLinearMap : Matrix n n ℂ →ₗ[ℂ] (Matrix n n ℂ)ᵐᵒᵖ)
            (hφ.matrixIsPosDef.rpow s))) :=
  by
  intro a b h
  have :
    ∀ a,
      a =
        (LinearMap.mulLeft ℂ
            (hφ.matrixIsPosDef.rpow (-t) ⊗ₜ[ℂ]
              ((op ℂ (A := Matrix n n ℂ)).toLinearMap : Matrix n n ℂ →ₗ[ℂ] (Matrix n n ℂ)ᵐᵒᵖ)
                (hφ.matrixIsPosDef.rpow (-s))))
          (LinearMap.mulLeft ℂ
            (hφ.matrixIsPosDef.rpow t ⊗ₜ[ℂ]
              ((op ℂ (A := Matrix n n ℂ)).toLinearMap : Matrix n n ℂ →ₗ[ℂ] (Matrix n n ℂ)ᵐᵒᵖ)
                (hφ.matrixIsPosDef.rpow s))
            a) :=
    by
    intro a
    simp_rw [← LinearMap.comp_apply, ← LinearMap.mulLeft_mul, Algebra.TensorProduct.tmul_mul_tmul,
      LinearEquiv.coe_coe, op_apply, ← MulOpposite.op_mul, PosDef.rpow_mul_rpow, neg_add_cancel,
      add_neg_cancel, PosDef.rpow_zero, MulOpposite.op_one, ← Algebra.TensorProduct.one_def,
      LinearMap.mulLeft_one, LinearMap.id_apply]
  rw [this a, h, ← this]


-- @@ L162-186 expanded
theorem map_sig_mulRight_injective [hφ : φ.IsFaithfulPosMap] (t s : ℝ) :
    Function.Injective
      (LinearMap.mulRight ℂ
        (hφ.matrixIsPosDef.rpow t ⊗ₜ[ℂ]
          ((op ℂ (A := Matrix n n ℂ)).toLinearMap : Matrix n n ℂ →ₗ[ℂ] (Matrix n n ℂ)ᵐᵒᵖ)
            (hφ.matrixIsPosDef.rpow s))) :=
  by
  intro a b h
  have :
    ∀ a,
      a =
        (LinearMap.mulRight ℂ
            (hφ.matrixIsPosDef.rpow (-t) ⊗ₜ[ℂ]
              ((op ℂ (A := Matrix n n ℂ)).toLinearMap : Matrix n n ℂ →ₗ[ℂ] (Matrix n n ℂ)ᵐᵒᵖ)
                (hφ.matrixIsPosDef.rpow (-s))))
          (LinearMap.mulRight ℂ
            (hφ.matrixIsPosDef.rpow t ⊗ₜ[ℂ]
              ((op ℂ (A := Matrix n n ℂ)).toLinearMap : Matrix n n ℂ →ₗ[ℂ] (Matrix n n ℂ)ᵐᵒᵖ)
                (hφ.matrixIsPosDef.rpow s))
            a) :=
    by
    intro a
    simp_rw [← LinearMap.comp_apply, ← LinearMap.mulRight_mul, Algebra.TensorProduct.tmul_mul_tmul,
      LinearEquiv.coe_coe, op_apply, ← MulOpposite.op_mul, PosDef.rpow_mul_rpow, neg_add_cancel,
      add_neg_cancel, PosDef.rpow_zero, MulOpposite.op_one, ← Algebra.TensorProduct.one_def,
      LinearMap.mulRight_one, LinearMap.id_apply]
  rw [this a, h, ← this]


-- @@ L188-198 expanded
theorem LinearMap.matrix.mulRight_adjoint [hφ : φ.IsFaithfulPosMap] (x : Matrix n n ℂ) :
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    (LinearMap.adjoint (LinearMap.mulRight ℂ x) = LinearMap.mulRight ℂ (hφ.sig (-1) xᴴ)) :=
  letI := Matrix.isStarAlgebra (φ := φ)
  letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
  letI := Module.Dual.NormedAddCommGroup φ
  letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
  letI := Module.Dual.InnerProductSpace (φ := φ)
  (by
    symm
    rw [@LinearMap.eq_adjoint_iff ℂ _]
    intro a b
    simp_rw [LinearMap.mulRight_apply, Module.Dual.IsFaithfulPosMap.sig_apply, neg_neg,
      PosDef.rpow_one_eq_self, PosDef.rpow_neg_one_eq_inv_self, ←
      Module.Dual.IsFaithfulPosMap.inner_left_conj])


-- @@ L200-211 expanded
omit [DecidableEq n] in
theorem LinearMap.matrix.mulLeft_adjoint [hφ : φ.IsFaithfulPosMap] (x : Matrix n n ℂ) :
    letI : DecidableEq n := Classical.decEq n
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    (LinearMap.adjoint (LinearMap.mulLeft ℂ x) = LinearMap.mulLeft ℂ xᴴ) :=
  by
  classical
    exact
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    (by
      symm
      rw [@LinearMap.eq_adjoint_iff ℂ _]
      intro a b
      simp_rw [LinearMap.mulLeft_apply, ← Module.Dual.IsFaithfulPosMap.inner_right_hMul])

