/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import LeanPool.Monlib4.LinearAlgebra.PiDirectSum
public import LeanPool.Monlib4.LinearAlgebra.Ips.MatIps
public import LeanPool.Monlib4.LinearAlgebra.KroneckerToTensor
public import LeanPool.Monlib4.LinearAlgebra.Nacgor
import LeanPool.Monlib4.LinearAlgebra.MulPrimePrime
import LeanPool.Monlib4.LinearAlgebra.TensorProduct.BasicLemmas
import LeanPool.Monlib4.Preq.Dite
import LeanPool.Monlib4.Preq.Ites


-- @@ L17-21 verbatim
/-!
 # Frobenius equations

 This file contains the proof of the Frobenius equations.
-/


-- @@ L23-23 verbatim
@[expose] public section



-- @@ L26-30 verbatim
variable {n p : Type _} [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]
  {φ : Module.Dual ℂ (Matrix n n ℂ)} (hφ : φ.IsFaithfulPosMap) {ψ : Module.Dual ℂ (Matrix p p ℂ)}
  (hψ : ψ.IsFaithfulPosMap) {k : Type _} [Fintype k] [DecidableEq k] {s : k → Type _}
  [∀ i, Fintype (s i)] [∀ i, DecidableEq (s i)] {θ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)}
  [hθ : ∀ i, (θ i).IsFaithfulPosMap]


-- @@ L32-32 verbatim
open scoped Matrix Kronecker TensorProduct BigOperators Functional InnerProductSpace


-- @@ L34-34 verbatim
open Matrix


-- @@ L36-39 verbatim
/-- Tensor product of two matrix-valued module dual functionals. -/
noncomputable def Module.Dual.tensorMul {n p : Type _} (φ₁ : Module.Dual ℂ (Matrix n n ℂ))
    (φ₂ : Module.Dual ℂ (Matrix p p ℂ)) : Module.Dual ℂ (Matrix n n ℂ ⊗[ℂ] Matrix p p ℂ) :=
  (TensorProduct.lid ℂ ℂ : ℂ ⊗[ℂ] ℂ →ₗ[ℂ] ℂ) ∘ₗ TensorProduct.map φ₁ φ₂


-- @@ L41-45 verbatim
omit [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p] in
theorem Module.Dual.tensorMul_apply (φ₁ : Module.Dual ℂ (Matrix n n ℂ))
    (φ₂ : Module.Dual ℂ (Matrix p p ℂ)) (x : Matrix n n ℂ) (y : Matrix p p ℂ) :
    (φ₁.tensorMul φ₂) (x ⊗ₜ[ℂ] y) = φ₁ x * φ₂ y :=
  rfl


-- @@ L47-54 verbatim
theorem Module.Dual.tensorMul_apply' (φ₁ : Module.Dual ℂ (Matrix n n ℂ))
    (φ₂ : Module.Dual ℂ (Matrix p p ℂ)) (x : Matrix n n ℂ ⊗[ℂ] Matrix p p ℂ) :
    φ₁.tensorMul φ₂ x =
      ∑ i, ∑ j, ∑ k, ∑ l,
        (TensorProduct.toKronecker x) (i, k) (j, l) *
          (φ₁ (stdBasisMatrix i j (1 : ℂ)) * φ₂ (stdBasisMatrix k l (1 : ℂ))) := by
  simp_rw [← Module.Dual.tensorMul_apply, ← smul_eq_mul, ← _root_.map_smul, ← map_sum]
  rw [← x.matrix_eq_sum_std_basis]


-- @@ L56-70 verbatim
theorem Module.Dual.tensorMul_apply'' (φ₁ : Module.Dual ℂ (Matrix n n ℂ))
    (φ₂ : Module.Dual ℂ (Matrix p p ℂ)) (a : Matrix (n × p) (n × p) ℂ) :
    ((φ₁.tensorMul φ₂).comp kroneckerToTensorProduct) a = (φ₁.matrix ⊗ₖ φ₂.matrix * a).trace := by
  have :
    (φ₁.matrix ⊗ₖ φ₂.matrix * a).trace =
      ((traceLinearMap _ ℂ ℂ).comp (LinearMap.mulLeft ℂ (φ₁.matrix ⊗ₖ φ₂.matrix))) a :=
    rfl
  simp_rw [this]
  clear this
  revert a
  rw [← LinearMap.ext_iff, KroneckerProduct.ext_iff]
  intro x y
  simp_rw [LinearMap.comp_apply, kroneckerToTensorProduct_apply, Module.Dual.tensorMul_apply,
    LinearMap.mulLeft_apply, traceLinearMap_apply, ← mul_kronecker_mul,
    trace_kronecker, Module.Dual.apply]


-- @@ L72-79 verbatim
theorem Module.Dual.tensorMul_matrix (φ₁ : Module.Dual ℂ (Matrix n n ℂ))
    (φ₂ : Module.Dual ℂ (Matrix p p ℂ)) :
    Module.Dual.matrix ((φ₁.tensorMul φ₂).comp kroneckerToTensorProduct) = φ₁.matrix ⊗ₖ φ₂.matrix :=
  by
  symm
  apply Module.Dual.apply_eq_of
  simp_rw [← Module.Dual.tensorMul_apply'' φ₁ φ₂]
  simp_all


-- @@ L81-87 verbatim
/-- Tensor products of faithful positive matrix functionals are faithful and positive. -/
theorem Module.Dual.IsFaithfulPosMap.tensorMul {φ₁ : Module.Dual ℂ (Matrix n n ℂ)}
    {φ₂ : Module.Dual ℂ (Matrix p p ℂ)} [hφ₁ : φ₁.IsFaithfulPosMap]
    [hφ₂ : φ₂.IsFaithfulPosMap] :
    (Module.Dual.IsFaithfulPosMap ((φ₁.tensorMul φ₂).comp kroneckerToTensorProduct)) := by
  rw [Module.Dual.isFaithfulPosMap_iff_of_matrix, Module.Dual.tensorMul_matrix]
  exact PosDef.kronecker hφ₁.matrixIsPosDef hφ₂.matrixIsPosDef


-- @@ L89-89 verbatim
attribute [instance] Module.Dual.IsFaithfulPosMap.tensorMul


-- @@ L91-164 verbatim
theorem Matrix.kroneckerToTensorProduct_adjoint [hφ : φ.IsFaithfulPosMap]
    [hψ : ψ.IsFaithfulPosMap] :
      letI : _root_.NormedAddCommGroup (Matrix n n ℂ) := Module.Dual.NormedAddCommGroup φ
      letI : _root_.SeminormedAddCommGroup (Matrix n n ℂ) :=
        (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
      letI : _root_.InnerProductSpace ℂ (Matrix n n ℂ) := Module.Dual.InnerProductSpace φ
      letI : _root_.NormedAddCommGroup (Matrix p p ℂ) := Module.Dual.NormedAddCommGroup ψ
      letI : _root_.SeminormedAddCommGroup (Matrix p p ℂ) :=
        (Module.Dual.NormedAddCommGroup ψ).toSeminormedAddCommGroup
      letI : _root_.InnerProductSpace ℂ (Matrix p p ℂ) := Module.Dual.InnerProductSpace ψ
      letI : _root_.NormedAddCommGroup (Matrix (n × p) (n × p) ℂ) :=
        Module.Dual.NormedAddCommGroup ((φ.tensorMul ψ).comp kroneckerToTensorProduct)
      letI : _root_.SeminormedAddCommGroup (Matrix (n × p) (n × p) ℂ) :=
        (Module.Dual.NormedAddCommGroup
          ((φ.tensorMul ψ).comp kroneckerToTensorProduct)).toSeminormedAddCommGroup
      letI : _root_.InnerProductSpace ℂ (Matrix (n × p) (n × p) ℂ) :=
        Module.Dual.InnerProductSpace ((φ.tensorMul ψ).comp kroneckerToTensorProduct)
      (@TensorProduct.toKronecker ℂ n p _ _ _ _ _ :
        Matrix n n ℂ ⊗[ℂ] Matrix p p ℂ →ₗ[ℂ] Matrix (n × p) (n × p) ℂ) =
      LinearMap.adjoint (kroneckerToTensorProduct :
          Matrix (n × p) (n × p) ℂ →ₗ[ℂ] Matrix n n ℂ ⊗[ℂ] Matrix p p ℂ) := by
  let : _root_.NormedAddCommGroup (Matrix n n ℂ) := Module.Dual.NormedAddCommGroup φ
  let : _root_.SeminormedAddCommGroup (Matrix n n ℂ) :=
    (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
  let : _root_.InnerProductSpace ℂ (Matrix n n ℂ) := Module.Dual.InnerProductSpace φ
  let : _root_.NormedAddCommGroup (Matrix p p ℂ) := Module.Dual.NormedAddCommGroup ψ
  let : _root_.SeminormedAddCommGroup (Matrix p p ℂ) :=
    (Module.Dual.NormedAddCommGroup ψ).toSeminormedAddCommGroup
  let : _root_.InnerProductSpace ℂ (Matrix p p ℂ) := Module.Dual.InnerProductSpace ψ
  let : _root_.NormedAddCommGroup (Matrix (n × p) (n × p) ℂ) :=
    Module.Dual.NormedAddCommGroup ((φ.tensorMul ψ).comp kroneckerToTensorProduct)
  let : _root_.SeminormedAddCommGroup (Matrix (n × p) (n × p) ℂ) :=
    (Module.Dual.NormedAddCommGroup
      ((φ.tensorMul ψ).comp kroneckerToTensorProduct)).toSeminormedAddCommGroup
  let : _root_.InnerProductSpace ℂ (Matrix (n × p) (n × p) ℂ) :=
    Module.Dual.InnerProductSpace ((φ.tensorMul ψ).comp kroneckerToTensorProduct)
  rw [TensorProduct.ext_iff']
  intro x y
  apply @ext_inner_left ℂ _ _
  intro a
  rw [TensorProduct.toKronecker_apply, LinearMap.adjoint_inner_right, Matrix.kmul_representation a]
  simp_rw [map_sum, _root_.map_smul, sum_inner, inner_smul_left]
  apply Finset.sum_congr rfl
  intros x_1 _
  apply Finset.sum_congr rfl
  intros x_2 _
  apply Finset.sum_congr rfl
  intros x_3 _
  apply Finset.sum_congr rfl
  intros x_4 _
  symm
  calc
    (starRingEnd ℂ) (a (x_1, x_3) (x_2, x_4)) *
          (⟪(kroneckerToTensorProduct
              (stdBasisMatrix x_1 x_2 (1 : ℂ) ⊗ₖ stdBasisMatrix x_3 x_4 (1 : ℂ))),
            x ⊗ₜ[ℂ] y⟫_ℂ) =
        (starRingEnd ℂ) (a (x_1, x_3) (x_2, x_4)) *
          (⟪(stdBasisMatrix x_1 x_2 (1 : ℂ) ⊗ₜ[ℂ] stdBasisMatrix x_3 x_4 (1 : ℂ)),
            x ⊗ₜ[ℂ] y⟫_ℂ) :=
      by rw [kroneckerToTensorProduct_apply]
    _ =
        (starRingEnd ℂ) (a (x_1, x_3) (x_2, x_4)) *
          (⟪stdBasisMatrix x_1 x_2 (1 : ℂ), x⟫_ℂ *
            ⟪stdBasisMatrix x_3 x_4 (1 : ℂ), y⟫_ℂ) :=
      by rw [TensorProduct.inner_tmul]
    _ =
        (starRingEnd ℂ) (a (x_1, x_3) (x_2, x_4)) *
          (⟪(stdBasisMatrix x_1 x_2 (1 : ℂ) ⊗ₖ stdBasisMatrix x_3 x_4 (1 : ℂ)),
            x ⊗ₖ y⟫_ℂ) := by
        rw [Module.Dual.IsFaithfulPosMap.inner_eq' _
          ((stdBasisMatrix x_1 x_2 (1 : ℂ)) ⊗ₖ (stdBasisMatrix x_3 x_4 (1 : ℂ))) (x ⊗ₖ y),
          Module.Dual.tensorMul_matrix, kronecker_conjTranspose, ← mul_kronecker_mul,
            ← mul_kronecker_mul, trace_kronecker,
          Module.Dual.IsFaithfulPosMap.inner_eq', Module.Dual.IsFaithfulPosMap.inner_eq']


-- @@ L166-201 verbatim
theorem TensorProduct.toKronecker_adjoint [hφ : φ.IsFaithfulPosMap]
    [hψ : ψ.IsFaithfulPosMap] :
    letI : _root_.NormedAddCommGroup (Matrix n n ℂ) := Module.Dual.NormedAddCommGroup φ
    letI : _root_.SeminormedAddCommGroup (Matrix n n ℂ) :=
      (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI : _root_.InnerProductSpace ℂ (Matrix n n ℂ) := Module.Dual.InnerProductSpace φ
    letI : _root_.NormedAddCommGroup (Matrix p p ℂ) := Module.Dual.NormedAddCommGroup ψ
    letI : _root_.SeminormedAddCommGroup (Matrix p p ℂ) :=
      (Module.Dual.NormedAddCommGroup ψ).toSeminormedAddCommGroup
    letI : _root_.InnerProductSpace ℂ (Matrix p p ℂ) := Module.Dual.InnerProductSpace ψ
    letI : _root_.NormedAddCommGroup (Matrix (n × p) (n × p) ℂ) :=
      Module.Dual.NormedAddCommGroup ((φ.tensorMul ψ).comp kroneckerToTensorProduct)
    letI : _root_.SeminormedAddCommGroup (Matrix (n × p) (n × p) ℂ) :=
      (Module.Dual.NormedAddCommGroup
        ((φ.tensorMul ψ).comp kroneckerToTensorProduct)).toSeminormedAddCommGroup
    letI : _root_.InnerProductSpace ℂ (Matrix (n × p) (n × p) ℂ) :=
      Module.Dual.InnerProductSpace ((φ.tensorMul ψ).comp kroneckerToTensorProduct)
    (kroneckerToTensorProduct : Matrix (n × p) (n × p) ℂ →ₗ[ℂ] Matrix n n ℂ ⊗[ℂ] Matrix p p ℂ) =
      LinearMap.adjoint (@TensorProduct.toKronecker ℂ n p _ _ _ _ _ :
          Matrix n n ℂ ⊗[ℂ] Matrix p p ℂ →ₗ[ℂ] Matrix (n × p) (n × p) ℂ) := by
  let : _root_.NormedAddCommGroup (Matrix n n ℂ) := Module.Dual.NormedAddCommGroup φ
  let : _root_.SeminormedAddCommGroup (Matrix n n ℂ) :=
    (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
  let : _root_.InnerProductSpace ℂ (Matrix n n ℂ) := Module.Dual.InnerProductSpace φ
  let : _root_.NormedAddCommGroup (Matrix p p ℂ) := Module.Dual.NormedAddCommGroup ψ
  let : _root_.SeminormedAddCommGroup (Matrix p p ℂ) :=
    (Module.Dual.NormedAddCommGroup ψ).toSeminormedAddCommGroup
  let : _root_.InnerProductSpace ℂ (Matrix p p ℂ) := Module.Dual.InnerProductSpace ψ
  let : _root_.NormedAddCommGroup (Matrix (n × p) (n × p) ℂ) :=
    Module.Dual.NormedAddCommGroup ((φ.tensorMul ψ).comp kroneckerToTensorProduct)
  let : _root_.SeminormedAddCommGroup (Matrix (n × p) (n × p) ℂ) :=
    (Module.Dual.NormedAddCommGroup
      ((φ.tensorMul ψ).comp kroneckerToTensorProduct)).toSeminormedAddCommGroup
  let : _root_.InnerProductSpace ℂ (Matrix (n × p) (n × p) ℂ) :=
    Module.Dual.InnerProductSpace ((φ.tensorMul ψ).comp kroneckerToTensorProduct)
  rw [@Matrix.kroneckerToTensorProduct_adjoint n p _ _ _ _ φ ψ hφ hψ, LinearMap.adjoint_adjoint]


-- @@ L203-209 verbatim
theorem Matrix.kroneckerToTensorProduct_comp_toKronecker :
    (kroneckerToTensorProduct : Matrix (n × p) (n × p) ℂ →ₗ[ℂ] _).comp
        (TensorProduct.toKronecker : Matrix n n ℂ ⊗[ℂ] Matrix p p ℂ →ₗ[ℂ] _) =
      1 := by
  rw [TensorProduct.ext_iff']
  intro x y
  simp_rw [LinearMap.comp_apply, TensorProduct.toKronecker_to_tensorProduct, Module.End.one_apply]


-- @@ L211-211 verbatim
local notation "ℍ" => Matrix n n ℂ


-- @@ L213-213 verbatim
local notation "ℍ_" i => Matrix (s i) (s i) ℂ


-- @@ L215-215 verbatim
local notation x " ⊗ₘ " y => TensorProduct.map x y


-- @@ L217-217 verbatim
local notation "id" => (1 : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)


-- @@ L219-227 verbatim
/-- The normed additive group of matrices induced by a faithful positive functional. -/
@[reducible]
noncomputable def Module.Dual.isNormedAddCommGroupOfRing {n : Type _} [Fintype n]
    [DecidableEq n] (ψ : Module.Dual ℂ (Matrix n n ℂ)) [ψ.IsFaithfulPosMap] :
    NormedAddCommGroupOfRing (Matrix n n ℂ)
    where
  toNorm := (Module.Dual.NormedAddCommGroup ψ).toNorm
  toMetricSpace := (Module.Dual.NormedAddCommGroup ψ).toMetricSpace
  dist_eq := (Module.Dual.NormedAddCommGroup ψ).dist_eq


-- @@ L229-237 verbatim
/-- The normed additive commutative group structure induced by faithful block functionals. -/
@[reducible]
noncomputable def Pi.module.Dual.isNormedAddCommGroupOfRing
    (ψ : ∀ i, Module.Dual ℂ (Matrix (s i) (s i) ℂ)) [∀ i, (ψ i).IsFaithfulPosMap] :
    NormedAddCommGroupOfRing (PiMat ℂ k s)
    where
  toNorm := (Module.Dual.PiNormedAddCommGroup (φ := ψ)).toNorm
  toMetricSpace := (Module.Dual.PiNormedAddCommGroup (φ := ψ)).toMetricSpace
  dist_eq := (Module.Dual.PiNormedAddCommGroup (φ := ψ)).dist_eq


-- @@ L239-239 verbatim
local notation "l(" x ")" => x →ₗ[ℂ] x


-- @@ L241-241 verbatim
open scoped BigOperators


-- @@ L243-249 verbatim
/-- Linear map from one matrix summand to another in a direct product of matrix blocks. -/
noncomputable def matrixDirectSumFromTo
    (i j : k) :
        Matrix
        (s i) (s i) ℂ →ₗ[ℂ]
      Matrix (s j) (s j) ℂ :=
  @directSumFromTo ℂ _ k _ (fun a => Matrix (s a) (s a) ℂ) _ (fun _ => Matrix.module) i j


-- @@ L251-254 verbatim
omit [Fintype k] [(i : k) → Fintype (s i)] [(i : k) → DecidableEq (s i)] in
theorem matrixDirectSumFromTo_same (i : k) :
    (matrixDirectSumFromTo i i : Matrix (s i) (s i) ℂ →ₗ[ℂ] _) = 1 :=
  directSumFromTo_apply_same _


-- @@ L256-281 expanded
open scoped Classical in
omit [Fintype k] [(i : k) → DecidableEq (s i)] in
theorem LinearMap.pi_mul'_apply_includeBlock' {i j : k} :
    letI : ∀ i, DecidableEq (s i) := fun i => Classical.decEq (s i)
    (LinearMap.mul' ℂ (PiMat ℂ k s)) ∘ₗ
        (TensorProduct.map (includeBlock : (Matrix (s i) (s i) ℂ) →ₗ[ℂ] (PiMat ℂ k s))
          (includeBlock : (Matrix (s j) (s j) ℂ) →ₗ[ℂ] (PiMat ℂ k s))) =
      if i = j then
        (includeBlock : (Matrix (s j) (s j) ℂ) →ₗ[ℂ] (PiMat ℂ k s)) ∘ₗ
          (LinearMap.mul' ℂ (Matrix (s j) (s j) ℂ)) ∘ₗ
            (TensorProduct.map (matrixDirectSumFromTo i j)
              (1 : (Matrix (s j) (s j) ℂ) →ₗ[ℂ] Matrix (s j) (s j) ℂ))
      else 0 :=
  by
  classical
  rw [TensorProduct.ext_iff']
  intro x y
  rw [funext_iff]
  intro a
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply, includeBlock_apply,
    Pi.mul_apply, dite_hMul, hMul_dite, MulZeroClass.mul_zero, MulZeroClass.zero_mul, ite_apply_lm,
    LinearMap.zero_apply, ite_apply, Pi.zero_apply, Module.End.one_apply]
  by_cases h : j = a
  · simp_rw [matrixDirectSumFromTo, directSumFromTo, LinearMap.comp_apply]
    simp [Pi.single, Function.update, h]
    split_ifs <;> aesop
  · simp [h]


-- @@ L283-289 expanded
/-- Linear equivalence splitting the tensor product of matrix-block products into block tensor
  products. -/
noncomputable def directSumTensorMatrix :
    ((PiMat ℂ k s) ⊗[ℂ] PiMat ℂ k s) ≃ₗ[ℂ]
      Π i : k × k, (Matrix (s i.1) (s i.1) ℂ) ⊗[ℂ] Matrix (s i.2) (s i.2) ℂ :=
  @directSumTensor ℂ _ k k _ _ _ _ (fun i => Matrix (s i) (s i) ℂ) (fun i => Matrix (s i) (s i) ℂ) _
    _ (fun _ => Matrix.module) fun _ => Matrix.module


-- @@ L291-294 expanded
@[simp]
theorem Module.Dual.IsFaithfulPosMap.sig_apply' [hφ : φ.IsFaithfulPosMap] {r : ℝ}
    {x : Matrix n n ℂ} : hφ.sig r x = hφ.matrixIsPosDef.rpow (-r) * x * hφ.matrixIsPosDef.rpow r :=
  rfl

