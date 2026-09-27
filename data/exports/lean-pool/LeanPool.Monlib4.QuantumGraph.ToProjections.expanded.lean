/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import LeanPool.Monlib4.QuantumGraph.PiMatFinTwo
public import LeanPool.Monlib4.LinearAlgebra.Ips.Nontracial
import LeanPool.Monlib4.Preq.Finset
import LeanPool.Monlib4.QuantumGraph.Nontracial


-- @@ L13-19 verbatim
/-!

# Quantum graphs as projections

This file contains the definition of a quantum graph as a projection, and the proof that the

-/


-- @@ L21-21 verbatim
@[expose] public section



-- @@ L24-25 verbatim
variable {p : Type _} [Fintype p] [DecidableEq p] {n : p → Type _} [∀ i, Fintype (n i)]
  [∀ i, DecidableEq (n i)]


-- @@ L27-27 verbatim
open scoped TensorProduct BigOperators Kronecker Functional ComplexOrder


-- @@ L29-30 verbatim
@[reducible]
local notation "ℍ" => Matrix p p ℂ

-- @@ L31-32 verbatim
@[reducible]
local notation "ℍ_" i => Matrix (n i) (n i) ℂ


-- @@ L34-35 verbatim
@[reducible]
local notation "l(" x ")" => x →ₗ[ℂ] x

-- @@ L36-37 verbatim
@[reducible]
local notation "L(" x ")" => x →L[ℂ] x

-- @@ L38-39 verbatim
@[reducible]
local notation "e_{" i "," j "}" => Matrix.stdBasisMatrix i j (1 : ℂ)


-- @@ L41-41 verbatim
variable {φ : Module.Dual ℂ (Matrix p p ℂ)}


-- @@ L43-43 verbatim
open scoped Matrix


-- @@ L45-45 verbatim
open Matrix


-- @@ L47-47 verbatim
local notation "|" x "⟩⟨" y "|" => @rankOne ℂ _ _ _ _ _ _ _ x y


-- @@ L49-49 expanded
local notation "m" => LinearMap.mul' ℂ (Matrix p p ℂ)


-- @@ L51-51 expanded
local notation "η" => Algebra.linearMap ℂ (Matrix p p ℂ)


-- @@ L53-53 verbatim
local notation x " ⊗ₘ " y => TensorProduct.map x y


-- @@ L55-55 expanded
local notation "υ" =>
  (TensorProduct.assoc ℂ (Matrix p p ℂ) (Matrix p p ℂ) (Matrix p p ℂ) :
    (Matrix p p ℂ ⊗[ℂ] Matrix p p ℂ) ⊗[ℂ] Matrix p p ℂ →ₗ[ℂ]
      Matrix p p ℂ ⊗[ℂ] Matrix p p ℂ ⊗[ℂ] Matrix p p ℂ)


-- @@ L57-58 expanded
local notation "υ⁻¹" =>
  (LinearEquiv.symm (TensorProduct.assoc ℂ (Matrix p p ℂ) (Matrix p p ℂ) (Matrix p p ℂ)) :
    Matrix p p ℂ ⊗[ℂ] Matrix p p ℂ ⊗[ℂ] Matrix p p ℂ →ₗ[ℂ]
      (Matrix p p ℂ ⊗[ℂ] Matrix p p ℂ) ⊗[ℂ] Matrix p p ℂ)


-- @@ L60-60 expanded
local notation "ϰ" =>
  ((TensorProduct.comm ℂ (Matrix p p ℂ) ℂ) : Matrix p p ℂ ⊗[ℂ] ℂ →ₗ[ℂ] ℂ ⊗[ℂ] Matrix p p ℂ)


-- @@ L62-62 expanded
local notation "ϰ⁻¹" =>
  (LinearEquiv.symm (TensorProduct.comm ℂ (Matrix p p ℂ) ℂ) :
    ℂ ⊗[ℂ] Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ ⊗[ℂ] ℂ)


-- @@ L64-64 expanded
local notation "τ" => (TensorProduct.lid ℂ (Matrix p p ℂ) : ℂ ⊗[ℂ] Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ)


-- @@ L66-66 expanded
local notation "τ⁻¹" =>
  (LinearEquiv.symm (TensorProduct.lid ℂ (Matrix p p ℂ)) : Matrix p p ℂ →ₗ[ℂ] ℂ ⊗[ℂ] Matrix p p ℂ)


-- @@ L68-68 expanded
local notation "id" => (1 : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ)


-- @@ L70-71 verbatim
/-- Elaborate projection/QAM statements with the matrix coalgebra induced by `φ`. -/
syntax "withProjectionMatrixCoalgebraQuantum[" term "] " term : term

-- @@ L72-76 expanded
macro_rules
  |
  `(letI := Matrix.isStarAlgebra (φ := $φ)
      letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := $φ)
      letI := Module.Dual.NormedAddCommGroup $φ
      letI :=
        (Module.Dual.NormedAddCommGroup $φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      letI := (Module.Dual.NormedAddCommGroup $φ).toSeminormedAddCommGroup
      letI := Module.Dual.InnerProductSpace (φ := $φ)
      letI : Coalgebra ℂ (Matrix p p ℂ) := Coalgebra.ofFiniteDimensionalHilbertAlgebra
      $p) =>
    `(letI := Matrix.isStarAlgebra (φ := $φ)
      letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := $φ)
      letI := Module.Dual.NormedAddCommGroup $φ
      letI :=
        (Module.Dual.NormedAddCommGroup $φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      letI := (Module.Dual.NormedAddCommGroup $φ).toSeminormedAddCommGroup
      letI := Module.Dual.InnerProductSpace (φ := $φ)
      letI : Coalgebra ℂ (Matrix p p ℂ) := Coalgebra.ofFiniteDimensionalHilbertAlgebra
      $p)


-- @@ L78-79 verbatim
/-- Introduce the projection matrix coalgebra context induced by `φ` in a proof. -/
syntax "withProjectionMatrixCoalgebraQuantumCtx" "[" term "]" : tactic

-- @@ L80-84 expanded
macro_rules
  |
  `(tactic|
      let := Matrix.isStarAlgebra (φ := $φ);
          let := Module.Dual.IsFaithfulPosMap.quantumSet (φ := $φ);
          let := Module.Dual.NormedAddCommGroup $φ;
          let :=
            (Module.Dual.NormedAddCommGroup
                $φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace;
          let := (Module.Dual.NormedAddCommGroup $φ).toSeminormedAddCommGroup;
          let := Module.Dual.InnerProductSpace (φ := $φ);
        let : Coalgebra ℂ (Matrix p p ℂ) := Coalgebra.ofFiniteDimensionalHilbertAlgebra) =>
    `(tactic|
      let := Matrix.isStarAlgebra (φ := $φ);
        let := Module.Dual.IsFaithfulPosMap.quantumSet (φ := $φ);
        let := Module.Dual.NormedAddCommGroup $φ;
        let :=
          (Module.Dual.NormedAddCommGroup $φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace;
        let := (Module.Dual.NormedAddCommGroup $φ).toSeminormedAddCommGroup;
        let := Module.Dual.InnerProductSpace (φ := $φ);
      let : Coalgebra ℂ (Matrix p p ℂ) := Coalgebra.ofFiniteDimensionalHilbertAlgebra)


-- @@ L86-86 verbatim
namespace FiniteDimensional


-- @@ L88-91 verbatim
/-- Compatibility spelling for the old `FiniteDimensional.finrank` namespace. -/
noncomputable abbrev finrank (𝕜 E : Type*) [DivisionRing 𝕜] [AddCommGroup E]
    [Module 𝕜 E] : ℕ :=
  Module.finrank 𝕜 E


-- @@ L93-93 verbatim
end FiniteDimensional


-- @@ L95-95 verbatim
namespace Qam


-- @@ L97-101 expanded
/-- The reflexive idempotent product used in older Monlib quantum-graph files. -/
noncomputable abbrev reflIdempotent (hφ : φ.IsFaithfulPosMap)
    (A : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ) :
    (Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ) →ₗ[ℂ] Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ :=
  letI : φ.IsFaithfulPosMap := hφ
  letI := Matrix.isStarAlgebra (φ := φ)
  letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
  letI := Module.Dual.NormedAddCommGroup φ
  letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
  letI := Module.Dual.InnerProductSpace (φ := φ)
  letI : Coalgebra ℂ (Matrix p p ℂ) := Coalgebra.ofFiniteDimensionalHilbertAlgebra
  (schurMul A)


-- @@ L103-117 expanded
theorem isReal_and_idempotent_iff_psi_orthogonal_projection (hφ : φ.IsFaithfulPosMap)
    (A : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ) :
    Qam.reflIdempotent hφ A A = A ∧ LinearMap.IsReal A ↔
      IsIdempotentElem ((hφ.psi (ψ := φ) 0 (1 / 2)) A) ∧
        IsSelfAdjoint ((hφ.psi (ψ := φ) 0 (1 / 2)) A) :=
  by
  let : φ.IsFaithfulPosMap := hφ
  let := Matrix.isStarAlgebra (φ := φ);
      let := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ);
      let := Module.Dual.NormedAddCommGroup φ;
      let :=
        (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace;
      let := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup;
      let := Module.Dual.InnerProductSpace (φ := φ);
    let : Coalgebra ℂ (Matrix p p ℂ) := Coalgebra.ofFiniteDimensionalHilbertAlgebra
  change
    schurMul A A = A ∧ LinearMap.IsReal A ↔
      IsIdempotentElem ((QuantumSet.Psi (A := Matrix p p ℂ) (B := Matrix p p ℂ) 0 (1 / 2)) A) ∧
        IsSelfAdjoint ((QuantumSet.Psi (A := Matrix p p ℂ) (B := Matrix p p ℂ) 0 (1 / 2)) A)
  rw [← schurIdempotent_iff_Psi_isIdempotentElem A 0 (1 / 2)]
  convert (and_congr_right ?_) using 1
  intro _
  rw [isReal_iff_Psi_isSelfAdjoint A, show QuantumSet.k (Matrix p p ℂ) = 0 by rfl]
  norm_num


-- @@ L119-119 verbatim
end Qam


-- @@ L121-133 expanded
/-- Linear equivalence from block-diagonal matrix coordinates to the tensor product of
  block-diagonal matrices. -/
noncomputable def blockDiag'KroneckerEquiv {φ : ∀ i, Module.Dual ℂ (Matrix (n i) (n i) ℂ)}
    (hφ : ∀ i, (φ i).IsFaithfulPosMap) :
    Matrix (Σ i, n i × n i) (Σ i, n i × n i) ℂ ≃ₗ[ℂ]
      { x : Matrix (Σ i, n i) (Σ i, n i) ℂ // x.IsBlockDiagonal } ⊗[ℂ]
        { x : Matrix (Σ i, n i) (Σ i, n i) ℂ // x.IsBlockDiagonal } :=
  ((Module.Dual.pi.IsFaithfulPosMap.toMatrix fun i => (hφ i)).symm.toLinearEquiv.trans
        ((Module.Dual.pi.IsFaithfulPosMap.psi hφ hφ 0 0).trans
          (LinearEquiv.TensorProduct.map (1 : (∀ i, Matrix (n i) (n i) ℂ) ≃ₗ[ℂ] _)
            (Pi.transposeAlgEquiv p n : _ ≃ₐ[ℂ] _ᵐᵒᵖ).symm.toLinearEquiv))).trans
    (LinearEquiv.TensorProduct.map isBlockDiagonalPiAlgEquiv.symm.toLinearEquiv
      isBlockDiagonalPiAlgEquiv.symm.toLinearEquiv)


-- @@ L135-139 expanded
theorem Matrix.conj_conjTranspose' {R n₁ n₂ : Type _} [InvolutiveStar R] (A : Matrix n₁ n₂ R) :
    (Matrix.conj A)ᴴ = Aᵀ := by
  rw [← conj_conjTranspose A]
    -- Porting the inherited block-diagonal matrix calculation needs more heartbeats after Mathlib
    -- changes.


-- @@ L140-168 expanded
theorem toMatrix_mulLeft_mulRight_adjoint {φ : ∀ i, Module.Dual ℂ (Matrix (n i) (n i) ℂ)}
    (hφ : ∀ i, (φ i).IsFaithfulPosMap) (x y : ∀ i, Matrix (n i) (n i) ℂ) :
    letI : ∀ i, (φ i).IsFaithfulPosMap := hφ
    letI := PiMat.isStarAlgebra (ψ := φ)
    letI := Module.Dual.pi.IsFaithfulPosMap.quantumSet (ψ := φ)
    letI := Module.Dual.PiNormedAddCommGroup (φ := φ)
    letI :=
      (Module.Dual.PiNormedAddCommGroup (φ :=
          φ)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.PiNormedAddCommGroup (φ := φ)).toSeminormedAddCommGroup
    letI := Module.Dual.pi.InnerProductSpace (φ := φ)
    letI := fun i => Matrix.isStarAlgebra (φ := φ i)
    letI := fun i => Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ i)
    letI := fun i => Module.Dual.NormedAddCommGroup (φ i)
    letI := fun i =>
      (Module.Dual.NormedAddCommGroup (φ i)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := fun i => (Module.Dual.NormedAddCommGroup (φ i)).toSeminormedAddCommGroup
    letI := fun i => Module.Dual.InnerProductSpace (φ := φ i)
    ((Module.Dual.pi.IsFaithfulPosMap.toMatrix fun i => (hφ i))
        (LinearMap.mulLeft ℂ x *
          (LinearMap.adjoint (LinearMap.mulRight ℂ y) :
            (∀ i, Matrix (n i) (n i) ℂ) →ₗ[ℂ] ∀ i, Matrix (n i) (n i) ℂ)) =
      blockDiagonal' fun i => x i ⊗ₖ Matrix.conj ((hφ i).sig (1 / 2) (y i))) :=
  by
  let : ∀ i, (φ i).IsFaithfulPosMap := hφ
  let := PiMat.isStarAlgebra (ψ := φ);
      let := Module.Dual.pi.IsFaithfulPosMap.quantumSet (ψ := φ);
      let := Module.Dual.PiNormedAddCommGroup (φ := φ);
      let :=
        (Module.Dual.PiNormedAddCommGroup (φ :=
            φ)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace;
      let := (Module.Dual.PiNormedAddCommGroup (φ := φ)).toSeminormedAddCommGroup;
      let := Module.Dual.pi.InnerProductSpace (φ := φ);
    let := fun i => Matrix.isStarAlgebra (φ := φ i);
    let := fun i => Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ i);
    let := fun i => Module.Dual.NormedAddCommGroup (φ i);
    let := fun i =>
      (Module.Dual.NormedAddCommGroup (φ i)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace;
    let := fun i => (Module.Dual.NormedAddCommGroup (φ i)).toSeminormedAddCommGroup;
    let := fun i => Module.Dual.InnerProductSpace (φ := φ i)
  simp_rw [_root_.map_mul, ← lmul_eq_mul, ← rmul_eq_mul, rmul_adjoint, pi_lmul_toMatrix,
    pi_rmul_toMatrix, ← blockDiagonal'_mul, ← mul_kronecker_mul]
  simp only [Matrix.mul_one, Matrix.one_mul]
  apply Matrix.blockDiagonal'_inj.mpr
  funext i
  rw [show
      (modAut (-QuantumSet.k ((i : p) → Matrix (n i) (n i) ℂ) - 1) (star y)) i =
        (hφ i).sig (-1) ((y i)ᴴ)
      by
      change
        (Module.Dual.pi.IsFaithfulPosMap.sig hφ (-QuantumSet.k ((i : p) → Matrix (n i) (n i) ℂ) - 1)
              (star y))
            i =
          (hφ i).sig (-1) (y i)ᴴ
      rw [show QuantumSet.k ((i : p) → Matrix (n i) (n i) ℂ) = 0 by rfl]
      simp [Module.Dual.pi.IsFaithfulPosMap.sig_eq_pi_blocks, Pi.star_apply, star_eq_conjTranspose]]
  rw [show (hφ i).sig (1 / 2) ((hφ i).sig (-1) ((y i)ᴴ)) = ((hφ i).sig (1 / 2) (y i))ᴴ
      by
      rw [Module.Dual.IsFaithfulPosMap.sig_apply_sig]
      have : (1 / 2 : ℝ) + -1 = -(1 / 2) := by norm_num
      rw [this]
      exact (Module.Dual.IsFaithfulPosMap.sig_conjTranspose (hφ i) (1 / 2) (y i)).symm]
  rfl


-- @@ L170-189 verbatim
/-- Apply a linear map between dependent products to a selected input and output component. -/
@[simps]
def Pi.LinearMap.apply {ι₁ ι₂ : Type _} {E₁ : ι₁ → Type _} [DecidableEq ι₁]
    [∀ i, AddCommMonoid (E₁ i)] [∀ i, Module ℂ (E₁ i)] {E₂ : ι₂ → Type _}
    [∀ i, AddCommMonoid (E₂ i)] [∀ i, Module ℂ (E₂ i)] (i : ι₁) (j : ι₂) :
    ((∀ a, E₁ a) →ₗ[ℂ] ∀ a, E₂ a) →ₗ[ℂ] E₁ i →ₗ[ℂ] E₂ j
    where
  toFun x :=
    { toFun := fun a => (x ((LinearMap.single ℂ E₁ i : E₁ i →ₗ[ℂ] ∀ b, E₁ b) a)) j
      map_add' := fun a b => by simp only [map_add, Pi.add_apply]
      map_smul' := fun c a => by
        simp only [LinearMap.map_smul, Pi.smul_apply, RingHom.id_apply] }
  map_add' x y := by
    ext a
    simp_all
  map_smul' c x := by
    ext a
    simp_all

-- The matrix/tensor rank-one calculation unfolds several equivalences after the Mathlib port.

-- @@ L190-212 expanded
theorem rankOne_psi_transpose_to_lin {n : Type _} [DecidableEq n] [Fintype n]
    {φ : Module.Dual ℂ (Matrix n n ℂ)} [hφ : φ.IsFaithfulPosMap] (x y : Matrix n n ℂ) :
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    (hφ.toMatrix.symm
        (TensorProduct.toKronecker
          ((TensorProduct.map (1 : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
              (AlgEquiv.toLinearMap (transposeAlgEquiv n ℂ ℂ).symm))
            ((hφ.psi (ψ := φ) 0 (1 / 2)) (@rankOne ℂ _ _ _ _ _ _ _ x y)))) =
      LinearMap.mulLeft ℂ x *
        (LinearMap.adjoint (LinearMap.mulRight ℂ y) : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)) :=
  by
  let := Matrix.isStarAlgebra (φ := φ);
    let := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ);
    let := Module.Dual.NormedAddCommGroup φ;
    let := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace;
    let := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup;
    let := Module.Dual.InnerProductSpace (φ := φ)
  rw [← Function.Injective.eq_iff hφ.toMatrix.injective]
  simp_rw [_root_.map_mul, LinearMap.matrix.mulRight_adjoint, LinearMap.mulRight_toMatrix,
    LinearMap.mulLeft_toMatrix, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
    Module.Dual.IsFaithfulPosMap.sig_apply_sig]
  have : (1 / 2 : ℝ) + -1 = -(1 / 2) := by norm_num
  rw [AlgEquiv.apply_symm_apply, Module.Dual.IsFaithfulPosMap.psi, LinearEquiv.coe_mk]
  simp only [QuantumSet.Psi_apply, QuantumSet.PsiToFun_apply, TensorProduct.map_tmul,
    TensorProduct.toKronecker_apply, Module.End.one_apply, AlgEquiv.toLinearMap_apply,
    LinearEquiv.coe_coe, transposeAlgEquiv_symm_op_apply]
  rw [starAlgebra.modAut_zero, this]
  simp only [AlgEquiv.one_apply]
  rw [show modAut (1 / 2) y = hφ.sig (1 / 2) y by rfl, Matrix.star_eq_conjTranspose,
    Module.Dual.IsFaithfulPosMap.sig_conjTranspose hφ (1 / 2) y]


-- @@ L214-217 verbatim
private theorem matrix.stdBasisMatrix.transpose' {R n p : Type _} [DecidableEq n] [DecidableEq p]
    [Semiring R] {i : n} {j : p} {α : R} :
    (stdBasisMatrix i j α)ᵀ = stdBasisMatrix j i α := by
  simp_all


-- @@ L219-301 expanded
theorem rankOne_toMatrix_transpose_psi_symm [hφ : φ.IsFaithfulPosMap] (x y : Matrix p p ℂ) :
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    ((hφ.psi (ψ := φ) 0 (1 / 2)).symm
        ((TensorProduct.map (1 : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ)
            (transposeAlgEquiv p ℂ ℂ).toLinearMap)
          (kroneckerToTensorProduct (hφ.toMatrix (@rankOne ℂ _ _ _ _ _ _ _ x y)))) =
      LinearMap.mulLeft ℂ (x * φ.matrix) *
        (LinearMap.adjoint (LinearMap.mulRight ℂ (φ.matrix * y)) :
          Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ)) :=
  by
  let := Matrix.isStarAlgebra (φ := φ);
    let := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ);
    let := Module.Dual.NormedAddCommGroup φ;
    let := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace;
    let := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup;
    let := Module.Dual.InnerProductSpace (φ := φ)
  have hbasis : hφ.basis = hφ.orthonormalBasis.toBasis :=
    by
    ext ij i j
    simp [Module.Dual.IsFaithfulPosMap.orthonormalBasis_apply,
      Module.Dual.IsFaithfulPosMap.basis_apply]
  rw [show
      hφ.toMatrix (@rankOne ℂ _ _ _ _ _ _ _ x y) =
        LinearMap.toMatrix hφ.orthonormalBasis.toBasis hφ.orthonormalBasis.toBasis
          (@rankOne ℂ _ _ _ _ _ _ _ x y : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ)
      by
      ext i j
      simp [Module.Dual.IsFaithfulPosMap.toMatrix, hbasis, LinearMap.toMatrixAlgEquiv_apply,
        LinearMap.toMatrix_apply]]
  rw [rankOne_toMatrix_of_onb hφ.orthonormalBasis hφ.orthonormalBasis x y]
  simp only [Module.Dual.IsFaithfulPosMap.psi, Matrix.conjTranspose_replicateCol]
  rw [show
      replicateCol (Fin 1) (hφ.orthonormalBasis.repr x).ofLp *
          replicateRow (Fin 1) (star (hφ.orthonormalBasis.repr y).ofLp) =
        vecMulVec (hφ.orthonormalBasis.repr x).ofLp (star (hφ.orthonormalBasis.repr y).ofLp)
      from
      (Matrix.vecMulVec_eq (Fin 1) (hφ.orthonormalBasis.repr x).ofLp
          (star (hφ.orthonormalBasis.repr y).ofLp)).symm]
  rw [Matrix.kmul_representation
      (vecMulVec (hφ.orthonormalBasis.repr x).ofLp (star (hφ.orthonormalBasis.repr y).ofLp))]
  simp only [map_sum, _root_.map_smul, kroneckerToTensorProduct_apply, TensorProduct.map_tmul,
    QuantumSet.Psi_symm_apply, QuantumSet.PsiInvFun_apply, vecMulVec_apply, neg_zero,
    starAlgebra.modAut_zero, AlgEquiv.one_apply]
  simp_rw [AlgEquiv.toLinearMap_apply, transposeAlgEquiv_apply, MulOpposite.unop_op,
    Module.End.one_apply, ← rankOne_lm_smul_smul, Pi.star_apply, star_star,
    matrix.stdBasisMatrix.transpose', star_eq_conjTranspose, Matrix.single_conjTranspose, star_one]
  ext a i j
  simp only [LinearMap.sum_apply, ContinuousLinearMap.coe_coe, rankOne_apply, inner_smul_left,
    QuantumSet.modAut_isSymmetric, Module.End.mul_apply, LinearMap.matrix.mulRight_adjoint,
    LinearMap.mulRight_apply, LinearMap.mulLeft_apply, OrthonormalBasis.repr_apply_apply,
    inner_single_left, Module.Dual.IsFaithfulPosMap.inner_coord hφ]
  simp_rw [starRingEnd_apply, smul_smul, mul_assoc, ←
    mul_comm _ ((modAut (-(1 / 2)) (_ : Matrix p p ℂ) * φ.matrix) _ _)]
  rw [Finset.sum_sum_comm_sum]
  simp only [← Finset.sum_smul, ← Finset.mul_sum, ← mul_apply]
  simp_rw [mul_comm (star _), ← conjTranspose_apply, ← mul_apply, ← Matrix.smul_single']
  rw [show
      (∑ x_1,
          ∑ x_2,
            Matrix.single x_1 x_2
              ((x * hφ.matrixIsPosDef.rpow (1 / 2) *
                    ((modAut (-(1 / 2)) : Matrix p p ℂ ≃ₐ[ℂ] Matrix p p ℂ) a * φ.matrix) *
                  (y * hφ.matrixIsPosDef.rpow (1 / 2))ᴴ)
                x_1 x_2)) =
        x * hφ.matrixIsPosDef.rpow (1 / 2) *
            ((modAut (-(1 / 2)) : Matrix p p ℂ ≃ₐ[ℂ] Matrix p p ℂ) a * φ.matrix) *
          (y * hφ.matrixIsPosDef.rpow (1 / 2))ᴴ
      by
      exact
        (Matrix.matrix_eq_sum_single
            (x * hφ.matrixIsPosDef.rpow (1 / 2) *
                ((modAut (-(1 / 2)) : Matrix p p ℂ ≃ₐ[ℂ] Matrix p p ℂ) a * φ.matrix) *
              (y * hφ.matrixIsPosDef.rpow (1 / 2))ᴴ)).symm]
  rw [show (modAut (-(1 / 2)) : Matrix p p ℂ ≃ₐ[ℂ] Matrix p p ℂ) = hφ.sig (-(1 / 2)) from rfl]
  simp only [Module.Dual.IsFaithfulPosMap.sig_apply, conjTranspose_mul,
    (PosDef.rpow.isPosDef _ _).1.eq, hφ.matrixIsPosDef.1.eq]
  simp only [neg_neg]
  simp_rw [← mul_assoc]
  nth_rw 1 [mul_assoc x (hφ.matrixIsPosDef.rpow (1 / 2)) (hφ.matrixIsPosDef.rpow (1 / 2))]
  rw [show hφ.matrixIsPosDef.rpow (1 / 2) * hφ.matrixIsPosDef.rpow (1 / 2) = φ.matrix by
      rw [PosDef.rpow_mul_rpow, add_halves, PosDef.rpow_one_eq_self]]
  simp_rw [← PosDef.rpow_one_eq_self hφ.matrixIsPosDef]
  nth_rw
    1 [mul_assoc (x * hφ.matrixIsPosDef.rpow 1 * a) (hφ.matrixIsPosDef.rpow (-(1 / 2)))
      (hφ.matrixIsPosDef.rpow 1)]
  rw [PosDef.rpow_mul_rpow]
  ring_nf
  nth_rw
    1 [mul_assoc (x * hφ.matrixIsPosDef.rpow 1 * a * hφ.matrixIsPosDef.rpow 1 * yᴴ)
      (hφ.matrixIsPosDef.rpow 1) (hφ.matrixIsPosDef.rpow (-1))]
  rw [PosDef.rpow_mul_rpow]
  ring_nf
  simp only [PosDef.rpow_zero, mul_one]
  nth_rw
    1 [mul_assoc (x * hφ.matrixIsPosDef.rpow 1 * a) (hφ.matrixIsPosDef.rpow (1 / 2))
      (hφ.matrixIsPosDef.rpow (1 / 2))]
  rw [PosDef.rpow_mul_rpow]
  ring_nf


-- @@ L303-307 verbatim
open LinearMap in
private theorem lm_to_clm_comp {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {p q : E →ₗ[𝕜] E} :
    toContinuousLinearMap p * toContinuousLinearMap q = toContinuousLinearMap (p * q) :=
  rfl


-- @@ L309-313 verbatim
open LinearMap in
private theorem is_idempotent_elem_to_clm {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {p : E →ₗ[𝕜] E} :
    IsIdempotentElem p ↔ IsIdempotentElem (toContinuousLinearMap p) := by
  simp_rw [IsIdempotentElem, lm_to_clm_comp, Function.Injective.eq_iff (LinearEquiv.injective _)]


-- @@ L315-315 verbatim
open scoped FiniteDimensional

-- @@ L316-323 verbatim
open LinearMap in
private theorem is_self_adjoint_to_clm {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace E]
    {p : E →ₗ[𝕜] E} :
    IsSelfAdjoint p ↔ IsSelfAdjoint (toContinuousLinearMap p) :=
  (LinearMap.isSelfAdjoint_toContinuousLinearMap p).symm

-- Orthogonal projection existence goes through finite-dimensional completeness and CLM coercions.

-- @@ L324-339 verbatim
open LinearMap in
theorem orthogonal_projection_iff_lm {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {p : E →ₗ[𝕜] E} :
    (∃ U : Submodule 𝕜 E, (orthogonalProjection' U : E →ₗ[𝕜] E) = p) ↔
      IsSelfAdjoint p ∧ IsIdempotentElem p := by
  let : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  have := @orthogonal_projection_iff 𝕜 E _ _ _ _ _ (toContinuousLinearMap p)
  simp_rw [is_idempotent_elem_to_clm, is_self_adjoint_to_clm] at this ⊢
  rw [← this]
  constructor
  all_goals
    rintro ⟨U, hU⟩
    use U
  · rw [← hU]
    rfl
  · simp_all


-- @@ L341-343 expanded
theorem Matrix.conj_eq_transpose_conjTranspose {R n₁ n₂ : Type _} [Star R] (A : Matrix n₁ n₂ R) :
    Matrix.conj A = (Aᵀ)ᴴ :=
  rfl


-- @@ L345-347 expanded
theorem Matrix.conj_eq_conjTranspose_transpose {R n₁ n₂ : Type _} [Star R] (A : Matrix n₁ n₂ R) :
    Matrix.conj A = (Aᴴ)ᵀ :=
  rfl


-- @@ L349-353 verbatim
theorem Matrix.star_transpose_eq_star_transpose {R n : Type _} [Star R] (A : Matrix n n R) :
    (star A)ᵀ = star Aᵀ :=
  rfl

-- Star preservation for this tensor-product algebra equivalence requires deep instance search.

-- @@ L354-377 expanded
/-- Star algebra equivalence between a matrix tensor product and matrices on product indices. -/
noncomputable def oneMapTranspose :
    Matrix p p ℂ ⊗[ℂ] (Matrix p p ℂ)ᵐᵒᵖ ≃⋆ₐ[ℂ] Matrix (p × p) (p × p) ℂ :=
  StarAlgEquiv.ofAlgEquiv
    ((AlgEquiv.TensorProduct.map (1 : Matrix p p ℂ ≃ₐ[ℂ] Matrix p p ℂ)
          (transposeAlgEquiv p ℂ ℂ).symm).trans
      tensorToKronecker)
    (by
      let F : Matrix p p ℂ ⊗[ℂ] (Matrix p p ℂ)ᵐᵒᵖ ≃ₐ[ℂ] Matrix (p × p) (p × p) ℂ :=
        (AlgEquiv.TensorProduct.map (1 : Matrix p p ℂ ≃ₐ[ℂ] Matrix p p ℂ)
              (transposeAlgEquiv p ℂ ℂ).symm).trans
          tensorToKronecker
      change ∀ x, F (star x) = star (F x)
      intro x
      refine x.inductionOn ?tmul ?add
      · intro x₁ x₂
        simp only [TensorProduct.star_tmul]
        exact (TensorProduct.toKronecker_star (x₁ ⊗ₜ[ℂ] (MulOpposite.unop x₂)ᵀ)).symm
      · intro a b ha hb
        calc
          F (star (a + b)) = F (star a + star b) := by rw [star_add]
          _ = F (star a) + F (star b) := (F.map_add (star a) (star b))
          _ = star (F a) + star (F b) := by rw [ha, hb]
          _ = star (F a + F b) := by rw [star_add]
          _ = star (F (a + b)) := by rw [show F (a + b) = F a + F b from F.map_add a b])


-- @@ L379-383 expanded
theorem oneMapTranspose_eq (x : Matrix p p ℂ ⊗[ℂ] (Matrix p p ℂ)ᵐᵒᵖ) :
    (oneMapTranspose : Matrix p p ℂ ⊗[ℂ] (Matrix p p ℂ)ᵐᵒᵖ ≃⋆ₐ[ℂ] _) x =
      TensorProduct.toKronecker
        ((TensorProduct.map (1 : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ)
            (transposeAlgEquiv p ℂ ℂ).symm.toLinearMap)
          x) :=
  rfl


-- @@ L385-389 expanded
theorem oneMapTranspose_symm_eq (x : Matrix (p × p) (p × p) ℂ) :
    (oneMapTranspose : Matrix p p ℂ ⊗[ℂ] (Matrix p p ℂ)ᵐᵒᵖ ≃⋆ₐ[ℂ] _).symm x =
      (TensorProduct.map (1 : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ)
          (transposeAlgEquiv p ℂ ℂ).toLinearMap)
        (Matrix.kroneckerToTensorProduct x) :=
  rfl


-- @@ L391-395 expanded
theorem oneMapTranspose_apply (x y : Matrix p p ℂ) :
    (oneMapTranspose : _ ≃⋆ₐ[ℂ] Matrix (p × p) (p × p) ℂ) (x ⊗ₜ MulOpposite.op y) = x ⊗ₖ yᵀ :=
  by
  rw [oneMapTranspose_eq, TensorProduct.map_tmul, AlgEquiv.toLinearMap_apply,
    TensorProduct.toKronecker_apply, transposeAlgEquiv_symm_op_apply]
  rfl


-- @@ L397-405 expanded
theorem toMatrix''_map_star [hφ : φ.IsFaithfulPosMap] (x : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ) :
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    (hφ.toMatrix (LinearMap.adjoint (x : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ)) =
      star (hφ.toMatrix x)) :=
  by
  let := Matrix.isStarAlgebra (φ := φ);
    let := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ);
    let := Module.Dual.NormedAddCommGroup φ;
    let := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace;
    let := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup;
    let := Module.Dual.InnerProductSpace (φ := φ)
  ext
  simp only [Module.Dual.IsFaithfulPosMap.toMatrix, LinearMap.toMatrixAlgEquiv_apply, star_apply,
    LinearMap.adjoint_inner_right, RCLike.star_def, inner_conj_symm,
    Module.Dual.IsFaithfulPosMap.basis_repr_apply]


-- @@ L407-409 expanded
private theorem ffsugh [hφ : φ.IsFaithfulPosMap] {x : Matrix (p × p) (p × p) ℂ}
    {y : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ} : hφ.toMatrix.symm x = y ↔ x = hφ.toMatrix y :=
  Equiv.symm_apply_eq _


-- @@ L411-415 expanded
theorem toMatrix''_symm_map_star [hφ : φ.IsFaithfulPosMap] (x : Matrix (p × p) (p × p) ℂ) :
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    (hφ.toMatrix.symm (star x) = LinearMap.adjoint (hφ.toMatrix.symm x)) :=
  by
  let := Matrix.isStarAlgebra (φ := φ);
    let := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ);
    let := Module.Dual.NormedAddCommGroup φ;
    let := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace;
    let := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup;
    let := Module.Dual.InnerProductSpace (φ := φ)
  rw [ffsugh, toMatrix''_map_star, AlgEquiv.apply_symm_apply]


-- @@ L417-430 expanded
/-- The orthogonal projection onto a submodule, using the finite-dimensional matrix context. -/
noncomputable def Qam.fdOrthogonalProjection [hφ : φ.IsFaithfulPosMap]
    (U : Submodule ℂ (Matrix p p ℂ)) : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ :=
  by
  let := Matrix.isStarAlgebra (φ := φ);
    let := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ);
    let := Module.Dual.NormedAddCommGroup φ;
    let := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace;
    let := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup;
    let := Module.Dual.InnerProductSpace (φ := φ)
  letI : AddCommGroup U := Submodule.addCommGroup U
  letI : NormedAddCommGroup U := Submodule.normedAddCommGroup U
  letI : NormedSpace ℂ U := Submodule.normedSpace U
  letI : FiniteDimensional ℂ U :=
    Submodule.finiteDimensional_of_le (show U ≤ (⊤ : Submodule ℂ (Matrix p p ℂ)) from le_top)
  letI : ProperSpace U := FiniteDimensional.proper ℂ U
  let completeU : @CompleteSpace U PseudoMetricSpace.toUniformSpace := complete_of_proper
  letI : U.HasOrthogonalProjection :=
    @Submodule.HasOrthogonalProjection.ofCompleteSpace ℂ (Matrix p p ℂ) _ _ _ U completeU
  exact (orthogonalProjection' U : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ)


-- @@ L432-439 expanded
theorem Qam.fd_orthogonal_projection_iff_lm [hφ : φ.IsFaithfulPosMap]
    {q : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ} :
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    ((∃ U : Submodule ℂ (Matrix p p ℂ), Qam.fdOrthogonalProjection (φ := φ) U = q) ↔
      IsSelfAdjoint q ∧ IsIdempotentElem q) :=
  by
  let := Matrix.isStarAlgebra (φ := φ);
    let := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ);
    let := Module.Dual.NormedAddCommGroup φ;
    let := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace;
    let := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup;
    let := Module.Dual.InnerProductSpace (φ := φ)
  change
    (∃ U : Submodule ℂ (Matrix p p ℂ),
        (orthogonalProjection' U : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ) = q) ↔
      IsSelfAdjoint q ∧ IsIdempotentElem q
  exact orthogonal_projection_iff_lm


-- @@ L441-462 expanded
theorem Qam.fdOrthogonalProjection_eq_sum_rankOne [hφ : φ.IsFaithfulPosMap] {ι : Type _} [Fintype ι]
    {U : Submodule ℂ (Matrix p p ℂ)} :
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    (∀ b : OrthonormalBasis ι ℂ U,
      Qam.fdOrthogonalProjection (φ := φ) U =
        ∑ i : ι,
          ((rankOne ℂ (b i).1 (b i).1 : Matrix p p ℂ →L[ℂ] Matrix p p ℂ) :
            Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ)) :=
  by
  let := Matrix.isStarAlgebra (φ := φ);
    let := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ);
    let := Module.Dual.NormedAddCommGroup φ;
    let := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace;
    let := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup;
    let := Module.Dual.InnerProductSpace (φ := φ)
  intro b
  let : AddCommGroup U := Submodule.addCommGroup U
  let : NormedAddCommGroup U := Submodule.normedAddCommGroup U
  let : NormedSpace ℂ U := Submodule.normedSpace U
  let : FiniteDimensional ℂ U :=
    Submodule.finiteDimensional_of_le (show U ≤ (⊤ : Submodule ℂ (Matrix p p ℂ)) from le_top)
  let : ProperSpace U := FiniteDimensional.proper ℂ U
  let completeU : @CompleteSpace U PseudoMetricSpace.toUniformSpace := complete_of_proper
  let : U.HasOrthogonalProjection :=
    @Submodule.HasOrthogonalProjection.ofCompleteSpace ℂ (Matrix p p ℂ) _ _ _ U completeU
  unfold Qam.fdOrthogonalProjection
  change
    ((orthogonalProjection' U : Matrix p p ℂ →L[ℂ] Matrix p p ℂ) :
        Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ) =
      ∑ i : ι,
        ((rankOne ℂ (b i).1 (b i).1 : Matrix p p ℂ →L[ℂ] Matrix p p ℂ) :
          Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ)
  rw [← ContinuousLinearMap.toLinearMap_sum,
    @OrthonormalBasis.orthogonalProjection'_eq_sum_rankOne ι ℂ _ (Matrix p p ℂ) _ _ _ U completeU b]


-- @@ L464-479 expanded
theorem Qam.idempotent_and_real_iff_exists_ortho_proj [hφ : φ.IsFaithfulPosMap]
    (A : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ) :
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    (Qam.reflIdempotent hφ A A = A ∧ LinearMap.IsReal A ↔
      ∃ U : Submodule ℂ (Matrix p p ℂ),
        Qam.fdOrthogonalProjection (φ := φ) U =
          hφ.toMatrix.symm
            (TensorProduct.toKronecker
              ((TensorProduct.map (1 : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ)
                  (transposeAlgEquiv p ℂ ℂ).symm.toLinearMap)
                ((hφ.psi (ψ := φ) 0 (1 / 2)) A)))) :=
  by
  let := Matrix.isStarAlgebra (φ := φ);
    let := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ);
    let := Module.Dual.NormedAddCommGroup φ;
    let := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace;
    let := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup;
    let := Module.Dual.InnerProductSpace (φ := φ)
  rw [Qam.isReal_and_idempotent_iff_psi_orthogonal_projection, Qam.fd_orthogonal_projection_iff_lm,
    ← oneMapTranspose_eq, IsIdempotentElem.algEquiv, IsIdempotentElem.starAlgEquiv, and_comm]
  simp_rw [_root_.IsSelfAdjoint, LinearMap.star_eq_adjoint, ← toMatrix''_symm_map_star, ← map_star,
    Function.Injective.eq_iff (AlgEquiv.injective _),
    Function.Injective.eq_iff (StarAlgEquiv.injective _)]


-- @@ L481-486 expanded
/-- The submodule associated to an idempotent real quantum adjacency map. -/
noncomputable def Qam.submoduleOfIdempotentAndReal [hφ : φ.IsFaithfulPosMap]
    {A : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ} (hA1 : Qam.reflIdempotent hφ A A = A)
    (hA2 : LinearMap.IsReal A) : Submodule ℂ (Matrix p p ℂ) :=
  by
  let := Matrix.isStarAlgebra (φ := φ);
    let := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ);
    let := Module.Dual.NormedAddCommGroup φ;
    let := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace;
    let := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup;
    let := Module.Dual.InnerProductSpace (φ := φ)
  choose U _ using (Qam.idempotent_and_real_iff_exists_ortho_proj A).mp ⟨hA1, hA2⟩
  exact U


-- @@ L488-497 expanded
theorem Qam.orthogonalProjection'_eq [hφ : φ.IsFaithfulPosMap] {A : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ}
    (hA1 : Qam.reflIdempotent hφ A A = A) (hA2 : LinearMap.IsReal A) :
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    (Qam.fdOrthogonalProjection (φ := φ) (Qam.submoduleOfIdempotentAndReal hA1 hA2) =
      hφ.toMatrix.symm
        (TensorProduct.toKronecker
          ((TensorProduct.map (1 : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ)
              (transposeAlgEquiv p ℂ ℂ).symm.toLinearMap)
            ((hφ.psi (ψ := φ) 0 (1 / 2)) A)))) :=
  by
  let := Matrix.isStarAlgebra (φ := φ);
    let := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ);
    let := Module.Dual.NormedAddCommGroup φ;
    let := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace;
    let := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup;
    let := Module.Dual.InnerProductSpace (φ := φ)
  exact (Qam.idempotent_and_real_iff_exists_ortho_proj A).mp ⟨hA1, hA2⟩ |>.choose_spec


-- @@ L499-508 expanded
/-- A canonical orthonormal basis for the submodule associated to an idempotent real QAM. -/
noncomputable def Qam.onbOfIdempotentAndReal [hφ : φ.IsFaithfulPosMap]
    {A : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ} (hA1 : Qam.reflIdempotent hφ A A = A)
    (hA2 : LinearMap.IsReal A) :
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    (OrthonormalBasis (Fin (FiniteDimensional.finrank ℂ (Qam.submoduleOfIdempotentAndReal hA1 hA2)))
      ℂ (Qam.submoduleOfIdempotentAndReal hA1 hA2)) :=
  by
  let := Matrix.isStarAlgebra (φ := φ);
    let := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ);
    let := Module.Dual.NormedAddCommGroup φ;
    let := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace;
    let := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup;
    let := Module.Dual.InnerProductSpace (φ := φ)
  exact
    stdOrthonormalBasis ℂ
      _
        -- The orthonormal-basis finrank index requires synthesizing the restored submodule structure.


-- @@ L509-533 expanded
theorem Qam.IdempotentAndReal.eq [hφ : φ.IsFaithfulPosMap] {A : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ}
    (hA1 : Qam.reflIdempotent hφ A A = A) (hA2 : LinearMap.IsReal A) :
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    (A =
      ∑ i,
        LinearMap.mulLeft ℂ (((Qam.onbOfIdempotentAndReal hA1 hA2 i).1 * φ.matrix)) *
          (LinearMap.adjoint
            (LinearMap.mulRight ℂ (φ.matrix * (Qam.onbOfIdempotentAndReal hA1 hA2 i).1)))) :=
  by
  let := Matrix.isStarAlgebra (φ := φ);
    let := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ);
    let := Module.Dual.NormedAddCommGroup φ;
    let := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace;
    let := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup;
    let := Module.Dual.InnerProductSpace (φ := φ)
  let U := Qam.submoduleOfIdempotentAndReal hA1 hA2
  let : AddCommGroup U := Submodule.addCommGroup U
  let : NormedAddCommGroup U := Submodule.normedAddCommGroup U
  let : NormedSpace ℂ U := Submodule.normedSpace U
  let : FiniteDimensional ℂ U :=
    Submodule.finiteDimensional_of_le (show U ≤ (⊤ : Submodule ℂ (Matrix p p ℂ)) from le_top)
  simp_rw [← rankOne_toMatrix_transpose_psi_symm, ← map_sum, ←
    Qam.fdOrthogonalProjection_eq_sum_rankOne (Qam.onbOfIdempotentAndReal hA1 hA2),
    Qam.orthogonalProjection'_eq, AlgEquiv.apply_symm_apply]
  simp_rw [← oneMapTranspose_symm_eq, ← oneMapTranspose_eq, StarAlgEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply]


-- @@ L535-541 expanded
/-- Quantum adjacency maps that are both Schur-idempotent and real. -/
@[class]
structure RealQam (hφ : φ.IsFaithfulPosMap) (A : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ) : Prop where
  /-- The Schur idempotence condition. -/
  toIdempotent : Qam.reflIdempotent hφ A A = A
  /-- The realness condition. -/
  toIsReal : LinearMap.IsReal A


-- @@ L543-545 expanded
lemma RealQam_iff [hφ : φ.IsFaithfulPosMap] {A : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ} :
    RealQam hφ A ↔ Qam.reflIdempotent hφ A A = A ∧ LinearMap.IsReal A :=
  ⟨fun h => ⟨h.toIdempotent, h.toIsReal⟩, fun h => ⟨h.1, h.2⟩⟩


-- @@ L547-553 expanded
theorem RealQam.add_iff [hφ : φ.IsFaithfulPosMap] {A B : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ}
    (hA : RealQam hφ A) (hB : RealQam hφ B) :
    RealQam hφ (A + B) ↔ Qam.reflIdempotent hφ A B + Qam.reflIdempotent hφ B A = 0 :=
  by
  simp only [RealQam_iff] at hA hB ⊢
  simp [map_add, LinearMap.add_apply, hA, hB, add_assoc, add_left_comm, add_comm,
    LinearMap.isReal_iff, LinearMap.real_add, (LinearMap.isReal_iff _).mp hA.2,
    (LinearMap.isReal_iff _).mp hB.2]


-- @@ L555-559 expanded
/-- The zero map as a real QAM. -/
theorem RealQam.zero [hφ : φ.IsFaithfulPosMap] : RealQam hφ (0 : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ) :=
  by
  simp_rw [RealQam_iff, LinearMap.map_zero, true_and]
  intro
  simp only [LinearMap.zero_apply, star_zero]


-- @@ L561-563 verbatim
@[reducible, instance]
noncomputable def RealQam.hasZero [hφ : φ.IsFaithfulPosMap] :
    Zero { x // RealQam hφ x } where zero := ⟨0, RealQam.zero⟩


-- @@ L565-567 expanded
theorem Qam.reflIdempotent_zero [hφ : φ.IsFaithfulPosMap] (a : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ) :
    Qam.reflIdempotent hφ a 0 = 0 :=
  map_zero _


-- @@ L569-571 expanded
theorem Qam.zero_reflIdempotent [hφ : φ.IsFaithfulPosMap] (a : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ) :
    Qam.reflIdempotent hφ 0 a = 0 := by simp_rw [LinearMap.map_zero, LinearMap.zero_apply]


-- @@ L573-576 expanded
/-- Number of edges of a real QAM, computed as the rank of its associated submodule. -/
@[reducible]
noncomputable def RealQam.edges [hφ : φ.IsFaithfulPosMap] {x : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ}
    (hx : RealQam hφ x) : ℕ :=
  FiniteDimensional.finrank ℂ (Qam.submoduleOfIdempotentAndReal hx.1 hx.2)


-- @@ L578-584 expanded
/-- Edge-count function on the subtype of real QAMs. -/
@[reducible]
noncomputable def RealQam.edges' [hφ : φ.IsFaithfulPosMap] :
    { x : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ // RealQam hφ x } → ℕ := fun x =>
  FiniteDimensional.finrank ℂ
    (Qam.submoduleOfIdempotentAndReal (Set.mem_ofPred.mp (Subtype.mem x)).1
      (Set.mem_ofPred.mp (Subtype.mem x)).2)


-- @@ L586-629 expanded
theorem RealQam.edges_eq [hφ : φ.IsFaithfulPosMap] {A : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ}
    (hA : RealQam hφ A) :
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    ((hA.edges : ℂ) = (A φ.matrix⁻¹).trace) :=
  by
  let := Matrix.isStarAlgebra (φ := φ);
    let := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ);
    let := Module.Dual.NormedAddCommGroup φ;
    let := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace;
    let := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup;
    let := Module.Dual.InnerProductSpace (φ := φ)
  obtain ⟨hA1, hA2⟩ := hA
  symm
  nth_rw 1 [Qam.IdempotentAndReal.eq hA1 hA2]
  let U := Qam.submoduleOfIdempotentAndReal hA1 hA2
  simp_rw [LinearMap.sum_apply, LinearMap.matrix.mulRight_adjoint, Module.End.mul_apply,
    LinearMap.mulRight_apply, LinearMap.mulLeft_apply, conjTranspose_mul, hφ.matrixIsPosDef.1.eq, ←
    Matrix.mul_assoc, sig_apply_matrix_hMul_posDef']
  have :
    ∀ x : Fin (FiniteDimensional.finrank ℂ ↥U),
      ((Qam.onbOfIdempotentAndReal hA1 hA2 x).1 * φ.matrix * φ.matrix⁻¹ * φ.matrix *
            (Qam.onbOfIdempotentAndReal hA1 hA2 x).1ᴴ).trace =
        1 :=
    by
    intro x
    calc
      ((Qam.onbOfIdempotentAndReal hA1 hA2 x).1 * φ.matrix * φ.matrix⁻¹ * φ.matrix *
              (Qam.onbOfIdempotentAndReal hA1 hA2 x).1ᴴ).trace =
          ((Qam.onbOfIdempotentAndReal hA1 hA2 x).1 * hφ.matrixIsPosDef.rpow 1 *
                  hφ.matrixIsPosDef.rpow (-1) *
                φ.matrix *
              (Qam.onbOfIdempotentAndReal hA1 hA2 x).1ᴴ).trace :=
        by simp_rw [PosDef.rpow_one_eq_self, PosDef.rpow_neg_one_eq_inv_self]
      _ =
          ((Qam.onbOfIdempotentAndReal hA1 hA2 x).1 *
                  (hφ.matrixIsPosDef.rpow 1 * hφ.matrixIsPosDef.rpow (-1)) *
                φ.matrix *
              (Qam.onbOfIdempotentAndReal hA1 hA2 x).1ᴴ).trace :=
        by simp_rw [Matrix.mul_assoc]
      _ =
          ((Qam.onbOfIdempotentAndReal hA1 hA2 x).1 * φ.matrix *
              (Qam.onbOfIdempotentAndReal hA1 hA2 x).1ᴴ).trace :=
        by simp_rw [PosDef.rpow_mul_rpow, add_neg_cancel, PosDef.rpow_zero, Matrix.mul_one]
      _ =
          inner ℂ (Qam.onbOfIdempotentAndReal hA1 hA2 x).1
            (Qam.onbOfIdempotentAndReal hA1 hA2 x).1 :=
        by rw [Module.Dual.IsFaithfulPosMap.inner_eq' hφ, ← trace_mul_cycle]
      _ = inner ℂ (Qam.onbOfIdempotentAndReal hA1 hA2 x) (Qam.onbOfIdempotentAndReal hA1 hA2 x) :=
        rfl
      _ = 1 := by simp_all
  simp_rw [trace_sum, ← Matrix.mul_assoc, this, Finset.sum_const, Finset.card_fin,
    Nat.smul_one_eq_cast]


-- @@ L631-635 expanded
theorem completeGraphRealQam [hφ : φ.IsFaithfulPosMap] :
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    letI : Coalgebra ℂ (Matrix p p ℂ) := Coalgebra.ofFiniteDimensionalHilbertAlgebra
    (RealQam hφ (Qam.completeGraph (Matrix p p ℂ) (Matrix p p ℂ))) :=
  by
  let := Matrix.isStarAlgebra (φ := φ);
      let := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ);
      let := Module.Dual.NormedAddCommGroup φ;
      let :=
        (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace;
      let := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup;
      let := Module.Dual.InnerProductSpace (φ := φ);
    let : Coalgebra ℂ (Matrix p p ℂ) := Coalgebra.ofFiniteDimensionalHilbertAlgebra
  exact ⟨Qam.Nontracial.CompleteGraph.qam, Qam.Nontracial.CompleteGraph.isReal⟩


-- @@ L637-653 expanded
theorem Qam.completeGraph_edges [hφ : φ.IsFaithfulPosMap] :
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    letI : Coalgebra ℂ (Matrix p p ℂ) := Coalgebra.ofFiniteDimensionalHilbertAlgebra
    ((@completeGraphRealQam p _ _ φ hφ).edges =
      FiniteDimensional.finrank ℂ (⊤ : Submodule ℂ (Matrix p p ℂ))) :=
  by
  let := Matrix.isStarAlgebra (φ := φ);
      let := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ);
      let := Module.Dual.NormedAddCommGroup φ;
      let :=
        (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace;
      let := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup;
      let := Module.Dual.InnerProductSpace (φ := φ);
    let : Coalgebra ℂ (Matrix p p ℂ) := Coalgebra.ofFiniteDimensionalHilbertAlgebra
  have this :
    (RealQam.edges completeGraphRealQam : ℂ) =
      (Qam.completeGraph (Matrix p p ℂ) (Matrix p p ℂ) φ.matrix⁻¹).trace :=
    RealQam.edges_eq _
  have ig := hφ.matrixIsPosDef.invertible
  simp_rw [Qam.completeGraph, ContinuousLinearMap.coe_coe, rankOne_apply,
    Module.Dual.IsFaithfulPosMap.inner_eq', conjTranspose_one, Matrix.mul_one,
    mul_inv_of_invertible, trace_smul, smul_eq_mul, trace_one, ← Nat.cast_mul, Nat.cast_inj] at this
  simp_rw [Qam.completeGraph, finrank_top, Module.finrank_matrix, Module.finrank_self, mul_one]
  exact this


-- @@ L654-660 expanded
theorem Qam.trivialGraphRealQam [hφ : φ.IsFaithfulPosMap] [Nonempty p] :
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    letI : Coalgebra ℂ (Matrix p p ℂ) := Coalgebra.ofFiniteDimensionalHilbertAlgebra
    (letI : QuantumSetDeltaForm (Matrix p p ℂ) := Matrix.quantumSetDeltaForm (φ := φ)
    RealQam hφ (Qam.trivialGraph (Matrix p p ℂ))) :=
  by
  let := Matrix.isStarAlgebra (φ := φ);
      let := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ);
      let := Module.Dual.NormedAddCommGroup φ;
      let :=
        (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace;
      let := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup;
      let := Module.Dual.InnerProductSpace (φ := φ);
    let : Coalgebra ℂ (Matrix p p ℂ) := Coalgebra.ofFiniteDimensionalHilbertAlgebra
  let : QuantumSetDeltaForm (Matrix p p ℂ) := Matrix.quantumSetDeltaForm (φ := φ)
  exact ⟨Qam.Nontracial.TrivialGraph.qam, Qam.Nontracial.trivialGraph.isReal⟩


-- @@ L662-673 expanded
theorem Qam.trivialGraph_edges [hφ : φ.IsFaithfulPosMap] [Nonempty p] :
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    letI : Coalgebra ℂ (Matrix p p ℂ) := Coalgebra.ofFiniteDimensionalHilbertAlgebra
    (letI : QuantumSetDeltaForm (Matrix p p ℂ) := Matrix.quantumSetDeltaForm (φ := φ)
    (@Qam.trivialGraphRealQam p _ _ φ hφ _).edges = 1) :=
  by
  let := Matrix.isStarAlgebra (φ := φ);
      let := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ);
      let := Module.Dual.NormedAddCommGroup φ;
      let :=
        (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace;
      let := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup;
      let := Module.Dual.InnerProductSpace (φ := φ);
    let : Coalgebra ℂ (Matrix p p ℂ) := Coalgebra.ofFiniteDimensionalHilbertAlgebra
  let : QuantumSetDeltaForm (Matrix p p ℂ) := Matrix.quantumSetDeltaForm (φ := φ)
  have := RealQam.edges_eq (@Qam.trivialGraphRealQam p _ _ φ hφ _)
  nth_rw 2 [Qam.trivialGraph_eq] at this
  simp_rw [LinearMap.smul_apply, Module.End.one_apply, trace_smul, smul_eq_mul] at this
  rw [show QuantumSetDeltaForm.delta (Matrix p p ℂ) = φ.matrix⁻¹.trace by rfl] at this
  have hδ : φ.matrix⁻¹.trace ≠ 0 := ne_of_gt (Qam.Nontracial.delta_pos (φ := φ))
  simp_all


-- @@ L675-690 expanded
theorem RealQam.edges_eq_zero_iff [hφ : φ.IsFaithfulPosMap] {A : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ}
    (hA : RealQam hφ A) : hA.edges = 0 ↔ A = 0 :=
  by
  constructor
  · intro h
    rw [RealQam.edges] at h
    have h' := h
    simp only [Submodule.finrank_eq_zero] at h
    rw [Qam.IdempotentAndReal.eq hA.1 hA.2]
    let u := Qam.onbOfIdempotentAndReal hA.1 hA.2
    apply Finset.sum_eq_zero
    intro i _
    rw [finrank_zero_iff_forall_zero.mp h' (u i)]
    simp_all
  · intro h
    rw [← Nat.cast_inj (R := ℂ), RealQam.edges_eq, h, LinearMap.zero_apply, trace_zero]
    norm_cast


-- @@ L692-698 expanded
theorem psi_apply_complete_graph [hφ : φ.IsFaithfulPosMap] {t s : ℝ} :
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    (hφ.psi (ψ := φ) t s (@rankOne ℂ _ _ _ _ _ _ _ (1 : Matrix p p ℂ) (1 : Matrix p p ℂ)) = 1) :=
  by
  let := Matrix.isStarAlgebra (φ := φ);
    let := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ);
    let := Module.Dual.NormedAddCommGroup φ;
    let := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace;
    let := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup;
    let := Module.Dual.InnerProductSpace (φ := φ)
  simp only [Module.Dual.IsFaithfulPosMap.psi, QuantumSet.Psi_apply, QuantumSet.PsiToFun_apply,
    _root_.map_one]
  simp [star_one, MulOpposite.op_one, Algebra.TensorProduct.one_def]


-- @@ L700-706 verbatim
lemma AlgEquiv.TensorProduct.map_toLinearMap' {R S T U V : Type _} [CommSemiring R]
  [Semiring S] [Semiring T] [Semiring U] [Semiring V]
  [Algebra R S] [Algebra R T] [Algebra R U] [Algebra R V]
  (f : S ≃ₐ[R] T) (g : U ≃ₐ[R] V) :
  (AlgEquiv.TensorProduct.map f g).toLinearMap =
    _root_.TensorProduct.map f.toLinearMap g.toLinearMap :=
rfl


-- @@ L708-710 verbatim
lemma AlgEquiv.toLinearMap_one {R S : Type _} [CommSemiring R] [Semiring S] [Algebra R S] :
  (AlgEquiv.toLinearMap (1 : S ≃ₐ[R] S)) = 1 :=
rfl


-- @@ L712-754 expanded
theorem RealQam.edges_eq_dim_iff [hφ : φ.IsFaithfulPosMap] {A : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ}
    (hA : RealQam hφ A) :
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    (hA.edges = FiniteDimensional.finrank ℂ (⊤ : Submodule ℂ (Matrix p p ℂ)) ↔
      A = @rankOne ℂ _ _ _ _ _ _ _ (1 : Matrix p p ℂ) (1 : Matrix p p ℂ)) :=
  by
  let := Matrix.isStarAlgebra (φ := φ);
    let := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ);
    let := Module.Dual.NormedAddCommGroup φ;
    let := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace;
    let := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup;
    let := Module.Dual.InnerProductSpace (φ := φ)
  constructor
  · intro h
    rw [RealQam.edges] at h
    simp only [finrank_top] at h
    let U := Qam.submoduleOfIdempotentAndReal hA.1 hA.2
    have hU : U = (⊤ : Submodule ℂ (Matrix p p ℂ)) := Submodule.eq_top_of_finrank_eq h
    rw [← Function.Injective.eq_iff (LinearEquiv.injective (hφ.psi (ψ := φ) 0 (1 / 2))),
      psi_apply_complete_graph]
    have t1 := Qam.orthogonalProjection'_eq hA.1 hA.2
    have : Qam.fdOrthogonalProjection (φ := φ) U = 1 :=
      by
      rw [hU]
      unfold Qam.fdOrthogonalProjection
      change
        ((orthogonalProjection' (⊤ : Submodule ℂ (Matrix p p ℂ)) :
              Matrix p p ℂ →L[ℂ] Matrix p p ℂ) :
            Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ) =
          1
      rw [orthogonalProjection_of_top]
      rfl
    change
      Qam.fdOrthogonalProjection (φ := φ) U =
        hφ.toMatrix.symm
          (TensorProduct.toKronecker
            ((TensorProduct.map (1 : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ)
                (transposeAlgEquiv p ℂ ℂ).symm.toLinearMap)
              ((hφ.psi (ψ := φ) 0 (1 / 2)) A))) at t1
    rw [this] at t1
    have this' := (AlgEquiv.eq_apply_iff_symm_eq _).mpr t1.symm
    rw [_root_.map_one] at this'
    change
      (tensorToKronecker : Matrix p p ℂ ⊗[ℂ] Matrix p p ℂ ≃ₐ[ℂ] Matrix (p × p) (p × p) ℂ)
          ((TensorProduct.map 1 (transposeAlgEquiv p ℂ ℂ).symm.toLinearMap)
            ((hφ.psi 0 (1 / 2)) A)) =
        1 at this'
    rw [MulEquivClass.map_eq_one_iff] at this'
    have this'' :=
      AlgEquiv.TensorProduct.map_toLinearMap (1 : Matrix p p ℂ ≃ₐ[ℂ] Matrix p p ℂ)
        (transposeAlgEquiv p ℂ ℂ).symm
    rw [AlgEquiv.toLinearMap_one] at this''
    rw [← this'', AlgEquiv.toLinearMap_apply, MulEquivClass.map_eq_one_iff] at this'
    exact this'
  · intro h
    rw [← @Qam.completeGraph_edges p _ _ φ]
    simp_rw [← @Nat.cast_inj ℂ, RealQam.edges_eq, h]
    rfl
      -- The dimension-one projection extraction uses finite-dimensional basis instance synthesis.


-- @@ L755-772 verbatim
private theorem orthogonal_projection_of_dim_one {𝕜 E : Type _} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {U : Submodule 𝕜 E}
    (hU : FiniteDimensional.finrank 𝕜 U = 1) :
    ∃ v : { x : E // (x : E) ≠ 0 },
      orthogonalProjection' U = (1 / (‖(v : E)‖ ^ 2 : 𝕜)) • rankOne 𝕜 (v : E) (v : E) := by
  let u : OrthonormalBasis (Fin 1) 𝕜 U := by
    rw [← hU]
    exact stdOrthonormalBasis 𝕜 U
  rw [OrthonormalBasis.orthogonalProjection'_eq_sum_rankOne u, Fin.sum_univ_one]
  have hcc : (u 0 : E) ≠ 0 := by
    intro h
    exact (u.orthonormal.ne_zero 0) (Subtype.ext h)
  have : ‖(u 0 : E)‖ = 1 := by
    rw [@norm_eq_sqrt_re_inner 𝕜, Real.sqrt_eq_one]
    simp_rw [← Submodule.coe_inner, orthonormal_iff_ite.mp u.orthonormal, ite_true,
      RCLike.one_re]
  use ⟨u 0, hcc⟩
  simp only [this, RCLike.ofReal_one, one_div_one, one_smul, one_pow]


-- @@ L774-776 verbatim
lemma Complex.ofReal'_eq_isROrC_ofReal (a : ℝ) :
  (a : ℂ) = RCLike.ofReal a :=
rfl


-- @@ L778-826 expanded
theorem RealQam.edges_eq_one_iff [hφ : φ.IsFaithfulPosMap] {A : Matrix p p ℂ →ₗ[ℂ] Matrix p p ℂ}
    (hA : RealQam hφ A) :
    letI := Matrix.isStarAlgebra (φ := φ)
    letI := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ)
    letI := Module.Dual.NormedAddCommGroup φ
    letI := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup
    letI := Module.Dual.InnerProductSpace (φ := φ)
    (hA.edges = 1 ↔
      ∃ x : { x : Matrix p p ℂ // x ≠ 0 },
        A =
          (1 / (‖x.1‖ ^ 2 : ℂ)) •
            (LinearMap.mulLeft ℂ (x.1 * φ.matrix) *
              LinearMap.adjoint (LinearMap.mulRight ℂ (φ.matrix * x.1)))) :=
  by
  let := Matrix.isStarAlgebra (φ := φ);
    let := Module.Dual.IsFaithfulPosMap.quantumSet (φ := φ);
    let := Module.Dual.NormedAddCommGroup φ;
    let := (Module.Dual.NormedAddCommGroup φ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace;
    let := (Module.Dual.NormedAddCommGroup φ).toSeminormedAddCommGroup;
    let := Module.Dual.InnerProductSpace (φ := φ)
  constructor
  · intro h
    let h' := h
    rw [← @Nat.cast_inj ℂ, RealQam.edges_eq hA] at h'
    rw [RealQam.edges] at h
    let this : (hA.toIdempotent : ((Qam.reflIdempotent hφ) A) A = A) = hA.toIdempotent := rfl
    rw [this] at h
    obtain ⟨u, hu⟩ := orthogonal_projection_of_dim_one h
    let hu' : (u : Matrix p p ℂ) ≠ 0 := u.property
    use ⟨u, hu'⟩
    let t1 := Qam.orthogonalProjection'_eq hA.toIdempotent hA.toIsReal
    simp_rw [← rankOne_toMatrix_transpose_psi_symm, ← LinearEquiv.map_smul, ← LinearMap.map_smul, ←
      _root_.map_smul, ← ContinuousLinearMap.toLinearMap_smul, Complex.ofReal'_eq_isROrC_ofReal, ←
      hu]
    simp_rw [LinearEquiv.eq_symm_apply, ← oneMapTranspose_symm_eq,
      StarAlgEquiv.eq_apply_iff_symm_eq, StarAlgEquiv.symm_symm, AlgEquiv.eq_apply_iff_symm_eq,
      oneMapTranspose_eq]
    rw [← t1]
    unfold Qam.fdOrthogonalProjection
    rfl
  · rintro ⟨x, rfl⟩
    let := hφ.matrixIsPosDef.invertible
    have ugh :
      ((x : Matrix p p ℂ) * φ.matrix * (x : Matrix p p ℂ)ᴴ).trace = ‖(x : Matrix p p ℂ)‖ ^ 2 :=
      by
      rw [← trace_mul_cycle, ← Module.Dual.IsFaithfulPosMap.inner_eq' hφ,
        inner_self_eq_norm_sq_to_K]
      rfl
    have := RealQam.edges_eq hA
    rw [← @Nat.cast_inj ℂ, this]
    simp only [LinearMap.smul_apply, trace_smul, Module.End.mul_apply,
      LinearMap.matrix.mulRight_adjoint, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
      conjTranspose_mul, hφ.matrixIsPosDef.1.eq, sig_apply_matrix_hMul_posDef',
      inv_mul_cancel_left_of_invertible, ugh, smul_eq_mul, one_div] at this ⊢
    have this' : ((‖(x : Matrix p p ℂ)‖ : ℝ) ^ 2 : ℂ) ≠ (0 : ℂ) :=
      by
      simp_rw [ne_eq, sq_eq_zero_iff, Complex.ofReal_eq_zero, norm_eq_zero]
      exact x.property
    rw [inv_mul_cancel₀ this', Nat.cast_one]
      -- },

