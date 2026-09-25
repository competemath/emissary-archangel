import QuantumOptimization.Quantum.Operators.Types
import QuantumOptimization.Quantum.Operators.BraKet
import QuantumOptimization.Quantum.TensorProducts.Basic


-- @@ L5-5 verbatim
namespace Quantum.TensorProducts


-- @@ L7-7 verbatim
open Quantum.Operators

-- @@ L8-8 verbatim
open scoped Matrix BigOperators ComplexConjugate TensorProduct Kronecker

-- @@ L9-9 verbatim
open Matrix


-- @@ L11-11 verbatim
noncomputable section


-- @@ L13-28 verbatim
/-!
# Type-Safe Quantum Mechanics - Tensor Product Calculus

This module contains the calculus properties of tensor products:
- Factorization of inner products over tensor products
- Distributivity over addition
- Compatibility with scalar multiplication
- Inner product linearity
- Norm-squared properties

These properties are essential for proving theorems about composite quantum systems.
-/

-- ============================================================================
-- Tensor Product Calculus
-- ============================================================================


-- @@ L30-68 expanded
/-- Tensor product of operators acts componentwise on tensor product of kets:
    (A ⊗ B)|ψ ⊗ φ⟩ = (A|ψ⟩) ⊗ (B|φ⟩)

    This is a fundamental infrastructure lemma that enables physics-like proofs.
    The proof uses index manipulation because it establishes the basic property
    that tensor products act componentwise - subsequent proofs can use this
    lemma directly without indices. -/
@[simp]
theorem Op.tensor_mulKet {n m : ℕ} (A : Op n) (B : Op m) (ψ : Ket n) (φ : Ket m) :
    (Ket.tensor A B) * (Ket.tensor ψ φ) = Ket.tensor (A * ψ) (B * φ) :=
  by
  ext k
  simp only [Ket.tensor, Op.tensor, Matrix.reindex_apply]
    -- Step 1: Convert sum over Fin(n*m) to sum over Fin n × Fin m
    
  trans
    (∑ p : Fin n × Fin m,
      A (finProdFinEquiv.symm k).1 p.1 * B (finProdFinEquiv.symm k).2 p.2 * (ψ.vec p.1 * φ.vec p.2))
  · apply Fintype.sum_equiv finProdFinEquiv.symm
    intro j;
    simp [finProdFinEquiv]
      -- Step 2: Rearrange: (A·B)·(ψ·φ) = (A·ψ)·(B·φ)
      
  trans
    (∑ p : Fin n × Fin m,
      (A (finProdFinEquiv.symm k).1 p.1 * ψ.vec p.1) *
        (B (finProdFinEquiv.symm k).2 p.2 * φ.vec p.2))
  · congr 1; ext p;
    ring
      -- Step 3: Split double sum: ∑_{i,j} f(i)·g(j) = (∑_i f(i))·(∑_j g(j))
      
  rw [Fintype.sum_prod_type]
    -- Simplify (x, y).1 to x and (x, y).2 to y
    
  conv_lhs =>
    arg 2; ext x; arg 2; ext y
    rw [show ((x, y) : Fin n × Fin m).1 = x from rfl, show ((x, y) : Fin n × Fin m).2 = y from rfl]
  rw [← Finset.sum_mul_sum]
    -- Step 4: Unfold (A * ψ).vec and (B * φ).vec to match
    
  simp only [HMul.hMul, Matrix.mulVec, dotProduct]
  rfl
    -- ============================================================================
    -- Helper Lemmas for Cleaner Proofs
    -- ============================================================================


-- @@ L70-75 expanded
/-- Helper: vec field extraction for tensor product -/
@[simp]
lemma Ket.tensor_vec {n m : ℕ} (ψ : Ket n) (φ : Ket m) (k : Fin (n * m)) :
    (Ket.tensor ψ φ).vec k = ψ.vec (finProdFinEquiv.symm k).1 * φ.vec (finProdFinEquiv.symm k).2 :=
  rfl


-- @@ L77-84 verbatim
/-- Helper: vec field for scalar multiplication applied to index -/
@[simp]
lemma Ket.smul_vec_apply {n : ℕ} (c : ℂ) (ψ : Ket n) (i : Fin n) :
    (c • ψ).vec i = c * ψ.vec i := rfl

-- ============================================================================
-- Inner Product Factorization
-- ============================================================================


-- @@ L86-114 expanded
/-- Inner product of tensor products factorizes:
    ⟨ψ₁⊗φ₁|ψ₂⊗φ₂⟩ = ⟨ψ₁|ψ₂⟩ · ⟨φ₁|φ₂⟩ -/
@[simp]
theorem Ket.inner_tensor {n m : ℕ} (ψ₁ ψ₂ : Ket n) (φ₁ φ₂ : Ket m) :
    Ket.dag (Ket.tensor (ToKet.toKet ψ₁) (ToKet.toKet φ₁)) *
        Ket.tensor (ToKet.toKet ψ₂) (ToKet.toKet φ₂) =
      (ToBra.toBra ψ₁ * ToKet.toKet ψ₂) • (ToBra.toBra φ₁ * ToKet.toKet φ₂) :=
  by
  -- Unfold definitions
  
  unfold Ket.dag Ket.tensor
  simp only
    -- Convert sum over Fin (n * m) to double sum over Fin n × Fin m
    
  trans (∑ p : Fin n × Fin m, conj (ψ₁.vec p.1 * φ₁.vec p.2) * (ψ₂.vec p.1 * φ₂.vec p.2))
  · apply Fintype.sum_equiv finProdFinEquiv.symm
    intro p
    simp [finProdFinEquiv]
      -- Use map_mul for conjugation: conj(a * b) = conj(a) * conj(b)
      
  trans (∑ p : Fin n × Fin m, (conj (ψ₁.vec p.1) * conj (φ₁.vec p.2)) * (ψ₂.vec p.1 * φ₂.vec p.2))
  · congr 1
    ext p
    rw [map_mul]
      -- Rearrange the product using ring commutativity
      
  trans (∑ p : Fin n × Fin m, (conj (ψ₁.vec p.1) * ψ₂.vec p.1) * (conj (φ₁.vec p.2) * φ₂.vec p.2))
  · congr 1
    ext p
    ring
      -- Separate the double sum into a product of sums
      
  rw [Fintype.sum_prod_type]
    -- Use sum_mul_sum in reverse: (∑ f) * (∑ g) = ∑∑ f * g
    
  simp_rw [← Finset.sum_mul_sum]
    -- Unfold the RHS to match the LHS
    
  simp only [HMul.hMul, HSMul.hSMul, SMul.smul, ToBra.toBra_ket, Ket.dag_vec, ToKet.toKet, id]


-- @@ L116-122 expanded
/-- Tensor product distributes over addition (left) -/
@[simp]
theorem Ket.tensor_add_left {n m : ℕ} (ψ φ : Ket n) (χ : Ket m) :
    Ket.tensor (ψ + φ) χ = Ket.tensor ψ χ + Ket.tensor φ χ := by ext k;
  simp only [tensor_vec, Ket.add_vec];
  ring
    -- Note: Ket.smul_vec is in BasicCalculusHMul.lean


-- @@ L124-128 expanded
/-- Tensor product distributes over addition (right) -/
@[simp]
theorem Ket.tensor_add_right {n m : ℕ} (ψ : Ket n) (φ χ : Ket m) :
    Ket.tensor ψ (φ + χ) = Ket.tensor ψ φ + Ket.tensor ψ χ := by ext k;
  simp only [tensor_vec, Ket.add_vec]; ring


-- @@ L130-134 expanded
/-- Tensor product is compatible with scalar multiplication (left) -/
@[simp]
theorem Ket.tensor_smul_left {n m : ℕ} (c : ℂ) (ψ : Ket n) (χ : Ket m) :
    Ket.tensor (c • ψ) χ = c • (Ket.tensor ψ χ) := by ext k; simp only [tensor_vec, smul_vec_apply];
  ring


-- @@ L136-140 expanded
/-- Tensor product is compatible with scalar multiplication (right) -/
@[simp]
theorem Ket.tensor_smul_right {n m : ℕ} (c : ℂ) (ψ : Ket n) (χ : Ket m) :
    Ket.tensor ψ (c • χ) = c • (Ket.tensor ψ χ) := by ext k; simp only [tensor_vec, smul_vec_apply];
  ring


-- @@ L142-146 expanded
/-- Tensor product with zero on the left -/
@[simp]
theorem Ket.tensor_zero_left {n m : ℕ} (φ : Ket m) : Ket.tensor (0 : Ket n) φ = 0 := by ext k;
  simp only [tensor_vec, Ket.zero_vec, zero_mul]


-- @@ L148-152 expanded
/-- Tensor product with zero on the right -/
@[simp]
theorem Ket.tensor_zero_right {n m : ℕ} (ψ : Ket n) : Ket.tensor ψ (0 : Ket m) = 0 := by ext k;
  simp only [tensor_vec, Ket.zero_vec, mul_zero]


-- @@ L154-158 expanded
/-- Inner product of tensor products factorizes (alternate name for backward compatibility) -/
@[simp]
theorem braket_tensor {n m : ℕ} (ψ₁ φ₁ : Ket n) (ψ₂ φ₂ : Ket m) :
    Ket.inner (Ket.tensor ψ₁ ψ₂) (Ket.tensor φ₁ φ₂) = Ket.inner ψ₁ φ₁ * Ket.inner ψ₂ φ₂ := by
  exact Ket.inner_tensor ψ₁ φ₁ ψ₂ φ₂


-- @@ L160-177 expanded
/-- (⟨α| ⊗ ⟨β|)(|ψ⟩ ⊗ |φ⟩) = ⟨α|ψ⟩ · ⟨β|φ⟩ (bra-ket tensor factorization) -/
@[simp]
theorem bra_tensor_mul_ket_tensor {n m : ℕ} (α : Bra n) (β : Bra m) (ψ : Ket n) (φ : Ket m) :
    (Ket.tensor α β) * (Ket.tensor ψ φ) = (α * ψ) * (β * φ) :=
  by
  simp only [bra_mul_ket_eq, Bra.tensor, Ket.tensor]
    -- Step 1: Convert sum over Fin(n*m) to sum over Fin n × Fin m
    
  trans (∑ p : Fin n × Fin m, α.vec p.1 * β.vec p.2 * (ψ.vec p.1 * φ.vec p.2))
  · apply Fintype.sum_equiv finProdFinEquiv.symm
    intro j;
    simp [finProdFinEquiv]
      -- Step 2: Rearrange: (α·β)·(ψ·φ) = (α·ψ)·(β·φ)
      
  trans (∑ p : Fin n × Fin m, (α.vec p.1 * ψ.vec p.1) * (β.vec p.2 * φ.vec p.2))
  · congr 1; ext p;
    ring
      -- Step 3: Split double sum: ∑_{i,j} f(i)·g(j) = (∑_i f(i))·(∑_j g(j))
      
  rw [Fintype.sum_prod_type]
  conv_lhs =>
    arg 2; ext x; arg 2; ext y
    rw [show ((x, y) : Fin n × Fin m).1 = x from rfl, show ((x, y) : Fin n × Fin m).2 = y from rfl]
  rw [← Finset.sum_mul_sum]


-- @@ L179-185 expanded
/-- Tensor product of normalized kets: ⟨ψ⊗φ|ψ⊗φ⟩ = ⟨ψ|ψ⟩·⟨φ|φ⟩ = 1·1 = 1 -/
def NormKet.tensor {n m : ℕ} (ψ : NormKet n) (φ : NormKet m) : NormKet (n * m) :=
  ⟨Ket.tensor ψ.toKet φ.toKet, by
    unfold Ket.IsNormalized
    rw [Ket.dag_tensor, bra_tensor_mul_ket_tensor]
    rw [ψ.normalized, φ.normalized]
    ring⟩


-- @@ L187-187 verbatim
infixl:70 " ⊗ " => NormKet.tensor


-- @@ L189-196 expanded
/-- Tensor product of NormKets as Kets -/
@[simp]
theorem NormKet.tensor_toKet {n m : ℕ} (ψ : NormKet n) (φ : NormKet m) :
    (Ket.tensor ψ φ).toKet = Ket.tensor ψ.toKet φ.toKet :=
  rfl


-- @@ L198-205 expanded
/-- Tensor product of operators distributes over addition (left) -/
@[simp]
lemma Op.tensor_add_left {n m : ℕ} (A B : Op n) (C : Op m) :
    Ket.tensor (A + B) C = Ket.tensor A C + Ket.tensor B C :=
  by
  unfold Op.tensor
  ext i j
  simp only [Matrix.add_kronecker, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.add_apply,
    Matrix.kroneckerMap_apply]


-- @@ L207-218 expanded
/-- Tensor product of operators distributes over addition (right) -/
@[simp]
lemma Op.tensor_add_right {n m : ℕ} (A : Op n) (B C : Op m) :
    Ket.tensor A (B + C) = Ket.tensor A B + Ket.tensor A C :=
  by
  unfold Op.tensor
  ext i j
  simp only [Matrix.kronecker_add, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.add_apply,
    Matrix.kroneckerMap_apply]
    -- ============================================================================
    -- Ketbra Tensor Product Factorization
    -- ============================================================================


-- @@ L220-242 expanded
/-- Ketbra of tensor products equals tensor of ketbras:
    (|ψ₁⟩ ⊗ |ψ₂⟩)(⟨φ₁| ⊗ ⟨φ₂|) = |ψ₁⟩⟨φ₁| ⊗ |ψ₂⟩⟨φ₂| -/
@[simp]
lemma ketbra_tensor {n m : ℕ} (ψ₁ : Ket n) (φ₁ : Bra n) (ψ₂ : Ket m) (φ₂ : Bra m) :
    (Ket.tensor ψ₁ ψ₂) * (Ket.tensor φ₁ φ₂) = Ket.tensor (ψ₁ * φ₁) (ψ₂ * φ₂) :=
  by
  ext i j
  simp only [Op.tensor, Ket.tensor, Bra.tensor, HMul.hMul, Matrix.of_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Equiv.toFun_as_coe]
    -- (a * b) * (c * d) = (a * c) * (b * d) by commutativity
    
  exact
    mul_mul_mul_comm _ _ _
      _
        -- ============================================================================
        -- Completeness Relations
        -- ============================================================================
        
        -- ============================================================================
        -- Norm-Squared Properties
        -- ============================================================================
        
        -- ============================================================================
        -- Tensor Product of Normalized Kets
        -- ============================================================================


-- @@ L244-251 expanded
/-- Tensor product of normalized kets is normalized: ⟨ψ⊗φ|ψ⊗φ⟩ = ⟨ψ|ψ⟩·⟨φ|φ⟩ = 1·1 = 1 -/
@[simp]
theorem NormKet.tensor_normalized {n m : ℕ} (ψ : NormKet n) (φ : NormKet m) :
    (Ket.tensor ψ.toKet φ.toKet).IsNormalized :=
  by
  unfold Ket.IsNormalized
  rw [Ket.dag_tensor, bra_tensor_mul_ket_tensor]
  rw [ψ.normalized, φ.normalized]
  ring


-- @@ L253-253 verbatim
end  -- noncomputable section


-- @@ L255-255 verbatim
end Quantum.TensorProducts
