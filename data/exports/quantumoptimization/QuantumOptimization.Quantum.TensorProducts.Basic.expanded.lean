import QuantumOptimization.Quantum.Operators.BraKet
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Analysis.Matrix.Order  -- For PosSemidef.kronecker


-- @@ L7-7 verbatim
namespace Quantum.TensorProducts


-- @@ L9-9 verbatim
open Quantum.Operators

-- @@ L10-10 verbatim
open scoped Matrix BigOperators ComplexConjugate ComplexOrder TensorProduct Kronecker

-- @@ L11-11 verbatim
open Matrix


-- @@ L13-13 verbatim
noncomputable section


-- @@ L15-32 verbatim
/-!
# Type-Safe Quantum Mechanics - Tensor Products (HMul Foundation)

This module defines tensor products of quantum states and operators,
built on the HMul-primary foundation from BasicCalculusHMul.

## Key Definitions:
- `⊗` (Ket.tensor, NormKet.tensor, Op.tensor): Unified tensor product notation
  - Works for kets, normalized kets, and operators (Kronecker product)
  - Type inference determines which tensor product to use
- Tensor products of unitary and density operators

The calculus properties (linearity, distributivity) are in TensorCalculus.lean.
-/

-- ============================================================================
-- Section 15: Tensor Product Definitions
-- ============================================================================


-- @@ L34-38 verbatim
/-- Tensor product of kets -/
def Ket.tensor {n m : ℕ} (ψ : Ket n) (φ : Ket m) : Ket (n * m) :=
  ⟨fun k =>
    let ⟨i, j⟩ := finProdFinEquiv.symm k
    ψ.vec i * φ.vec j⟩


-- @@ L40-44 verbatim
/-- Tensor product of bras -/
def Bra.tensor {n m : ℕ} (β₁ : Bra n) (β₂ : Bra m) : Bra (n * m) :=
  ⟨fun k =>
    let ⟨i, j⟩ := finProdFinEquiv.symm k
    β₁.vec i * β₂.vec j⟩


-- @@ L46-51 verbatim
/-- Tensor product of operators (Kronecker product) -/
def Op.tensor {n m : ℕ} (A : Op n) (B : Op m) : Op (n * m) :=
  reindex finProdFinEquiv finProdFinEquiv (A ⊗ₖ B)  -- Uses Matrix.kronecker (⊗ₖ)

-- Unified tensor product notation ⊗ (works for Ket, Bra, Op)
-- Note: NormKet.tensor is defined in TensorCalculusHMul (needs bra_tensor_mul_ket_tensor)

-- @@ L52-52 verbatim
infixl:70 " ⊗ " => Ket.tensor

-- @@ L53-53 verbatim
infixl:70 " ⊗ " => Bra.tensor

-- @@ L54-58 verbatim
infixl:70 " ⊗ " => Op.tensor

-- ============================================================================
-- Bra Tensor Properties
-- ============================================================================


-- @@ L60-70 expanded
/-- Dag distributes over tensor: (ψ ⊗ φ).dag = ψ.dag ⊗ φ.dag -/
@[simp]
theorem Ket.dag_tensor {n m : ℕ} (ψ : Ket n) (φ : Ket m) : (ψ ⊗ φ).dag = ψ.dag ⊗ φ.dag :=
  by
  ext k
  unfold Ket.dag Ket.tensor Bra.tensor
  simp only [starRingEnd_apply, star_mul']
    -- ============================================================================
    -- Kronecker Product Lemmas (Physics Properties)
    -- ============================================================================


-- @@ L72-79 expanded
/-- Physics: Conjugate transpose distributes over tensor product: (A⊗B)† = A†⊗B† -/
@[simp]
theorem Op.tensor_conjTranspose {n m : ℕ} (A : Op n) (B : Op m) :
    Matrix.conjTranspose (A ⊗ B) = Matrix.conjTranspose A ⊗ Matrix.conjTranspose B := by
  -- Proof strategy: Use properties of reindex and kronecker
    -- (reindex e f (A ⊗ₖ B))† = reindex e f ((A ⊗ₖ B)†) = reindex e f (A† ⊗ₖ B†)
  
  unfold Op.tensor
  simp only [conjTranspose_reindex, conjTranspose_kronecker]


-- @@ L81-101 expanded
/-- Physics: Tensor product preserves matrix multiplication: (A⊗B)(C⊗D) = (AC)⊗(BD) -/
@[simp]
theorem Op.tensor_mul {n m : ℕ} (A C : Op n) (B D : Op m) : (A ⊗ B) * (C ⊗ D) = (A * C) ⊗ (B * D) :=
  by
  unfold Op.tensor
  ext i j
  simp only [Matrix.mul_apply, Matrix.reindex_apply, Matrix.submatrix_apply, kroneckerMap_apply]
    -- Convert sum over Fin(n*m) to sum over Fin n × Fin m
    
  trans
    (∑ k : Fin n × Fin m,
      (A (finProdFinEquiv.symm i).1 k.1 * B (finProdFinEquiv.symm i).2 k.2) *
        (C k.1 (finProdFinEquiv.symm j).1 * D k.2 (finProdFinEquiv.symm j).2))
  · apply Fintype.sum_equiv finProdFinEquiv.symm
    intro k;
    simp [finProdFinEquiv]
      -- Split into double sum and rearrange: (a*b)*(c*d) = (a*c)*(b*d)
      
  rw [Fintype.sum_prod_type]
  trans
    (∑ a : Fin n,
      ∑ b : Fin m,
        (A (finProdFinEquiv.symm i).1 a * C a (finProdFinEquiv.symm j).1) *
          (B (finProdFinEquiv.symm i).2 b * D b (finProdFinEquiv.symm j).2))
  · congr 1; ext a; congr 1; ext b;
    ring
      -- Factor: ∑_{a,b} f(a)*g(b) = (∑_a f(a))*(∑_b g(b))
      
  rw [Finset.sum_mul_sum]


-- @@ L103-112 expanded
/-- Physics: Identity tensor product: I⊗I = I -/
@[simp]
theorem Op.tensor_one {n m : ℕ} : (1 : Op n) ⊗ (1 : Op m) = 1 := by
  -- Proof: 1 ⊗ 1 = I_{n*m}
    -- Use Mathlib's one_kronecker_one and submatrix_one_equiv
  
  unfold Op.tensor
  rw [Matrix.one_kronecker_one]
    -- submatrix of identity with equivalence is identity
    
  exact Matrix.submatrix_one_equiv finProdFinEquiv.symm


-- @@ L114-127 expanded
/-- Physics: Trace factorizes over tensor product: Tr(A⊗B) = Tr(A)·Tr(B) -/
@[simp]
theorem Op.trace_tensor {n m : ℕ} (A : Op n) (B : Op m) : (A ⊗ B).trace = A.trace * B.trace :=
  by
  unfold Op.tensor trace
  simp only [Matrix.diag, Matrix.reindex_apply, Matrix.submatrix_apply]
    -- Convert sum over Fin(n*m) to sum over Fin n × Fin m
    
  trans (∑ p : Fin n × Fin m, (A ⊗ₖ B) p p)
  · apply Fintype.sum_equiv finProdFinEquiv.symm
    intro i;
    simp [finProdFinEquiv]
      -- Unfold kronecker at diagonal: (A ⊗ₖ B)[(i,j), (i,j)] = A[i,i] * B[j,j]
      
  simp only [kroneckerMap_apply]
    -- Factor: ∑_{i,j} A[i,i] * B[j,j] = (∑_i A[i,i]) * (∑_j B[j,j])
    
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]


-- @@ L129-129 verbatim
end  -- noncomputable section

-- @@ L130-132 verbatim
end Quantum.TensorProducts

-- DensityOp extensions must be in the same namespace as DensityOp for dot notation

-- @@ L133-133 verbatim
noncomputable section

-- @@ L134-134 verbatim
namespace Quantum.Operators


-- @@ L136-136 verbatim
open Quantum.TensorProducts

-- @@ L137-137 verbatim
open scoped Matrix BigOperators ComplexConjugate ComplexOrder TensorProduct Kronecker

-- @@ L138-142 verbatim
open Matrix

-- ============================================================================
-- Tensor Purity Lemmas
-- ============================================================================


-- @@ L144-144 verbatim
end Quantum.Operators

-- @@ L145-145 verbatim
end -- noncomputable section


-- @@ L147-147 verbatim
noncomputable section

-- @@ L148-148 verbatim
namespace Quantum.TensorProducts


-- @@ L150-150 verbatim
open Quantum.Operators

-- @@ L151-151 verbatim
open scoped Matrix BigOperators ComplexConjugate ComplexOrder TensorProduct Kronecker

-- @@ L152-156 verbatim
open Matrix

-- ============================================================================
-- Physics Notation for Multi-Qubit States
-- ============================================================================


-- @@ L158-166 verbatim
/-!
## Multi-Qubit State Notation

Usage: These expand to tensor products via ⊗
-/

-- ============================================================================
-- General Tensor Product Notation (for arbitrary kets/bras)
-- ============================================================================


-- @@ L168-179 verbatim
/-!
## General Tensor Product Notation

Uses ToKet type class and macros for flexible notation that accepts both Kets and Bras
with any number of comma-separated arguments:
- `|x, y⟩`, `|x, y, z⟩`, `|x, y, z, w⟩`, ... converts all to Kets, then tensors
- `⟨x, y|`, `⟨x, y, z|`, ... converts to Kets, tensors, then dags

This allows mixing Kets and Bras: `|ket, bra⟩` will dag the bra to make it a ket.
-/

-- ToKet instance for ℕ - allows natural number literals 0, 1 in qubit notation

-- @@ L180-183 verbatim
instance instToKetNat2 : ToKet ℕ 2 where
  toKet n := stdKet 2 ⟨n % 2, Nat.mod_lt n (by decide)⟩

-- Syntax for tensor ket: |x, y, z, ...⟩

-- @@ L184-186 verbatim
syntax (name := tensorKet) "|" term,+ "⟩" : term

-- Macro expansion for tensor ket

-- @@ L187-194 unexpanded
macro_rules
  | `(| $x:term, $xs:term,* ⟩) => do
    let mut result ← `(ToKet.toKet $x)
    for x in xs.getElems do
      result ← `($result ⊗ ToKet.toKet $x)
    return result

-- Syntax for tensor bra: ⟨x, y, z, ...|

-- @@ L195-197 verbatim
syntax (name := tensorBra) "⟨" term,+ "|" : term

-- Macro expansion for tensor bra

-- @@ L198-208 unexpanded
set_option quotPrecheck false in
macro_rules
  | `(⟨ $x:term, $xs:term,* |) => do
    let mut result ← `(ToKet.toKet $x)
    for x in xs.getElems do
      result ← `($result ⊗ ToKet.toKet $x)
    `(Ket.dag $result)

-- ============================================================================
-- NormKet Tensor Notation
-- ============================================================================


-- @@ L210-222 verbatim
/-!
## NormKet Tensor Product Notation

- `‖x, y, ...⟩` → tensor product of NormKets via `ToNormKet.toNormKet`

Examples:
- `‖ψ, φ⟩` tensors two NormKet variables
- `‖ψ, 0⟩` tensors ψ with qubit |0⟩ (uses ToNormKet ℕ 2 instance)

Single-state notation (`‖i:n⟩`, `‖0⟩`, `‖1⟩`) is defined in BasicCalculusHMul.
-/

-- ToNormKet instance for Fin 2 - allows ‖ψ, 0⟩ and ‖ψ, 1⟩ notation for qubits

-- @@ L223-226 verbatim
instance instToNormKetFin2 : ToNormKet (Fin 2) 2 where
  toNormKet i := stdNormKet 2 i

-- ToNormKet instance for ℕ - allows natural number literals 0, 1 in qubit notation

-- @@ L227-230 verbatim
instance instToNormKetNat2 : ToNormKet ℕ 2 where
  toNormKet n := stdNormKet 2 ⟨n % 2, Nat.mod_lt n (by decide)⟩

-- Syntax for tensor NormKet: ‖x, y, z, ...⟩

-- @@ L231-233 verbatim
syntax (name := tensorNormKet) "‖" term,+ "⟩" : term

-- Macro expansion for tensor NormKet

-- @@ L234-239 unexpanded
macro_rules
  | `(‖ $x:term, $xs:term,* ⟩) => do
    let mut result ← `(ToNormKet.toNormKet $x)
    for x in xs.getElems do
      result ← `($result ⊗ ToNormKet.toNormKet $x)
    return result


-- @@ L241-241 verbatim
end Quantum.TensorProducts


-- @@ L243-243 verbatim
end  -- noncomputable section


-- @@ L245-245 verbatim
namespace Quantum.TensorProducts


-- @@ L247-247 verbatim
open Quantum.Operators


-- @@ L249-249 verbatim
end Quantum.TensorProducts
