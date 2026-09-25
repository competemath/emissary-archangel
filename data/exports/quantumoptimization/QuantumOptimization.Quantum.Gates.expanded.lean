import QuantumOptimization.Quantum.Operators.BraKet
-- Re-exported so downstream files keep transitive access to TensorProducts.
import QuantumOptimization.Quantum.TensorProducts.PartialTrace


-- @@ L5-10 verbatim
/-!
# Quantum Gates — Pauli operators

The single-qubit Pauli gates `pauliX`, `pauliY`, `pauliZ` (notations `X`, `Y`,
`Z`) and the Hermiticity of `X` and `Z`.
-/


-- @@ L12-12 verbatim
namespace Quantum.Gates


-- @@ L14-14 verbatim
open Quantum.Operators

-- @@ L15-15 verbatim
open scoped Matrix BigOperators ComplexConjugate ComplexOrder

-- @@ L16-16 verbatim
open Matrix


-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-21 expanded
/-- Pauli X gate (NOT gate): |0⟩ ↔ |1⟩ -/
def pauliX : Op 2 :=
  stdKet 2 1 * Ket.dag (stdKet 2 0) + stdKet 2 0 * Ket.dag (stdKet 2 1)


-- @@ L23-24 expanded
/-- Pauli Y gate -/
def pauliY : Op 2 :=
  Complex.I • (stdKet 2 1 * Ket.dag (stdKet 2 0)) - Complex.I • (stdKet 2 0 * Ket.dag (stdKet 2 1))


-- @@ L26-27 expanded
/-- Pauli Z gate (phase flip): |0⟩ → |0⟩, |1⟩ → -|1⟩ -/
def pauliZ : Op 2 :=
  stdKet 2 0 * Ket.dag (stdKet 2 0) - stdKet 2 1 * Ket.dag (stdKet 2 1)


-- @@ L29-29 verbatim
notation "X" => pauliX

-- @@ L30-30 verbatim
notation "Y" => pauliY

-- @@ L31-31 verbatim
notation "Z" => pauliZ


-- @@ L33-38 expanded
/-- Pauli X is Hermitian: X† = X -/
@[simp]
theorem pauliX_hermitian : Matrix.conjTranspose pauliX = pauliX :=
  by
  unfold pauliX
  (simp (config := { decide := true }) [Op.dag_smul, smul_mul_assoc, mul_smul_comm, smul_smul,
      smul_sub, smul_add, Op.dag_sub, Op.dag_add, ket_mul_bra_conjTranspose, stdKet_dag_dag,
      sub_mul, mul_sub, add_mul, mul_add, ketbra_mul_ketbra, ketbra_mul_ket, add_op_mul_ket,
      sub_op_mul_ket, smul_op_mul_ket, stdKet_braket, bra_mul_smul_ket, bra_mul_add_ket,
      Complex.star_def, Complex.conj_I, Complex.I_mul_I, mul_neg, neg_mul, neg_neg, neg_one_smul,
      one_smul, neg_smul, zero_mul, mul_zero, zero_smul, smul_zero, zero_add, add_zero, zero_sub,
      sub_zero, mul_one, one_mul, zero_ket_mul_bra, ket_mul_zero_bra, Ket.add_vec, Ket.sub_vec,
      Ket.smul_vec, Ket.neg_vec, Ket.sub_zero, Ket.zero_sub, sub_neg_eq_add, neg_add,
      add_neg_cancel_right, add_neg_cancel_left, completeness_2])
  abel


-- @@ L40-44 expanded
/-- Pauli Z is Hermitian: Z† = Z -/
@[simp]
theorem pauliZ_hermitian : Matrix.conjTranspose pauliZ = pauliZ :=
  by
  unfold pauliZ
  (simp (config := { decide := true }) [Op.dag_smul, smul_mul_assoc, mul_smul_comm, smul_smul,
      smul_sub, smul_add, Op.dag_sub, Op.dag_add, ket_mul_bra_conjTranspose, stdKet_dag_dag,
      sub_mul, mul_sub, add_mul, mul_add, ketbra_mul_ketbra, ketbra_mul_ket, add_op_mul_ket,
      sub_op_mul_ket, smul_op_mul_ket, stdKet_braket, bra_mul_smul_ket, bra_mul_add_ket,
      Complex.star_def, Complex.conj_I, Complex.I_mul_I, mul_neg, neg_mul, neg_neg, neg_one_smul,
      one_smul, neg_smul, zero_mul, mul_zero, zero_smul, smul_zero, zero_add, add_zero, zero_sub,
      sub_zero, mul_one, one_mul, zero_ket_mul_bra, ket_mul_zero_bra, Ket.add_vec, Ket.sub_vec,
      Ket.smul_vec, Ket.neg_vec, Ket.sub_zero, Ket.zero_sub, sub_neg_eq_add, neg_add,
      add_neg_cancel_right, add_neg_cancel_left, completeness_2])


-- @@ L46-46 verbatim
end


-- @@ L48-48 verbatim
end Quantum.Gates
