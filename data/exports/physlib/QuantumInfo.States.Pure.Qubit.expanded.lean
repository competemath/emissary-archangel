/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.Channels.Bundled
public import QuantumInfo.Channels.CPTP
public import QuantumInfo.Channels.Dual
public import QuantumInfo.Channels.MatrixMap
public import QuantumInfo.Channels.Unbundled
public import Physlib.Meta.TODO.Basic


-- @@ L15-22 verbatim
/-!
Quantum theory and operations specific to qubits.
 - Standard named (single-qubit) gates: Z, X, Y, H, S, T
 - Controlled versions of gates
 - Completeness of the PPT test: a state is separable iff it is PPT.
 - Fidelity for qubits: `F(ρ,σ) = 2√(ρ.det * σ.det)`.
 - The singlet/triplet split.
-/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-27 verbatim
TODO "Improve the module doc-string of the `Qubit` file, to explain the
  current implementation."


-- @@ L29-29 verbatim
abbrev Qubit := Fin 2


-- @@ L31-38 verbatim
open Lean.Parser.Tactic in
open Lean in
/--
Proves goals equating small matrices by expanding out products and simpliying standard Real arithmetic.
-/
syntax (name := matrix_expand) "matrix_expand"
  (" [" ((simpStar <|> simpErase <|> simpLemma),*,?) "]")?
  (" with " rcasesPat+)? : tactic


-- @@ L40-57 verbatim
macro_rules
  | `(tactic| matrix_expand $[[$rules,*]]? $[with $withArg*]?) => do
    let id1 := (withArg.getD ⟨[]⟩).getD 0 (← `(rcasesPat| _))
    let id2 := (withArg.getD ⟨[]⟩).getD 1 (← `(rcasesPat| _))
    let rules' := rules.getD ⟨#[]⟩
    `(tactic| (
      ext i j
      repeat rcases (i : Prod _ _) with ⟨i, $id1⟩
      repeat rcases (j : Prod _ _) with ⟨j, $id2⟩
      fin_cases i
      <;> fin_cases j
      <;> simp [Complex.ext_iff,
        Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, field,
        $rules',* ]
      <;> norm_num
      <;> try field_simp
      <;> try ring_nf
      ))


-- @@ L59-59 verbatim
namespace Qubit

-- @@ L60-60 verbatim
open Real

-- @@ L61-61 verbatim
open Complex


-- @@ L63-63 verbatim
variable {k : Type*} [Fintype k] [DecidableEq k]


-- @@ L65-67 expanded
/-- The Pauli Z gate on a qubit. -/
def Z : Matrix.unitaryGroup Qubit ℂ :=
  ⟨!![1, 0; 0, -1], by
    constructor <;>
      ( ext i j
        repeat rcases (i : Prod _ _) with ⟨i, _⟩
        repeat rcases (j : Prod _ _) with ⟨j, _⟩
        fin_cases i <;> fin_cases j <;>
              simp [Complex.ext_iff, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply,
                field, ] <;>
            norm_num <;>
          try field_simp <;> try ring_nf)⟩


-- @@ L69-71 expanded
/-- The Pauli X gate on a qubit. -/
def X : Matrix.unitaryGroup Qubit ℂ :=
  ⟨!![0, 1; 1, 0], by
    constructor <;>
      ( ext i j
        repeat rcases (i : Prod _ _) with ⟨i, _⟩
        repeat rcases (j : Prod _ _) with ⟨j, _⟩
        fin_cases i <;> fin_cases j <;>
              simp [Complex.ext_iff, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply,
                field, ] <;>
            norm_num <;>
          try field_simp <;> try ring_nf)⟩


-- @@ L73-75 expanded
/-- The Pauli Y gate on a qubit. -/
def Y : Matrix.unitaryGroup Qubit ℂ :=
  ⟨!![0, -I; I, 0], by
    constructor <;>
      ( ext i j
        repeat rcases (i : Prod _ _) with ⟨i, _⟩
        repeat rcases (j : Prod _ _) with ⟨j, _⟩
        fin_cases i <;> fin_cases j <;>
              simp [Complex.ext_iff, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply,
                field, ] <;>
            norm_num <;>
          try field_simp <;> try ring_nf)⟩


-- @@ L77-79 expanded
/-- The H gate, a Hadamard gate, on a qubit. -/
noncomputable def H : Matrix.unitaryGroup Qubit ℂ :=
  ⟨√(1 / 2) • (!![1, 1; 1, -1]), by
    constructor <;>
      ( ext i j
        repeat rcases (i : Prod _ _) with ⟨i, _⟩
        repeat rcases (j : Prod _ _) with ⟨j, _⟩
        fin_cases i <;> fin_cases j <;>
              simp [Complex.ext_iff, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply,
                field, ] <;>
            norm_num <;>
          try field_simp <;> try ring_nf)⟩


-- @@ L81-83 expanded
/-- The S gate, or Rz(π/2) rotation on a qubit. -/
def S : Matrix.unitaryGroup Qubit ℂ :=
  ⟨!![1, 0; 0, I], by
    constructor <;>
      ( ext i j
        repeat rcases (i : Prod _ _) with ⟨i, _⟩
        repeat rcases (j : Prod _ _) with ⟨j, _⟩
        fin_cases i <;> fin_cases j <;>
              simp [Complex.ext_iff, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply,
                field, ] <;>
            norm_num <;>
          try field_simp <;> try ring_nf)⟩


-- @@ L85-87 expanded
/-- The T gate, or Rz(π/4) rotation on a qubit. -/
noncomputable def T : Matrix.unitaryGroup Qubit ℂ :=
  ⟨!![1, 0; 0, (1 + I) / √2], by
    constructor <;>
      ( ext i j
        repeat rcases (i : Prod _ _) with ⟨i, _⟩
        repeat rcases (j : Prod _ _) with ⟨j, _⟩
        fin_cases i <;> fin_cases j <;>
              simp [Complex.ext_iff, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply,
                field, ] <;>
            norm_num <;>
          try field_simp <;> try ring_nf)⟩


-- @@ L89-91 expanded
@[simp]
theorem Z_sq : Z * Z = 1 := by
  ( ext i j
    repeat rcases (i : Prod _ _) with ⟨i, _⟩
    repeat rcases (j : Prod _ _) with ⟨j, _⟩
    fin_cases i <;> fin_cases j <;>
          simp [Complex.ext_iff, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, field,
            Z] <;>
        norm_num <;>
      try field_simp <;> try ring_nf)


-- @@ L93-95 expanded
@[simp]
theorem X_sq : X * X = 1 := by
  ( ext i j
    repeat rcases (i : Prod _ _) with ⟨i, _⟩
    repeat rcases (j : Prod _ _) with ⟨j, _⟩
    fin_cases i <;> fin_cases j <;>
          simp [Complex.ext_iff, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, field,
            X] <;>
        norm_num <;>
      try field_simp <;> try ring_nf)


-- @@ L97-99 expanded
@[simp]
theorem Y_sq : Y * Y = 1 := by
  ( ext i j
    repeat rcases (i : Prod _ _) with ⟨i, _⟩
    repeat rcases (j : Prod _ _) with ⟨j, _⟩
    fin_cases i <;> fin_cases j <;>
          simp [Complex.ext_iff, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, field,
            Y] <;>
        norm_num <;>
      try field_simp <;> try ring_nf)


-- @@ L101-103 expanded
@[simp]
theorem H_sq : H * H = 1 := by
  ( ext i j
    repeat rcases (i : Prod _ _) with ⟨i, _⟩
    repeat rcases (j : Prod _ _) with ⟨j, _⟩
    fin_cases i <;> fin_cases j <;>
          simp [Complex.ext_iff, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, field,
            H] <;>
        norm_num <;>
      try field_simp <;> try ring_nf)


-- @@ L105-107 expanded
@[simp]
theorem S_sq : S * S = Z := by
  ( ext i j
    repeat rcases (i : Prod _ _) with ⟨i, _⟩
    repeat rcases (j : Prod _ _) with ⟨j, _⟩
    fin_cases i <;> fin_cases j <;>
          simp [Complex.ext_iff, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, field,
            S, Z] <;>
        norm_num <;>
      try field_simp <;> try ring_nf)


-- @@ L109-111 expanded
@[simp]
theorem T_sq : T * T = S := by
  ( ext i j
    repeat rcases (i : Prod _ _) with ⟨i, _⟩
    repeat rcases (j : Prod _ _) with ⟨j, _⟩
    fin_cases i <;> fin_cases j <;>
          simp [Complex.ext_iff, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, field,
            T, S] <;>
        norm_num <;>
      try field_simp <;> try ring_nf)


-- @@ L113-116 expanded
/--
The anticommutator `{X,Y}` is zero. Marked simp as to put Pauli products in a canonical Y-X-Z order. -/
@[simp]
theorem X_Y_anticomm : X * Y = -Y * X := by
  ( ext i j
    repeat rcases (i : Prod _ _) with ⟨i, _⟩
    repeat rcases (j : Prod _ _) with ⟨j, _⟩
    fin_cases i <;> fin_cases j <;>
          simp [Complex.ext_iff, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, field,
            X, Y] <;>
        norm_num <;>
      try field_simp <;> try ring_nf)


-- @@ L118-120 expanded
/-- The anticommutator `{Y,Z}` is zero. -/
theorem Y_Z_anticomm : Z * Y = -Y * Z := by
  ( ext i j
    repeat rcases (i : Prod _ _) with ⟨i, _⟩
    repeat rcases (j : Prod _ _) with ⟨j, _⟩
    fin_cases i <;> fin_cases j <;>
          simp [Complex.ext_iff, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, field,
            Z, Y] <;>
        norm_num <;>
      try field_simp <;> try ring_nf)


-- @@ L122-124 expanded
/-- The anticommutator `{Z,X}` is zero. -/
theorem Z_X_anticomm : Z * X = -X * Z := by
  ( ext i j
    repeat rcases (i : Prod _ _) with ⟨i, _⟩
    repeat rcases (j : Prod _ _) with ⟨j, _⟩
    fin_cases i <;> fin_cases j <;>
          simp [Complex.ext_iff, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, field,
            Z, X] <;>
        norm_num <;>
      try field_simp <;> try ring_nf)


-- @@ L126-128 expanded
@[simp]
theorem H_mul_X_eq_Z_mul_H : H * X = Z * H := by
  ( ext i j
    repeat rcases (i : Prod _ _) with ⟨i, _⟩
    repeat rcases (j : Prod _ _) with ⟨j, _⟩
    fin_cases i <;> fin_cases j <;>
          simp [Complex.ext_iff, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, field,
            H, X, Z] <;>
        norm_num <;>
      try field_simp <;> try ring_nf)


-- @@ L130-132 expanded
@[simp]
theorem H_mul_Z_eq_X_mul_H : H * Z = X * H := by
  ( ext i j
    repeat rcases (i : Prod _ _) with ⟨i, _⟩
    repeat rcases (j : Prod _ _) with ⟨j, _⟩
    fin_cases i <;> fin_cases j <;>
          simp [Complex.ext_iff, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, field,
            H, X, Z] <;>
        norm_num <;>
      try field_simp <;> try ring_nf)


-- @@ L134-136 verbatim
@[simp]
theorem S_Z_comm : Z * S = S * Z := by
  simp [← S_sq, mul_assoc]


-- @@ L138-140 verbatim
@[simp]
theorem T_Z_comm : Z * T = T * Z := by
  simp [← S_sq, ← T_sq, mul_assoc]


-- @@ L142-144 verbatim
@[simp]
theorem S_T_comm : S * T = T * S := by
  simp [← T_sq, mul_assoc]


-- @@ L146-161 expanded
/--
Given a unitary `U` on some Hilbert space `k`, we have the controllized version that acts on `Fin 2 ⊗ k`
where `U` is conditionally applied if the first qubit is `1`. -/
def controllize (g : Matrix.unitaryGroup k ℂ) : Matrix.unitaryGroup (Qubit × k) ℂ :=
  ⟨Matrix.of fun (q₁, t₁) (q₂, t₂) ↦
      if (q₁, q₂) = (0, 0) then (if t₁ = t₂ then 1 else 0)
      else if (q₁, q₂) = (1, 1) then g t₁ t₂ else 0,
    by
    rw [Matrix.mem_unitaryGroup_iff]
    ( ext i j
      repeat rcases (i : Prod _ _) with ⟨i, ti⟩
      repeat rcases (j : Prod _ _) with ⟨j, tj⟩
      fin_cases i <;> fin_cases j <;>
            simp [Complex.ext_iff, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, field,
              -Complex.ext_iff] <;>
          norm_num <;>
        try field_simp <;> try ring_nf);
    · congr 1
      exact propext eq_comm
    · exact congrFun₂ g.2.2 ti tj⟩


-- @@ L163-163 verbatim
scoped notation "C[" g "]" => controllize g


-- @@ L165-167 expanded
/-- Controlled-NOT gate on two qubits.
The first qubit is the control and the second qubit is the target. -/
def CNOT : Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ :=
  C[X]


-- @@ L169-178 verbatim
/-- The matrix representation of CNOT is the standard 4×4 permutation matrix. -/
lemma CNOT_matrix :
    Matrix.reindex finProdFinEquiv finProdFinEquiv CNOT.val =
      ![![(1:ℂ), 0, 0, 0],
        ![0, 1, 0, 0],
        ![0, 0, 0, 1],
        ![0, 0, 1, 0]] := by
        ext i j
        simp only [CNOT, Qubit.X, Matrix.reindex_apply]
        fin_cases i <;> fin_cases j <;> rfl


-- @@ L180-180 expanded
variable (g : Matrix.unitaryGroup k ℂ) (j₁ j₂ : k)


-- @@ L182-184 expanded
@[simp]
theorem controllize_apply_zero_zero : C[g] (0, j₁) (0, j₂) = (1 : Matrix.unitaryGroup k ℂ) j₁ j₂ :=
  by rfl


-- @@ L186-188 verbatim
@[simp]
theorem controllize_apply_zero_one : C[g] (0, j₁) (1, j₂) = 0 := by
  rfl


-- @@ L190-192 verbatim
@[simp]
theorem controllize_apply_one_zero : C[g] (1, j₁) (0, j₂) = 0 := by
  rfl


-- @@ L194-196 verbatim
@[simp]
theorem controllize_apply_one_one : C[g] (1, j₁) (1, j₂) = g j₁ j₂ := by
  rfl


-- @@ L198-200 expanded
@[simp]
theorem controllize_mul (g₁ g₂ : Matrix.unitaryGroup k ℂ) : C[g₁] * C[g₂] = C[g₁ * g₂] := by
  ( ext i j
    repeat rcases (i : Prod _ _) with ⟨i, _⟩
    repeat rcases (j : Prod _ _) with ⟨j, _⟩
    fin_cases i <;> fin_cases j <;>
          simp [Complex.ext_iff, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, field,
            ] <;>
        norm_num <;>
      try field_simp <;> try ring_nf)


-- @@ L202-204 expanded
@[simp]
theorem controllize_one : C[(1 : Matrix.unitaryGroup k ℂ)] = 1 := by
  ( ext i j
    repeat rcases (i : Prod _ _) with ⟨i, _⟩
    repeat rcases (j : Prod _ _) with ⟨j, _⟩
    fin_cases i <;> fin_cases j <;>
          simp [Complex.ext_iff, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, field,
            ] <;>
        norm_num <;>
      try field_simp <;> try ring_nf)


-- @@ L206-208 verbatim
@[simp]
theorem controllize_mul_inv : C[g] * C[g⁻¹] = 1 := by
  simp


-- @@ L210-216 expanded
open scoped Matrix in
@[simp]
theorem X_controllize_X : (X ⊗ᵤ 1) * C[g] * (X ⊗ᵤ 1) = (1 ⊗ᵤ g) * C[g⁻¹] :=
  by
  ( ext i j
    repeat rcases (i : Prod _ _) with ⟨i, ki⟩
    repeat rcases (j : Prod _ _) with ⟨j, kj⟩
    fin_cases i <;> fin_cases j <;>
          simp [Complex.ext_iff, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, field,
            X, -Complex.ext_iff] <;>
        norm_num <;>
      try field_simp <;> try ring_nf);
  suffices (1 : Matrix k k ℂ) ki kj = (g * g⁻¹) ki kj by convert! this
  simp


-- @@ L218-218 verbatim
end Qubit
