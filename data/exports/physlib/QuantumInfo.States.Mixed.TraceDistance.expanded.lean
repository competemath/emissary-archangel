/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.States.Mixed.MState

public import QuantumInfo.ForMathlib.ContinuousLinearMap
public import QuantumInfo.ForMathlib.ComplexLaplaceTransform
public import QuantumInfo.ForMathlib.ContinuousSup
public import QuantumInfo.ForMathlib.Filter
public import QuantumInfo.ForMathlib.HermitianMat
public import QuantumInfo.ForMathlib.Isometry
public import QuantumInfo.ForMathlib.LinearEquiv
public import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
public import QuantumInfo.ForMathlib.Matrix
public import QuantumInfo.ForMathlib.Minimax
public import QuantumInfo.ForMathlib.Misc
public import QuantumInfo.ForMathlib.Unitary


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
open Classical

-- @@ L28-28 verbatim
open BigOperators

-- @@ L29-29 verbatim
open ComplexConjugate

-- @@ L30-30 verbatim
open Kronecker

-- @@ L31-31 verbatim
open scoped Matrix ComplexOrder


-- @@ L33-33 verbatim
variable {d : Type*} [Fintype d] [DecidableEq d]


-- @@ L35-37 verbatim
/--The trace distance between two quantum states: half the trace norm of the difference (ρ - σ). -/
def TrDistance (ρ σ : MState d) : ℝ :=
  (1/2:ℝ) * (ρ.m - σ.m).traceNorm


-- @@ L39-39 verbatim
namespace TrDistance


-- @@ L41-41 verbatim
variable {d d₂ : Type*} [Fintype d] [Fintype d₂] (ρ σ : MState d)


-- @@ L43-45 verbatim
theorem ge_zero : 0 ≤ TrDistance ρ σ := by
  rw [TrDistance]
  simp [Matrix.traceNorm_nonneg]


-- @@ L47-51 verbatim
theorem le_one : TrDistance ρ σ ≤ 1 := by
  have htri := Matrix.traceNorm_add_le ρ.m (-σ.m)
  simp [TrDistance, sub_eq_add_neg, Matrix.traceNorm_neg,
    ρ.traceNorm_eq_one, σ.traceNorm_eq_one] at htri ⊢
  linarith


-- @@ L53-55 verbatim
/-- The trace distance, as a `Prob` probability with value between 0 and 1. -/
def prob : Prob :=
  ⟨TrDistance ρ σ, ⟨ge_zero ρ σ, le_one ρ σ⟩⟩


-- @@ L57-60 verbatim
/-- The trace distance is a symmetric quantity. -/
theorem symm : TrDistance ρ σ = TrDistance σ ρ := by
  dsimp [TrDistance]
  rw [← Matrix.traceNorm_neg, neg_sub]


-- @@ L62-68 verbatim
/-- The trace distance is equal to half the 1-norm of the eigenvalues of their difference . -/
theorem eq_abs_eigenvalues : TrDistance ρ σ = (1/2:ℝ) *
    ∑ i, abs ((ρ.Hermitian.sub σ.Hermitian).eigenvalues i) := by
  rw [TrDistance, Matrix.traceNorm_Hermitian_eq_sum_abs_eigenvalues]

-- Fuchs–van de Graaf inequalities
-- Relation to classical TV distance
