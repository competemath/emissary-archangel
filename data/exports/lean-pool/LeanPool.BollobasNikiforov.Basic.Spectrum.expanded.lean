/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import LeanPool.BollobasNikiforov.Basic.Inner
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.DegreeSum


-- @@ L12-20 verbatim
/-!
# Ordered spectrum of a Hermitian matrix

This file records the ordered real spectrum of a Hermitian matrix, matching the
conventions in `docs/sol.tex`. The ordered family is Mathlib's antitone
`eigenvalues₀`, which is the paper's `λ₁ ≥ ⋯ ≥ λₙ` with `λ₁` at index `0`.
`F` is the sum of squares of the two largest positive eigenvalues, with missing
terms replaced by zero.
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
namespace BollobasNikiforov


-- @@ L26-26 verbatim
open Matrix


-- @@ L28-28 verbatim
variable {n : Type*} [Fintype n] [DecidableEq n]

-- @@ L29-29 verbatim
variable {A : Matrix n n ℝ}


-- @@ L31-34 verbatim
/-- The eigenvalues of a Hermitian matrix in nonincreasing order. The value at
`i` is the paper's `λ_{i+1}`. -/
noncomputable def eigs₀ (hA : A.IsHermitian) : Fin (Fintype.card n) → ℝ :=
  hA.eigenvalues₀


-- @@ L36-37 verbatim
lemma eigs₀_antitone (hA : A.IsHermitian) : Antitone (eigs₀ hA) :=
  hA.eigenvalues₀_antitone


-- @@ L39-41 verbatim
/-- The largest eigenvalue `λ₁(A)`. -/
noncomputable def lambdaMax (hA : A.IsHermitian) [Nonempty n] : ℝ :=
  eigs₀ hA ⟨0, Fintype.card_pos⟩


-- @@ L43-45 verbatim
/-- The second-largest eigenvalue `λ₂(A)`. -/
noncomputable def lambdaSecond (hA : A.IsHermitian) [Nontrivial n] : ℝ :=
  eigs₀ hA ⟨1, Fintype.one_lt_card⟩


-- @@ L47-55 verbatim
/-- The sum of squares of the two largest positive eigenvalues of a Hermitian
matrix, with missing terms replaced by zero. -/
noncomputable def F (hA : A.IsHermitian) : ℝ :=
  if h0 : 0 < Fintype.card n then
    let t0 := (max (hA.eigenvalues₀ ⟨0, h0⟩) 0) ^ 2
    if h1 : 1 < Fintype.card n then
      t0 + (max (hA.eigenvalues₀ ⟨1, h1⟩) 0) ^ 2
    else t0
  else 0


-- @@ L57-62 verbatim
lemma F_eq (hA : A.IsHermitian) [Nontrivial n] :
    F hA = (max (lambdaMax hA) 0) ^ 2 + (max (lambdaSecond hA) 0) ^ 2 := by
  have h1 : 1 < Fintype.card n := Fintype.one_lt_card
  have h0 : 0 < Fintype.card n := Nat.zero_lt_of_lt h1
  unfold F lambdaMax lambdaSecond eigs₀
  rw [dite_eq_left h0, dite_eq_left h1]


-- @@ L64-66 verbatim
lemma F_nonneg (hA : A.IsHermitian) : 0 ≤ F hA := by
  dsimp [F]
  split_ifs <;> positivity


-- @@ L68-76 verbatim
lemma F_zero : F (A := (0 : Matrix n n ℝ)) isHermitian_zero = 0 := by
  have hz : (isHermitian_zero : (0 : Matrix n n ℝ).IsHermitian).eigenvalues₀ = 0 := by
    have h := (IsHermitian.eigenvalues_eq_zero_iff
        (A := (0 : Matrix n n ℝ)) isHermitian_zero).2 rfl
    funext i
    simpa [IsHermitian.eigenvalues] using
      congr_fun h ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))) i)
  dsimp [F]
  split_ifs <;> simp [hz]


-- @@ L78-78 verbatim
/-! ### N11 — Adjacency Frobenius mass -/


-- @@ L80-80 verbatim
variable {V : Type*} [Fintype V] [DecidableEq V]

-- @@ L81-81 verbatim
variable (G : SimpleGraph V) [DecidableRel G.Adj]



-- @@ L84-90 verbatim
omit [DecidableEq V] in
/-- The adjacency matrix is symmetric, so the Frobenius pairing with itself is
the trace of the square. -/
lemma inner_adjMatrix_eq_trace_mul :
    inner (G.adjMatrix ℝ) (G.adjMatrix ℝ) =
      (G.adjMatrix ℝ * G.adjMatrix ℝ).trace := by
  rw [inner, G.transpose_adjMatrix]


-- @@ L92-96 verbatim
omit [DecidableEq V] in
/-- The diagonal of `A_G²` records vertex degrees. -/
lemma trace_adjMatrix_mul_self :
    (G.adjMatrix ℝ * G.adjMatrix ℝ).trace = ∑ v, (G.degree v : ℝ) := by
  simp [trace, G.adjMatrix_mul_self_apply_self]


-- @@ L98-104 verbatim
omit [DecidableEq V] in
/-- The Frobenius mass of the adjacency matrix is twice the number of edges. -/
lemma inner_adjMatrix_self :
    inner (G.adjMatrix ℝ) (G.adjMatrix ℝ) = 2 * (G.edgeFinset.card : ℝ) := by
  rw [inner_adjMatrix_eq_trace_mul, trace_adjMatrix_mul_self, ← Nat.cast_sum,
    G.sum_degrees_eq_twice_card_edges]
  exact_mod_cast rfl


-- @@ L106-106 verbatim
end BollobasNikiforov
