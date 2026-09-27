/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order


-- @@ L11-20 verbatim
/-!
# Schur Product Theorem

Proves the Schur product theorem (real, finite-index case): if `A` and `B` are positive
semidefinite Hermitian matrices, then their entrywise (Hadamard) product `D` with entries
`D i j = A i j * B i j` is also positive semidefinite. The proof reduces positivity of the
Hadamard form `x ᵀ (A ∘ B) x` to positivity of the Kronecker product `A ⊗ B` applied to
the diagonal embedding of `x` into `ι × ι`. Used in the OS3 reflection positivity argument
to transfer PSD properties through the matrix exponential via `HadamardExp.lean`.
-/


-- @@ L22-22 verbatim
@[expose] public section



-- @@ L25-25 verbatim
open scoped BigOperators

-- @@ L26-26 verbatim
open scoped Kronecker


-- @@ L28-28 verbatim
namespace OSforGFF


-- @@ L30-30 verbatim
universe u


-- @@ L32-32 verbatim
variable {ι : Type u}


-- @@ L34-35 verbatim
/-- Notation alias for the Hadamard (entrywise) product from Mathlib. -/
notation:100 A "∘ₕ" B => Matrix.hadamard A B


-- @@ L37-42 verbatim
/-- Auxiliary: diagonal embedding of a vector `x : ι → ℝ` into `ι×ι` used for the restriction
argument: only the diagonal entries are nonzero and equal to `x`.
-/
@[simp] noncomputable def diagEmbed (x : ι → ℝ) : ι × ι → ℝ := by
  classical
  exact fun p => if p.2 = p.1 then x p.1 else 0


-- @@ L44-51 verbatim
lemma diagEmbed_ne_zero_of_ne_zero {x : ι → ℝ} (hx : x ≠ 0) : diagEmbed (ι:=ι) x ≠ 0 := by
  classical
  -- If diagEmbed x = 0 then all diagonal entries vanish, hence x = 0, contradiction.
  intro h
  apply hx
  funext i
  have := congrArg (fun f => f (i, i)) h
  simpa [diagEmbed] using this


-- @@ L53-55 verbatim
/-- Finite sum over pairs equals iterated double sum over coordinates (binderless sums). -/
lemma sum_pairs_eq_double [Fintype ι] (g : ι × ι → ℝ) :
  (∑ p, g p) = ∑ i, ∑ j, g (i, j) := Fintype.sum_prod_type g


-- @@ L57-64 expanded
/-- Over `ℝ`, the Hadamard product of Hermitian matrices is Hermitian. -/
private lemma isHermitian_hadamard_real {A B : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) : (Matrix.hadamard A B).IsHermitian :=
  by
  rw [Matrix.IsHermitian]
  ext i j
  have hAij : A i j = A j i := by simpa using (Matrix.IsHermitian.apply hA i j).symm
  have hBij : B i j = B j i := by simpa using (Matrix.IsHermitian.apply hB i j).symm
  simp [Matrix.conjTranspose, Matrix.hadamard, hAij, hBij]


-- @@ L66-117 expanded
/-- Schur product theorem (real case, finite index):
If A B are positive definite matrices over ℝ, then the Hadamard product is positive definite.
-/
@[simp]
theorem schur_product_posDef [Finite ι] (A B : Matrix ι ι ℝ) (hA : A.PosDef) (hB : B.PosDef) :
    (Matrix.hadamard A B).PosDef := by
  classical
  let := Fintype.ofFinite ι
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · exact isHermitian_hadamard_real (ι := ι) hA.isHermitian hB.isHermitian
  · -- Positivity: diagonal restriction of the Kronecker form
    
    intro x hx
    let y : ι × ι → ℝ := diagEmbed (ι := ι) x
    have hy : y ≠ 0 := diagEmbed_ne_zero_of_ne_zero (ι := ι) hx
    have hk : 0 < y ⬝ᵥ (A ⊗ₖ B).mulVec y := (Matrix.PosDef.kronecker hA hB).dotProduct_mulVec_pos hy
    have hquad_eq : y ⬝ᵥ (A ⊗ₖ B).mulVec y = x ⬝ᵥ (Matrix.hadamard A B).mulVec x := by
      classical
        -- expand LHS to sums over pairs
        calc
        y ⬝ᵥ (A ⊗ₖ B).mulVec y = ∑ p, y p * ((A ⊗ₖ B).mulVec y) p := by simp [dotProduct]
        _ = ∑ i, ∑ j, y (i, j) * ((A ⊗ₖ B).mulVec y) (i, j) := by
          exact sum_pairs_eq_double (fun p => y p * ((A ⊗ₖ B).mulVec y p))
        _ = ∑ i, ∑ j, y (i, j) * (∑ k, ∑ l, (A i k * B j l) * y (k, l)) :=
          by
          apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
          congr 1
          calc
            ((A ⊗ₖ B).mulVec y) (i, j) = ∑ q, ((A ⊗ₖ B) (i, j) q) * y q := by
              simp [Matrix.mulVec, dotProduct]
            _ = ∑ q, (A i q.1 * B j q.2) * y q := by rfl
            _ = ∑ k, ∑ l, (A i k * B j l) * y (k, l) := by
              simpa using (sum_pairs_eq_double (fun q => (A i q.1 * B j q.2) * y q))
        _ = ∑ i, ∑ k, x i * ((A i k * B i k) * x k) := by
          -- Kill off-diagonal terms using diagEmbed definition
          simp [y, diagEmbed, Finset.mul_sum, eq_comm]
        _ = x ⬝ᵥ (Matrix.hadamard A B).mulVec x := by
          -- expand RHS: Hadamard mulVec then dot
          simp [dotProduct, Matrix.mulVec, Matrix.hadamard, Finset.mul_sum, mul_comm, mul_left_comm]
            -- transport positivity
            
    simpa [hquad_eq] using hk


-- @@ L119-119 verbatim
end OSforGFF
