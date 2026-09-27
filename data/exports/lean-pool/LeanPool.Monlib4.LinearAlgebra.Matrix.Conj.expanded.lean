/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hermitian
import LeanPool.Monlib4.Preq.Ites


-- @@ L11-16 verbatim
/-!
 # Conjugate of a matrix

This file defines the conjugate of a matrix, `matrix.conj` with the notation `ᴴᵀ`
(i.e., `xᴴᵀ i j = star (x i j)`), and shows basic properties about it.
-/


-- @@ L18-18 verbatim
@[expose] public section



-- @@ L21-21 verbatim
namespace Matrix


-- @@ L23-23 verbatim
open scoped Matrix


-- @@ L25-25 verbatim
variable {α n₁ n₂ : Type _}


-- @@ L27-30 verbatim
/--
conjugate of matrix defined as $\bar{x} := {(x^*)}^\top$, i.e., $\bar{x}_{ij}=\overline{x_{ij}}$ -/
def conj [Star α] (x : Matrix n₁ n₂ α) : Matrix n₁ n₂ α :=
  xᴴᵀ


-- @@ L32-33 verbatim
/-- Postfix notation `ᴴᵀ` for `Matrix.conj`. -/
scoped postfix:1024 "ᴴᵀ" => Matrix.conj


-- @@ L35-36 verbatim
theorem conj_apply [Star α] (x : Matrix n₁ n₂ α) (i : n₁) (j : n₂) : xᴴᵀ i j = star (x i j) :=
  rfl


-- @@ L38-39 verbatim
theorem conj_conj [InvolutiveStar α] (x : Matrix n₁ n₂ α) : xᴴᵀᴴᵀ = x :=
  (conjTranspose_conjTranspose (xᵀᵀ)).trans (transpose_transpose _)


-- @@ L41-42 verbatim
theorem conj_add [AddMonoid α] [StarAddMonoid α] (x y : Matrix n₁ n₂ α) : (x + y)ᴴᵀ = xᴴᵀ + yᴴᵀ :=
  by simp_rw [conj, ← transpose_add, ← conjTranspose_add]


-- @@ L44-46 verbatim
theorem conj_smul {R : Type _} [Star R] [Star α] [SMul R α] [StarModule R α] (c : R)
    (x : Matrix n₁ n₂ α) : (c • x)ᴴᵀ = star c • xᴴᵀ := by
  simp_rw [conj, ← transpose_smul, ← conjTranspose_smul]


-- @@ L48-49 verbatim
theorem conj_conjTranspose [InvolutiveStar α] (x : Matrix n₁ n₂ α) : xᴴᵀᴴ = xᵀ :=
  conjTranspose_conjTranspose (xᵀ)


-- @@ L51-52 verbatim
theorem conjTranspose_conj [InvolutiveStar α] (x : Matrix n₁ n₂ α) : xᴴᴴᵀ = xᵀ :=
  conj_conjTranspose _


-- @@ L54-55 verbatim
theorem transpose_conj_eq_conjTranspose [Star α] (x : Matrix n₁ n₂ α) : xᴴᵀᵀ = xᴴ :=
  rfl


-- @@ L57-57 verbatim
namespace IsHermitian


-- @@ L59-60 verbatim
theorem conj {α n : Type _} [Star α] {x : Matrix n n α} (hx : x.IsHermitian) :
    xᴴᵀ = xᵀ := by simp_rw [Matrix.conj, hx.eq]


-- @@ L62-62 verbatim
end IsHermitian


-- @@ L64-67 verbatim
theorem conj_mul {α m n p : Type _} [Fintype n] [CommSemiring α] [StarRing α] (x : Matrix m n α)
    (y : Matrix n p α) : (x * y)ᴴᵀ = xᴴᵀ * yᴴᵀ := by
  ext
  simp_rw [conj_apply, mul_apply, star_sum, StarMul.star_mul, conj_apply, mul_comm]


-- @@ L69-72 verbatim
theorem conj_one {α n : Type _} [DecidableEq n] [Semiring α] [StarRing α] :
    (1 : Matrix n n α)ᴴᵀ = 1 := by
  ext
  simp_rw [conj_apply, one_apply, star_ite, star_one, star_zero]


-- @@ L74-77 verbatim
theorem conj_zero {α n₁ n₂ : Type _} [AddMonoid α] [StarAddMonoid α] :
  (0 : Matrix n₁ n₂ α)ᴴᵀ = 0 := by
  ext
  simp_rw [conj_apply, zero_apply, star_zero]


-- @@ L79-79 verbatim
end Matrix
