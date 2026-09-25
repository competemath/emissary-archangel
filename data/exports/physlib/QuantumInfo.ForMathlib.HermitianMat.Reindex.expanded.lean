/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ForMathlib.HermitianMat.Basic
public import QuantumInfo.ForMathlib.ContinuousLinearMap
public import QuantumInfo.ForMathlib.LinearEquiv


-- @@ L12-18 verbatim
/-!
Much like `Matrix.reindex` and `Matrix.submatrix`, we can reindex a Hermitian matrix to get another
Hermitian matrix; however, this only makes sense when both permutations are the same, accordingly,
`HermitianMat.reindex` only takes one `Equiv` argument (as opposed to `Matrix.reindex`'s two).

This file then gives relevant lemmas for simplifying this.
-/


-- @@ L20-20 verbatim
@[expose] public section

-- @@ L21-21 verbatim
namespace HermitianMat


-- @@ L23-23 verbatim
variable {d d₂ d₃ d₄ 𝕜 : Type*} [RCLike 𝕜]


-- @@ L25-25 verbatim
variable (A B : HermitianMat d 𝕜) (e : d ≃ d₂)


-- @@ L27-28 verbatim
def reindex (e : d ≃ d₂) : HermitianMat d₂ 𝕜 :=
  ⟨A.mat.reindex e e, A.H.submatrix e.symm⟩


-- @@ L30-32 verbatim
@[simp]
theorem mat_reindex : (A.reindex e).mat = A.mat.reindex e e := by
  rfl


-- @@ L34-37 verbatim
/-! Our simp-normal form for expressions involving `HermitianMat.reindex` is that we try to push
the reindexing as far out as possible, so that it can be absorbed by `HermitianMat.trace`, or
cancelled our in a `HermitianMat.inner`. In places where it commutes (like `HermitianMat.inner`)
we push it to the right side. One downside is that we're not as likely to hit `reindex_one`. -/


-- @@ L39-42 verbatim
@[simp]
theorem reindex_refl (A : HermitianMat d 𝕜) :
    A.reindex (.refl _) = A := by
  rfl


-- @@ L44-47 verbatim
@[simp]
theorem reindex_reindex (A : HermitianMat d 𝕜) (e : d ≃ d₂) (f : d₂ ≃ d₃) :
    (A.reindex e).reindex f = A.reindex (e.trans f) := by
  ext1; simp


-- @@ L49-51 verbatim
@[simp]
theorem reindex_zero : (0 : HermitianMat d 𝕜).reindex e = 0 := by
  ext1; simp


-- @@ L53-57 verbatim
@[simp]
theorem reindex_one [DecidableEq d] [DecidableEq d₂] :
    (1 : HermitianMat d 𝕜).reindex e = 1 := by
  ext1
  simp [reindex]


-- @@ L59-61 verbatim
@[simp]
theorem reindex_add : A.reindex e + B.reindex e = (A + B).reindex e := by
  ext1; simp [Matrix.submatrix_add]


-- @@ L63-65 verbatim
@[simp]
theorem reindex_sub  : A.reindex e - B.reindex e = (A - B).reindex e := by
  ext1; simp [Matrix.submatrix_sub]


-- @@ L67-69 verbatim
@[simp]
theorem reindex_neg : (-A).reindex e = -(A.reindex e) := by
  ext1; simp [Matrix.submatrix_neg]


-- @@ L71-73 verbatim
@[simp]
theorem reindex_smul (c : ℝ) : (c • A).reindex e = c • (A.reindex e) := by
  ext1; simp [Matrix.submatrix_smul]


-- @@ L75-82 verbatim
@[simp]
theorem reindex_conj [Fintype d₂] [Fintype d] (B : Matrix d₃ d₂ 𝕜) :
    (A.reindex e).conj B = A.conj (B.submatrix id e) := by
  ext1
  simp only [conj_apply, mat_reindex, Matrix.reindex_apply, mat_mk]
  rw [← Matrix.submatrix_id_mul_right, Matrix.mul_assoc]
  rw [← Matrix.submatrix_id_mul_left, ← Matrix.mul_assoc]
  simp


-- @@ L84-84 verbatim
variable [Fintype d]


-- @@ L86-90 verbatim
set_option backward.isDefEq.respectTransparency false in
theorem conj_submatrix (B : Matrix d₂ d₄ 𝕜) (e : d₃ ≃ d₂) (f : d → d₄) :
    A.conj (B.submatrix e f) = (A.conj (B.submatrix id f)).reindex e.symm := by
  ext1
  simp [conj_apply, ← Matrix.submatrix_mul_equiv (e₂ := .refl d)]


-- @@ L92-97 verbatim
set_option backward.isDefEq.respectTransparency false in
theorem reindex_eq_conj [DecidableEq d] (e : d ≃ d₂) :
    A.reindex e = A.conj (Matrix.reindex e (.refl d) 1) := by
  ext : 3
  simp [-mat_apply, reindex, conj_apply, Matrix.submatrix,
    Matrix.mul_apply, Matrix.one_apply]


-- @@ L99-99 verbatim
variable [Fintype d₂] [DecidableEq d] [DecidableEq d₂]


-- @@ L101-106 verbatim
set_option backward.isDefEq.respectTransparency false in
theorem ker_reindex :
    (A.reindex e).ker = A.ker.comap (LinearEquiv.euclideanOfRelabel 𝕜 e).toLinearMap := by
  dsimp only [reindex, ker, lin]
  simp only [mat_mk]
  rw [Matrix.reindex_toEuclideanLin, LinearEquiv.ker_comp, LinearMap.ker_comp]


-- @@ L108-113 verbatim
@[simp]
theorem ker_reindex_le_iff :
    (A.reindex e).ker ≤ (B.reindex e).ker ↔ A.ker ≤ B.ker := by
  rw [ker_reindex, ker_reindex]
  apply Submodule.comap_le_comap_iff_of_surjective
  exact LinearEquiv.surjective (LinearEquiv.euclideanOfRelabel 𝕜 e)


-- @@ L115-115 verbatim
end HermitianMat
