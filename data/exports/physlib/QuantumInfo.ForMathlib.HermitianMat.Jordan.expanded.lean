/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib.Algebra.Jordan.Basic

public import QuantumInfo.ForMathlib.HermitianMat.CFC
public import QuantumInfo.ForMathlib.HermitianMat.Order


-- @@ L13-18 verbatim
/-!
Hermitian matrices have a Jordan algebra structure given by
`A * B := 2⁻¹ • (A.toMat * B.toMat + B.toMat * A.toMat)`. We call this operation
`HermitianMat.symmMul`, but it's available as `*` multiplication scoped under
`HermMul`. When `A` and `B` commute, this reduces to standard matrix multiplication.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
section starRing


-- @@ L26-26 verbatim
variable {d 𝕜 : Type*} [Fintype d] [Field 𝕜] [StarRing 𝕜]

-- @@ L27-27 verbatim
variable (A B : HermitianMat d 𝕜)


-- @@ L29-29 verbatim
namespace HermitianMat


-- @@ L31-33 verbatim
def symmMul : HermitianMat d 𝕜 :=
  ⟨(2 : 𝕜)⁻¹ • (A.mat * B.mat + B.mat * A.mat),
    by simp [selfAdjoint, IsSelfAdjoint, add_comm, Matrix.star_eq_conjTranspose]⟩


-- @@ L35-37 verbatim
set_option backward.isDefEq.respectTransparency false in
theorem symmMul_comm : A.symmMul B = B.symmMul A := by
  rw [symmMul, symmMul, Subtype.mk.injEq, add_comm]


-- @@ L39-42 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem symmMul_zero : A.symmMul 0 = 0:= by
  simp [symmMul]


-- @@ L44-47 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem zero_symmMul : symmMul 0 A = 0 := by
  simp [symmMul]


-- @@ L49-51 verbatim
theorem symmMul_toMat : (A.symmMul B).mat =
    (2 : 𝕜)⁻¹ • (A.mat * B.mat + B.mat * A.mat) := by
  rfl


-- @@ L53-53 verbatim
variable [Invertible (2 : 𝕜)]


-- @@ L55-61 verbatim
variable {A B} in
@[simp]
theorem symmMul_of_commute (hAB : Commute A.mat B.mat) :
    (A.symmMul B).mat = A.mat * B.mat := by
  rw [symmMul_toMat, hAB]
  rw [smul_add, ← add_smul, inv_eq_one_div, ← add_div]
  rw [add_self_div_two, one_smul]


-- @@ L63-64 verbatim
theorem symmMul_self : (symmMul A A).mat = A.mat * A.mat := by
  simp


-- @@ L66-66 verbatim
variable [DecidableEq d]


-- @@ L68-70 verbatim
@[simp]
theorem symmMul_one : A.symmMul 1 = A := by
  ext1; simp


-- @@ L72-74 verbatim
@[simp]
theorem one_symmMul : symmMul 1 A = A := by
  ext1; simp


-- @@ L76-78 verbatim
@[simp]
theorem symmMul_neg_one : A.symmMul (-1) = -A := by
  ext1; simp


-- @@ L80-82 verbatim
@[simp]
theorem neg_one_symmMul : symmMul (-1) A = -A := by
  ext1; simp


-- @@ L84-84 verbatim
end HermitianMat

-- @@ L85-85 verbatim
end starRing


-- @@ L87-87 verbatim
namespace HermMul


-- @@ L89-89 verbatim
section starRing


-- @@ L91-91 verbatim
variable {d 𝕜 : Type*} [Fintype d] [Field 𝕜] [StarRing 𝕜]

-- @@ L92-92 verbatim
variable (A B : HermitianMat d 𝕜)


-- @@ L94-100 verbatim
scoped instance : CommMagma (HermitianMat d 𝕜) where
  mul := HermitianMat.symmMul
  mul_comm := HermitianMat.symmMul_comm

-- --Stupid shortcut that might actually help a lot
-- scoped instance : Mul (HermitianMat d 𝕜) :=
  -- CommMagma.toMul


-- @@ L102-103 verbatim
theorem mul_eq_symmMul : A * B = A.symmMul B := by
  rfl


-- @@ L105-110 verbatim
scoped instance : IsCommJordan (HermitianMat d 𝕜) where
  lmul_comm_rmul_rmul a b := by
    ext1
    simp only [mul_eq_symmMul, HermitianMat.symmMul_toMat, smul_add,
      mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    abel


-- @@ L112-114 verbatim
scoped instance : MulZeroClass (HermitianMat d 𝕜) where
  zero_mul := by simp [mul_eq_symmMul]
  mul_zero := by simp [mul_eq_symmMul]


-- @@ L116-116 verbatim
variable [DecidableEq d] [Invertible (2 : 𝕜)]


-- @@ L118-120 verbatim
scoped instance : MulZeroOneClass (HermitianMat d 𝕜) where
  one_mul := by simp [mul_eq_symmMul]
  mul_one := by simp [mul_eq_symmMul]


-- @@ L122-122 verbatim
end starRing


-- @@ L124-124 verbatim
section field


-- @@ L126-126 verbatim
variable {d 𝕜 : Type*} [Fintype d] [Field 𝕜] [StarRing 𝕜]


-- @@ L128-136 verbatim
scoped instance : NonUnitalNonAssocRing (HermitianMat d 𝕜) where
  left_distrib a b c := by
    ext1
    simp [mul_eq_symmMul, HermitianMat.symmMul_toMat, mul_add, add_mul]
    abel
  right_distrib a b c := by
    ext1
    simp [mul_eq_symmMul, HermitianMat.symmMul_toMat, mul_add, add_mul]
    abel


-- @@ L138-138 verbatim
variable [Invertible (2 : 𝕜)] [DecidableEq d]


-- @@ L140-141 verbatim
scoped instance : NonAssocCommRing (HermitianMat d 𝕜) where
  mul_comm := HermitianMat.symmMul_comm


-- @@ L143-143 verbatim
end field


-- @@ L145-145 verbatim
section rclike


-- @@ L147-147 verbatim
variable {d 𝕜 : Type*} [Fintype d] [RCLike 𝕜]


-- @@ L149-154 verbatim
scoped instance : IsScalarTower ℝ (HermitianMat d 𝕜) (HermitianMat d 𝕜) where
  smul_assoc r x y := by
    ext : 2
    simp only [smul_eq_mul, mul_eq_symmMul, HermitianMat.symmMul_toMat,
      HermitianMat.mat_smul, smul_add]
    simp


-- @@ L156-156 verbatim
end rclike


-- @@ L158-158 verbatim
end HermMul
