import OAI.Analysis.CharacterCriterion.TensorSections


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped TensorProduct

-- @@ L7-7 verbatim
open scoped InnerProductSpace

-- @@ L8-8 verbatim
open scoped BigOperators

-- @@ L9-9 verbatim
open Set Module

-- @@ L10-10 verbatim
open Topology

-- @@ L11-11 verbatim
open NormedSpace

-- @@ L12-12 verbatim
open scoped ComplexOrder

-- @@ L13-13 verbatim
open scoped ComplexOrder

-- @@ L14-14 verbatim
open scoped InnerProductSpace

-- @@ L15-15 verbatim
open scoped InnerProductSpace

-- @@ L16-16 verbatim
open NormedSpace

-- @@ L17-17 verbatim
open scoped TensorProduct InnerProductSpace

-- @@ L18-18 verbatim
open UniformSpace

-- @@ L19-19 verbatim
variable [KirchbergRordam.GenericRW.Size]

-- @@ L20-20 verbatim
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n

-- @@ L21-21 verbatim
variable [KirchbergRordam.GenericRW.PauliData]

-- @@ L22-22 verbatim
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]

-- @@ L23-23 verbatim
open Filter Topology BoundedContinuousFunction

-- @@ L24-24 verbatim
open Filter Topology

-- @@ L25-25 verbatim
open Topology

-- @@ L26-26 verbatim
open scoped TensorProduct CStarAlgebra

-- @@ L27-27 verbatim
open scoped CStarAlgebra ComplexOrder

-- @@ L28-28 verbatim
open NormedSpace

-- @@ L29-29 verbatim
open scoped ComplexOrder

-- @@ L30-30 verbatim
open scoped ComplexOrder

-- @@ L31-31 verbatim
open scoped InnerProductSpace


-- @@ L33-33 verbatim
namespace KirchbergRordam.FourLegSymmetries

-- @@ L34-34 verbatim
open scoped CStarAlgebra ComplexOrder Matrix Kronecker

-- @@ L35-35 verbatim
open MatrixTensor MatrixPermutationPath

-- @@ L36-36 verbatim
variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

-- @@ L37-37 verbatim
abbrev Index (P Q : Type*) := (P×Q)×(P×Q)

-- @@ L38-38 verbatim
abbrev Algebra (P Q : Type*) := MatrixTensor.Mat (Index P Q)

-- @@ L39-43 verbatim
def hflip : Equiv.Perm (Index P Q) where
  toFun x := ((x.2.1,x.1.2),(x.1.1,x.2.2))
  invFun x := ((x.2.1,x.1.2),(x.1.1,x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

-- @@ L44-48 verbatim
def kflip : Equiv.Perm (Index P Q) where
  toFun x := ((x.1.1,x.2.2),(x.2.1,x.1.2))
  invFun x := ((x.1.1,x.2.2),(x.2.1,x.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

-- @@ L49-49 verbatim
def H : unitary (Algebra P Q) := perm hflip

-- @@ L50-50 verbatim
def K : unitary (Algebra P Q) := perm kflip

-- @@ L51-54 verbatim
lemma H_selfadjoint : star (H (P:=P) (Q:=Q) : Algebra P Q)=(H (P:=P) (Q:=Q) : Algebra P Q) := by
  change (hflip⁻¹.permMatrix ℂ)ᴴ = hflip⁻¹.permMatrix ℂ
  rw [Matrix.conjTranspose_permMatrix]
  rfl

-- @@ L55-58 verbatim
lemma K_selfadjoint : star (K (P:=P) (Q:=Q) : Algebra P Q)=(K (P:=P) (Q:=Q) : Algebra P Q) := by
  change (kflip⁻¹.permMatrix ℂ)ᴴ = kflip⁻¹.permMatrix ℂ
  rw [Matrix.conjTranspose_permMatrix]
  rfl

-- @@ L59-62 verbatim
lemma flips_commute : Commute (H (P:=P) (Q:=Q)) K := by
  change perm hflip * perm kflip=perm kflip*perm hflip
  rw [←perm_mul,←perm_mul]
  congr 1

-- @@ L63-65 verbatim
lemma flip_product : H (P:=P) (Q:=Q)*K=perm (Equiv.prodComm (P×Q) (P×Q)) := by
  rw [H,K,←perm_mul]
  rfl

-- @@ L66-72 verbatim
lemma conj_flip_left (a : MatrixTensor.Mat (P×Q)) :
    Unitary.conjStarAlgAut ℂ _ (H (P:=P) (Q:=Q)*K) (MatrixTensor.leftMatrix a)=MatrixTensor.rightMatrix a := by
  rw [flip_product,perm_conjugation]
  ext i j
  change a i.2 j.2 * (1:Matrix (P×Q) (P×Q) ℂ) i.1 j.1 =
    (1:Matrix (P×Q) (P×Q) ℂ) i.1 j.1 * a i.2 j.2
  exact mul_comm _ _


-- @@ L74-86 verbatim
lemma conj_K_left_left (a : MatrixTensor.Mat P) :
    Unitary.conjStarAlgAut ℂ _ (K (P:=P) (Q:=Q)) (MatrixTensor.leftMatrix (MatrixTensor.leftMatrix a))=
      MatrixTensor.leftMatrix (MatrixTensor.leftMatrix a) := by
  rw [K,perm_conjugation]
  ext i j
  change (a i.1.1 j.1.1 * (1:Matrix Q Q ℂ) i.2.2 j.2.2) *
    (1:Matrix (P×Q) (P×Q) ℂ) (i.2.1,i.1.2) (j.2.1,j.1.2) =
    (a i.1.1 j.1.1 * (1:Matrix Q Q ℂ) i.1.2 j.1.2) *
    (1:Matrix (P×Q) (P×Q) ℂ) i.2 j.2
  simp only [Matrix.one_apply,Prod.mk.injEq]
  rcases i with ⟨⟨p,q⟩,⟨r,s⟩⟩; rcases j with ⟨⟨p',q'⟩,⟨r',s'⟩⟩
  simp only [Prod.mk.injEq]
  split_ifs <;> simp_all


-- @@ L88-99 verbatim
lemma conj_H_right_right (b : MatrixTensor.Mat Q) :
    Unitary.conjStarAlgAut ℂ _ (H (P:=P) (Q:=Q)) (MatrixTensor.rightMatrix (MatrixTensor.rightMatrix b))=
      MatrixTensor.rightMatrix (MatrixTensor.rightMatrix b) := by
  rw [H,perm_conjugation]
  ext i j
  change (1:Matrix (P×Q) (P×Q) ℂ) (i.2.1,i.1.2) (j.2.1,j.1.2) *
    ((1:Matrix P P ℂ) i.1.1 j.1.1 * b i.2.2 j.2.2) =
    (1:Matrix (P×Q) (P×Q) ℂ) i.1 j.1 *
    ((1:Matrix P P ℂ) i.2.1 j.2.1 * b i.2.2 j.2.2)
  rcases i with ⟨⟨p,q⟩,⟨r,s⟩⟩; rcases j with ⟨⟨p',q'⟩,⟨r',s'⟩⟩
  simp only [Matrix.one_apply,Prod.mk.injEq]
  split_ifs <;> simp_all


-- @@ L101-101 verbatim
end KirchbergRordam.FourLegSymmetries

-- @@ L102-102 verbatim
namespace KirchbergRordam.FourLegSymmetries

-- @@ L103-103 verbatim
open MatrixTensor MatrixPermutationPath

-- @@ L104-104 verbatim
open scoped CStarAlgebra ComplexOrder Matrix Kronecker TensorProduct

-- @@ L105-105 verbatim
variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

-- @@ L106-119 verbatim
lemma H_decompose : (H (P:=P) (Q:=Q) : Algebra P Q) =
    ∑ ij : P×P, MatrixTensor.leftMatrix (MatrixTensor.leftMatrix (κ:=Q) (unit ij.1 ij.2))*
      MatrixTensor.rightMatrix (MatrixTensor.leftMatrix (κ:=Q) (unit ij.2 ij.1)) := by
  simp_rw [legs_product]
  ext i j
  change (hflip⁻¹.permMatrix ℂ) i j =
    (∑ ab : P×P, Matrix.kronecker (Matrix.kronecker (Matrix.single ab.1 ab.2 (1:ℂ)) 1)
      (Matrix.kronecker (Matrix.single ab.2 ab.1 (1:ℂ)) 1)) i j
  rcases i with ⟨⟨p,q⟩,⟨r,s⟩⟩; rcases j with ⟨⟨p',q'⟩,⟨r',s'⟩⟩
  simp only [Equiv.Perm.permMatrix,PEquiv.toMatrix_apply,Equiv.toPEquiv_apply,
    Option.mem_some_iff,hflip,Equiv.Perm.inv_def,Equiv.coe_fn_symm_mk,Prod.mk.injEq,
    Matrix.sum_apply]
  simp [←Finset.univ_product_univ,Finset.sum_product,ite_and,Matrix.single_apply,Matrix.one_apply,eq_comm]
  split_ifs <;> simp_all

-- @@ L120-133 verbatim
lemma K_decompose : (K (P:=P) (Q:=Q) : Algebra P Q) =
    ∑ ij : Q×Q, MatrixTensor.leftMatrix (MatrixTensor.rightMatrix (ι:=P) (unit ij.1 ij.2))*
      MatrixTensor.rightMatrix (MatrixTensor.rightMatrix (ι:=P) (unit ij.2 ij.1)) := by
  simp_rw [legs_product]
  ext i j
  change (kflip⁻¹.permMatrix ℂ) i j =
    (∑ ab : Q×Q, Matrix.kronecker (Matrix.kronecker 1 (Matrix.single ab.1 ab.2 (1:ℂ)))
      (Matrix.kronecker 1 (Matrix.single ab.2 ab.1 (1:ℂ)))) i j
  rcases i with ⟨⟨p,q⟩,⟨r,s⟩⟩; rcases j with ⟨⟨p',q'⟩,⟨r',s'⟩⟩
  simp only [Equiv.Perm.permMatrix,PEquiv.toMatrix_apply,Equiv.toPEquiv_apply,
    Option.mem_some_iff,kflip,Equiv.Perm.inv_def,Equiv.coe_fn_symm_mk,Prod.mk.injEq,
    Matrix.sum_apply]
  simp [←Finset.univ_product_univ,Finset.sum_product,ite_and,Matrix.single_apply,Matrix.one_apply,eq_comm]
  split_ifs <;> simp_all

-- @@ L134-139 verbatim
lemma H_mem : (H (P:=P) (Q:=Q) : Algebra P Q)∈
    tensorRange (MatrixTensor.leftMatrix (ι:=P) (κ:=Q)).range (MatrixTensor.leftMatrix (ι:=P) (κ:=Q)).range := by
  rw [H_decompose]
  apply Subalgebra.sum_mem
  intro ij _
  exact tensorRange_tmul _ _ ⟨_,rfl⟩ ⟨_,rfl⟩

-- @@ L140-145 verbatim
lemma K_mem : (K (P:=P) (Q:=Q) : Algebra P Q)∈
    tensorRange (MatrixTensor.rightMatrix (ι:=P) (κ:=Q)).range (MatrixTensor.rightMatrix (ι:=P) (κ:=Q)).range := by
  rw [K_decompose]
  apply Subalgebra.sum_mem
  intro ij _
  exact tensorRange_tmul _ _ ⟨_,rfl⟩ ⟨_,rfl⟩

-- @@ L146-157 verbatim
lemma conj_K_left_right (b : MatrixTensor.Mat Q) :
    Unitary.conjStarAlgAut ℂ _ (K (P:=P) (Q:=Q)) (MatrixTensor.leftMatrix (MatrixTensor.rightMatrix b))=
      MatrixTensor.rightMatrix (MatrixTensor.rightMatrix b) := by
  rw [K,perm_conjugation]
  ext i j
  change ((1:Matrix P P ℂ) i.1.1 j.1.1 * b i.2.2 j.2.2) *
    (1:Matrix (P×Q) (P×Q) ℂ) (i.2.1,i.1.2) (j.2.1,j.1.2) =
    (1:Matrix (P×Q) (P×Q) ℂ) i.1 j.1 *
    ((1:Matrix P P ℂ) i.2.1 j.2.1 * b i.2.2 j.2.2)
  rcases i with ⟨⟨p,q⟩,⟨r,s⟩⟩; rcases j with ⟨⟨p',q'⟩,⟨r',s'⟩⟩
  simp only [Matrix.one_apply,Prod.mk.injEq]
  split_ifs <;> simp_all

-- @@ L158-169 verbatim
lemma conj_H_left_left (a : MatrixTensor.Mat P) :
    Unitary.conjStarAlgAut ℂ _ (H (P:=P) (Q:=Q)) (MatrixTensor.leftMatrix (MatrixTensor.leftMatrix a))=
      MatrixTensor.rightMatrix (MatrixTensor.leftMatrix a) := by
  rw [H,perm_conjugation]
  ext i j
  change (a i.2.1 j.2.1 * (1:Matrix Q Q ℂ) i.1.2 j.1.2) *
    (1:Matrix (P×Q) (P×Q) ℂ) (i.1.1,i.2.2) (j.1.1,j.2.2) =
    (1:Matrix (P×Q) (P×Q) ℂ) i.1 j.1 *
    (a i.2.1 j.2.1 * (1:Matrix Q Q ℂ) i.2.2 j.2.2)
  rcases i with ⟨⟨p,q⟩,⟨r,s⟩⟩; rcases j with ⟨⟨p',q'⟩,⟨r',s'⟩⟩
  simp only [Matrix.one_apply,Prod.mk.injEq]
  split_ifs <;> simp_all

-- @@ L170-181 verbatim
lemma conj_H_left_right (b : MatrixTensor.Mat Q) :
    Unitary.conjStarAlgAut ℂ _ (H (P:=P) (Q:=Q)) (MatrixTensor.leftMatrix (MatrixTensor.rightMatrix b))=
      MatrixTensor.leftMatrix (MatrixTensor.rightMatrix b) := by
  rw [H,perm_conjugation]
  ext i j
  change ((1:Matrix P P ℂ) i.2.1 j.2.1 * b i.1.2 j.1.2) *
    (1:Matrix (P×Q) (P×Q) ℂ) (i.1.1,i.2.2) (j.1.1,j.2.2) =
    ((1:Matrix P P ℂ) i.1.1 j.1.1 * b i.1.2 j.1.2) *
    (1:Matrix (P×Q) (P×Q) ℂ) i.2 j.2
  rcases i with ⟨⟨p,q⟩,⟨r,s⟩⟩; rcases j with ⟨⟨p',q'⟩,⟨r',s'⟩⟩
  simp only [Matrix.one_apply,Prod.mk.injEq]
  split_ifs <;> simp_all


-- @@ L183-193 verbatim
lemma K_cross_mem (a : MatrixTensor.Mat (P×Q)) :
    Unitary.conjStarAlgAut ℂ _ (K (P:=P) (Q:=Q)) (MatrixTensor.leftMatrix a) ∈
      tensorRange (MatrixTensor.leftMatrix (ι:=P) (κ:=Q)).range (MatrixTensor.rightMatrix (ι:=P) (κ:=Q)).range := by
  rw [←decompose a,map_sum,map_sum]
  apply Subalgebra.sum_mem
  intro ij _
  rw [map_smul,map_smul]
  apply Subalgebra.smul_mem
  rcases ij with ⟨⟨i,k⟩,⟨j,l⟩⟩
  rw [←matrixUnit_kronecker,map_mul,map_mul,conj_K_left_left,conj_K_left_right]
  exact tensorRange_tmul _ _ ⟨_,rfl⟩ ⟨_,rfl⟩

-- @@ L194-205 verbatim
lemma H_cross_mem (a : MatrixTensor.Mat (P×Q)) :
    Unitary.conjStarAlgAut ℂ _ (H (P:=P) (Q:=Q)) (MatrixTensor.leftMatrix a) ∈
      tensorRange (MatrixTensor.rightMatrix (ι:=P) (κ:=Q)).range (MatrixTensor.leftMatrix (ι:=P) (κ:=Q)).range := by
  rw [←decompose a,map_sum,map_sum]
  apply Subalgebra.sum_mem
  intro ij _
  rw [map_smul,map_smul]
  apply Subalgebra.smul_mem
  rcases ij with ⟨⟨i,k⟩,⟨j,l⟩⟩
  rw [←matrixUnit_kronecker,map_mul,map_mul,conj_H_left_left,conj_H_left_right,
    (legs_commute _ _).symm.eq]
  exact tensorRange_tmul _ _ ⟨_,rfl⟩ ⟨_,rfl⟩

-- @@ L206-206 verbatim
end KirchbergRordam.FourLegSymmetries



-- @@ L209-209 verbatim
end


-- @@ L211-211 verbatim
end OAI
