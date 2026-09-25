/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Basic

-- @@ L10-17 verbatim
/-!

# Tensorial nature of Lorentz vectors

We define the tensorial instance on `Lorentz.Vector`, and show
prove properties related to the Lorentz group action and the basis.

-/


-- @@ L19-19 verbatim
@[expose] public section



-- @@ L22-22 verbatim
open Module

-- @@ L23-23 verbatim
open Matrix

-- @@ L24-24 verbatim
open MatrixGroups

-- @@ L25-25 verbatim
open Complex

-- @@ L26-26 verbatim
open TensorProduct


-- @@ L28-28 verbatim
noncomputable section


-- @@ L30-30 verbatim
namespace Lorentz

-- @@ L31-31 verbatim
open realLorentzTensor


-- @@ L33-33 verbatim
namespace Vector


-- @@ L35-35 verbatim
open TensorSpecies

-- @@ L36-36 verbatim
open Tensor


-- @@ L38-42 verbatim
/-!

## Tensorial

-/


-- @@ L44-48 verbatim
/-- The equivalence between the type of indices of a Lorentz vector and
  `Fin 1 ⊕ Fin d`. -/
def indexEquiv {d : ℕ} :
    ComponentIdx (S := (realLorentzTensor d)) ![Color.up] ≃ Fin 1 ⊕ Fin d :=
  ComponentIdx.single (S := realLorentzTensor d) (c := Color.up)


-- @@ L50-61 verbatim
instance tensorial {d : ℕ} : Tensorial (realLorentzTensor d) ![.up] (Vector d) where
  toTensor := LinearEquiv.symm <|
    Equiv.toLinearEquiv
    ((Tensor.basis (S := (realLorentzTensor d)) ![.up]).repr.toEquiv.trans <|
  Finsupp.equivFunOnFinite.trans <|
  (Equiv.piCongrLeft' _ indexEquiv))
    { map_add := fun x y => by
        simp [map_add]
        rfl
      map_smul := fun c x => by
        simp [_root_.map_smul]
        rfl}


-- @@ L63-63 verbatim
open Tensorial


-- @@ L65-69 expanded
lemma toTensor_symm_apply {d : ℕ} (p : ((realLorentzTensor d).Tensor (vecCons .up ![]))) :
    (toTensor (self := tensorial)).symm p =
      (Equiv.piCongrLeft' _ indexEquiv <|
        Finsupp.equivFunOnFinite <| (Tensor.basis (S := (realLorentzTensor d)) _).repr p) :=
  rfl


-- @@ L71-77 verbatim
lemma toTensor_symm_pure {d : ℕ} (p : Pure (realLorentzTensor d) ![.up]) (i : Fin 1 ⊕ Fin d) :
    (toTensor (self := tensorial)).symm p.toTensor i =
    ((Lorentz.contrBasis d).repr (p 0)) (indexEquiv.symm i 0) := by
  rw [toTensor_symm_apply]
  simp only [Equiv.piCongrLeft'_apply, Finsupp.equivFunOnFinite_apply, Tensor.basis_repr_pure,
    Pure.component, Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton, cons_val_zero]
  rfl


-- @@ L79-83 verbatim
/-!

## Basis

-/


-- @@ L85-91 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma toTensor_symm_basis {d : ℕ} (μ : Fin 1 ⊕ Fin d) :
    (toTensor (self := tensorial)).symm (Tensor.basis ![Color.up] (indexEquiv.symm μ)) =
    basis μ := by
  funext i
  simp [Tensor.basis_apply, toTensor_symm_pure, Pure.basisVector, Finsupp.single_apply,
    indexEquiv]


-- @@ L93-96 verbatim
lemma toTensor_basis_eq_tensor_basis {d : ℕ} (μ : Fin 1 ⊕ Fin d) :
    toTensor (basis μ) = Tensor.basis ![Color.up] (indexEquiv.symm μ) := by
  rw [← toTensor_symm_basis]
  simp


-- @@ L98-103 verbatim
lemma basis_eq_map_tensor_basis {d} : basis =
    ((Tensor.basis
    (S := realLorentzTensor d) ![Color.up]).map toTensor.symm).reindex indexEquiv := by
  ext μ
  rw [← toTensor_symm_basis]
  simp


-- @@ L105-110 verbatim
lemma tensor_basis_map_eq_basis_reindex {d} :
    (Tensor.basis (S := realLorentzTensor d) ![Color.up]).map toTensor.symm =
    basis.reindex indexEquiv.symm := by
  rw [basis_eq_map_tensor_basis]
  ext μ
  simp


-- @@ L112-124 verbatim
lemma tensor_basis_repr_toTensor_apply {d : ℕ} (p : Vector d) (μ : ComponentIdx ![Color.up]) :
    (Tensor.basis ![Color.up]).repr (toTensor p) μ =
    p (indexEquiv μ) := by
  obtain ⟨p, rfl⟩ := toTensor.symm.surjective p
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, LinearEquiv.apply_symm_apply]
  apply induction_on_pure (t := p)
  · intro p
    simp [Tensor.basis_repr_pure, toTensor_symm_pure, Pure.component]
    rfl
  · intro r t h
    simp [h]
  · intro t1 t2 h1 h2
    simp [h1, h2]


-- @@ L126-130 verbatim
/-!

## Tensor products of vectors

-/


-- @@ L132-139 verbatim
/-- Evaluating both indices of an element of `Vector d ⊗ Vector d` gives its coefficient
  in the tensor-product basis. -/
lemma toField_eval_eval_eq_tensorProduct_repr {d} (F : Vector d ⊗[ℝ] Vector d)
    (μ ν : Fin 1 ⊕ Fin d) :
    toField {F | [μ] [ν]}ᵀ = (basis.tensorProduct basis).repr F (μ, ν) := by
  conv_rhs => rw [Tensorial.prod_eq_sum_eval basis_eq_map_tensor_basis basis_eq_map_tensor_basis F]
  simp [-Fintype.sum_sum_type, Basis.tensorProduct_repr_tmul_apply, Finsupp.single_apply]
  rfl


-- @@ L141-157 verbatim
/-- The coefficient of an element of `Vector d ⊗ Vector d` in the tensor basis is its
  coefficient in the tensor-product basis. -/
lemma tensor_basis_repr_toTensor_prod_apply {d} (F : Vector d ⊗[ℝ] Vector d)
    (b : ComponentIdx (S := realLorentzTensor d) (Fin.append ![Color.up] ![Color.up])) :
    (Tensor.basis _).repr (toTensor F) b = (basis.tensorProduct basis).repr F (b 0, b 1) := by
  rw [Tensorial.basis_toTensor_apply, Tensorial.basis_map_prod]
  simp only [Nat.reduceSucc, Nat.reduceAdd, Basis.repr_reindex, Finsupp.mapDomain_equiv_apply,
    Equiv.symm_symm, Fin.isValue]
  rw [tensor_basis_map_eq_basis_reindex]
  have hb : (((basis (d := d)).reindex indexEquiv.symm).tensorProduct
      (basis.reindex indexEquiv.symm)) =
      ((basis (d := d)).tensorProduct (basis (d := d))).reindex
      (indexEquiv.symm.prodCongr indexEquiv.symm) := by
    ext ⟨i, j⟩
    simp
  rw [hb, Module.Basis.repr_reindex_apply]
  congr 1


-- @@ L159-163 verbatim
/-!

## The action of the Lorentz group

-/


-- @@ L165-185 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma smul_eq_sum {d : ℕ} (i : Fin 1 ⊕ Fin d) (Λ : LorentzGroup d) (p : Vector d) :
    (Λ • p) i = ∑ j, Λ.1 i j * p j := by
  obtain ⟨p, rfl⟩ := toTensor.symm.surjective p
  rw [smul_toTensor_symm]
  apply induction_on_pure (t := p)
  · intro p
    have toTensor_symm_pure_val : ∀ (q : Pure (realLorentzTensor d) ![.up]) (j : Fin 1 ⊕ Fin d),
        (toTensor (self := tensorial)).symm q.toTensor j = (q 0).val j := fun q j => by
      rw [toTensor_symm_pure, contrBasis_repr_apply]
      rfl
    rw [actionT_pure]
    simp only [toTensor_symm_pure_val]
    show (Λ.1 *ᵥ (p 0)).val i = ∑ j, Λ.1 i j * (p 0).val j
    rw [ContrMod.mulVec_val, mulVec_eq_sum]
    simp only [Finset.sum_apply, Pi.smul_apply, transpose_apply,
      MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  · intro r t h
    simp only [actionT_smul, _root_.map_smul, apply_smul, h, Finset.mul_sum, mul_left_comm]
  · intro t1 t2 h1 h2
    simp only [actionT_add, map_add, apply_add, h1, h2, mul_add, Finset.sum_add_distrib]


-- @@ L187-192 verbatim
lemma smul_eq_mulVec {d} (Λ : LorentzGroup d) (p : Vector d) :
    Λ • p = Λ.1 *ᵥ p := by
  funext i
  rw [smul_eq_sum, mulVec_eq_sum]
  simp only [op_smul_eq_smul, Finset.sum_apply, Pi.smul_apply, transpose_apply, smul_eq_mul,
    mul_comm]


-- @@ L194-195 verbatim
lemma smul_add {d : ℕ} (Λ : LorentzGroup d) (p q : Vector d) :
    Λ • (p + q) = Λ • p + Λ • q := by simp


-- @@ L197-200 verbatim
@[simp]
lemma smul_sub {d : ℕ} (Λ : LorentzGroup d) (p q : Vector d) :
    Λ • (p - q) = Λ • p - Λ • q := by
  rw [smul_eq_mulVec, smul_eq_mulVec, smul_eq_mulVec, Matrix.mulVec_sub]


-- @@ L202-204 verbatim
lemma smul_zero {d : ℕ} (Λ : LorentzGroup d) :
    Λ • (0 : Vector d) = 0 := by
  rw [smul_eq_mulVec, Matrix.mulVec_zero]


-- @@ L206-208 verbatim
lemma smul_neg {d : ℕ} (Λ : LorentzGroup d) (p : Vector d) :
    Λ • (-p) = - (Λ • p) := by
  rw [smul_eq_mulVec, smul_eq_mulVec, Matrix.mulVec_neg]


-- @@ L210-213 verbatim
lemma neg_smul {d} (Λ : LorentzGroup d) (p : Vector d) :
    (-Λ) • p = - (Λ • p) := by
  funext i
  simp [smul_eq_sum, neg_apply]


-- @@ L215-219 verbatim
lemma _root_.LorentzGroup.eq_of_action_vector_eq {d : ℕ}
    {Λ Λ' : LorentzGroup d} (h : ∀ p : Vector d, Λ • p = Λ' • p) :
    Λ = Λ' := by
  apply LorentzGroup.eq_of_mulVec_eq
  simp_all [smul_eq_mulVec]


-- @@ L221-225 verbatim
/-!

## B. The continuous action of the Lorentz group

-/


-- @@ L227-236 verbatim
/-- The Lorentz action on vectors as a continuous linear map. -/
def actionCLM {d : ℕ} (Λ : LorentzGroup d) :
    Vector d →L[ℝ] Vector d :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => Λ • v
      map_add' := smul_add Λ
      map_smul' := fun c v => by
        simp only [RingHom.id_apply]
        funext i
        simp only [smul_eq_sum, apply_smul, Finset.mul_sum, mul_left_comm]}


-- @@ L238-239 verbatim
lemma actionCLM_apply {d : ℕ} (Λ : LorentzGroup d) (p : Vector d) :
    actionCLM Λ p = Λ • p := rfl


-- @@ L241-244 verbatim
lemma actionCLM_injective {d : ℕ} (Λ : LorentzGroup d) :
    Function.Injective (actionCLM Λ) := by
  intro x1 x2
  simp [actionCLM_apply]


-- @@ L246-250 verbatim
lemma actionCLM_surjective {d : ℕ} (Λ : LorentzGroup d) :
    Function.Surjective (actionCLM Λ) := by
  intro x1
  use (actionCLM Λ⁻¹) x1
  simp [actionCLM_apply]


-- @@ L252-256 verbatim
lemma smul_basis {d : ℕ} (Λ : LorentzGroup d) (μ : Fin 1 ⊕ Fin d) :
    Λ • basis μ = ∑ ν, Λ.1 ν μ • basis ν := by
  funext i
  rw [smul_eq_sum, Fintype.sum_apply]
  simp [basis_apply, Finset.sum_ite_eq, Finset.sum_ite_eq']


-- @@ L258-258 verbatim
end Vector


-- @@ L260-260 verbatim
end Lorentz
