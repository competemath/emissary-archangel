/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import RepresentationTheory.Alignment.Attribute


-- @@ L15-15 verbatim
/-! # Hom--tensor equivalences for Lie modules -/


-- @@ L17-17 verbatim
namespace RepresentationTheory.LieModule.HomTensorAdjunction


-- @@ L19-19 verbatim
open scoped TensorProduct


-- @@ L21-21 verbatim
variable {k : Type*} [Field k]

-- @@ L22-22 verbatim
variable {L : Type*} [LieRing L] [LieAlgebra k L]

-- @@ L23-27 verbatim
variable {V W U : Type*}
  [AddCommGroup V] [Module k V] [LieRingModule L V] [LieModule k L V]
  [AddCommGroup W] [Module k W] [LieRingModule L W] [LieModule k L W]
  [AddCommGroup U] [Module k U] [LieRingModule L U] [LieModule k L U]
  [FiniteDimensional k V] [FiniteDimensional k W] [FiniteDimensional k U]


-- @@ L29-49 verbatim
/-- A Lie-module equivalence identifies the linear-map module with the tensor product of the target
and the dual of the finite-dimensional source. -/
@[nolint defsWithUnderscore]
noncomputable def linearMapLieModuleEquivTensorDual :
    (W →ₗ[k] U) ≃ₗ⁅k,L⁆ TensorProduct k U (Module.Dual k W) :=
  LieModuleEquiv.symm
    { (TensorProduct.comm k U (Module.Dual k W)).trans (dualTensorHomEquiv k W U) with
      map_lie' := by
        intro x t
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul u φ =>
          ext w
          simp only [LinearMap.toFun_eq_coe, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
            TensorProduct.LieModule.lie_tmul_right, map_add, TensorProduct.comm_tmul,
            dualTensorHomEquiv, dualTensorHomEquivOfBasis_apply, dualTensorHom_apply,
            LinearMap.add_apply, Module.Dual.lie_apply, LieHom.lie_apply, lie_smul, neg_smul]
          abel
        | add a b ha hb =>
          simp only [LinearMap.toFun_eq_coe, LinearEquiv.coe_coe] at ha hb ⊢
          simp only [lie_add, map_add, ha, hb] }


-- @@ L51-62 verbatim
/-- Transfers equivariant linear maps along an equivalence of their target Lie modules. -/
@[nolint defsWithUnderscore]
def lieModuleHomCongr {B C : Type*}
    [AddCommGroup B] [Module k B] [LieRingModule L B] [LieModule k L B]
    [AddCommGroup C] [Module k C] [LieRingModule L C] [LieModule k L C]
    (d : B ≃ₗ⁅k,L⁆ C) : (V →ₗ⁅k,L⁆ B) ≃ₗ[k] (V →ₗ⁅k,L⁆ C) where
  toFun f := (d : B →ₗ⁅k,L⁆ C).comp f
  map_add' f g := by ext v; simp [LieModuleHom.comp_apply]
  map_smul' c f := by ext v; simp [LieModuleHom.comp_apply]
  invFun g := (d.symm : C →ₗ⁅k,L⁆ B).comp g
  left_inv f := by ext v; simp [LieModuleHom.comp_apply]
  right_inv g := by ext v; simp [LieModuleHom.comp_apply]


-- @@ L64-70 verbatim
/-- The equivariant Hom--tensor-dual equivalence for a finite-dimensional middle Lie module. -/
@[nolint defsWithUnderscore, source_ref "Chapter2/Problem2.14.3" (role := primary)]
noncomputable def lieModuleHomTensorDualEquiv :
    (TensorProduct k V W →ₗ⁅k,L⁆ U) ≃ₗ[k]
      (V →ₗ⁅k,L⁆ TensorProduct k U (Module.Dual k W)) :=
  (TensorProduct.LieModule.liftLie k L V W U).symm.trans
    (lieModuleHomCongr linearMapLieModuleEquivTensorDual)


-- @@ L72-77 verbatim
omit [FiniteDimensional k V] [FiniteDimensional k U] in
/-- Establishes existence of the equivariant Hom--tensor-dual linear equivalence. -/
theorem nonempty_lieModuleHomTensorDualEquiv :
    Nonempty ((TensorProduct k V W →ₗ⁅k,L⁆ U) ≃ₗ[k]
      (V →ₗ⁅k,L⁆ TensorProduct k U (Module.Dual k W))) :=
  ⟨lieModuleHomTensorDualEquiv⟩


-- @@ L79-79 verbatim
end RepresentationTheory.LieModule.HomTensorAdjunction
