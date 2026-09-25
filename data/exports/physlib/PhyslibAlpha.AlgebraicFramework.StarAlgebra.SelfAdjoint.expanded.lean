/-
Copyright (c) 2026 David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Star.Module
public import PhyslibAlpha.AlgebraicFramework.OrderUnit.Channel.Basic


-- @@ L13-21 verbatim
/-!

# Basic results on self-adjoint elements

Mathlib provides several formulations of self-adjointness. This module relates
`IsSelfAdjoint x`, `x ∈ selfAdjoint A`, and the two module structures on
self-adjoint elements.

-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
namespace selfAdjoint


-- @@ L27-29 verbatim
@[simp]
lemma mem_selfAdjoint_iff_isSelfAdjoint {R : Type*} [AddGroup R] [StarAddMonoid R] (x : R) :
    x ∈ selfAdjoint R ↔ IsSelfAdjoint x := isSelfAdjoint_iff.trans selfAdjoint.mem_iff.symm


-- @@ L31-32 verbatim
variable {R A : Type*} [Semiring R] [StarMul R] [TrivialStar R]
  [AddCommGroup A] [Module R A] [StarAddMonoid A] [StarModule R A]


-- @@ L34-36 verbatim
@[simp]
lemma submodule_mem_iff {x : A} : (x ∈ submodule R A) ↔ (x ∈ selfAdjoint A) := by
  rfl


-- @@ L38-44 verbatim
/-- The linear equivalence that forgets the `Submodule` structure on self-adjoint elements. -/
@[simps!]
def submoduleEquiv : selfAdjoint.submodule R A ≃ₗ[R] selfAdjoint A where
  toFun x := ⟨x.val, submodule_mem_iff.mp x.prop⟩
  invFun x := ⟨x.val, submodule_mem_iff.mpr x.prop⟩
  map_add' _ _ := by simp
  map_smul' _ _ := by ext; simp


-- @@ L46-46 verbatim
variable [PartialOrder A]


-- @@ L48-51 verbatim
/-- Forget the `Submodule` structure as a positive linear map. -/
@[simps!]
def submodulePLM : submodule R A →ₚ[R] selfAdjoint A :=
  { selfAdjoint.submoduleEquiv.toLinearMap with monotone' a b hab := by simpa }


-- @@ L53-57 verbatim
variable (R) in
/-- Inverse of `submodulePLM`. (There is no `PositiveLinearEquivalence` type.) -/
@[simps!]
def submodulePLMSymm : selfAdjoint A →ₚ[R] submodule R A :=
  { selfAdjoint.submoduleEquiv.symm.toLinearMap with monotone' a b hab := by simpa }


-- @@ L59-60 verbatim
variable {R A : Type*} [Semiring R] [StarMul R] [TrivialStar R]
  [Ring A] [StarRing A] [Module R A] [StarModule R A]


-- @@ L62-63 verbatim
instance : One (submodule R A) :=
  ⟨⟨1, .one _⟩⟩


-- @@ L65-65 verbatim
@[simp] lemma val_one_submodule : ↑(1 : submodule R A) = (1 : A) := rfl

-- @@ L66-66 verbatim
@[simp] lemma submoduleEquiv_one : ↑(submoduleEquiv (R := R) (A := A) 1) = 1 := rfl

-- @@ L67-67 verbatim
@[simp] lemma submoduleEquiv_symm_one : ↑(submoduleEquiv (R := R) (A := A).symm 1) = 1 := rfl


-- @@ L69-69 verbatim
variable [PartialOrder A]


-- @@ L71-74 expanded
/-- Forget the `Submodule` structure as a unital positive linear map. -/
@[simps! apply]
def submoduleUPLM : UnitalPositiveLinearMap R (submodule R A) (selfAdjoint A) :=
  { submoduleEquiv.toLinearMap with monotone' a b hab := by simpa, map_one' := by simp }


-- @@ L76-79 expanded
variable (R) in
/-- Inverse of `submoduleUPLM`. (There is no `UnitalPositiveLinearEquivalence` type.) -/
def submoduleUPLMSymm : UnitalPositiveLinearMap R (selfAdjoint A) (submodule R A) :=
  { submoduleEquiv.symm.toLinearMap with monotone' a b hab := by simpa, map_one' := by simp }


-- @@ L81-81 verbatim
end selfAdjoint


-- @@ L83-83 verbatim
open ComplexOrder


-- @@ L85-90 expanded
/-- The map from self-adjoint complex numbers to real numbers as a unital positive linear map. -/
@[simps!]
noncomputable def Complex.selfAdjointUPLM : UnitalPositiveLinearMap ℝ (selfAdjoint ℂ) ℝ
    where
  toLinearMap := Complex.selfAdjointEquiv.toLinearMap
  monotone' a b hab := by simp; gcongr
  map_one' := by simp

