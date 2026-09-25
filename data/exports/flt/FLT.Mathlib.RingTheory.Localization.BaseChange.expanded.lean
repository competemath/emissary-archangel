/-
Copyright (c) 2025 Matthew Jasper. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Jasper
-/

-- *TODO* should these simp lemmas be in mathlib?
module

public import Mathlib.RingTheory.Localization.BaseChange


-- @@ L12-16 verbatim
/-!
# Base Change

Material destined for Mathlib.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
namespace IsLocalization


-- @@ L22-22 verbatim
section


-- @@ L24-26 verbatim
variable {R : Type*} [CommSemiring R] (S : Submonoid R)
  (A : Type*) [CommSemiring A] [Algebra R A] [IsLocalization S A]
  (M₁ : Type*) [AddCommMonoid M₁] [Module R M₁] [Module A M₁] [IsScalarTower R A M₁]


-- @@ L28-29 verbatim
@[simp]
lemma moduleLid_symm_apply (m : M₁) : (moduleLid S A M₁).symm m = 1 ⊗ₜ[R] m := rfl


-- @@ L31-31 verbatim
variable (M₂ : Type*) [AddCommMonoid M₂] [Module R M₂] [Module A M₂] [IsScalarTower R A M₂]


-- @@ L33-35 verbatim
@[simp]
lemma map_moduleTensorEquiv_tmul (m₁ : M₁) (m₂ : M₂) :
    moduleTensorEquiv S A M₁ M₂ (m₁ ⊗ₜ[A] m₂) = m₁ ⊗ₜ[R] m₂ := rfl


-- @@ L37-39 verbatim
@[simp]
lemma map_moduleTensorEquiv_symm_tmul (m₁ : M₁) (m₂ : M₂) :
    (moduleTensorEquiv S A M₁ M₂).symm (m₁ ⊗ₜ[R] m₂) = m₁ ⊗ₜ[A] m₂ := rfl


-- @@ L41-41 verbatim
end


-- @@ L43-43 verbatim
section


-- @@ L45-45 verbatim
open TensorProduct


-- @@ L47-53 verbatim
variable {A : Type*} [CommSemiring A] (S : Submonoid A)
  (B : Type*) [CommSemiring B] [Algebra A B]
  (K : Type*) [CommSemiring K] [Algebra A K] [IsLocalization S K]
  (L : Type*) [CommSemiring L] [Algebra B L] [Algebra A L] [Algebra K L] [IsScalarTower A B L]
    [IsScalarTower A K L] [IsLocalizedModule (M := B) (M' := L) S (Algebra.linearMap B L)]
  (M : Type*) [AddCommMonoid M] [Module K M]
  (P : Type*) [AddCommMonoid P] [Module K P]


-- @@ L55-64 verbatim
include S in
theorem tensorProduct_ext {g h : L ⊗[K] M →ₗ[K] P}
    (H : ∀ (x : B) (y : M), g ((algebraMap _ L x) ⊗ₜ[K] y) = h ((algebraMap _ L x) ⊗ₜ[K] y))
    : g = h := by
  apply TensorProduct.ext'
  intro l m
  obtain ⟨⟨x, s⟩, hl : (s : A) • l = algebraMap B L x⟩ :=
    IsLocalizedModule.surj (M:=B) (M':=L) S (Algebra.linearMap B L) l
  rw [← IsUnit.smul_left_cancel <| map_units K s]
  simpa [← map_smul, TensorProduct.smul_tmul', IsScalarTower.algebraMap_smul K, hl] using H x m


-- @@ L66-82 verbatim
/-- If `A` is a localization of R, tensoring two A-modules over A is the same as tensoring
them over R. This is `IsLocalization.moduleTensorEquiv` as an `M₁`-linear equivalence (more
generally an `M'`-linear equivalence where `M₁` is an `M'`-module). -/
@[simps!]
noncomputable def leftModuleTensorEquiv {R : Type*} (M' : Type*)
    [Semiring M'] [CommSemiring R] (S : Submonoid R) (A : Type*) [CommSemiring A] [Algebra R A]
    [IsLocalization S A] (M₁ : Type*) (M₂ : Type*) [AddCommMonoid M₁] [AddCommMonoid M₂]
    [Module M' M₁] [Module R M₁] [Module R M₂] [Module A M₁] [Module A M₂]
    [SMulCommClass A M' M₁] [SMulCommClass R M' M₁] [IsScalarTower R A M₁]
    [IsScalarTower R A M₂] :
    M₁ ⊗[A] M₂ ≃ₗ[M'] M₁ ⊗[R] M₂ where
  __ := IsLocalization.moduleTensorEquiv S A M₁ M₂
  map_smul' r x := by
    induction x with
    | zero => simp
    | tmul m₁ m₂ => simp [TensorProduct.smul_tmul']
    | add => simp_all


-- @@ L84-92 verbatim
lemma leftModuleTensorEquiv_restrictScalars_eq {R M' : Type*} [CommSemiring M']
    [CommSemiring R] (S : Submonoid R) (A : Type*) [CommSemiring A] [Algebra R A] [Algebra A M']
    [Algebra M' R] [IsLocalization S A] (M₁ : Type*) (M₂ : Type*) [AddCommMonoid M₁]
    [AddCommMonoid M₂] [Module M' M₁] [Module R M₁] [Module R M₂] [Module A M₁]
    [Module A M₂] [IsScalarTower A M' M₁] [IsScalarTower M' R M₁] [IsScalarTower R A M₁]
    [IsScalarTower R A M₂] :
    (IsLocalization.leftModuleTensorEquiv M' S A M₁ M₂).restrictScalars A =
      IsLocalization.moduleTensorEquiv S A M₁ M₂ := by
  rfl


-- @@ L94-94 verbatim
end


-- @@ L96-96 verbatim
end IsLocalization
