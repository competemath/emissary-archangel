/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Salvatore Mercuri, Pietro Monticone
-/
module

public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import FLT.Mathlib.LinearAlgebra.Pi
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.Tactic.Positivity.Finset


-- @@ L16-20 verbatim
/-!
# Equiv

Material destined for Mathlib.
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-45 verbatim
/-- Let `f : α → β` be a function on index types. A family of `R b`-linear homeomorphisms, indexed
by `b : β`, between the product over the fiber of `b` under `f` given as
`∀ (σ : { a : α // f a = b }) → γ₁ σ.1) ≃ₗ[R b] γ₂ b` lifts to an equivalence over the products
`∀ a, γ₁ a ≃ₗ[∀ b, R b] ∀ b, γ₂ b` with product scalars `∀ b, R b`, provided that `∀ b, R b` acts on
`∀ a, γ₁ a` fiberwise. This is `Equiv.piCongrFiberwise` as a `ContinuousLinearEquiv` with product
scalars. -/
def ContinuousLinearEquiv.piScalarPiCongrFiberwise {α : Type*} {β : Type*} {R : β → Type*}
    {γ₁ : α → Type*} {γ₂ : β → Type*} {f : α → β} [(a : α) → TopologicalSpace (γ₁ a)]
    [(b : β) → TopologicalSpace (γ₂ b)] [(b : β) → Semiring (R b)] [(a : α) → AddCommMonoid (γ₁ a)]
    [(b : β) → AddCommMonoid (γ₂ b)] [(b : β) → (a : { a : α // f a = b }) → Module (R b) (γ₁ a)]
    [(b : β) → Module (R b) (γ₂ b)] [Module ((b : β) → R b) ((a : α) → γ₁ a)]
    [Pi.FiberwiseSMul f R γ₁]
    (e : (b : β) → ((σ : { a : α // f a = b }) → γ₁ σ.1) ≃L[R b] γ₂ b) :
    ((a : α) → γ₁ a) ≃L[∀ b, R b] ((b : β) → γ₂ b) where
  __ := LinearEquiv.piScalarPiCongrFiberwise fun b => (e b).toLinearEquiv
  continuous_invFun := by
    change Continuous (fun (g : (b : β) → γ₂ b) a ↦ (e (f a)).symm (g (f a)) ⟨a, rfl⟩)
    fun_prop
  continuous_toFun := by
    change Continuous (fun (x : (a : α) → γ₁ a) ↦
      Pi.map (fun a ↦ ⇑(e a)) fun _ y ↦ (fun _ ↦ x _) _)
    fun_prop


-- @@ L47-60 verbatim
/-- Given `φ : α → β → Type*` and `R : α → Type*` such that `φ a b` is an `R a` module for all
`a b`, this is the continuous linear equivalence between `∀ a b, φ a b` and `∀ b a, φ a b` with
product scalars. This is `Equiv.piComm` as a product-scalar `ContinuousLinearEquiv`. -/
def ContinuousLinearEquiv.piScalarPiComm {α β : Type*} (R : α → Type*) (φ : α → β → Type*)
    [(a : α) → Semiring (R a)] [(a : α) → (b : β) → AddCommMonoid (φ a b)]
    [(a : α) → (b : β) → Module (R a) (φ a b)] [(a : α) → (b : β) → TopologicalSpace (φ a b)] :
    ((a : α) → (b : β) → φ a b) ≃L[∀ a, R a] ((b : β) → (a : α) → φ a b) where
  __ := LinearEquiv.piScalarPiComm R φ
  continuous_toFun := by
    change Continuous (fun (x : (a : α) → (b : β) → φ a b) ↦ Function.swap x)
    fun_prop
  continuous_invFun := by
    change Continuous (fun x ↦ Function.swap x)
    fun_prop


-- @@ L62-66 verbatim
lemma ContinuousLinearEquiv.toContinuousAddEquiv_trans
    {R : Type*} {E : Type*} [Semiring R] [AddCommMonoid E] [Module R E]
    [TopologicalSpace E] {e f : E ≃L[R] E} :
    (e.trans f).toContinuousAddEquiv =
      e.toContinuousAddEquiv.trans f.toContinuousAddEquiv := rfl


-- @@ L68-72 verbatim
lemma ContinuousLinearEquiv.toMatrix_isUnit_det
    {F : Type*} [CommRing F] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : Type*} [AddCommGroup V] [Module F V] [TopologicalSpace V]
    (b : Module.Basis ι F V) (ρ : V ≃L[F] V) :
    IsUnit ((ρ.toLinearMap.toMatrix b b).det) := LinearEquiv.isUnit_det ρ.toLinearEquiv b b


-- @@ L74-80 verbatim
lemma ContinuousLinearEquiv.toMatrix_isUnit
    {F : Type*} [CommRing F] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : Type*} [AddCommGroup V] [Module F V] [TopologicalSpace V]
    (b : Module.Basis ι F V) (ρ : V ≃L[F] V) :
    IsUnit (ρ.toLinearMap.toMatrix b b) :=
  (Matrix.isUnit_iff_isUnit_det (ρ.toLinearMap.toMatrix b b)).mpr
    (toMatrix_isUnit_det b ρ)


-- @@ L82-87 verbatim
lemma ContinuousLinearEquiv.toMatrix_det_ne_zero
    {F : Type*} [CommRing F] [Nontrivial F] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : Type*} [AddCommGroup V] [Module F V] [TopologicalSpace V]
    (b : Module.Basis ι F V) (ρ : V ≃L[F] V) :
    (ρ.toLinearMap.toMatrix b b).det ≠ 0 :=
  IsUnit.ne_zero (ContinuousLinearEquiv.toMatrix_isUnit_det b ρ)


-- @@ L89-89 verbatim
section toContinuousLinearEquiv


-- @@ L91-91 verbatim
variable {F : Type*} [CommRing F] [TopologicalSpace F]

-- @@ L92-92 verbatim
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- @@ L93-93 verbatim
variable {V : Type*} [AddCommGroup V] [Module F V] [TopologicalSpace V]

-- @@ L94-94 verbatim
variable [IsModuleTopology F V] [ContinuousAdd V]


-- @@ L96-96 verbatim
namespace Matrix


-- @@ L98-108 verbatim
/-- Given `M : Matrix ι ι F`, `b : Module.Basis ι F V` and `h : M.det ≠ 0`,
  this is the continuous linear equivalence arising from
  `Matrix.toLinearEquiv b M (Ne.isUnit h)` -/
noncomputable def toContinuousLinearEquiv
    (M : Matrix ι ι F) (b : Module.Basis ι F V) (h : IsUnit M.det) : V ≃L[F] V :=
  let e := Matrix.toLinearEquiv b M h
  have ce : Continuous e :=
    IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have ce_inv : Continuous e.symm :=
    IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  ⟨e, ce, ce_inv⟩


-- @@ L110-113 verbatim
@[simp]
lemma toContinousLinearEquiv_apply
    (M : Matrix ι ι F) (b : Module.Basis ι F V) (h : IsUnit M.det) (x : V) :
    (M.toContinuousLinearEquiv b h) x = toLin b b M x := rfl


-- @@ L115-118 verbatim
@[simp]
lemma toContinuousLinearEquiv_toLin_coe
    (M : Matrix ι ι F) (b : Module.Basis ι F V) (h : IsUnit M.det) :
    ⇑(M.toContinuousLinearEquiv b h) = ⇑(toLin b b M) := rfl


-- @@ L120-123 verbatim
@[simp]
lemma toContinuousLinearEquiv_toLinearEquiv
    (b : Module.Basis ι F V) (M : Matrix ι ι F) (h : IsUnit M.det) :
    (M.toContinuousLinearEquiv b h).toLinearEquiv = Matrix.toLinearEquiv b M h := rfl


-- @@ L125-128 verbatim
lemma toContinousLinearEquiv_toMatrix
    (b : Module.Basis ι F V) (M : Matrix ι ι F) (h : IsUnit M.det) :
    (M.toContinuousLinearEquiv b h ).toLinearMap.toMatrix b b = M :=
  (LinearEquiv.eq_symm_apply (LinearMap.toMatrix b b)).mp rfl


-- @@ L130-137 verbatim
lemma toContinousLinearEquiv_mul
    (b : Module.Basis ι F V)
    (A : Matrix ι ι F) (hA : IsUnit A.det) (B : Matrix ι ι F) (hB : IsUnit B.det) :
    have hAB : IsUnit (A * B).det := by rw[Matrix.det_mul]; exact IsUnit.mul hA hB
    (A * B).toContinuousLinearEquiv b hAB =
    (B.toContinuousLinearEquiv b hB).trans (A.toContinuousLinearEquiv b hA) := by
  ext x
  simp [ContinuousLinearEquiv.trans_apply, Matrix.toLin_mul b b]


-- @@ L139-139 verbatim
end Matrix


-- @@ L141-146 verbatim
lemma ContinuousLinearEquiv.toMatrix_toContinousLinearEquiv
    (b : Module.Basis ι F V) (ρ : V ≃L[F] V) :
    (ρ.toLinearEquiv.toMatrix b b).toContinuousLinearEquiv b
    (ContinuousLinearEquiv.toMatrix_isUnit_det b ρ ) = ρ := by
  ext
  simp


-- @@ L148-151 verbatim
theorem ContinuousLinearEquiv.toContinuousAddEquiv_apply {R : Type*} {M N : Type*}
    [Semiring R] [TopologicalSpace M] [TopologicalSpace N] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N]
    (f : M ≃L[R] N) (m : M) : f.toContinuousAddEquiv m = f m := rfl


-- @@ L153-153 verbatim
end toContinuousLinearEquiv
