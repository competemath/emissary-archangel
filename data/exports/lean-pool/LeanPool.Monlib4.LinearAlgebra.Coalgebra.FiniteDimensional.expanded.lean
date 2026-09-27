/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import LeanPool.Monlib4.LinearAlgebra.Coalgebra.Lemmas
public import LeanPool.Monlib4.LinearAlgebra.Nacgor
public import LeanPool.Monlib4.LinearAlgebra.Ips.RankOne
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
import LeanPool.Monlib4.LinearAlgebra.Ips.TensorHilbert
import LeanPool.Monlib4.LinearAlgebra.MulPrimePrime
import LeanPool.Monlib4.LinearAlgebra.TensorProduct.BasicLemmas
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.Tactic.Positivity.Finset


-- @@ L18-22 verbatim
/-!
# LeanPool.Monlib4.LinearAlgebra.Coalgebra.FiniteDimensional

Imported Lean Pool material for `LeanPool.Monlib4.LinearAlgebra.Coalgebra.FiniteDimensional`.
-/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
variable {R A : Type*}

-- @@ L27-27 verbatim
local notation "lT" => LinearMap.lTensor

-- @@ L28-28 verbatim
local notation "rT" => LinearMap.rTensor

-- @@ L29-29 verbatim
local notation "m" => LinearMap.mul' R

-- @@ L30-30 verbatim
local notation "ϰ" => TensorProduct.assoc R

-- @@ L31-31 verbatim
local notation "τ" => TensorProduct.lid R

-- @@ L32-32 verbatim
local notation "η" => Algebra.linearMap R


-- @@ L34-34 verbatim
attribute [local instance] Algebra.ofIsScalarTowerSmulCommClass

-- @@ L35-35 verbatim
open scoped TensorProduct


-- @@ L37-40 verbatim
lemma algebraMapCLM_eq_ket_one {R A : Type*} [RCLike R] [NormedAddCommGroupOfRing A]
  [InnerProductSpace R A] [SMulCommClass R A A] [IsScalarTower R A A] :
  algebraMapCLM R A = ket R 1 :=
rfl


-- @@ L42-45 verbatim
lemma algebraMapCLM_adjoint_eq_bra_one {R A : Type*} [RCLike R] [NormedAddCommGroupOfRing A]
  [InnerProductSpace R A] [SMulCommClass R A A] [IsScalarTower R A A] [CompleteSpace A] :
  ContinuousLinearMap.adjoint (algebraMapCLM R A) = bra R 1 := by
  rw [algebraMapCLM_eq_ket_one, ← bra_adjoint_eq_ket, ContinuousLinearMap.adjoint_adjoint]


-- @@ L47-53 verbatim
lemma LinearMap.rTensor_adjoint {𝕜 A B C : Type*} [RCLike 𝕜]
  [NormedAddCommGroup A] [NormedAddCommGroup B] [NormedAddCommGroup C]
  [InnerProductSpace 𝕜 A] [InnerProductSpace 𝕜 B] [InnerProductSpace 𝕜 C]
  [FiniteDimensional 𝕜 A] [FiniteDimensional 𝕜 B] [FiniteDimensional 𝕜 C]
  (f : A →ₗ[𝕜] B) :
  adjoint (rTensor C f) = rTensor C (adjoint f) := by
  simp_rw [rTensor, TensorProduct.map_adjoint, adjoint_id]

-- @@ L54-60 verbatim
lemma LinearMap.lTensor_adjoint {𝕜 A B C : Type*} [RCLike 𝕜]
  [NormedAddCommGroup A] [NormedAddCommGroup B] [NormedAddCommGroup C]
  [InnerProductSpace 𝕜 A] [InnerProductSpace 𝕜 B] [InnerProductSpace 𝕜 C]
  [FiniteDimensional 𝕜 A] [FiniteDimensional 𝕜 B] [FiniteDimensional 𝕜 C]
  (f : A →ₗ[𝕜] B) :
  adjoint (lTensor C f) = lTensor C (adjoint f) := by
  simp_rw [lTensor, TensorProduct.map_adjoint, adjoint_id]


-- @@ L62-75 verbatim
lemma TensorProduct.rid_adjoint {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] :
  LinearMap.adjoint (TensorProduct.rid 𝕜 E).toLinearMap =
    (TensorProduct.rid 𝕜 E).symm.toLinearMap := by
  ext1
  apply @ext_inner_right 𝕜
  intro y
  simp only [LinearMap.adjoint_inner_left, LinearEquiv.coe_toLinearMap,
    TensorProduct.rid_symm_apply]
  exact y.inductionOn
    (fun α z => by
      simp only [TensorProduct.rid_tmul, TensorProduct.inner_tmul, RCLike.inner_apply,
        starRingEnd_apply, star_one, inner_smul_right, mul_comm, mul_one])
    (fun z w hz hw => by simp only [_root_.map_add, inner_add_right, hz, hw])



-- @@ L78-102 verbatim
@[reducible, instance]
noncomputable
def Coalgebra.ofFiniteDimensionalHilbertAlgebra
  [RCLike R] [NormedAddCommGroupOfRing A] [InnerProductSpace R A]
  [SMulCommClass R A A] [IsScalarTower R A A] [FiniteDimensional R A] :
  Coalgebra R A :=
{ comul :=
    (LinearMap.adjoint (LinearMap.mul' R A : (A ⊗[R] A) →ₗ[R] A) :
      A →ₗ[R] A ⊗[R] A)
  counit := (LinearMap.adjoint (Algebra.linearMap R A : R →ₗ[R] A) : A →ₗ[R] R)
  coassoc := by
    rw [← LinearMap.rTensor_adjoint, ← LinearMap.lTensor_adjoint,
      ← TensorProduct.assoc_symm_adjoint]
    simp_rw [← LinearMap.adjoint_comp, Algebra.mul_comp_rTensor_mul, LinearMap.comp_assoc]
    simp_all
  rTensor_counit_comp_comul := by
    rw [← LinearMap.rTensor_adjoint, ← LinearMap.adjoint_comp, Algebra.mul_comp_rTensor_unit,
      TensorProduct.lid_adjoint]
    rfl
  lTensor_counit_comp_comul := by
    rw [← LinearMap.lTensor_adjoint, ← LinearMap.adjoint_comp, Algebra.mul_comp_lTensor_unit,
      TensorProduct.rid_adjoint]
    rfl }

-- open scoped ofFiniteDimensionalHilbertAlgebra in

-- @@ L103-110 verbatim
lemma Coalgebra.comul_eq_mul_adjoint
  [RCLike R] [NormedAddCommGroupOfRing A] [InnerProductSpace R A]
  [SMulCommClass R A A] [IsScalarTower R A A] [FiniteDimensional R A] :
  Coalgebra.comul =
    (LinearMap.adjoint (LinearMap.mul' R A : (A ⊗[R] A) →ₗ[R] A) :
      A →ₗ[R] A ⊗[R] A) :=
rfl
-- open scoped ofFiniteDimensionalHilbertAlgebra in

-- @@ L111-115 verbatim
lemma Coalgebra.counit_eq_unit_adjoint
  [RCLike R] [NormedAddCommGroupOfRing A] [InnerProductSpace R A]
  [SMulCommClass R A A] [IsScalarTower R A A] [FiniteDimensional R A] :
  Coalgebra.counit = (LinearMap.adjoint (Algebra.linearMap R A : R →ₗ[R] A) : A →ₗ[R] R) :=
rfl


-- @@ L117-118 verbatim
open scoped InnerProductSpace
-- open scoped ofFiniteDimensionalHilbertAlgebra in

-- @@ L119-127 verbatim
lemma Coalgebra.inner_eq_counit' [RCLike R] [NormedAddCommGroupOfRing A] [InnerProductSpace R A]
  [SMulCommClass R A A] [IsScalarTower R A A] [FiniteDimensional R A] :
  (⟪(1 : A), ·⟫_R) = Coalgebra.counit := by
  simp_rw [Coalgebra.counit]
  ext
  apply ext_inner_left R
  intro a
  simp_rw [LinearMap.adjoint_inner_right, Algebra.linearMap_apply,
    Algebra.algebraMap_eq_smul_one, inner_smul_left, inner, mul_comm, starRingEnd_apply]


-- @@ L129-134 verbatim
lemma Coalgebra.counit_eq_bra_one [RCLike R] [NormedAddCommGroupOfRing A] [InnerProductSpace R A]
  [SMulCommClass R A A] [IsScalarTower R A A] [FiniteDimensional R A] :
  Coalgebra.counit = (bra R (1 : A)).toLinearMap := by
  have := FiniteDimensional.complete R A
  rw [counit_eq_unit_adjoint, ← algebraMapCLM_adjoint_eq_bra_one]
  rfl


-- @@ L136-153 expanded
open Coalgebra LinearMap TensorProduct in
theorem Coalgebra.rTensor_mul_comp_lTensor_comul [RCLike R] [NormedAddCommGroupOfRing A]
    [InnerProductSpace R A] [SMulCommClass R A A] [IsScalarTower R A A] [FiniteDimensional R A]
    (h : ∃ σ : A → A, ∀ x y z : A, ⟪x * y, z⟫_R = ⟪y, σ x * z⟫_R) :
    (LinearMap.rTensor A ((LinearMap.mul' R) A)) ∘ₗ
        ((TensorProduct.assoc R) A A A).symm.toLinearMap ∘ₗ (LinearMap.lTensor A comul) =
      comul ∘ₗ ((LinearMap.mul' R) A) :=
  by
  rw [TensorProduct.ext_iff']
  intro x y
  rw [TensorProduct.inner_ext_iff']
  intro a b
  simp_rw [comp_apply, lTensor_tmul]
  obtain ⟨σ, h⟩ := h
  obtain ⟨α, β, hy⟩ := TensorProduct.eq_span (comul y : A ⊗[R] A)
  simp_rw [← hy, tmul_sum, _root_.map_sum, sum_inner, LinearEquiv.coe_coe, assoc_symm_tmul,
    rTensor_tmul, mul'_apply, inner_tmul, h, ← inner_tmul, ← sum_inner, hy, comul_eq_mul_adjoint,
    LinearMap.adjoint_inner_left, mul'_apply, mul_assoc, h]
    -- open scoped ofFiniteDimensionalHilbertAlgebra in


-- @@ L154-161 expanded
theorem Coalgebra.rTensor_mul_comp_lTensor_mul_adjoint [RCLike R] [NormedAddCommGroupOfRing A]
    [InnerProductSpace R A] [SMulCommClass R A A] [IsScalarTower R A A] [FiniteDimensional R A]
    (h : ∃ σ : A → A, ∀ x y z : A, ⟪x * y, z⟫_R = ⟪y, σ x * z⟫_R) :
    (LinearMap.rTensor A ((LinearMap.mul' R) A)) ∘ₗ
        ((TensorProduct.assoc R) A A A).symm.toLinearMap ∘ₗ
          (LinearMap.lTensor A (LinearMap.adjoint ((LinearMap.mul' R) A))) =
      (LinearMap.adjoint ((LinearMap.mul' R) A)) ∘ₗ ((LinearMap.mul' R) A) :=
  Coalgebra.rTensor_mul_comp_lTensor_comul h


-- @@ L163-176 expanded
open Coalgebra LinearMap TensorProduct in
theorem Coalgebra.lTensor_mul_comp_rTensor_comul_of [RCLike R] [NormedAddCommGroupOfRing A]
    [InnerProductSpace R A] [SMulCommClass R A A] [IsScalarTower R A A] [FiniteDimensional R A]
    (h : ∃ σ : A → A, ∀ x y z : A, ⟪x * y, z⟫_R = ⟪y, σ x * z⟫_R) :
    (LinearMap.lTensor A ((LinearMap.mul' R) A)) ∘ₗ
        ((TensorProduct.assoc R) A A A).toLinearMap ∘ₗ (LinearMap.rTensor A comul) =
      comul ∘ₗ ((LinearMap.mul' R) A) :=
  by
  apply_fun adjoint using LinearEquiv.injective _
  simp_rw [comul_eq_mul_adjoint]
  let : NormedAddCommGroup (A ⊗[R] A) := by infer_instance
  let : InnerProductSpace R (A ⊗[R] A) := by infer_instance
  simp_rw [LinearMap.adjoint_comp]
  simp_rw [lTensor_adjoint, rTensor_adjoint, adjoint_adjoint, TensorProduct.assoc_adjoint,
    LinearMap.comp_assoc]
  exact Coalgebra.rTensor_mul_comp_lTensor_mul_adjoint h


-- @@ L178-186 expanded
open Coalgebra LinearMap TensorProduct in
theorem Coalgebra.lTensor_mul_comp_rTensor_mul_adjoint_of [RCLike R] [NormedAddCommGroupOfRing A]
    [InnerProductSpace R A] [SMulCommClass R A A] [IsScalarTower R A A] [FiniteDimensional R A]
    (h : ∃ σ : A → A, ∀ x y z : A, ⟪x * y, z⟫_R = ⟪y, σ x * z⟫_R) :
    (LinearMap.lTensor A ((LinearMap.mul' R) A)) ∘ₗ
        ((TensorProduct.assoc R) A A A).toLinearMap ∘ₗ
          (LinearMap.rTensor A (LinearMap.adjoint ((LinearMap.mul' R) A))) =
      LinearMap.adjoint ((LinearMap.mul' R) A) ∘ₗ ((LinearMap.mul' R) A) :=
  Coalgebra.lTensor_mul_comp_rTensor_comul_of h


-- @@ L188-196 verbatim
/-- Construct the Frobenius algebra structure from finite-dimensional Hilbert-algebra data. -/
@[reducible]
noncomputable def FiniteDimensionalCoAlgebraIsFrobeniusAlgebraOf
  [RCLike R] [NormedAddCommGroupOfRing A] [InnerProductSpace R A]
  [SMulCommClass R A A] [IsScalarTower R A A] [FiniteDimensional R A]
  (h : ∃ σ : A → A, ∀ x y z : A, ⟪x * y, z⟫_R = ⟪y, σ x * z⟫_R) :
    FrobeniusAlgebra R A where
  lTensor_mul_comp_rTensor_comul_commute := by
    rw [Coalgebra.lTensor_mul_comp_rTensor_comul_of h, Coalgebra.rTensor_mul_comp_lTensor_comul h]


-- @@ L198-198 verbatim
open CoalgebraStruct

-- @@ L199-204 verbatim
/-- Predicate for linear maps that preserve the counit and comultiplication. -/
structure LinearMap.IsCoalgHom {R A B : Type*}
  [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
  [CoalgebraStruct R A] [CoalgebraStruct R B] (x : A →ₗ[R] B) : Prop where
    counit_comp : counit ∘ₗ x = counit
    map_comp_comul : TensorProduct.map x x ∘ₗ comul = comul ∘ₗ x

-- @@ L205-209 verbatim
lemma LinearMap.isCoalgHom_iff {R A B : Type*}
  [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
  [CoalgebraStruct R A] [CoalgebraStruct R B] (x : A →ₗ[R] B) :
    x.IsCoalgHom ↔ counit ∘ₗ x = counit ∧ TensorProduct.map x x ∘ₗ comul = comul ∘ₗ x :=
⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩


-- @@ L211-215 verbatim
/-- Predicate for linear maps that preserve the unit and multiplication. -/
structure LinearMap.IsAlgHom {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] (x : A →ₗ[R] B) : Prop where
    comp_unit : x ∘ₗ Algebra.linearMap R A = Algebra.linearMap R B
    mul'_comp_map : (mul' R B) ∘ₗ (TensorProduct.map x x) = x ∘ₗ (mul' R A)

-- @@ L216-221 verbatim
lemma LinearMap.isAlgHom_iff {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] (x : A →ₗ[R] B) :
    x.IsAlgHom ↔
      x ∘ₗ Algebra.linearMap R A = Algebra.linearMap R B
        ∧ (mul' R B) ∘ₗ (TensorProduct.map x x) = x ∘ₗ (mul' R A) :=
⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩


-- @@ L223-229 verbatim
lemma AlgHom.isAlgHom
  {R A B : Type*} [CommSemiring R] [Semiring A]
  [Semiring B] [Algebra R A] [Algebra R B]
  (x : A →ₐ[R] B) :
  x.toLinearMap.IsAlgHom := by
  rw [LinearMap.isAlgHom_iff, commutes_with_mul'_iff, commutes_with_unit_iff]
  simp only [toLinearMap_apply, map_one, map_mul, implies_true, and_self]

-- @@ L230-235 verbatim
lemma AlgEquiv.isAlgHom
  {R A B : Type*} [CommSemiring R] [Semiring A]
  [Semiring B] [Algebra R A] [Algebra R B]
  (x : A ≃ₐ[R] B) :
  x.toLinearMap.IsAlgHom :=
AlgHom.isAlgHom x.toAlgHom


-- @@ L237-241 verbatim
variable {B : Type*} [RCLike R] [NormedAddCommGroupOfRing A] [NormedAddCommGroupOfRing B]
  [InnerProductSpace R A] [InnerProductSpace R B]
  [SMulCommClass R A A] [SMulCommClass R B B] [IsScalarTower R A A] [IsScalarTower R B B]
  [FiniteDimensional R A] [FiniteDimensional R B]
  (x : A →ₗ[R] B)


-- @@ L243-251 verbatim
theorem LinearMap.isAlgHom_iff_adjoint_isCoalgHom :
  x.IsAlgHom ↔ (LinearMap.adjoint x).IsCoalgHom := by
  simp_rw [isAlgHom_iff, isCoalgHom_iff, Coalgebra.counit_eq_unit_adjoint,
    Coalgebra.comul_eq_mul_adjoint, ← TensorProduct.map_adjoint, ← LinearMap.adjoint_comp]
  constructor
  · simp_all
  · rintro ⟨h1, h2⟩
    apply_fun adjoint at h1 h2
    simp_all


-- @@ L253-255 verbatim
theorem LinearMap.isCoalgHom_iff_adjoint_isAlgHom :
  x.IsCoalgHom ↔ (LinearMap.adjoint x).IsAlgHom := by
  rw [isAlgHom_iff_adjoint_isCoalgHom, adjoint_adjoint]
