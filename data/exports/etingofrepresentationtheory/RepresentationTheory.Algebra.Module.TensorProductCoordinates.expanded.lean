/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import RepresentationTheory.Algebra.Module.TensorScalarExtension
import RepresentationTheory.Alignment.Attribute


-- @@ L10-10 verbatim
/-! # Tensor-product coordinates -/


-- @@ L12-12 verbatim
open scoped TensorProduct


-- @@ L14-14 verbatim
namespace RepresentationTheory.Algebra.Module.TensorProductCoordinates


-- @@ L16-19 verbatim
variable {K A V L : Type*}
  [Field K] [Ring A] [Algebra K A]
  [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower K A V]
  [Field L] [Algebra K L]


-- @@ L21-28 verbatim
/-- The displayed tensor-product-algebra action on a pure tensor with unit scalar acts on its module factor. -/
theorem tensorProductAction_tmul_one (a : A) (l : L) (v : V) :
    RepresentationTheory.Algebra.Module.TensorScalarExtension.tensorProductAction
      (A := A) (V := V) (L := L) (1 ⊗ₜ[K] a) (l ⊗ₜ[K] v) = l ⊗ₜ[K] (a • v) := by
  rw [RepresentationTheory.Algebra.Module.TensorScalarExtension.tensorProductAction,
    AlgHom.liftEquiv_tmul, one_smul]
  simp [RepresentationTheory.Algebra.Module.TensorScalarExtension.scalarExtendedAction,
    Module.End.baseChangeHom, LinearMap.baseChange_tmul, Algebra.lsmul_apply]


-- @@ L30-30 verbatim
section Pow


-- @@ L32-32 verbatim
variable {n : ℕ}


-- @@ L34-39 verbatim
/-- A basis of a field extension gives a linear equivalence from a tensor product to a finite function module. -/
noncomputable def linearEquivFinFunOfBasis (b : Module.Basis (Fin n) K L) :
    (L ⊗[K] V) ≃ₗ[K] (Fin n → V) :=
  (TensorProduct.comm K L V) ≪≫ₗ
    (TensorProduct.congr (LinearEquiv.refl K V) b.equivFun) ≪≫ₗ
    (TensorProduct.piScalarRight K K V (Fin n))


-- @@ L41-47 verbatim
/-- The basis-induced linear equivalence sends a pure tensor to its coefficient function times the module factor. -/
@[simp]
theorem linearEquivFinFunOfBasis_tmul (b : Module.Basis (Fin n) K L) (l : L) (v : V) :
    linearEquivFinFunOfBasis b (l ⊗ₜ[K] v) = fun i => b.repr l i • v := by
  simp only [linearEquivFinFunOfBasis, LinearEquiv.trans_apply, TensorProduct.comm_tmul,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply, Module.Basis.equivFun_apply,
    TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]


-- @@ L49-49 verbatim
end Pow


-- @@ L51-54 verbatim
/-- An A-module structure on the tensor product of an extension field with an A-module. -/
noncomputable instance tensorProductModule : Module A (L ⊗[K] V) :=
  Module.compHom (L ⊗[K] V)
    (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := A)).toRingHom


-- @@ L56-60 verbatim
/-- The restricted scalar action agrees with the action induced by the right tensor-product inclusion. -/
theorem smul_eq_includeRight_smul (a : A) (x : L ⊗[K] V) :
    (a • x : L ⊗[K] V) =
      (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := A) a) • x :=
  rfl


-- @@ L62-67 verbatim
/-- The tensor-product-algebra scalar action agrees with the displayed algebra homomorphism action. -/
theorem tensorProductAlgebra_smul_eq_action (y : L ⊗[K] A) (x : L ⊗[K] V) :
    (y • x : L ⊗[K] V) =
      RepresentationTheory.Algebra.Module.TensorScalarExtension.tensorProductAction
        (A := A) (V := V) (L := L) y x :=
  rfl


-- @@ L69-73 verbatim
/-- Scalar multiplication on a pure tensor acts on its module factor. -/
theorem smul_tmul (a : A) (l : L) (v : V) :
    (a • (l ⊗ₜ[K] v) : L ⊗[K] V) = l ⊗ₜ[K] (a • v) := by
  rw [smul_eq_includeRight_smul, tensorProductAlgebra_smul_eq_action,
    Algebra.TensorProduct.includeRight_apply, tensorProductAction_tmul_one]


-- @@ L75-75 verbatim
section Pow


-- @@ L77-77 verbatim
variable {n : ℕ}


-- @@ L79-94 verbatim
/-- A chosen basis of the extending field gives a linear map from the tensor product to a finite function module. -/
noncomputable def linearMapFinFun (b : Module.Basis (Fin n) K L) :
    (L ⊗[K] V) →ₗ[A] (Fin n → V) where
  toFun := linearEquivFinFunOfBasis b
  map_add' := (linearEquivFinFunOfBasis b).map_add
  map_smul' a x := by
    simp only [RingHom.id_apply]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul l v =>
      rw [smul_tmul, linearEquivFinFunOfBasis_tmul, linearEquivFinFunOfBasis_tmul]
      funext i
      simp only [Pi.smul_apply]
      exact smul_comm (b.repr l i) a v
    | add x y hx hy =>
      rw [smul_add, map_add, map_add, hx, hy, smul_add]


-- @@ L96-99 verbatim
/-- A chosen basis of the extending field gives a linear equivalence from the tensor product to a finite function module. -/
noncomputable def linearEquivFinFun (b : Module.Basis (Fin n) K L) :
    (L ⊗[K] V) ≃ₗ[A] (Fin n → V) :=
  LinearEquiv.ofBijective (linearMapFinFun b) (linearEquivFinFunOfBasis b).bijective


-- @@ L101-101 verbatim
end Pow


-- @@ L103-107 verbatim
/-- The scalar-extended module is linearly equivalent to functions indexed by the dimension of the extending field. -/
@[source_ref "Chapter3/Problem3.8.4" (role := supporting)]
theorem nonempty_linearEquiv_fin_fun [FiniteDimensional K L] :
    Nonempty ((L ⊗[K] V) ≃ₗ[A] (Fin (Module.finrank K L) → V)) :=
  ⟨linearEquivFinFun (Module.finBasis K L)⟩


-- @@ L109-109 verbatim
end RepresentationTheory.Algebra.Module.TensorProductCoordinates
