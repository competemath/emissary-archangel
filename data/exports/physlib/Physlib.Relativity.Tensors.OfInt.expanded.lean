/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.Basic

-- @@ L9-13 verbatim
/-!

# Basis for tensors in a tensor species

-/


-- @@ L15-15 verbatim
@[expose] public section


-- @@ L17-17 verbatim
open Module


-- @@ L19-19 verbatim
namespace TensorSpecies


-- @@ L21-25 verbatim
variable {k : Type} [CommRing k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}
    (S : TensorSpecies k C G V basisIdx rep b)


-- @@ L27-27 verbatim
namespace Tensor


-- @@ L29-30 verbatim
/-- A tensor with integer components with respect to the basis. -/
abbrev TensorInt {n : ℕ} (c : Fin n → C) := (ComponentIdx (S := S) c) → ℤ


-- @@ L32-32 verbatim
namespace TensorInt


-- @@ L34-34 verbatim
variable {S : TensorSpecies k C G V basisIdx rep b}


-- @@ L36-40 verbatim
/-- The element of `S.Tensor c` created from a tensor `TensorInt S c`. -/
noncomputable def toTensor {n : ℕ} {c : Fin n → C} (f : TensorInt S c) :
    S.Tensor c := (Tensor.basis c).repr.symm <|
  (Finsupp.linearEquivFunOnFinite k k ((j : Fin n) → basisIdx (c j))).symm <|
  (fun j => Int.cast (f j))


-- @@ L42-46 verbatim
lemma basis_repr_apply {n : ℕ} {c : Fin n → C}
    (f : TensorInt S c) (b : ComponentIdx c) :
    (Tensor.basis c).repr (toTensor f) b = Int.cast (f b) := by
  simp only [toTensor, Basis.repr_symm_apply, Basis.repr_linearCombination]
  rfl


-- @@ L48-48 verbatim
end TensorInt


-- @@ L50-57 verbatim
lemma basis_eq_tensorInt {n : ℕ} {c : Fin n → C}
    (b : ComponentIdx c) :
    Tensor.basis c b = TensorInt.toTensor (S := S) (fun b' => if b = b' then 1 else 0) := by
  apply (Tensor.basis c).repr.injective
  simp only [Basis.repr_self]
  ext b'
  simp only [TensorInt.basis_repr_apply, Int.cast_ite, Int.cast_one, Int.cast_zero]
  rw [Finsupp.single_apply]


-- @@ L59-59 verbatim
end Tensor


-- @@ L61-61 verbatim
end TensorSpecies
