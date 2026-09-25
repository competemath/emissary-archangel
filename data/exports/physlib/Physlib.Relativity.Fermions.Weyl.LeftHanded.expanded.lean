/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Physlib.Meta.TODO.Basic
public import Physlib.Relativity.SL2C.Basic
public import Physlib.Meta.Informal.Basic
public import Physlib.Meta.TODO.Basic

-- @@ L13-22 verbatim
/-!

## Left handed Weyl fermions


In this file we define Left handed Weyl fermions.
These sit in the fundamental representation of `SL(2,ℂ)`,
and we consider them to have up indices `ψ^α` with `α = 1,2`.

-/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
namespace Fermion

-- @@ L27-27 verbatim
noncomputable section


-- @@ L29-29 verbatim
section LeftHanded


-- @@ L31-34 verbatim
/-- The module in which left handed fermions live. This is equivalent to `Fin 2 → ℂ`. -/
structure LeftHandedWeyl where
  /-- The underlying value in `Fin 2 → ℂ`. -/
  val : Fin 2 → ℂ


-- @@ L36-36 verbatim
namespace LeftHandedWeyl

-- @@ L37-37 verbatim
open Module Matrix

-- @@ L38-38 verbatim
open MatrixGroups

-- @@ L39-39 verbatim
open Complex

-- @@ L40-40 verbatim
open TensorProduct


-- @@ L42-46 verbatim
/-!

## Underlying module structure

-/


-- @@ L48-53 verbatim
/-- The equivalence between `LeftHandedWeyl` and `Fin 2 → ℂ`. -/
def toFin2ℂFun : LeftHandedWeyl ≃ (Fin 2 → ℂ) where
  toFun v := v.val
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl


-- @@ L55-57 verbatim
/-- The instance of `AddCommMonoid` on `LeftHandedWeyl` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : AddCommMonoid LeftHandedWeyl := Equiv.addCommMonoid toFin2ℂFun


-- @@ L59-61 verbatim
/-- The instance of `AddCommGroup` on `LeftHandedWeyl` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : AddCommGroup LeftHandedWeyl := Equiv.addCommGroup toFin2ℂFun


-- @@ L63-65 verbatim
/-- The instance of `Module` on `LeftHandedWeyl` defined via its equivalence
  with `Fin 2 → ℂ`. -/
instance : Module ℂ LeftHandedWeyl := Equiv.module ℂ toFin2ℂFun


-- @@ L67-75 verbatim
/-- The linear equivalence between `LeftHandedWeyl` and `(Fin 2 → ℂ)`. -/
@[simps!]
def toFin2ℂEquiv : LeftHandedWeyl ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun := toFin2ℂFun
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  invFun := toFin2ℂFun.symm
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl


-- @@ L77-79 verbatim
/-- The underlying element of `Fin 2 → ℂ` of a element in `LeftHandedWeyl` defined
  through the linear equivalence `toFin2ℂEquiv`. -/
abbrev toFin2ℂ (ψ : LeftHandedWeyl) := toFin2ℂEquiv ψ


-- @@ L81-81 verbatim
lemma toFin2ℂ_eq_val (ψ : LeftHandedWeyl) : ψ.toFin2ℂ = ψ.val := rfl


-- @@ L83-87 verbatim
/-!

## Basis

-/


-- @@ L89-91 verbatim
/-- The standard basis on left-handed Weyl fermions. -/
def basis : Basis (Fin 2) ℂ LeftHandedWeyl := Basis.ofEquivFun
  (Equiv.linearEquiv ℂ LeftHandedWeyl.toFin2ℂFun)


-- @@ L93-99 verbatim
lemma basis_apply (i j : Fin 2) : (basis i).1 j = if j = i then 1 else 0 := by
  simp only [basis, Equiv.linearEquiv, AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe,
    EquivLike.coe_coe, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm, Basis.coe_ofEquivFun,
    LinearEquiv.symm_mk, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.coe_mk,
    Equiv.addEquiv_symm_apply]
  change Pi.single i 1 j = _
  simp [Pi.single_apply]


-- @@ L101-103 verbatim
lemma eq_sum_basis (ψ : LeftHandedWeyl) : ψ = ∑ i, ψ.1 i • basis i := by
  conv_lhs => rw [← basis.sum_repr ψ]
  rfl


-- @@ L105-107 verbatim
lemma basis_val (i : Fin 2) : (basis i).val = Pi.single i 1 := by
  ext j
  simp [basis_apply, Pi.single_apply]


-- @@ L109-113 verbatim
/-!

## Representation

-/


-- @@ L115-134 verbatim
/-- The vector space ℂ^2 carrying the fundamental representation of SL(2,C).
  In index notation corresponds to a Weyl fermion with indices ψ^a. -/
def rep : Representation ℂ SL(2,ℂ) LeftHandedWeyl where
  toFun := fun M => {
    toFun := fun (ψ : LeftHandedWeyl) =>
      LeftHandedWeyl.toFin2ℂEquiv.symm (M.1 *ᵥ ψ.toFin2ℂ),
    map_add' := by
      intro ψ ψ'
      simp [mulVec_add]
    map_smul' := by
      intro r ψ
      simp [mulVec_smul]}
  map_one' := by
    ext i
    simp
  map_mul' := fun M N => by
    simp only [SpecialLinearGroup.coe_mul]
    ext1 x
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply, LinearEquiv.apply_symm_apply,
      mulVec_mulVec]


-- @@ L136-136 verbatim
lemma rep_apply (M : SL(2,ℂ)) (ψ : LeftHandedWeyl) : rep M ψ = ⟨M.1 *ᵥ ψ.1⟩ := rfl


-- @@ L138-141 verbatim
lemma rep_apply_eq_sum_basis (M : SL(2,ℂ)) (ψ : LeftHandedWeyl) :
    rep M ψ = ∑ i, (∑ j, M.1 i j * ψ.1 j) • basis i := by
  rw [eq_sum_basis (rep M ψ)]
  rfl


-- @@ L143-148 verbatim
lemma rep_apply_basis (M : SL(2,ℂ)) (i : Fin 2) :
    rep M (basis i) = ∑ j, M.1 j i • basis j := by
  rw [rep_apply_eq_sum_basis]
  congr
  funext j
  simp [basis_apply]


-- @@ L150-155 verbatim
lemma rep_toMatrix (M : SL(2,ℂ)) : (LinearMap.toMatrix basis basis) (rep M) = M.1 := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  simp only [basis, Basis.coe_ofEquivFun, Basis.ofEquivFun_repr_apply]
  change (M.1 *ᵥ (Pi.single j 1)) i = _
  simp


-- @@ L157-159 verbatim
lemma rep_apply_basis_repr (M : SL(2,ℂ)) (i j : Fin 2) :
    basis.repr (rep M (basis i)) j = M.1 j i := by
  fin_cases j <;> simp [rep_apply_basis]


-- @@ L161-161 verbatim
end LeftHandedWeyl


-- @@ L163-163 verbatim
end LeftHanded


-- @@ L165-165 verbatim
end

-- @@ L166-166 verbatim
end Fermion
