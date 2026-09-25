/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Fermions.Weyl.LeftHanded
public import Physlib.Relativity.Fermions.Weyl.RightHanded
public import Physlib.Relativity.Fermions.Weyl.DualLeftHanded
public import Physlib.Relativity.Fermions.Weyl.DualRightHanded

-- @@ L12-19 verbatim
/-!

# Duals for fermions

In this file we give the relationship between Weyl fermions
and their duals.

-/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
namespace Fermion

-- @@ L24-24 verbatim
noncomputable section


-- @@ L26-26 verbatim
open Module Matrix

-- @@ L27-27 verbatim
open MatrixGroups

-- @@ L28-28 verbatim
open Complex

-- @@ L29-29 verbatim
open TensorProduct


-- @@ L31-38 verbatim
/-!

## Duals of Weyl fermions

The dual of `LeftHandedWeyl` is `DualLeftHandedWeyl`, and the dual of `RightHandedWeyl` is
`DualRightHandedWeyl`.

-/


-- @@ L40-62 verbatim
/-- The morphism between the representation `leftHanded` and the representation
  `dualLeftHanded` defined by multiplying an element of
  `leftHanded` by the matrix `εᵃ⁰ᵃ¹ = !![0, 1; -1, 0]]`. -/
def LeftHandedWeyl.dual : LeftHandedWeyl.rep.IntertwiningMap DualLeftHandedWeyl.rep where
  toFun := fun ψ => DualLeftHandedWeyl.toFin2ℂEquiv.symm (!![0, 1; -1, 0] *ᵥ ψ.toFin2ℂ)
  map_add' := by
    intro ψ ψ'
    simp only [mulVec_add, LinearEquiv.map_add]
  map_smul' := by
    intro a ψ
    simp only [mulVec_smul, LinearEquiv.map_smul]
    rfl
  isIntertwining' := by
    intro M
    refine LinearMap.ext (fun ψ => ?_)
    change DualLeftHandedWeyl.toFin2ℂEquiv.symm (!![0, 1; -1, 0] *ᵥ M.1 *ᵥ ψ.val) =
      DualLeftHandedWeyl.toFin2ℂEquiv.symm ((M.1⁻¹)ᵀ *ᵥ !![0, 1; -1, 0] *ᵥ ψ.val)
    apply congrArg
    rw [mulVec_mulVec, mulVec_mulVec, Lorentz.SL2C.inverse_coe, eta_fin_two M.1]
    refine congrFun (congrArg _ ?_) _
    rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_fin_two, eta_fin_two !![M.1 1 1, -M.1 0 1; -M.1 1 0, M.1 0 0]ᵀ]
    simp


-- @@ L64-66 verbatim
lemma LeftHandedWeyl.dual_hom_apply (ψ : LeftHandedWeyl) :
    LeftHandedWeyl.dual ψ =
    DualLeftHandedWeyl.toFin2ℂEquiv.symm (!![0, 1; -1, 0] *ᵥ ψ.toFin2ℂ) := rfl


-- @@ L68-93 verbatim
/-- The morphism from `dualLeftHanded` to
  `leftHanded` defined by multiplying an element of
  DualLeftHandedWeyl by the matrix `εₐ₁ₐ₂ = !![0, -1; 1, 0]`. -/
def DualLeftHandedWeyl.dual : DualLeftHandedWeyl.rep.IntertwiningMap LeftHandedWeyl.rep where
  toFun := fun ψ =>
      LeftHandedWeyl.toFin2ℂEquiv.symm (!![0, -1; 1, 0] *ᵥ ψ.toFin2ℂ)
  map_add' := by
    intro ψ ψ'
    simp only [map_add]
    rw [mulVec_add, LinearEquiv.map_add]
  map_smul' := by
    intro a ψ
    simp only [LinearEquiv.map_smul]
    rw [mulVec_smul, LinearEquiv.map_smul]
    rfl
  isIntertwining' := by
    intro M
    refine LinearMap.ext (fun ψ => ?_)
    change LeftHandedWeyl.toFin2ℂEquiv.symm (!![0, -1; 1, 0] *ᵥ (M.1⁻¹)ᵀ *ᵥ ψ.val) =
      LeftHandedWeyl.toFin2ℂEquiv.symm (M.1 *ᵥ !![0, -1; 1, 0] *ᵥ ψ.val)
    rw [EquivLike.apply_eq_iff_eq, mulVec_mulVec, mulVec_mulVec, Lorentz.SL2C.inverse_coe,
      eta_fin_two M.1]
    refine congrFun (congrArg _ ?_) _
    rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_fin_two, eta_fin_two !![M.1 1 1, -M.1 0 1; -M.1 1 0, M.1 0 0]ᵀ]
    simp


-- @@ L95-97 verbatim
lemma DualLeftHandedWeyl.dual_hom_apply (ψ : DualLeftHandedWeyl) :
    DualLeftHandedWeyl.dual ψ =
    LeftHandedWeyl.toFin2ℂEquiv.symm (!![0, -1; 1, 0] *ᵥ ψ.toFin2ℂ) := rfl


-- @@ L99-119 verbatim
/-- The equivalence between the representation `leftHanded` and the representation
  `dualLeftHanded` defined by multiplying an element of
  `leftHanded` by the matrix `εᵃ⁰ᵃ¹ = !![0, 1; -1, 0]]`. -/
def LeftHandedWeyl.dualEquiv : LeftHandedWeyl.rep.Equiv DualLeftHandedWeyl.rep := by
  refine Representation.Equiv.mk'  LeftHandedWeyl.dual DualLeftHandedWeyl.dual ?_ ?_
  · intro x
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
      Representation.IntertwiningMap.coe_toLinearMap]
    rw [DualLeftHandedWeyl.dual_hom_apply, LeftHandedWeyl.dual_hom_apply]
    rw [DualLeftHandedWeyl.toFin2ℂ, LinearEquiv.apply_symm_apply, mulVec_mulVec]
    rw [show (!![0, -1; (1 : ℂ), 0] * !![0, 1; -1, 0]) = 1 by simpa using Eq.symm one_fin_two]
    rw [one_mulVec]
    rfl
  · intro ψ
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
      Representation.IntertwiningMap.coe_toLinearMap]
    rw [DualLeftHandedWeyl.dual_hom_apply, LeftHandedWeyl.dual_hom_apply, LeftHandedWeyl.toFin2ℂ,
      LinearEquiv.apply_symm_apply, mulVec_mulVec]
    rw [show (!![0, (1 : ℂ); -1, 0] * !![0, -1; 1, 0]) = 1 by simpa using Eq.symm one_fin_two]
    rw [one_mulVec]
    rfl


-- @@ L121-125 verbatim
/-- `leftHandedDualEquiv` acting on an element `ψ : leftHanded` corresponds
  to multiplying `ψ` by the matrix `!![0, 1; -1, 0]`. -/
lemma LeftHandedWeyl.dualEquiv_hom_hom_apply (ψ : LeftHandedWeyl) :
    LeftHandedWeyl.dualEquiv ψ =
    DualLeftHandedWeyl.toFin2ℂEquiv.symm (!![0, 1; -1, 0] *ᵥ ψ.toFin2ℂ) := rfl


-- @@ L127-131 verbatim
/-- The inverse of `leftHandedDualEquiv` acting on an element`ψ : dualLeftHanded` corresponds
  to multiplying `ψ` by the matrix `!![0, -1; 1, 0]`. -/
lemma LeftHandedWeyl.dualEquiv_inv_hom_apply (ψ : DualLeftHandedWeyl) :
    LeftHandedWeyl.dualEquiv.symm ψ =
    LeftHandedWeyl.toFin2ℂEquiv.symm (!![0, -1; 1, 0] *ᵥ ψ.toFin2ℂ) := rfl


-- @@ L133-138 expanded
/-- The linear equivalence between `rightHandedWeyl` and `DualRightHandedWeyl` given by multiplying
an element of `rightHandedWeyl` by the matrix `εᵃ⁰ᵃ¹ = !![0, 1; -1, 0]]`.
-/
def RightHandedWeyl.dualEquiv : InformalDefinition
    where
  deps := [``RightHandedWeyl, ``DualRightHandedWeyl]
  tag := "6VZR4"


-- @@ L140-145 expanded
/-- The linear equivalence `rightHandedWeylDualEquiv` is equivariant with respect to the action of
`SL(2,C)` on `rightHandedWeyl` and `DualRightHandedWeyl`.
-/
def RightHandedWeyl.dualEquiv_equivariant : InformalLemma
    where
  deps := [``RightHandedWeyl.dualEquiv]
  tag := "6VZSG"


-- @@ L147-147 verbatim
end


-- @@ L149-149 verbatim
end Fermion
