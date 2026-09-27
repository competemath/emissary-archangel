/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

The contragredient actions on Zhou's dual coordinates.  This is the
algebraic action layer behind the Fourier model in §§3--4; analytic
measurability is kept in the companion files.
Paper: §§3--4.
-/
module

public import LeanPool.ConnesRigidity.Construction.PaperActionInstances
public import LeanPool.ConnesRigidity.Paper.Section3.DualCoordinates
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc


-- @@ L21-23 verbatim
/-!
The dual actions component of the Connes rigidity formalization.
-/


-- @@ L25-25 verbatim
@[expose] public section


-- @@ L27-27 verbatim
namespace Connes

-- @@ L28-28 verbatim
namespace PaperDualActions


-- @@ L30-30 verbatim
open Construction

-- @@ L31-31 verbatim
open Construction.PaperKernel

-- @@ L32-32 verbatim
open PaperDualCoordinates


-- @@ L34-34 verbatim
noncomputable section


-- @@ L36-39 verbatim
/--
The `k` construction used in the Connes rigidity formalization.
-/
abbrev k := Construction.k

-- @@ L40-43 verbatim
/--
The `D` construction used in the Connes rigidity formalization.
-/
abbrev D := PaperKernel.D

-- @@ L44-47 verbatim
/--
The `H` construction used in the Connes rigidity formalization.
-/
abbrev H := Construction.H

-- @@ L48-51 verbatim
/--
The `Dual` construction used in the Connes rigidity formalization.
-/
abbrev Dual := Module.Dual k D

-- @@ L52-55 verbatim
/--
The `Coordinates` construction used in the Connes rigidity formalization.
-/
abbrev Coordinates := PaperFactorIsomorphism.DualCoordinates


-- @@ L57-77 verbatim
/-- Precomposition by the inverse is the contragredient of a kernel
automorphism. Paper: §3. -/
def dualPrecomp (e : D ≃ₗ[k] D) : Dual ≃ₗ[k] Dual where
  toFun ℓ := ℓ.comp (e⁻¹).toLinearMap
  invFun ℓ := ℓ.comp e.toLinearMap
  left_inv ℓ := by
    apply LinearMap.ext
    intro d
    simp
  right_inv ℓ := by
    apply LinearMap.ext
    intro d
    simp
  map_add' ℓ m := by
    apply LinearMap.ext
    intro d
    simp
  map_smul' a ℓ := by
    apply LinearMap.ext
    intro d
    simp


-- @@ L79-80 verbatim
@[simp] theorem dualPrecomp_apply (e : D ≃ₗ[k] D) (ℓ : Dual) (d : D) :
    dualPrecomp e ℓ d = ℓ (e⁻¹ d) := rfl


-- @@ L82-98 verbatim
/-- Contragredient action associated to a homomorphism of kernel actions.
Paper: §§3--4. -/
def dualPrecompHom (theta : H →* (D ≃ₗ[k] D)) :
    H →* (Dual ≃ₗ[k] Dual) where
  toFun h := dualPrecomp (theta h)
  map_one' := by
    apply LinearEquiv.ext
    intro ℓ
    apply LinearMap.ext
    intro d
    simp
  map_mul' h h' := by
    apply LinearEquiv.ext
    intro ℓ
    apply LinearMap.ext
    intro d
    simp [dualPrecomp]


-- @@ L100-102 verbatim
@[simp] theorem dualPrecompHom_apply
    (theta : H →* (D ≃ₗ[k] D)) (h : H) (ℓ : Dual) (d : D) :
    dualPrecompHom theta h ℓ d = ℓ ((theta h)⁻¹ d) := rfl


-- @@ L104-106 verbatim
/-- The first actual Zhou contragredient action on the full dual. Paper: §3. -/
def paperDualActionOne : H →* (Dual ≃ₗ[k] Dual) :=
  dualPrecompHom PaperKernel.paperThetaOneLinearHom


-- @@ L108-110 verbatim
/-- The second actual Zhou contragredient action on the full dual. Paper: §3. -/
def paperDualActionTwo : H →* (Dual ≃ₗ[k] Dual) :=
  dualPrecompHom PaperKernel.paperThetaTwoLinearHom


-- @@ L112-118 verbatim
/-- Transport a full-dual additive equivalence to Zhou's raw coordinates.
Paper: §3. -/
def coordinateAction (dualAction : H →* (Dual ≃ₗ[k] Dual)) (h : H) :
    Coordinates ≃+ Coordinates :=
  PaperDualCoordinates.dualEquiv.toAddEquiv.symm.trans
    ((dualAction h).toAddEquiv.trans
      PaperDualCoordinates.dualEquiv.toAddEquiv)


-- @@ L120-125 verbatim
theorem coordinateAction_one
    (dualAction : H →* (Dual ≃ₗ[k] Dual)) :
    coordinateAction dualAction 1 = AddEquiv.refl Coordinates := by
  apply AddEquiv.ext
  intro p
  simp [coordinateAction]


-- @@ L127-148 verbatim
theorem coordinateAction_mul
    (dualAction : H →* (Dual ≃ₗ[k] Dual)) (h h' : H) :
    coordinateAction dualAction (h * h') =
      (coordinateAction dualAction h').trans
        (coordinateAction dualAction h) := by
  apply AddEquiv.ext
  intro p
  calc
    coordinateAction dualAction (h * h') p =
        PaperDualCoordinates.dualEquiv
          (dualAction (h * h') (PaperDualCoordinates.dualEquiv.symm p)) := rfl
    _ = PaperDualCoordinates.dualEquiv
          ((dualAction h * dualAction h')
            (PaperDualCoordinates.dualEquiv.symm p)) := by
          rw [dualAction.map_mul]
    _ = PaperDualCoordinates.dualEquiv
          (dualAction h (dualAction h'
            (PaperDualCoordinates.dualEquiv.symm p))) := by
          rw [LinearEquiv.mul_apply]
    _ = (coordinateAction dualAction h').trans
          (coordinateAction dualAction h) p := by
          simp [coordinateAction, AddEquiv.trans_apply]


-- @@ L150-152 verbatim
/-- The first actual Zhou action on the raw dual coordinates. Paper: §3. -/
def paperCoordinateActionOne (h : H) : Coordinates ≃+ Coordinates :=
  coordinateAction paperDualActionOne h


-- @@ L154-156 verbatim
/-- The second actual Zhou action on the raw dual coordinates. Paper: §3. -/
def paperCoordinateActionTwo (h : H) : Coordinates ≃+ Coordinates :=
  coordinateAction paperDualActionTwo h


-- @@ L158-161 verbatim
@[simp] theorem paperCoordinateActionOne_apply (h : H) (p : Coordinates) :
    paperCoordinateActionOne h p =
      PaperDualCoordinates.dualEquiv
        (paperDualActionOne h (PaperDualCoordinates.dualEquiv.symm p)) := rfl


-- @@ L163-166 verbatim
@[simp] theorem paperCoordinateActionTwo_apply (h : H) (p : Coordinates) :
    paperCoordinateActionTwo h p =
      PaperDualCoordinates.dualEquiv
        (paperDualActionTwo h (PaperDualCoordinates.dualEquiv.symm p)) := rfl


-- @@ L168-185 verbatim
/-- Forget the additive structure when the factor witness needs permutation
actions. Paper: §3. -/
def paperCoordinatePermAction (dualAction : H →* (Dual ≃ₗ[k] Dual)) :
    H →* Equiv.Perm Coordinates where
  toFun h := (coordinateAction dualAction h).toEquiv
  map_one' := by
    apply Equiv.ext
    intro p
    change coordinateAction dualAction 1 p = p
    simpa using congrArg (fun e : Coordinates ≃+ Coordinates => e p)
      (coordinateAction_one dualAction)
  map_mul' h h' := by
    apply Equiv.ext
    intro p
    change coordinateAction dualAction (h * h') p =
      coordinateAction dualAction h (coordinateAction dualAction h' p)
    simpa using congrArg (fun e : Coordinates ≃+ Coordinates => e p)
      (coordinateAction_mul dualAction h h')


-- @@ L187-189 verbatim
/-- The first Zhou coordinate action as a permutation action. Paper: §3. -/
def paperCoordinatePermActionOne : H →* Equiv.Perm Coordinates :=
  paperCoordinatePermAction paperDualActionOne


-- @@ L191-193 verbatim
/-- The second Zhou coordinate action as a permutation action. Paper: §3. -/
def paperCoordinatePermActionTwo : H →* Equiv.Perm Coordinates :=
  paperCoordinatePermAction paperDualActionTwo


-- @@ L195-195 verbatim
end

-- @@ L196-196 verbatim
end PaperDualActions

-- @@ L197-197 verbatim
end Connes
