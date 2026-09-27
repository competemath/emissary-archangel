/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

Concrete Haar-action inputs for Zhou's dual-coordinate crossed products.
The topology is the transported compact-dual topology already developed in
the paper-facing layer. Paper: §3.
-/
module

public import LeanPool.ConnesRigidity.Paper.Section3.DualAutomorphism
public import LeanPool.ConnesRigidity.Paper.Section3.DualActions


-- @@ L17-19 verbatim
/-!
The crossed action component of the Connes rigidity formalization.
-/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
namespace Connes

-- @@ L24-24 verbatim
namespace PaperCrossedAction


-- @@ L26-26 verbatim
open MeasureTheory

-- @@ L27-27 verbatim
open Construction

-- @@ L28-28 verbatim
open Construction.PaperKernel

-- @@ L29-29 verbatim
open PaperDualActions

-- @@ L30-30 verbatim
open PaperDualHaar

-- @@ L31-31 verbatim
open PaperDualTopology

-- @@ L32-32 verbatim
open PaperDualAutomorphism

-- @@ L33-33 verbatim
open PaperFactorIsomorphism


-- @@ L35-35 verbatim
noncomputable section


-- @@ L37-40 verbatim
/--
The `k` construction used in the Connes rigidity formalization.
-/
abbrev k := Construction.k

-- @@ L41-44 verbatim
/--
The `D` construction used in the Connes rigidity formalization.
-/
abbrev D := PaperKernel.D

-- @@ L45-48 verbatim
/--
The `H` construction used in the Connes rigidity formalization.
-/
abbrev H := Construction.H

-- @@ L49-52 verbatim
/--
The `Coordinates` construction used in the Connes rigidity formalization.
-/
abbrev Coordinates := PaperFactorIsomorphism.DualCoordinates

-- @@ L53-60 verbatim
/--
The `CharacterSpace` construction used in the Connes rigidity formalization.
-/
abbrev CharacterSpace := PaperDualHaar.PaperCharacterSpace

/- The Pontryagin-dual contragredient is the existing paper action.
Paper: §3.
-/

-- @@ L61-73 verbatim
/--
The `characterActionOfLinear` construction used in the Connes rigidity formalization.
-/
def characterActionOfLinear (e : D ≃ₗ[k] D) :
    CharacterSpace ≃+ CharacterSpace where
  toFun := PaperDualAutomorphism.dualCharacterEquiv e.toAddEquiv
  invFun := (PaperDualAutomorphism.dualCharacterEquiv e.toAddEquiv).symm
  left_inv χ := (PaperDualAutomorphism.dualCharacterEquiv e.toAddEquiv).left_inv χ
  right_inv χ := (PaperDualAutomorphism.dualCharacterEquiv e.toAddEquiv).right_inv χ
  map_add' χ ψ := (PaperDualAutomorphism.dualCharacterEquiv e.toAddEquiv).map_add χ ψ

/- The dual linear coordinate of the contragredient is precomposition.
Paper: §3. -/

-- @@ L74-91 verbatim
theorem characterLinearEquiv_characterActionOfLinear
    (e : D ≃ₗ[k] D) (χ : CharacterSpace) :
    characterLinearEquiv (characterActionOfLinear e χ) =
      PaperDualActions.dualPrecomp e (characterLinearEquiv χ) := by
  apply LinearMap.ext
  intro d
  apply ZMod.injective_toCircle
  change ZMod.toCircle
      (BinaryPontryaginDual.characterLinear
        (M := D) (Additive.toMul (characterActionOfLinear e χ)) d) =
    ZMod.toCircle
      ((BinaryPontryaginDual.characterLinear
        (M := D) (Additive.toMul χ)) (e.symm d))
  rw [BinaryPontryaginDual.characterLinear_circle,
    BinaryPontryaginDual.characterLinear_circle]
  rfl

/- The compact dual action is continuous. Paper: §3. -/

-- @@ L92-96 verbatim
theorem continuous_characterActionOfLinear (e : D ≃ₗ[k] D) :
    Continuous (characterActionOfLinear e : CharacterSpace → CharacterSpace) := by
  exact PaperDualAutomorphism.dualCharacterEquiv_continuous e.toAddEquiv

/- Coordinate action is the compact-dual action in Zhou coordinates. Paper: §3. -/

-- @@ L97-110 verbatim
theorem coordinateAction_eq_characterTransport
    (theta : H →* (D ≃ₗ[k] D)) (h : H) (p : Coordinates) :
    coordinateAction (dualPrecompHom theta) h p =
      PaperDualHaar.characterCoordinatesEquiv
        (characterActionOfLinear (theta h)
          (PaperDualHaar.characterCoordinatesEquiv.symm p)) := by
  apply PaperDualCoordinates.dualEquiv.symm.injective
  change PaperDualCoordinates.dualEquiv.symm
      (coordinateAction (dualPrecompHom theta) h p) = _
  simp [PaperDualHaar.characterCoordinatesEquiv, coordinateAction,
    characterLinearEquiv_characterActionOfLinear]
  rfl

/- The first Zhou coordinate action is continuous. Paper: §3. -/

-- @@ L111-125 verbatim
theorem continuous_paperCoordinateActionOne (h : H) :
    Continuous (paperCoordinateActionOne h : Coordinates → Coordinates) := by
  rw [show (paperCoordinateActionOne h : Coordinates → Coordinates) =
      (fun p => PaperDualHaar.characterCoordinatesEquiv
        (characterActionOfLinear (paperThetaOneLinearHom h)
          (PaperDualHaar.characterCoordinatesEquiv.symm p))) by
      funext p
      change coordinateAction paperDualActionOne h p = _
      simpa [paperDualActionOne] using
        (coordinateAction_eq_characterTransport paperThetaOneLinearHom h p)]
  exact characterCoordinatesHomeomorph.continuous.comp
    ((continuous_characterActionOfLinear (paperThetaOneLinearHom h)).comp
      characterCoordinatesHomeomorph.symm.continuous)

/- The second Zhou coordinate action is continuous. Paper: §3. -/

-- @@ L126-138 verbatim
theorem continuous_paperCoordinateActionTwo (h : H) :
    Continuous (paperCoordinateActionTwo h : Coordinates → Coordinates) := by
  rw [show (paperCoordinateActionTwo h : Coordinates → Coordinates) =
      (fun p => PaperDualHaar.characterCoordinatesEquiv
        (characterActionOfLinear (paperThetaTwoLinearHom h)
          (PaperDualHaar.characterCoordinatesEquiv.symm p))) by
      funext p
      change coordinateAction paperDualActionTwo h p = _
      simpa [paperDualActionTwo] using
        (coordinateAction_eq_characterTransport paperThetaTwoLinearHom h p)]
  exact characterCoordinatesHomeomorph.continuous.comp
    ((continuous_characterActionOfLinear (paperThetaTwoLinearHom h)).comp
      characterCoordinatesHomeomorph.symm.continuous)


-- @@ L140-140 verbatim
end

-- @@ L141-141 verbatim
end PaperCrossedAction

-- @@ L142-142 verbatim
end Connes
