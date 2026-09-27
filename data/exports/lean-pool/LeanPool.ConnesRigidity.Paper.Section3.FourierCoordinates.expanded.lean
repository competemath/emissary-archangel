/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

Fourier transport from Zhou's actual compact dual to the raw coordinate Haar
model. This is the kernel part of the §3 crossed-product bridge. Paper: §3.
-/
module

public import LeanPool.ConnesRigidity.Paper.Section3.FourierAction
public import LeanPool.ConnesRigidity.Paper.Section3.DualTopology
import LeanPool.ConnesRigidity.Paper.Section3.DualShearMeasure


-- @@ L17-19 verbatim
/-!
The fourier coordinates component of the Connes rigidity formalization.
-/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
namespace Connes

-- @@ L24-24 verbatim
namespace PaperFourierCoordinates


-- @@ L26-26 verbatim
open MeasureTheory

-- @@ L27-27 verbatim
open Construction

-- @@ L28-28 verbatim
open Construction.PaperKernel

-- @@ L29-29 verbatim
open PaperDualHaar

-- @@ L30-30 verbatim
open PaperDualTopology

-- @@ L31-31 verbatim
open PaperFactorIsomorphism

-- @@ L32-32 verbatim
open PaperFourier

-- @@ L33-33 verbatim
open PaperFourierAction


-- @@ L35-35 verbatim
noncomputable section


-- @@ L37-40 verbatim
/--
The `D` construction used in the Connes rigidity formalization.
-/
abbrev D := PaperKernel.D

-- @@ L41-44 verbatim
/--
The `CharacterSpace` construction used in the Connes rigidity formalization.
-/
abbrev CharacterSpace := PaperDualHaar.PaperCharacterSpace

-- @@ L45-48 verbatim
/--
The `Coordinates` construction used in the Connes rigidity formalization.
-/
abbrev Coordinates := PaperFactorIsomorphism.DualCoordinates

-- @@ L49-52 verbatim
/--
The `CharacterL2` construction used in the Connes rigidity formalization.
-/
abbrev CharacterL2 := Lp ℂ 2 paperCharacterHaar

-- @@ L53-56 verbatim
/--
The `CoordinateL2` construction used in the Connes rigidity formalization.
-/
abbrev CoordinateL2 := Lp ℂ 2 coordinatesHaar


-- @@ L58-61 verbatim
/--
The `paperDDecidableEq` construction used in the Connes rigidity formalization.
-/
local instance paperDDecidableEq : DecidableEq D := Classical.decEq D

-- @@ L62-69 verbatim
/--
The `paperMultiplicativeDDecidableEq` construction used in the Connes rigidity formalization.
-/
local instance paperMultiplicativeDDecidableEq :
    DecidableEq (Multiplicative D) := Classical.decEq _

/- The algebraic coordinate equivalence with its Borel inverse. Paper: §3.
-/

-- @@ L70-76 verbatim
/--
The `characterCoordinatesMeasurableEquiv` construction used in the Connes rigidity formalization.
-/
def characterCoordinatesMeasurableEquiv : CharacterSpace ≃ᵐ Coordinates where
  toEquiv := PaperDualHaar.characterCoordinatesEquiv.toEquiv
  measurable_toFun := characterCoordinatesHomeomorph.continuous.measurable
  measurable_invFun := characterCoordinatesHomeomorph.symm.continuous.measurable


-- @@ L78-102 verbatim
/-- Transport of normalized Haar from the compact dual to Zhou coordinates.
Paper: §3. -/
theorem characterCoordinates_measurePreserving :
    MeasurePreserving characterCoordinatesMeasurableEquiv
      paperCharacterHaar coordinatesHaar := by
  let μ := paperCharacterHaar
  let _ : Measure.IsAddHaarMeasure μ := by
    dsimp [μ, paperCharacterHaar]
    infer_instance
  have _ : Measure.IsAddHaarMeasure
      (Measure.map characterCoordinatesMeasurableEquiv μ) :=
    AddEquiv.isAddHaarMeasure_map μ PaperDualHaar.characterCoordinatesEquiv
      characterCoordinatesHomeomorph.continuous
      characterCoordinatesHomeomorph.symm.continuous
  have _ : IsProbabilityMeasure
      (Measure.map characterCoordinatesMeasurableEquiv μ) :=
    inferInstance
  refine ⟨characterCoordinatesMeasurableEquiv.measurable, ?_⟩
  change Measure.map characterCoordinatesMeasurableEquiv μ = coordinatesHaar
  unfold coordinatesHaar
  exact NormalizedHaar.normalizedAddHaar_unique Coordinates
    (Measure.map characterCoordinatesMeasurableEquiv μ)

/- The L² pullback along the character/coordinate equivalence. Paper: §3.
-/

-- @@ L103-148 verbatim
/--
The `characterCoordinatesLpEquiv` construction used in the Connes rigidity formalization.
-/
def characterCoordinatesLpEquiv : CharacterL2 ≃ₗᵢ[ℂ] CoordinateL2 where
  toLinearEquiv :=
    { toFun := Lp.compMeasurePreserving
        (characterCoordinatesMeasurableEquiv.symm : Coordinates → CharacterSpace)
        (MeasurePreserving.symm characterCoordinatesMeasurableEquiv
          characterCoordinates_measurePreserving)
      invFun := Lp.compMeasurePreserving
        characterCoordinatesMeasurableEquiv characterCoordinates_measurePreserving
      left_inv := by
        intro f
        have h := Lp.compMeasurePreserving_comp_apply f
          (MeasurePreserving.symm characterCoordinatesMeasurableEquiv
            characterCoordinates_measurePreserving)
          characterCoordinates_measurePreserving
        simpa only [Function.comp_def, MeasurableEquiv.symm_apply_apply,
          show (fun z : CharacterSpace ↦ z) = id from rfl,
          Lp.compMeasurePreserving_id, AddMonoidHom.id_apply] using h.symm
      right_inv := by
        intro f
        have h := Lp.compMeasurePreserving_comp_apply f
          characterCoordinates_measurePreserving
          (MeasurePreserving.symm characterCoordinatesMeasurableEquiv
            characterCoordinates_measurePreserving)
        simpa only [Function.comp_def, MeasurableEquiv.apply_symm_apply,
          show (fun z : Coordinates ↦ z) = id from rfl,
          Lp.compMeasurePreserving_id, AddMonoidHom.id_apply] using h.symm
      map_add' := by
        intro f g
        exact map_add
          (Lp.compMeasurePreserving
            (characterCoordinatesMeasurableEquiv.symm : Coordinates → CharacterSpace)
            (MeasurePreserving.symm characterCoordinatesMeasurableEquiv
              characterCoordinates_measurePreserving)) f g
      map_smul' := by
        intro c f
        exact map_smul
          (Lp.compMeasurePreservingₗ ℂ
            (characterCoordinatesMeasurableEquiv.symm : Coordinates → CharacterSpace)
            (MeasurePreserving.symm characterCoordinatesMeasurableEquiv
              characterCoordinates_measurePreserving)) c f }
  norm_map' := fun f => Lp.norm_compMeasurePreserving f
    (MeasurePreserving.symm characterCoordinatesMeasurableEquiv
      characterCoordinates_measurePreserving)


-- @@ L150-155 verbatim
@[simp] theorem characterCoordinatesLpEquiv_apply (f : CharacterL2) :
    characterCoordinatesLpEquiv f =
      Lp.compMeasurePreserving
        (characterCoordinatesMeasurableEquiv.symm : Coordinates → CharacterSpace)
        (MeasurePreserving.symm characterCoordinatesMeasurableEquiv
          characterCoordinates_measurePreserving) f := rfl


-- @@ L157-161 verbatim
/-- The paper Fourier transform with target in Zhou coordinates. Paper: §3.
-/
def paperFourierCoordinateUnitary :
    GroupL2 (Multiplicative D) ≃ₗᵢ[ℂ] CoordinateL2 :=
  paperFourierUnitary.trans characterCoordinatesLpEquiv


-- @@ L163-167 verbatim
/--
The `coordinateCharacterL2` construction used in the Connes rigidity formalization.
-/
def coordinateCharacterL2 (d : D) : CoordinateL2 :=
  characterCoordinatesLpEquiv (characterL2 d)


-- @@ L169-174 verbatim
@[simp] theorem paperFourierCoordinateUnitary_single (d : D) :
    paperFourierCoordinateUnitary
        (lp.single 2 (Multiplicative.ofAdd d) (1 : ℂ)) =
      coordinateCharacterL2 d := by
  exact congrArg characterCoordinatesLpEquiv
    (paperFourierUnitary_single d)


-- @@ L176-184 verbatim
/-- The transported kernel multiplier in raw coordinates. Paper: §3.
-/
def coordinateCharacterMultiplier (d : D) :
    CoordinateL2 →L[ℂ] CoordinateL2 :=
  characterCoordinatesLpEquiv.conjStarAlgEquiv
    (characterMultiplier (complexCharacter d))

/- Kernel regular translations become the transported Zhou-coordinate
multiplier. Paper: §3. -/

-- @@ L185-197 verbatim
theorem paperFourierCoordinate_conjugates_regular (d : D) :
    paperFourierCoordinateUnitary.conjStarAlgEquiv
        (leftRegularUnitary (Multiplicative.ofAdd d) :
          GroupL2 (Multiplicative D) →L[ℂ]
            GroupL2 (Multiplicative D)) =
      coordinateCharacterMultiplier d := by
  change (characterCoordinatesLpEquiv.conjStarAlgEquiv
      (paperFourierUnitary.conjStarAlgEquiv
        (leftRegularUnitary (Multiplicative.ofAdd d) :
          GroupL2 (Multiplicative D) →L[ℂ]
            GroupL2 (Multiplicative D)))) = _
  rw [paperFourier_conjugates_regular]
  rfl


-- @@ L199-199 verbatim
end

-- @@ L200-200 verbatim
end PaperFourierCoordinates

-- @@ L201-201 verbatim
end Connes
