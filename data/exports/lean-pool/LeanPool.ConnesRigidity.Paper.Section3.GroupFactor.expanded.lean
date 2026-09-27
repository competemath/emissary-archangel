/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

Concrete Zhou group-factor Hilbert models.  The carrier is the semidirect
product from §2 and the base is the Fourier crossed-product model from §3.
-/
module

public import LeanPool.ConnesRigidity.Foundation.OperatorAlgebra.SemidirectFubini
public import LeanPool.ConnesRigidity.Paper.Section3.CrossedKernel


-- @@ L16-18 verbatim
/-!
The group factor component of the Connes rigidity formalization.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
namespace Connes

-- @@ L23-23 verbatim
namespace PaperGroupFactor


-- @@ L25-25 verbatim
open MeasureTheory

-- @@ L26-26 verbatim
open Construction

-- @@ L27-27 verbatim
open Construction.PaperKernel

-- @@ L28-28 verbatim
open PaperFourierCoordinates

-- @@ L29-29 verbatim
open PaperCrossedHaar

-- @@ L30-30 verbatim
open PaperCrossedKernel

-- @@ L31-31 verbatim
open SemidirectFubini

-- @@ L32-32 verbatim
open CrossedProduct


-- @@ L34-34 verbatim
noncomputable section


-- @@ L36-39 verbatim
/--
The `D` construction used in the Connes rigidity formalization.
-/
abbrev D := PaperKernel.D

-- @@ L40-43 verbatim
/--
The `H` construction used in the Connes rigidity formalization.
-/
abbrev H := Construction.H

-- @@ L44-44 verbatim
local notation "Γ₁" => PaperKernel.paperGammaCarrier paperThetaOneHom

-- @@ L45-45 verbatim
local notation "Γ₂" => PaperKernel.paperGammaCarrier paperThetaTwoHom

-- @@ L46-49 verbatim
/--
The `CrossedOne` construction used in the Connes rigidity formalization.
-/
abbrev CrossedOne := crossedHilbert paperHaarActionOne

-- @@ L50-56 verbatim
/--
The `CrossedTwo` construction used in the Connes rigidity formalization.
-/
abbrev CrossedTwo := crossedHilbert paperHaarActionTwo

/- The first concrete Zhou group-factor unitary. Paper: §3.
-/

-- @@ L57-63 verbatim
/--
The `paperGroupFactorUnitaryOne` construction used in the Connes rigidity formalization.
-/
def paperGroupFactorUnitaryOne :
    GroupL2 Γ₁ ≃ₗᵢ[ℂ] CrossedOne :=
  (semidirectFubini paperThetaOneHom).trans
    (crossedFiberwiseEquiv (K := H) paperFourierCoordinateUnitary)


-- @@ L65-70 verbatim
/-- The second concrete Zhou group-factor unitary. Paper: §3.
-/
def paperGroupFactorUnitaryTwo :
    GroupL2 Γ₂ ≃ₗᵢ[ℂ] CrossedTwo :=
  (semidirectFubini paperThetaTwoHom).trans
    (crossedFiberwiseEquiv (K := H) paperFourierCoordinateUnitary)


-- @@ L72-75 verbatim
@[simp] theorem paperGroupFactorUnitaryOne_apply
    (ξ : GroupL2 Γ₁) (h : H) :
    paperGroupFactorUnitaryOne ξ h =
      paperFourierCoordinateUnitary (semidirectFubini paperThetaOneHom ξ h) := rfl


-- @@ L77-85 verbatim
@[simp] theorem paperGroupFactorUnitaryTwo_apply
    (ξ : GroupL2 Γ₂) (h : H) :
    paperGroupFactorUnitaryTwo ξ h =
      paperFourierCoordinateUnitary (semidirectFubini paperThetaTwoHom ξ h) := rfl

/- Kernel translations become the concrete crossed-base multipliers for the
first Zhou factor. Paper: §3. -/
-- The nested L² transport normalization exceeds Lean's default
-- elaboration budget.

-- @@ L86-152 verbatim
theorem paperGroupFactorUnitaryOne_conj_inl (d : D) :
    paperGroupFactorUnitaryOne.conjStarAlgEquiv
      (leftRegularUnitary
        (SemidirectProduct.inl (Multiplicative.ofAdd d) : Γ₁) :
          GroupL2 Γ₁ →L[ℂ] GroupL2 Γ₁) =
      crossedKernelMultiplier d := by
  apply ContinuousLinearMap.ext
  intro η
  let ξ := paperGroupFactorUnitaryOne.symm η
  have hη : paperGroupFactorUnitaryOne ξ = η :=
    paperGroupFactorUnitaryOne.apply_symm_apply η
  let T : GroupL2 Γ₁ →L[ℂ] GroupL2 Γ₁ :=
    leftRegularUnitary
      (SemidirectProduct.inl (Multiplicative.ofAdd d) : Γ₁)
  change paperGroupFactorUnitaryOne
      (T (paperGroupFactorUnitaryOne.symm η)) = crossedKernelMultiplier d η
  change paperGroupFactorUnitaryOne (T ξ) = crossedKernelMultiplier d η
  rw [← hη]
  apply lp.ext
  funext h
  change paperFourierCoordinateUnitary
      (semidirectFubini paperThetaOneHom
        ((leftRegularUnitary
          (SemidirectProduct.inl (Multiplicative.ofAdd d) : Γ₁) :
            GroupL2 Γ₁ →L[ℂ] GroupL2 Γ₁)
          ξ) h) =
    crossedBaseMultiplier paperHaarActionOne
      (coordinateCharacterCoefficient d)
      (paperFourierCoordinateUnitary
        (semidirectFubini paperThetaOneHom
          ξ h))
  have hfiber :
      semidirectFubini paperThetaOneHom
          ((leftRegularUnitary
            (SemidirectProduct.inl (Multiplicative.ofAdd d) : Γ₁) :
              GroupL2 Γ₁ →L[ℂ] GroupL2 Γ₁) ξ) h =
        (leftRegularUnitary (Multiplicative.ofAdd d) :
          GroupL2 (Multiplicative D) →L[ℂ] GroupL2 (Multiplicative D))
          (semidirectFubini paperThetaOneHom ξ h) := by
    ext a
    rw [semidirectFubini_leftRegular_inl_apply]
    rfl
  rw [hfiber]
  have hkernel := congrArg
      (fun T : PaperFourierCoordinates.CoordinateL2 →L[ℂ]
          PaperFourierCoordinates.CoordinateL2 =>
        T (paperFourierCoordinateUnitary
          (semidirectFubini paperThetaOneHom
            ξ h)))
      (paperFourierCoordinate_conjugates_regular d)
  rw [coordinateCharacterMultiplier_eq_baseMultiplier] at hkernel
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply] at hkernel
  rw [paperFourierCoordinateUnitary.symm_apply_apply] at hkernel
  change paperFourierCoordinateUnitary
      ((leftRegularUnitary (Multiplicative.ofAdd d) :
        GroupL2 (Multiplicative D) →L[ℂ] GroupL2 (Multiplicative D))
        (semidirectFubini paperThetaOneHom ξ h)) =
    crossedBaseMultiplier paperHaarActionOne
      (coordinateCharacterCoefficient d)
      (paperFourierCoordinateUnitary
        (semidirectFubini paperThetaOneHom ξ h)) at hkernel
  exact hkernel

/- Kernel translations become the concrete crossed-base multipliers for the
second Zhou factor. Paper: §3. -/
-- The nested L² transport normalization exceeds Lean's default
-- elaboration budget.

-- @@ L153-216 verbatim
theorem paperGroupFactorUnitaryTwo_conj_inl (d : D) :
    paperGroupFactorUnitaryTwo.conjStarAlgEquiv
      (leftRegularUnitary
        (SemidirectProduct.inl (Multiplicative.ofAdd d) : Γ₂) :
          GroupL2 Γ₂ →L[ℂ] GroupL2 Γ₂) =
      crossedMultiplier paperHaarActionTwo (coordinateCharacterCoefficient d) := by
  apply ContinuousLinearMap.ext
  intro η
  let ξ := paperGroupFactorUnitaryTwo.symm η
  have hη : paperGroupFactorUnitaryTwo ξ = η :=
    paperGroupFactorUnitaryTwo.apply_symm_apply η
  let T : GroupL2 Γ₂ →L[ℂ] GroupL2 Γ₂ :=
    leftRegularUnitary
      (SemidirectProduct.inl (Multiplicative.ofAdd d) : Γ₂)
  change paperGroupFactorUnitaryTwo
      (T (paperGroupFactorUnitaryTwo.symm η)) =
        crossedMultiplier paperHaarActionTwo (coordinateCharacterCoefficient d) η
  change paperGroupFactorUnitaryTwo (T ξ) =
    crossedMultiplier paperHaarActionTwo (coordinateCharacterCoefficient d) η
  rw [← hη]
  apply lp.ext
  funext h
  change paperFourierCoordinateUnitary
      (semidirectFubini paperThetaTwoHom
        ((leftRegularUnitary
          (SemidirectProduct.inl (Multiplicative.ofAdd d) : Γ₂) :
            GroupL2 Γ₂ →L[ℂ] GroupL2 Γ₂)
          ξ) h) =
    crossedBaseMultiplier paperHaarActionTwo
      (coordinateCharacterCoefficient d)
      (paperFourierCoordinateUnitary
        (semidirectFubini paperThetaTwoHom
          ξ h))
  have hfiber :
      semidirectFubini paperThetaTwoHom
          ((leftRegularUnitary
            (SemidirectProduct.inl (Multiplicative.ofAdd d) : Γ₂) :
              GroupL2 Γ₂ →L[ℂ] GroupL2 Γ₂) ξ) h =
        (leftRegularUnitary (Multiplicative.ofAdd d) :
          GroupL2 (Multiplicative D) →L[ℂ] GroupL2 (Multiplicative D))
          (semidirectFubini paperThetaTwoHom ξ h) := by
    ext a
    rw [semidirectFubini_leftRegular_inl_apply]
    rfl
  rw [hfiber]
  have hkernel := congrArg
      (fun T : PaperFourierCoordinates.CoordinateL2 →L[ℂ]
          PaperFourierCoordinates.CoordinateL2 =>
        T (paperFourierCoordinateUnitary
          (semidirectFubini paperThetaTwoHom
            ξ h)))
      (paperFourierCoordinate_conjugates_regular d)
  rw [coordinateCharacterMultiplier_eq_baseMultiplier] at hkernel
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply] at hkernel
  rw [paperFourierCoordinateUnitary.symm_apply_apply] at hkernel
  change paperFourierCoordinateUnitary
      ((leftRegularUnitary (Multiplicative.ofAdd d) :
        GroupL2 (Multiplicative D) →L[ℂ] GroupL2 (Multiplicative D))
        (semidirectFubini paperThetaTwoHom ξ h)) =
    crossedBaseMultiplier paperHaarActionTwo
      (coordinateCharacterCoefficient d)
      (paperFourierCoordinateUnitary
        (semidirectFubini paperThetaTwoHom ξ h)) at hkernel
  exact hkernel


-- @@ L218-218 verbatim
end

-- @@ L219-219 verbatim
end PaperGroupFactor

-- @@ L220-220 verbatim
end Connes
