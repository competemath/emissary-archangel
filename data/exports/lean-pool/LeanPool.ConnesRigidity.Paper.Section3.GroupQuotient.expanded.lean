/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

The acting-group generators of the two concrete Zhou crossed-product models.
Paper: §3.
-/
module

public import LeanPool.ConnesRigidity.Paper.Section3.GroupFactor
import LeanPool.ConnesRigidity.Paper.Section3.QuotientAction
import LeanPool.ConnesRigidity.Porting.CoreTransfer


-- @@ L17-19 verbatim
/-!
The group quotient component of the Connes rigidity formalization.
-/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
namespace Connes

-- @@ L24-24 verbatim
namespace PaperGroupQuotient


-- @@ L26-26 verbatim
open MeasureTheory

-- @@ L27-27 verbatim
open Construction

-- @@ L28-28 verbatim
open Construction.PaperKernel

-- @@ L29-29 verbatim
open PaperQuotientAction

-- @@ L30-30 verbatim
open PaperFourierCoordinates

-- @@ L31-31 verbatim
open SemidirectFubini

-- @@ L32-32 verbatim
open PaperGroupFactor

-- @@ L33-33 verbatim
open PaperCrossedHaar

-- @@ L34-34 verbatim
open CrossedProduct


-- @@ L36-36 verbatim
noncomputable section


-- @@ L38-41 verbatim
/--
The `D` construction used in the Connes rigidity formalization.
-/
abbrev D := PaperKernel.D

-- @@ L42-45 verbatim
/--
The `H` construction used in the Connes rigidity formalization.
-/
abbrev H := Construction.H

-- @@ L46-46 verbatim
local notation "Γ₁" => PaperKernel.paperGammaCarrier paperThetaOneHom

-- @@ L47-52 verbatim
local notation "Γ₂" => PaperKernel.paperGammaCarrier paperThetaTwoHom

/- The first acting-group generator becomes the crossed action unitary.
Paper: §3. -/
-- The nested L² transport normalization exceeds Lean's default
-- elaboration budget.

-- @@ L53-101 verbatim
theorem paperGroupFactorUnitaryOne_conj_inr (h : H) :
    paperGroupFactorUnitaryOne.conjStarAlgEquiv
      (leftRegularUnitary
        (SemidirectProduct.inr h : Γ₁) :
          GroupL2 Γ₁ →L[ℂ] GroupL2 Γ₁) =
      (crossedGroupUnitary paperHaarActionOne h).toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro η
  let ξ := paperGroupFactorUnitaryOne.symm η
  have hη : paperGroupFactorUnitaryOne ξ = η :=
    paperGroupFactorUnitaryOne.apply_symm_apply η
  let T : GroupL2 Γ₁ →L[ℂ] GroupL2 Γ₁ :=
    leftRegularUnitary (SemidirectProduct.inr h : Γ₁)
  change paperGroupFactorUnitaryOne
      (T (paperGroupFactorUnitaryOne.symm η)) =
        (crossedGroupUnitary paperHaarActionOne h).toContinuousLinearEquiv.toContinuousLinearMap η
  change paperGroupFactorUnitaryOne (T ξ) =
    (crossedGroupUnitary paperHaarActionOne h).toContinuousLinearEquiv.toContinuousLinearMap η
  rw [← hη]
  apply lp.ext
  funext h'
  change paperFourierCoordinateUnitary
      (semidirectFubini paperThetaOneHom
        ((leftRegularUnitary
          (SemidirectProduct.inr h : Γ₁) :
            GroupL2 Γ₁ →L[ℂ] GroupL2 Γ₁) ξ) h') =
    crossedActionL2Equiv paperHaarActionOne h
      (paperFourierCoordinateUnitary
        (semidirectFubini paperThetaOneHom ξ (h⁻¹ * h')))
  have hnormal :
      semidirectFubini paperThetaOneHom
        ((leftRegularUnitary
          (SemidirectProduct.inr h : Γ₁) :
            GroupL2 Γ₁ →L[ℂ] GroupL2 Γ₁) ξ) h' =
      l2Reindex (paperThetaOneMulEquiv h)
        (semidirectFubini paperThetaOneHom ξ (h⁻¹ * h')) := by
    ext a
    rw [semidirectFubini_leftRegular_inr_apply, OpenAIPort.l2Reindex_apply]
    apply congrArg (fun b : Multiplicative D ↦
      (semidirectFubini paperThetaOneHom ξ (h⁻¹ * h')) b)
    change (paperThetaOneHom h⁻¹) a = (paperThetaOneHom h).symm a
    rw [map_inv]
    rfl
  rw [hnormal, paperFourierCoordinate_actionOne_comp]

/- The second acting-group generator becomes the crossed action unitary.
Paper: §3. -/
-- The nested L² transport normalization exceeds Lean's default
-- elaboration budget.

-- @@ L102-145 verbatim
theorem paperGroupFactorUnitaryTwo_conj_inr (h : H) :
    paperGroupFactorUnitaryTwo.conjStarAlgEquiv
      (leftRegularUnitary
        (SemidirectProduct.inr h : Γ₂) :
          GroupL2 Γ₂ →L[ℂ] GroupL2 Γ₂) =
      (crossedGroupUnitary paperHaarActionTwo h).toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro η
  let ξ := paperGroupFactorUnitaryTwo.symm η
  have hη : paperGroupFactorUnitaryTwo ξ = η :=
    paperGroupFactorUnitaryTwo.apply_symm_apply η
  let T : GroupL2 Γ₂ →L[ℂ] GroupL2 Γ₂ :=
    leftRegularUnitary (SemidirectProduct.inr h : Γ₂)
  change paperGroupFactorUnitaryTwo
      (T (paperGroupFactorUnitaryTwo.symm η)) =
        (crossedGroupUnitary paperHaarActionTwo h).toContinuousLinearEquiv.toContinuousLinearMap η
  change paperGroupFactorUnitaryTwo (T ξ) =
    (crossedGroupUnitary paperHaarActionTwo h).toContinuousLinearEquiv.toContinuousLinearMap η
  rw [← hη]
  apply lp.ext
  funext h'
  change paperFourierCoordinateUnitary
      (semidirectFubini paperThetaTwoHom
        ((leftRegularUnitary
          (SemidirectProduct.inr h : Γ₂) :
            GroupL2 Γ₂ →L[ℂ] GroupL2 Γ₂) ξ) h') =
    crossedActionL2Equiv paperHaarActionTwo h
      (paperFourierCoordinateUnitary
        (semidirectFubini paperThetaTwoHom ξ (h⁻¹ * h')))
  have hnormal :
      semidirectFubini paperThetaTwoHom
        ((leftRegularUnitary
          (SemidirectProduct.inr h : Γ₂) :
            GroupL2 Γ₂ →L[ℂ] GroupL2 Γ₂) ξ) h' =
      l2Reindex (paperThetaTwoMulEquiv h)
        (semidirectFubini paperThetaTwoHom ξ (h⁻¹ * h')) := by
    ext a
    rw [semidirectFubini_leftRegular_inr_apply, OpenAIPort.l2Reindex_apply]
    apply congrArg (fun b : Multiplicative D ↦
      (semidirectFubini paperThetaTwoHom ξ (h⁻¹ * h')) b)
    change (paperThetaTwoHom h⁻¹) a = (paperThetaTwoHom h).symm a
    rw [map_inv]
    rfl
  rw [hnormal, paperFourierCoordinate_actionTwo_comp]


-- @@ L147-147 verbatim
end

-- @@ L148-148 verbatim
end PaperGroupQuotient

-- @@ L149-149 verbatim
end Connes
