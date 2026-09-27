/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-
-/
module

public import LeanPool.ConnesRigidity.Paper.Section4.PropertyT
import LeanPool.ConnesRigidity.Paper.Section3.FactorClosure
import LeanPool.ConnesRigidity.Paper.Section4.SpectralFiniteDetection
import LeanPool.ConnesRigidity.Paper.Section5.ICCOrbits
import LeanPool.ConnesRigidity.Paper.Section6.ModuleSemisimpleTransport


-- @@ L16-18 verbatim
/-!
Concrete completion boundary for Zhou's Theorem A. Paper: §§3--7.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
namespace Connes

-- @@ L23-23 verbatim
namespace PaperTheoremACompletion


-- @@ L25-25 verbatim
open Construction

-- @@ L26-26 verbatim
open Construction.PaperKernel


-- @@ L28-28 verbatim
noncomputable section


-- @@ L30-30 verbatim
universe v


-- @@ L32-48 verbatim
/-- The concrete headline follows from the cited EJZK property-(T) input.
All remaining spectral, factor, ICC, and nonisomorphism certificates are
constructed internally. Paper: §§7. -/
theorem theoremA (propertyTInput : PaperPropertyT.EJZKInput.{v}) :
    ∃ Γ₁ Γ₂ : CountableDiscreteGroup.{0},
      HasKazhdanPropertyT.{0, v} Γ₁ ∧ HasKazhdanPropertyT.{0, v} Γ₂ ∧
      IsICC Γ₁ ∧ IsICC Γ₂ ∧
      TracialGroupFactorsIsomorphic Γ₁ Γ₂ ∧
      ¬ Nonempty (Γ₁ ≃* Γ₂) := by
  have hT := PaperSpectralPropertyT.completion_of_spectralData
    propertyTInput PaperSpectralFiniteDetection.lambdaOneSpectralData
      PaperSpectralFiniteDetection.lambdaTwoSpectralData
  have hFactor := PaperFactorClosure.paperGroupFactors_isomorphic
  have hNoniso := PaperModuleSemisimpleTransport.paperGroups_not_isomorphic
  exact ⟨PaperKernel.paperGammaOne, PaperKernel.paperGammaTwo,
    hT.1, hT.2, PaperICC.paper_gammaOne_icc,
    PaperICC.paper_gammaTwo_icc, hFactor, hNoniso⟩


-- @@ L50-50 verbatim
end

-- @@ L51-51 verbatim
end PaperTheoremACompletion

-- @@ L52-52 verbatim
end Connes
