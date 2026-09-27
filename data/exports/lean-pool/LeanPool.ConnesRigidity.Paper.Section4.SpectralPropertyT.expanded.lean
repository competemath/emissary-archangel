/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

The action-indexed positive scalar spectral bridge for Zhou §4. The analytic
spectral measures are constructed by joint functional calculus, so the only
paper-specific input is finite spectral detection. Paper: §4.
-/
module

public import LeanPool.ConnesRigidity.Paper.Section4.SplitExtensions
public import LeanPool.ConnesRigidity.Paper.Section3.DualHaar
public import LeanPool.ConnesRigidity.Foundation.OperatorAlgebra.SpectralCriterion
import LeanPool.ConnesRigidity.Foundation.OperatorAlgebra.PositiveSpectralMeasure
import LeanPool.ConnesRigidity.Paper.Section4.FiniteExtensions


-- @@ L20-22 verbatim
/-!
The spectral property t component of the Connes rigidity formalization.
-/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
namespace Connes

-- @@ L27-27 verbatim
namespace PaperSpectralPropertyT


-- @@ L29-29 verbatim
open Construction

-- @@ L30-30 verbatim
open Construction.PaperKernel

-- @@ L31-31 verbatim
open PaperPropertyT


-- @@ L33-33 verbatim
noncomputable section


-- @@ L35-35 verbatim
universe v


-- @@ L37-40 verbatim
/-- Borel structure on the raw compact character carrier used by §4. Paper: §4. -/
noncomputable instance paperRawCharacterMeasurableSpace :
    MeasurableSpace (DiscreteCharacterSpace PaperKernel.D) :=
  borel (DiscreteCharacterSpace PaperKernel.D)


-- @@ L42-44 verbatim
/-- The raw compact character carrier is a Borel space. Paper: §4. -/
instance paperRawCharacterBorelSpace :
    BorelSpace (DiscreteCharacterSpace PaperKernel.D) := ⟨rfl⟩


-- @@ L46-49 verbatim
/-- Singletons are measurable in the paper's compact character space. Paper: §4. -/
instance paperRawCharacterMeasurableSingletonClass :
    MeasurableSingletonClass (DiscreteCharacterSpace PaperKernel.D) := by
  infer_instance


-- @@ L51-54 verbatim
/-- The first actual split extension used by the spectral argument. Paper: §4. -/
noncomputable abbrev lambdaOneExtension :
    SplitAbelianExtension PaperKernel.D lambdaOne SpecialLinear.sl3Group :=
  PaperSplitExtensions.lambdaExtension PaperKernel.paperThetaOneHom


-- @@ L56-60 verbatim
/-- The second actual split extension used by the spectral argument. Paper: §4. -/
noncomputable abbrev lambdaTwoExtension :
    SplitAbelianExtension PaperKernel.D
      lambdaTwo SpecialLinear.sl3Group :=
  PaperSplitExtensions.lambdaExtension PaperKernel.paperThetaTwoHom


-- @@ L62-75 verbatim
/-- Spectral data for the intermediate group associated to an action. Paper: §4. -/
structure SpectralData
    (action : H →* MulAut (Multiplicative PaperKernel.D)) where
  /--
  The `J` component of `SpectralData`.
  -/
  J : Finset PaperKernel.D
  /--
  The `c` component of `SpectralData`.
  -/
  c : ℝ
  c_pos : 0 < c
  detection : HasFiniteSpectralDetection
    (PaperSplitExtensions.lambdaExtension action) J c


-- @@ L77-85 verbatim
/-- The intermediate group of an action is property-(T) from spectral data. Paper: §4. -/
theorem lambda_propertyT_of_spectralData
    (input : EJZKInput.{v})
    (action : H →* MulAut (Multiplicative PaperKernel.D))
    (data : SpectralData action) :
    HasKazhdanPropertyT.{0, v} (lambdaOf action) := by
  exact spectral_criterion_unconditional
    (PaperSplitExtensions.lambdaExtension action) (sl3_propertyT_from_EJZK input)
      data.J data.c_pos data.detection


-- @@ L87-96 verbatim
/-- The full semidirect group of an action is property-(T) from spectral data. Paper: §4. -/
theorem gamma_propertyT_of_spectralData
    (input : EJZKInput.{v})
    (action : H →* MulAut (Multiplicative PaperKernel.D))
    (data : SpectralData action) :
    HasKazhdanPropertyT.{0, v} (PaperKernel.paperGammaOf action) := by
  exact PropertyTTransfer.hasKazhdanPropertyT_of_finiteExtension
    (PaperFiniteExtensions.finiteExtension action)
    (lambda_propertyT_of_spectralData input action data)
    PaperPropertyT.finiteSymplecticGroup_propertyT


-- @@ L98-109 verbatim
/-- Both concrete Zhou groups have property-(T) from the two spectral inputs. Paper: §4. -/
theorem completion_of_spectralData
    (input : EJZKInput.{v})
    (dataOne : SpectralData PaperKernel.paperThetaOneHom)
    (dataTwo : SpectralData PaperKernel.paperThetaTwoHom) :
    HasKazhdanPropertyT.{0, v} PaperKernel.paperGammaOne ∧
      HasKazhdanPropertyT.{0, v} PaperKernel.paperGammaTwo := by
  exact ⟨
    gamma_propertyT_of_spectralData input
      PaperKernel.paperThetaOneHom dataOne,
    gamma_propertyT_of_spectralData input
      PaperKernel.paperThetaTwoHom dataTwo⟩


-- @@ L111-111 verbatim
end

-- @@ L112-112 verbatim
end PaperSpectralPropertyT

-- @@ L113-113 verbatim
end Connes
