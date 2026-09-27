/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

The actual compact dual and normalized Haar measure for Zhou's kernel.
Paper: §§3--4.
-/
module

public import LeanPool.ConnesRigidity.Foundation.OperatorAlgebra.BinaryPontryaginDual
public import LeanPool.ConnesRigidity.Foundation.OperatorAlgebra.NormalizedHaar
public import LeanPool.ConnesRigidity.Paper.Section3.DualCoordinates


-- @@ L17-19 verbatim
/-!
The dual haar component of the Connes rigidity formalization.
-/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
namespace Connes

-- @@ L24-24 verbatim
namespace PaperDualHaar


-- @@ L26-26 verbatim
open MeasureTheory

-- @@ L27-27 verbatim
open Construction

-- @@ L28-28 verbatim
open Construction.PaperKernel

-- @@ L29-29 verbatim
open BinaryPontryaginDual


-- @@ L31-31 verbatim
noncomputable section


-- @@ L33-34 verbatim
/-- The discrete topology on the actual abelian kernel. Paper: §3. -/
noncomputable instance paperKernelTopology : TopologicalSpace PaperKernel.D := ⊥


-- @@ L36-38 verbatim
/-- The actual abelian kernel is discrete for the dual construction. Paper: §3. -/
instance paperKernelDiscreteTopology : DiscreteTopology PaperKernel.D :=
  discreteTopology_bot _


-- @@ L40-42 verbatim
/-- The compact binary character space of the actual kernel. Paper: §3. -/
abbrev PaperCharacterSpace :=
  Additive (PontryaginDual (Multiplicative PaperKernel.D))


-- @@ L44-47 verbatim
/-- The multiplicative copy of Zhou's countable kernel remains countable. Paper: §3. -/
noncomputable instance paperKernelMulCountable :
    Countable (Multiplicative PaperKernel.D) :=
  Countable.of_equiv PaperKernel.D Multiplicative.ofAdd


-- @@ L49-52 verbatim
/-- The compact dual of Zhou's countable discrete kernel is second countable. Paper: §3. -/
noncomputable instance paperCharacterSecondCountable :
    SecondCountableTopology PaperCharacterSpace :=
  ContinuousMonoidHom.isClosedEmbedding_coe.toIsEmbedding.secondCountableTopology


-- @@ L54-56 verbatim
/-- The Borel measurable structure on the compact character space. Paper: §3. -/
noncomputable instance paperCharacterMeasurableSpace :
    MeasurableSpace PaperCharacterSpace := borel PaperCharacterSpace


-- @@ L58-59 verbatim
/-- The character space carries its Borel measurable structure. Paper: §3. -/
instance paperCharacterBorelSpace : BorelSpace PaperCharacterSpace := ⟨rfl⟩


-- @@ L61-63 verbatim
/-- The normalized Haar probability on the actual character space. Paper: §3. -/
noncomputable def paperCharacterHaar : Measure PaperCharacterSpace :=
  NormalizedHaar.normalizedAddHaar PaperCharacterSpace


-- @@ L65-69 verbatim
/-- The normalized dual Haar measure is a probability measure. Paper: §3. -/
instance paperCharacterHaar_isProbability :
    IsProbabilityMeasure paperCharacterHaar := by
  unfold paperCharacterHaar
  infer_instance


-- @@ L71-75 verbatim
/-- The normalized dual Haar measure is translation invariant. Paper: §3. -/
instance paperCharacterHaar_isAddHaar :
    Measure.IsAddLeftInvariant paperCharacterHaar := by
  unfold paperCharacterHaar
  infer_instance


-- @@ L77-84 verbatim
/-- A binary linear form gives its continuous circle character. Paper: §3. -/
def linearCharacter (ℓ : PaperKernel.D →ₗ[ZMod 2] ZMod 2) :
    PontryaginDual (Multiplicative PaperKernel.D) :=
  { toMonoidHom :=
      (AddChar.toMonoidHomEquiv
        (ZMod.toCircle : AddChar (ZMod 2) Circle)).comp
        ℓ.toAddMonoidHom.toMultiplicative
    continuous_toFun := continuous_of_discreteTopology }


-- @@ L86-88 verbatim
@[simp] theorem linearCharacter_apply
    (ℓ : PaperKernel.D →ₗ[ZMod 2] ZMod 2) (x : PaperKernel.D) :
    linearCharacter ℓ (Multiplicative.ofAdd x) = ZMod.toCircle (ℓ x) := rfl


-- @@ L90-100 verbatim
/-- Character extraction recovers every binary linear form. Paper: §3. -/
theorem characterLinear_linearCharacter
    (ℓ : PaperKernel.D →ₗ[ZMod 2] ZMod 2) :
    BinaryPontryaginDual.characterLinear (M := PaperKernel.D)
        (linearCharacter ℓ) = ℓ := by
  apply LinearMap.ext
  intro x
  apply ZMod.injective_toCircle
  rw [BinaryPontryaginDual.characterLinear_circle (M := PaperKernel.D)
    (linearCharacter ℓ) x]
  rfl


-- @@ L102-113 verbatim
/-- Every continuous binary character is recovered from its linear form. Paper: §3. -/
theorem linearCharacter_characterLinear
    (χ : PontryaginDual (Multiplicative PaperKernel.D)) :
    linearCharacter
        (BinaryPontryaginDual.characterLinear (M := PaperKernel.D) χ) = χ := by
  apply PontryaginDual.ext
  intro x
  change ZMod.toCircle
      ((BinaryPontryaginDual.characterLinear (M := PaperKernel.D) χ)
        (Multiplicative.toAdd x)) = χ x
  convert (BinaryPontryaginDual.characterLinear_circle (M := PaperKernel.D) χ
    (Multiplicative.toAdd x)) using 1; rfl


-- @@ L115-142 verbatim
/-- Character extraction is additive in the binary character group. Paper: §3. -/
def characterToLinear :
    PaperCharacterSpace →+ Module.Dual (ZMod 2) PaperKernel.D where
  toFun χ := BinaryPontryaginDual.characterLinear
    (M := PaperKernel.D) (Additive.toMul χ)
  map_zero' := by
    apply LinearMap.ext
    intro x
    apply ZMod.injective_toCircle
    rw [BinaryPontryaginDual.characterLinear_circle
      (M := PaperKernel.D) (Additive.toMul (0 : PaperCharacterSpace)) x]
    simp
  map_add' χ ψ := by
    apply LinearMap.ext
    intro x
    apply ZMod.injective_toCircle
    rw [BinaryPontryaginDual.characterLinear_circle
      (M := PaperKernel.D) (Additive.toMul (χ + ψ)) x]
    change (Additive.toMul χ) (Multiplicative.ofAdd x) *
      (Additive.toMul ψ) (Multiplicative.ofAdd x) =
      ZMod.toCircle ((characterLinear (M := PaperKernel.D)
        (Additive.toMul χ) + characterLinear (M := PaperKernel.D)
          (Additive.toMul ψ)) x)
    rw [LinearMap.add_apply, AddChar.map_add_eq_mul]
    rw [← BinaryPontryaginDual.characterLinear_circle
      (M := PaperKernel.D) (Additive.toMul χ) x,
      ← BinaryPontryaginDual.characterLinear_circle
        (M := PaperKernel.D) (Additive.toMul ψ) x]


-- @@ L144-165 verbatim
/-- A binary linear form is sent to its circle character. Paper: §3. -/
def linearToCharacter :
    Module.Dual (ZMod 2) PaperKernel.D →+ PaperCharacterSpace where
  toFun ℓ := Additive.ofMul (linearCharacter ℓ)
  map_zero' := by
    apply Additive.toMul.injective
    apply PontryaginDual.ext
    intro x
    change ZMod.toCircle
        ((0 : PaperKernel.D →ₗ[ZMod 2] ZMod 2)
          (Multiplicative.toAdd x)) = 1
    simp
  map_add' ℓ m := by
    apply Additive.toMul.injective
    apply PontryaginDual.ext
    intro x
    change ZMod.toCircle
        ((ℓ + m) (Multiplicative.toAdd x)) =
      ZMod.toCircle (ℓ (Multiplicative.toAdd x)) *
        ZMod.toCircle (m (Multiplicative.toAdd x))
    rw [LinearMap.add_apply]
    rw [AddChar.map_add_eq_mul]


-- @@ L167-196 verbatim
/-- The actual compact dual is algebraically the full binary linear dual. Paper: §3. -/
def characterLinearEquiv :
    PaperCharacterSpace ≃+ Module.Dual (ZMod 2) PaperKernel.D :=
  AddEquiv.ofBijective characterToLinear ⟨by
    intro χ ψ h
    apply Additive.toMul.injective
    apply PontryaginDual.ext
    intro x
    have hχ := linearCharacter_characterLinear (Additive.toMul χ)
    have hψ := linearCharacter_characterLinear (Additive.toMul ψ)
    have h' := congrArg linearCharacter h
    change linearCharacter (characterToLinear χ) =
      linearCharacter (characterToLinear ψ) at h'
    calc
      (Additive.toMul χ) x = linearCharacter
          (characterLinear (M := PaperKernel.D) (Additive.toMul χ)) x := by
            rw [hχ]
      _ = linearCharacter (characterToLinear ψ) x :=
        congrArg (fun f => f x) h'
      _ = (Additive.toMul ψ) x := by
        change linearCharacter (characterLinear
          (M := PaperKernel.D) (Additive.toMul ψ)) x = _
        rw [hψ],
    by
      intro ℓ
      refine ⟨linearToCharacter ℓ, ?_⟩
      apply LinearMap.ext
      intro x
      change characterLinear (M := PaperKernel.D) (linearCharacter ℓ) x = ℓ x
      exact congrArg (fun f => f x) (characterLinear_linearCharacter ℓ)⟩


-- @@ L198-201 verbatim
/-- The actual Zhou dual coordinates. Paper: §3. -/
def characterCoordinatesEquiv :
    PaperCharacterSpace ≃+ PaperFactorIsomorphism.DualCoordinates :=
  characterLinearEquiv.trans PaperDualCoordinates.dualEquiv.toAddEquiv


-- @@ L203-203 verbatim
end

-- @@ L204-204 verbatim
end PaperDualHaar

-- @@ L205-205 verbatim
end Connes
