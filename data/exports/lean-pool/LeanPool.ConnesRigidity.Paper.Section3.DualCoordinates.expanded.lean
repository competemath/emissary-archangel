/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

Algebraic identification of Zhou's actual dual coordinates. Paper: §3.
-/
module

public import LeanPool.ConnesRigidity.Paper.Section3.FactorIsomorphism
import Mathlib.Algebra.Algebra.ZMod


-- @@ L15-17 verbatim
/-!
The dual coordinates component of the Connes rigidity formalization.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
namespace Connes

-- @@ L22-22 verbatim
namespace PaperDualCoordinates


-- @@ L24-24 verbatim
open Construction

-- @@ L25-25 verbatim
open Construction.PaperKernel


-- @@ L27-27 verbatim
noncomputable section


-- @@ L29-32 verbatim
/--
The `k` construction used in the Connes rigidity formalization.
-/
abbrev k := Construction.k

-- @@ L33-36 verbatim
/--
The `A` construction used in the Connes rigidity formalization.
-/
abbrev A := Construction.A

-- @@ L37-40 verbatim
/--
The `V` construction used in the Connes rigidity formalization.
-/
abbrev V := PaperKernel.PaperV

-- @@ L41-44 verbatim
/--
The `VStar` construction used in the Connes rigidity formalization.
-/
abbrev VStar := PaperKernel.VStar

-- @@ L45-48 verbatim
/--
The `AVStar` construction used in the Connes rigidity formalization.
-/
abbrev AVStar := PaperKernel.AVStar

-- @@ L49-52 verbatim
/--
The `C` construction used in the Connes rigidity formalization.
-/
abbrev C := PaperKernel.C

-- @@ L53-56 verbatim
/--
The `D` construction used in the Connes rigidity formalization.
-/
abbrev D := PaperKernel.D

-- @@ L57-60 verbatim
/--
The `DualCoordinates` construction used in the Connes rigidity formalization.
-/
abbrev DualCoordinates := PaperFactorIsomorphism.DualCoordinates


-- @@ L62-66 verbatim
/--
The `vStarDualEquiv` construction used in the Connes rigidity formalization.
-/
noncomputable def vStarDualEquiv : Module.Dual k VStar ≃ₗ[k] V :=
  (Module.evalEquiv k V).symm


-- @@ L68-81 verbatim
/--
The `transposeToDual` construction used in the Connes rigidity formalization.
-/
def transposeToDual : (A →ₗ[k] V) →ₗ[k]
    (VStar →ₗ[k] Module.Dual k A) where
  toFun f :=
    { toFun := fun φ =>
        { toFun := fun a => φ (f a)
          map_add' := by intro a b; simp
          map_smul' := by intro r a; simp }
      map_add' := by intro φ ψ; ext a; simp
      map_smul' := by intro r φ; ext a; simp }
  map_add' := by intro f g; ext φ a; simp
  map_smul' := by intro r f; ext φ a; simp


-- @@ L83-117 verbatim
/--
The `transposeFromDual` construction used in the Connes rigidity formalization.
-/
def transposeFromDual : (VStar →ₗ[k] Module.Dual k A) →ₗ[k]
    (A →ₗ[k] V) where
  toFun g :=
    { toFun := fun a =>
        (Module.evalEquiv k V).symm
          { toFun := fun φ => g φ a
            map_add' := by intro φ ψ; simp
            map_smul' := by intro r φ; simp }
      map_add' := by
        intro a b
        apply (Module.evalEquiv k V).injective
        ext φ
        simp
      map_smul' := by
        intro r a
        apply (Module.evalEquiv k V).injective
        ext φ
        simp }
  map_add' := by
    intro f g
    apply LinearMap.ext
    intro a
    apply (Module.evalEquiv k V).injective
    ext φ
    simp
  map_smul' := by
    intro r g
    apply LinearMap.ext
    intro a
    apply (Module.evalEquiv k V).injective
    ext φ
    simp


-- @@ L119-125 verbatim
theorem transposeFromDual_left_inverse (f : A →ₗ[k] V) :
    transposeFromDual (transposeToDual f) = f := by
  apply LinearMap.ext
  intro a
  apply (Module.evalEquiv k V).injective
  ext φ
  simp [transposeFromDual, transposeToDual]


-- @@ L127-134 verbatim
theorem transposeFromDual_right_inverse
    (g : VStar →ₗ[k] Module.Dual k A) :
    transposeToDual (transposeFromDual g) = g := by
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro a
  simp [transposeFromDual, transposeToDual]


-- @@ L136-143 verbatim
/--
The `transposeEquiv` construction used in the Connes rigidity formalization.
-/
noncomputable def transposeEquiv : (A →ₗ[k] V) ≃ₗ[k]
    (VStar →ₗ[k] Module.Dual k A) :=
  LinearEquiv.ofLinearMap transposeToDual transposeFromDual
    (by apply LinearMap.ext; intro g; exact transposeFromDual_right_inverse g)
    (by apply LinearMap.ext; intro f; exact transposeFromDual_left_inverse f)


-- @@ L145-175 verbatim
/--
The `dualTensorToPartial` construction used in the Connes rigidity formalization.
-/
def dualTensorToPartial : Module.Dual k AVStar →ₗ[k]
    (VStar →ₗ[k] Module.Dual k A) where
  toFun f :=
    { toFun := fun φ =>
        { toFun := fun a => f (a ⊗ₜ[k] φ)
          map_add' := by
            intro a b
            change f ((a + b) ⊗ₜ[k] φ) = f (a ⊗ₜ[k] φ) + f (b ⊗ₜ[k] φ)
            rw [TensorProduct.add_tmul, map_add]
          map_smul' := by
            intro r a
            change f ((r • a) ⊗ₜ[k] φ) = r • f (a ⊗ₜ[k] φ)
            simpa only [← TensorProduct.smul_tmul'] using f.map_smul r (a ⊗ₜ[k] φ) }
      map_add' := by
        intro φ ψ
        apply LinearMap.ext
        intro a
        change f (a ⊗ₜ[k] (φ + ψ)) =
          f (a ⊗ₜ[k] φ) + f (a ⊗ₜ[k] ψ)
        rw [TensorProduct.tmul_add, map_add]
      map_smul' := by
        intro r φ
        apply LinearMap.ext
        intro a
        change f (a ⊗ₜ[k] (r • φ)) = r • f (a ⊗ₜ[k] φ)
        simpa only [TensorProduct.tmul_smul] using f.map_smul r (a ⊗ₜ[k] φ) }
  map_add' := by intro f g; ext φ a; simp
  map_smul' := by intro r f; ext φ a; simp


-- @@ L177-190 verbatim
/--
The `partialToDual` construction used in the Connes rigidity formalization.
-/
def partialToDual : (VStar →ₗ[k] Module.Dual k A) →ₗ[k]
    Module.Dual k AVStar where
  toFun g := TensorProduct.lift
    { toFun := fun a =>
        { toFun := fun φ => g φ a
          map_add' := by intro φ ψ; simp
          map_smul' := by intro r φ; simp }
      map_add' := by intro a b; ext φ; simp
      map_smul' := by intro r a; ext φ; simp }
  map_add' := by intro f g; apply TensorProduct.ext'; intro a φ; simp
  map_smul' := by intro r g; apply TensorProduct.ext'; intro a φ; simp


-- @@ L192-200 verbatim
theorem partialToDual_left_inverse (f : Module.Dual k AVStar) :
    partialToDual (dualTensorToPartial f) = f := by
  apply LinearMap.ext
  intro x
  refine TensorProduct.inductionOn x ?_ ?_
  · intro a φ
    rfl
  · intro x y hx hy
    simp only [map_add, hx, hy]


-- @@ L202-209 verbatim
theorem partialToDual_right_inverse
    (g : VStar →ₗ[k] Module.Dual k A) :
    dualTensorToPartial (partialToDual g) = g := by
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro a
  rfl


-- @@ L211-218 verbatim
/--
The `dualTensorPartialEquiv` construction used in the Connes rigidity formalization.
-/
noncomputable def dualTensorPartialEquiv : Module.Dual k AVStar ≃ₗ[k]
    (VStar →ₗ[k] Module.Dual k A) :=
  LinearEquiv.ofLinearMap dualTensorToPartial partialToDual
    (by apply LinearMap.ext; intro g; exact partialToDual_right_inverse g)
    (by apply LinearMap.ext; intro f; exact partialToDual_left_inverse f)


-- @@ L220-227 verbatim
/--
The `avDualEquiv` construction used in the Connes rigidity formalization.
-/
noncomputable def avDualEquiv : Module.Dual k AVStar ≃ₗ[k] A →ₗ[k] V :=
  dualTensorPartialEquiv.trans transposeEquiv.symm

/- The full algebraic dual splits over the two kernel summands. Paper: §3.
-/

-- @@ L228-233 verbatim
/--
The `dualEquiv` construction used in the Connes rigidity formalization.
-/
noncomputable def dualEquiv : Module.Dual k D ≃ₗ[k] DualCoordinates :=
  (Module.dualProdDualEquivDual k AVStar C).symm.trans
    (avDualEquiv.prodCongr (LinearEquiv.refl k (C →ₗ[k] k)))


-- @@ L235-235 verbatim
end

-- @@ L236-236 verbatim
end PaperDualCoordinates

-- @@ L237-237 verbatim
end Connes
