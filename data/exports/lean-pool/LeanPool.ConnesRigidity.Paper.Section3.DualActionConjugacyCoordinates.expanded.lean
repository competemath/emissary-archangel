/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

Coordinate formulas used by the Zhou fiber-shear conjugacy. Paper: §3.
-/
module

public import LeanPool.ConnesRigidity.Paper.Section3.DualActions
import LeanPool.ConnesRigidity.Paper.Section3.DualActionConjugacyAlgebra
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc


-- @@ L20-22 verbatim
/-!
The dual action conjugacy coordinates component of the Connes rigidity formalization.
-/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
namespace Connes

-- @@ L27-27 verbatim
namespace PaperDualActionConjugacyCoordinates


-- @@ L29-29 verbatim
open Construction

-- @@ L30-30 verbatim
open Construction.PaperKernel

-- @@ L31-31 verbatim
open PaperDualActions

-- @@ L32-32 verbatim
open PaperDualCoordinates

-- @@ L33-33 verbatim
open PaperFactorIsomorphism

-- @@ L34-34 verbatim
open PaperDualActionConjugacyAlgebra


-- @@ L36-36 verbatim
noncomputable section


-- @@ L38-41 verbatim
/--
The `k` construction used in the Connes rigidity formalization.
-/
abbrev k := Construction.k

-- @@ L42-45 verbatim
/--
The `H` construction used in the Connes rigidity formalization.
-/
abbrev H := Construction.H

-- @@ L46-49 verbatim
/--
The `A` construction used in the Connes rigidity formalization.
-/
abbrev A := Construction.A

-- @@ L50-55 verbatim
/--
The `PaperV` construction used in the Connes rigidity formalization.
-/
abbrev PaperV := PaperKernel.PaperV

/- Evaluation of a coordinate action on its second summand. Paper: §3. -/

-- @@ L56-66 verbatim
theorem coordinateAction_snd_eval
    (dualAction : H →* (Module.Dual k PaperKernel.D ≃ₗ[k]
      Module.Dual k PaperKernel.D)) (h : H)
    (z : A →ₗ[k] PaperV) (lam : PaperKernel.C →ₗ[k] k)
    (c : PaperKernel.C) :
    (coordinateAction dualAction h (z, lam)).2 c =
      (dualAction h (PaperDualCoordinates.dualEquiv.symm (z, lam)))
        (0, c) := by
  rfl

/- Pairing of raw coordinates with a kernel element. Paper: §3. -/

-- @@ L67-75 verbatim
theorem dualEquiv_symm_pairing (z : A →ₗ[k] PaperV)
    (lam : PaperKernel.C →ₗ[k] k)
    (u : PaperKernel.AVStar) (c : PaperKernel.C) :
    PaperDualCoordinates.dualEquiv.symm (z, lam) (u, c) =
      PaperDualCoordinates.avDualEquiv.symm z u + lam c := by
  simp [PaperDualCoordinates.dualEquiv,
    Module.dualProdDualEquivDual]

/- First raw coordinate of the first dual action. Paper: §3. -/

-- @@ L76-97 verbatim
theorem paperCoordinateActionOne_fst
    (h : H) (z : A →ₗ[k] PaperV) (lam : PaperKernel.C →ₗ[k] k) :
    (paperCoordinateActionOne h (z, lam)).1 =
      avDualEquiv
        ((LinearMap.coprod (avDualEquiv.symm z) lam) ∘ₗ
          (paperThetaOneLinearHom h).symm ∘ₗ
            LinearMap.inl k PaperKernel.AVStar PaperKernel.C) := by
  apply LinearMap.ext
  intro u
  apply (Module.evalEquiv k PaperV).injective
  ext φ
  simp only [paperCoordinateActionOne_apply,
    paperDualActionOne, dualPrecompHom, dualPrecomp,
    Module.evalEquiv_apply, Module.Dual.eval_apply]
  change φ (avDualEquiv _ u) = _
  rw [avDualEquiv_eval]
  simp only [LinearMap.comp_apply, LinearMap.inl_apply]
  rw [avDualEquiv_eval]
  simp [PaperDualCoordinates.dualEquiv,
    Module.dualProdDualEquivDual]

/- First raw coordinate of the second dual action. Paper: §3. -/

-- @@ L98-119 verbatim
theorem paperCoordinateActionTwo_fst
    (h : H) (z : A →ₗ[k] PaperV) (lam : PaperKernel.C →ₗ[k] k) :
    (paperCoordinateActionTwo h (z, lam)).1 =
      avDualEquiv
        ((LinearMap.coprod (avDualEquiv.symm z) lam) ∘ₗ
          (paperThetaTwoLinearHom h).symm ∘ₗ
            LinearMap.inl k PaperKernel.AVStar PaperKernel.C) := by
  apply LinearMap.ext
  intro u
  apply (Module.evalEquiv k PaperV).injective
  ext φ
  simp only [paperCoordinateActionTwo_apply, paperDualActionTwo,
    dualPrecompHom, dualPrecomp, Module.evalEquiv_apply,
    Module.Dual.eval_apply]
  change φ (avDualEquiv _ u) = _
  rw [avDualEquiv_eval]
  simp only [LinearMap.comp_apply, LinearMap.inl_apply]
  rw [avDualEquiv_eval]
  simp [PaperDualCoordinates.dualEquiv,
    Module.dualProdDualEquivDual]

/- Second raw coordinate of the first dual action. Paper: §3. -/

-- @@ L120-128 verbatim
theorem paperCoordinateActionOne_snd_eval
    (h : H) (z : A →ₗ[k] PaperV) (lam : PaperKernel.C →ₗ[k] k)
    (c : PaperKernel.C) :
    (paperCoordinateActionOne h (z, lam)).2 c =
      PaperDualCoordinates.dualEquiv.symm (z, lam)
        ((paperThetaOneLinearHom h).symm (0, c)) := by
  exact coordinateAction_snd_eval paperDualActionOne h z lam c

/- Second raw coordinate of the second dual action. Paper: §3. -/

-- @@ L129-135 verbatim
theorem paperCoordinateActionTwo_snd_eval
    (h : H) (z : A →ₗ[k] PaperV) (lam : PaperKernel.C →ₗ[k] k)
    (c : PaperKernel.C) :
    (paperCoordinateActionTwo h (z, lam)).2 c =
      PaperDualCoordinates.dualEquiv.symm (z, lam)
        ((paperThetaTwoLinearHom h).symm (0, c)) := by
  exact coordinateAction_snd_eval paperDualActionTwo h z lam c


-- @@ L137-137 verbatim
end

-- @@ L138-138 verbatim
end PaperDualActionConjugacyCoordinates

-- @@ L139-139 verbatim
end Connes
