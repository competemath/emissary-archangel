/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

The first-coordinate formula for Zhou's contragredient action. Paper: §3.
-/
module

public import LeanPool.ConnesRigidity.Paper.Section3.DualActionConjugacyAlgebra
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc


-- @@ L19-21 verbatim
/-!
The dual action conjugacy first component of the Connes rigidity formalization.
-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
namespace Connes

-- @@ L26-26 verbatim
namespace PaperDualActionConjugacyFirst


-- @@ L28-28 verbatim
open Construction

-- @@ L29-29 verbatim
open Construction.PaperKernel

-- @@ L30-30 verbatim
open PaperDualCoordinates

-- @@ L31-31 verbatim
open PaperFactorIsomorphism

-- @@ L32-32 verbatim
open PaperDualActionConjugacyAlgebra


-- @@ L34-34 verbatim
noncomputable section


-- @@ L36-39 verbatim
/--
The `k` construction used in the Connes rigidity formalization.
-/
abbrev k := Construction.k

-- @@ L40-43 verbatim
/--
The `H` construction used in the Connes rigidity formalization.
-/
abbrev H := Construction.H

-- @@ L44-47 verbatim
/--
The `A` construction used in the Connes rigidity formalization.
-/
abbrev A := Construction.A

-- @@ L48-53 verbatim
/--
The `PaperV` construction used in the Connes rigidity formalization.
-/
abbrev PaperV := PaperKernel.PaperV

/- Precomposition by the first inverse action produces `zAction`. Paper: §3. -/

-- @@ L54-81 verbatim
theorem first_coordinate_eq_zAction (h : H)
    (z : A →ₗ[k] PaperV) (lam : PaperKernel.C →ₗ[k] k) :
    avDualEquiv
        ((LinearMap.coprod (avDualEquiv.symm z) lam) ∘ₗ
          (paperThetaOneLinear h).symm ∘ₗ
            LinearMap.inl k PaperKernel.AVStar PaperKernel.C) =
      zAction h z := by
  apply LinearMap.ext
  intro a
  apply (Module.evalEquiv k PaperV).injective
  ext φ
  simp only [Module.evalEquiv_apply, Module.Dual.eval_apply]
  rw [avDualEquiv_eval]
  simp only [LinearMap.comp_apply, LinearMap.inl_apply,
    LinearMap.coprod_apply]
  change (avDualEquiv.symm z)
      ((paperThetaOneLinear h).symm (a ⊗ₜ[k] φ, 0)).1 +
      lam ((paperThetaOneLinear h).symm (a ⊗ₜ[k] φ, 0)).2 =
    φ (zAction h z a)
  rw [paperThetaOne_symm_inl]
  simp only [map_zero, add_zero]
  rw [zAction_apply]
  simp only [avStarAction, Prod.fst_inv, map_inv, qVStarActionHom,
    Prod.snd_inv, MonoidHom.coe_mk, OneHom.coe_mk,
    TensorProduct.congr_tmul, LinearEquiv.coe_inv, qVAction,
    LinearEquiv.coe_mk, LinearMap.coe_mk]
  rw [avDualEquiv_symm_eval]
  rfl


-- @@ L83-83 verbatim
end

-- @@ L84-84 verbatim
end PaperDualActionConjugacyFirst

-- @@ L85-85 verbatim
end Connes
