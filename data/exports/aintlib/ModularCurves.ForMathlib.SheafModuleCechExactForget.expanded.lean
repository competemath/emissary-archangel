/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import ModularCurves.ForMathlib.SheafModuleCechTopExact


-- @@ L9-14 verbatim
/-!
# Exactness after forgetting Cech-complex coefficients

Exactness of a module-valued Cech complex can be checked after forgetting
the module structure.
-/


-- @@ L16-16 verbatim
open CategoryTheory TopologicalSpace


-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-20 verbatim
universe u


-- @@ L22-22 verbatim
namespace TopCat.Sheaf


-- @@ L24-24 verbatim
variable {R : Type u} [CommRing R] {X : TopCat.{u}}


-- @@ L26-50 verbatim
/-- A native module-valued Cech complex is exact in a degree exactly when
the native additive Cech complex of the forgotten sheaf is exact there. -/
theorem moduleCechComplex_exactAt_iff_forget
    (F : Sheaf (ModuleCat.{u} R) X) {ι : Type u} (U : ι → Opens X) (n : ℕ) :
    ((cechComplexFunctor U).obj F.obj).ExactAt n ↔
      ((cechComplexFunctor U).obj (moduleForgetSheaf F).obj).ExactAt n := by
  constructor
  · intro h
    have hmap :
        (((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex
          (.up ℕ)).obj ((cechComplexFunctor U).obj F.obj)).ExactAt n := by
      rw [HomologicalComplex.exactAt_iff]
      change ((((cechComplexFunctor U).obj F.obj).sc n).map
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).Exact
      exact (ShortComplex.exact_iff_exact_map_forget₂
        (S := ((cechComplexFunctor U).obj F.obj).sc n)).mp h
    exact hmap.of_iso (moduleCechComplexForgetIso F U)
  · intro h
    have hmap :
        (((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex
          (.up ℕ)).obj ((cechComplexFunctor U).obj F.obj)).ExactAt n :=
      h.of_iso (moduleCechComplexForgetIso F U).symm
    rw [HomologicalComplex.exactAt_iff] at hmap ⊢
    exact (ShortComplex.exact_iff_exact_map_forget₂
      (S := ((cechComplexFunctor U).obj F.obj).sc n)).mpr hmap


-- @@ L52-52 verbatim
end TopCat.Sheaf
