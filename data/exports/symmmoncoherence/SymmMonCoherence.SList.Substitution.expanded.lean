/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import SymmMonCoherence.SList.Equivalence
public import Mathlib.CategoryTheory.Pi.Monoidal
public import SymmMonCoherence.ForMathlib.CategoryTheory.Pi.CompMonoidal
public import SymmMonCoherence.ForMathlib.CategoryTheory.Pi.FlipMonoidal
public import SymmMonCoherence.ForMathlib.CategoryTheory.Monoidal.FunctorCategoryBraided
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory


-- @@ L15-29 verbatim
/-!
# Symmetric monoidal substitution and symmetric lists

In this file, we define "symmetric monoidal substitution" for symmetric lists,
i.e., given a symmetric monoidal category `C` and a type `K`, a symmetric
monoidal functor
SList K ⥤ (K → C) ⥤ C, which, informally, "substitutes" in the first argument
the values obtainable in the second.

When `C` is `FreeSymmetricMonoidalCategory K`, and the given family of objects is
`of : K → FreeSymmetricMonoidalCategory K`, this is the "inclusion" functor
from symmetric lists in the free symmetric monoidal category, which is a part of
the equivalence between the two categories.

-/


-- @@ L31-31 verbatim
@[expose] public section


-- @@ L33-33 verbatim
open CategoryTheory MonoidalCategory


-- @@ L35-35 verbatim
namespace CategoryTheory.SList


-- @@ L37-49 verbatim
/-- Monoidal lifting as a symmetric monoidal functor (K → C) ⥤ (SList K ⥤ C) -/
@[simps]
abbrev monoidalLiftFunctor (K C : Type*) [Category* C] [MonoidalCategory C] [SymmetricCategory C] :
    (K → C) ⥤ SList K ⥤ C where
  obj X := monoidalLift X
  map f := monoidalLiftNatTrans (fun k ↦
    (monoidalLiftConsNilIso ..).hom ≫ f k ≫ (monoidalLiftConsNilIso ..).inv)
  map_id X := by
    apply monoidalNatTrans_ext_app_singleton
    simp
  map_comp {X Y Z} f g := by
    apply monoidalNatTrans_ext_app_singleton
    simp


-- @@ L51-94 verbatim
@[simps! ε μ δ η]
instance (K C : Type*) [Category* C] [MonoidalCategory C] [SymmetricCategory C] :
    (monoidalLiftFunctor K C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := monoidalLiftNatIso
        (fun c ↦ (monoidalLiftConsNilIso ((𝟙_ (K → C))) c).symm)
      μIso X Y := monoidalLiftNatIso
        (fun c ↦ by
          dsimp
          let e₁ := monoidalLiftConsNilIso X c
          let e₂ := monoidalLiftConsNilIso Y c
          let e₃ := monoidalLiftConsNilIso (X ⊗ Y) c
          exact tensorIso e₁ e₂ ≪≫ e₃.symm)
      associativity _ _ _ := by
        dsimp
        apply monoidalNatTrans_ext_app_singleton
        intro _
        simp only [Monoidal.tensorObj_obj, tensorHom_def, Category.assoc,
          tensor_whiskerLeft, NatTrans.comp_app, Monoidal.whiskerRight_app,
          monoidalLiftNatTrans_app_singleton, comp_whiskerRight, whisker_assoc,
          Iso.inv_hom_id_assoc, inv_hom_whiskerRight_assoc,
          Monoidal.associator_hom_app, Monoidal.whiskerLeft_app, whiskerLeft_comp]
        simp_rw [associator_naturality_left_assoc, whisker_exchange_assoc, cancel_epi,
          whiskerLeft_inv_hom_assoc]
      μIso_hom_natural_left _ _ := by
        dsimp
        apply monoidalNatTrans_ext_app_singleton
        intro _
        simp [tensorHom_def, whisker_exchange_assoc]
      μIso_hom_natural_right _ _ := by
        dsimp
        apply monoidalNatTrans_ext_app_singleton
        intro _
        simp [tensorHom_def, whisker_exchange_assoc]
      left_unitality X := by
        dsimp
        apply monoidalNatTrans_ext_app_singleton
        intro _
        simp [tensorHom_def]
      right_unitality X := by
        dsimp
        apply monoidalNatTrans_ext_app_singleton
        intro _
        simp [tensorHom_def, whisker_exchange_assoc] }


-- @@ L96-102 verbatim
instance (K C : Type*) [Category* C] [MonoidalCategory C] [SymmetricCategory C] :
    (monoidalLiftFunctor K C).Braided where
  braided X Y := by
    dsimp
    apply monoidalNatTrans_ext_app_singleton
    intro _
    simp [tensorHom_def, whisker_exchange_assoc, BraidedCategory.braiding]


-- @@ L104-108 verbatim
def monoidalSubst
    (K C : Type*) [Category* C] [MonoidalCategory C] [SymmetricCategory C] :
    SList K ⥤ (K → C) ⥤ C :=
  monoidalLift fun k ↦ Pi.eval _ k
  deriving Functor.Braided


-- @@ L110-113 expanded
def monoidalSubstSingletonIso {K : Type*} (C : Type*) [Category* C] [MonoidalCategory C]
    [SymmetricCategory C] (k : K) : (monoidalSubst K C).obj ((cons k).obj nil) ≅ Pi.eval _ k :=
  monoidalLiftConsNilIso _ _


-- @@ L115-115 verbatim
end CategoryTheory.SList
