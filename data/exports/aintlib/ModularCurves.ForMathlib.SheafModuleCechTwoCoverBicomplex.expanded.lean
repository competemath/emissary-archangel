/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import Mathlib.Algebra.Homology.HomologicalBicomplex
import ModularCurves.ForMathlib.SheafModuleCechTopAugmentation


-- @@ L9-16 verbatim
/-!
# The module-valued Cech bicomplex of two open families

Applying the native Cech functor for one open family degreewise to the
sheaf-level Cech complex for another produces a coefficient-preserving
bicomplex. Its two edge augmentations are compatible with both
differentials.
-/


-- @@ L18-18 verbatim
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
universe u


-- @@ L24-24 verbatim
namespace TopCat.Sheaf


-- @@ L26-26 verbatim
variable {R : Type u} [CommRing R] {X : TopCat.{u}}

-- @@ L27-27 verbatim
variable (F : Sheaf (ModuleCat.{u} R) X)

-- @@ L28-28 verbatim
variable {ι κ : Type u} (U : ι → Opens X) (V : κ → Opens X)


-- @@ L30-30 verbatim
attribute [local instance] moduleCechSheafPreadditive


-- @@ L32-36 verbatim
private theorem modulePiMap_zero {β : Type u}
    (G H : β → ModuleCat.{u} R) :
    Limits.Pi.map (fun i => (0 : G i ⟶ H i)) = 0 := by
  refine Limits.Pi.hom_ext _ _ fun i => ?_
  rw [Pi.map_π, comp_zero, zero_comp]


-- @@ L38-45 verbatim
noncomputable instance moduleCechComplexFunctor_preservesZeroMorphisms :
    (cechComplexFunctor (A := ModuleCat.{u} R) V).PreservesZeroMorphisms := by
  constructor
  intro G H
  apply HomologicalComplex.Hom.ext
  funext p
  change Limits.Pi.map (fun _ => 0) = 0
  exact modulePiMap_zero _ _


-- @@ L47-53 verbatim
/-- The native module-valued Cech functor restricted from presheaves to
sheaves. -/
noncomputable def moduleCechSheafComplexFunctor :
    Sheaf (ModuleCat.{u} R) X ⥤ CochainComplex (ModuleCat.{u} R) ℕ :=
  CategoryTheory.sheafToPresheaf
      (Opens.grothendieckTopology X) (ModuleCat.{u} R) ⋙
    cechComplexFunctor V


-- @@ L55-65 verbatim
noncomputable instance moduleCechSheafComplexFunctor_preservesZeroMorphisms :
    (moduleCechSheafComplexFunctor (R := R) (X := X) V).PreservesZeroMorphisms := by
  letI : (CategoryTheory.sheafToPresheaf
      (Opens.grothendieckTopology X)
      (ModuleCat.{u} R)).PreservesZeroMorphisms :=
    Functor.FullyFaithful.preservesZeroMorphisms _
      (CategoryTheory.fullyFaithfulSheafToPresheaf _ _)
  change (CategoryTheory.sheafToPresheaf
      (Opens.grothendieckTopology X) (ModuleCat.{u} R) ⋙
    cechComplexFunctor V).PreservesZeroMorphisms
  infer_instance


-- @@ L67-73 verbatim
/-- The coefficient-preserving double-Cech bicomplex of two open families.
The outer axis is the sheaf-level Cech complex for `U`, and the inner axis is
the native Cech complex for `V`. -/
noncomputable def moduleCechTwoCoverBicomplex :
    HomologicalComplex₂ (ModuleCat.{u} R) (.up ℕ) (.up ℕ) :=
  ((moduleCechSheafComplexFunctor (R := R) (X := X) V).mapHomologicalComplex
    (.up ℕ)).obj (moduleCechComplex F U)


-- @@ L75-79 verbatim
@[simp]
theorem moduleCechTwoCoverBicomplex_X (q : ℕ) :
    (moduleCechTwoCoverBicomplex F U V).X q =
      (cechComplexFunctor V).obj (moduleCechTerm F U q).obj :=
  rfl


-- @@ L81-86 verbatim
@[simp]
theorem moduleCechTwoCoverBicomplex_d_f (q q' p : ℕ) :
    ((moduleCechTwoCoverBicomplex F U V).d q q').f p =
      ((cechComplexFunctor V).map
        ((moduleCechComplex F U).d q q').hom).f p :=
  rfl


-- @@ L88-94 verbatim
/-- The horizontal augmentation from the native Cech complex for `U` to
inner degree zero of the two-cover bicomplex. -/
noncomputable def moduleCechTwoCoverHorizontalAugmentation (q : ℕ) :
    ((cechComplexFunctor U).obj F.obj).X q ⟶
      ((moduleCechTwoCoverBicomplex F U V).X q).X 0 :=
  (moduleCechTermTopSectionsIso F U q).inv ≫
    moduleCechTopSectionsAugmentation (moduleCechTerm F U q) V


-- @@ L96-112 verbatim
/-- The horizontal augmentation commutes with the outer differential. -/
theorem moduleCechTwoCoverHorizontalAugmentation_comm
    (q q' : ℕ) (_ : (ComplexShape.up ℕ).Rel q q') :
    moduleCechTwoCoverHorizontalAugmentation F U V q ≫
        ((moduleCechTwoCoverBicomplex F U V).d q q').f 0 =
      ((cechComplexFunctor U).obj F.obj).d q q' ≫
        moduleCechTwoCoverHorizontalAugmentation F U V q' := by
  rw [moduleCechTwoCoverHorizontalAugmentation,
    moduleCechTwoCoverHorizontalAugmentation,
    moduleCechTwoCoverBicomplex_d_f]
  erw [Category.assoc,
    moduleCechTopSectionsAugmentation_naturality]
  erw [← Category.assoc]
  have hcomm :=
    (moduleCechTopSectionsComplexIso F U).inv.comm q q'
  exact congrArg (fun g =>
    g ≫ moduleCechTopSectionsAugmentation (moduleCechTerm F U q') V) hcomm


-- @@ L114-126 verbatim
/-- The horizontal augmentation lands in the kernel of the first inner
differential. -/
@[reassoc]
theorem moduleCechTwoCoverHorizontalAugmentation_comp_d (q : ℕ) :
    moduleCechTwoCoverHorizontalAugmentation F U V q ≫
        ((moduleCechTwoCoverBicomplex F U V).X q).d 0 1 = 0 := by
  rw [moduleCechTwoCoverHorizontalAugmentation]
  change ((moduleCechTermTopSectionsIso F U q).inv ≫
      moduleCechTopSectionsAugmentation (moduleCechTerm F U q) V) ≫
    ((cechComplexFunctor V).obj (moduleCechTerm F U q).obj).d 0 1 = 0
  erw [Category.assoc,
    moduleCechTopSectionsAugmentation_comp_d]
  rw [comp_zero]


-- @@ L128-133 verbatim
/-- The vertical augmentation is obtained by applying the native Cech
functor for `V` to the sheaf-level augmentation for `U`. -/
noncomputable def moduleCechTwoCoverVerticalAugmentation :
    (cechComplexFunctor V).obj F.obj ⟶
      (moduleCechTwoCoverBicomplex F U V).X 0 :=
  (cechComplexFunctor V).map (moduleCechAugmentation F U).hom


-- @@ L135-140 verbatim
@[simp]
theorem moduleCechTwoCoverVerticalAugmentation_f (p : ℕ) :
    (moduleCechTwoCoverVerticalAugmentation F U V).f p =
      ((cechComplexFunctor V).map
        (moduleCechAugmentation F U).hom).f p :=
  rfl


-- @@ L142-150 verbatim
/-- The vertical augmentation commutes with the inner differential. -/
theorem moduleCechTwoCoverVerticalAugmentation_comm
    (p p' : ℕ) (_ : (ComplexShape.up ℕ).Rel p p') :
    (moduleCechTwoCoverVerticalAugmentation F U V).f p ≫
        ((moduleCechTwoCoverBicomplex F U V).X 0).d p p' =
      ((cechComplexFunctor V).obj F.obj).d p p' ≫
        (moduleCechTwoCoverVerticalAugmentation F U V).f p' :=
  HomologicalComplex.Hom.comm
    (moduleCechTwoCoverVerticalAugmentation F U V) p p'


-- @@ L152-171 verbatim
/-- The vertical augmentation lands in the kernel of the first outer
differential. -/
@[reassoc]
theorem moduleCechTwoCoverVerticalAugmentation_comp_d (p : ℕ) :
    (moduleCechTwoCoverVerticalAugmentation F U V).f p ≫
        ((moduleCechTwoCoverBicomplex F U V).d 0 1).f p = 0 := by
  rw [moduleCechTwoCoverVerticalAugmentation_f,
    moduleCechTwoCoverBicomplex_d_f]
  rw [moduleCechComplex_d]
  change (((cechComplexFunctor V).map
      (moduleCechAugmentation F U).hom) ≫
    (cechComplexFunctor V).map
      (moduleCechDifferential F U 0).hom).f p = 0
  rw [← Functor.map_comp]
  have hzero :
      (moduleCechAugmentation F U).hom ≫
        (moduleCechDifferential F U 0).hom = 0 :=
    congrArg (fun g => g.hom) (moduleCechAugmentation_comp F U)
  rw [hzero, Functor.map_zero]
  rfl


-- @@ L173-173 verbatim
end TopCat.Sheaf
