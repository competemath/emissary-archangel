/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import Mathlib.RepresentationTheory.Induced
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Linear.LinearFunctor
import RepresentationTheory.Alignment.Attribute


-- @@ L14-19 verbatim
/-!
# Additive and linear functors

This module records additivity and linearity properties of induction, restriction,
co-Yoneda, and restriction-of-scalars functors.
-/


-- @@ L21-21 verbatim
open CategoryTheory Opposite


-- @@ L23-23 verbatim
namespace RepresentationTheory.CategoryTheory.LinearFunctors


-- @@ L25-32 verbatim
set_option backward.defeqAttrib.useBackward true in
/-- A left adjoint is linear when its right adjoint is both additive and linear. -/
lemma leftAdjoint_linear_of_rightAdjoint_additive_linear
    {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] (R : Type*) [Semiring R] [Linear R C] [Linear R D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [G.Additive] [G.Linear R] : F.Linear R where
  map_smul {X Y} f r :=
    (adj.homEquiv X (F.obj Y)).injective (by simp [Adjunction.homEquiv_unit])


-- @@ L34-34 verbatim
section GroupRepresentations


-- @@ L36-36 verbatim
universe u


-- @@ L38-38 verbatim
variable {k G H : Type u} [Field k] [Group G] [Group H] (φ : G →* H)


-- @@ L40-42 verbatim
/-- Restriction along a group homomorphism is an additive functor. -/
@[source_ref "Chapter7/Example7.9.2" (role := supporting)]
theorem resFunctor_additive : (Rep.resFunctor (k := k) φ).Additive := inferInstance


-- @@ L44-46 verbatim
/-- Restriction along a group homomorphism is linear over the coefficient field. -/
@[source_ref "Chapter7/Example7.9.2" (role := supporting)]
theorem resFunctor_linear : (Rep.resFunctor (k := k) φ).Linear k := inferInstance


-- @@ L48-51 verbatim
/-- Induction along a group homomorphism is an additive functor. -/
@[source_ref "Chapter7/Example7.9.2" (role := supporting)]
theorem indFunctor_additive : (Rep.indFunctor.{u} k φ).Additive :=
  (Rep.indResAdjunction k φ).left_adjoint_additive


-- @@ L53-56 verbatim
/-- Induction along a group homomorphism is linear over the coefficient field. -/
@[source_ref "Chapter7/Example7.9.2" (role := supporting)]
theorem indFunctor_linear : (Rep.indFunctor.{u} k φ).Linear k :=
  leftAdjoint_linear_of_rightAdjoint_additive_linear k (Rep.indResAdjunction k φ)


-- @@ L58-58 verbatim
variable (V : Rep k G)


-- @@ L60-63 verbatim
/-- The linear co-Yoneda functor evaluated at a representation is additive. -/
@[source_ref "Chapter7/Example7.9.2" (role := supporting)]
theorem linearCoyoneda_obj_additive : ((linearCoyoneda k (Rep k G)).obj (op V)).Additive :=
  inferInstance


-- @@ L65-70 verbatim
/-- The linear co-Yoneda functor evaluated at a representation is linear over the coefficient field. -/
@[source_ref "Chapter7/Example7.9.2" (role := supporting)]
theorem linearCoyoneda_obj_linear : ((linearCoyoneda k (Rep k G)).obj (op V)).Linear k where
  map_smul {X Y} f r := by
    ext g
    exact Linear.comp_smul V X Y g r f


-- @@ L72-72 verbatim
end GroupRepresentations


-- @@ L74-74 verbatim
open scoped ModuleCat.Algebra


-- @@ L76-80 verbatim
/-- Restriction of scalars along a ring homomorphism is an additive functor. -/
instance restrictScalars_additive
    {R S : Type*} [Ring R] [Ring S] (f : R →+* S) :
    Functor.Additive (ModuleCat.restrictScalars f) :=
  inferInstance


-- @@ L82-87 verbatim
/-- Restriction of scalars along an algebra homomorphism is linear over the base semiring. -/
instance restrictScalars_linear
    {R₀ R S : Type*} [CommSemiring R₀] [Ring R] [Ring S]
    [Algebra R₀ R] [Algebra R₀ S] (f : R →ₐ[R₀] S) :
    Functor.Linear R₀ (ModuleCat.restrictScalars f.toRingHom) :=
  inferInstance


-- @@ L89-89 verbatim
end RepresentationTheory.CategoryTheory.LinearFunctors
