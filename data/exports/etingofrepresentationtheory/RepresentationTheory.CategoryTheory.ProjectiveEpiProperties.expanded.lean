/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import RepresentationTheory.Alignment.Attribute


-- @@ L12-12 verbatim
universe u v w


-- @@ L14-14 verbatim
open CategoryTheory CategoryTheory.Limits


-- @@ L16-16 verbatim
namespace RepresentationTheory.CategoryTheory.ProjectiveEpiProperties


-- @@ L18-20 verbatim
/-- A property characterized by projectivity and epimorphic coproduct desc morphisms. -/
def IsProjectiveEpiSigmaDesc {C : Type u} [Category.{v} C] (P : C) : Prop :=
  Projective P ∧ IsSeparator P


-- @@ L22-22 verbatim
namespace IsProjectiveEpiSigmaDesc


-- @@ L24-24 verbatim
variable {C : Type u} [Category.{v} C] {P : C}


-- @@ L26-27 verbatim
/-- Every object satisfying this property is projective. -/
theorem projective (h : IsProjectiveEpiSigmaDesc P) : Projective P := h.1


-- @@ L29-30 verbatim
/-- Every object satisfying this property is a separator. -/
theorem isSeparator (h : IsProjectiveEpiSigmaDesc P) : IsSeparator P := h.2


-- @@ L32-36 verbatim
/-- Projectivity together with epimorphic coproduct desc morphisms characterizes this property. -/
theorem iff_projective_and_epi_sigma_desc [∀ X : C, HasCoproduct fun _ : P ⟶ X => P] :
    IsProjectiveEpiSigmaDesc P ↔
      Projective P ∧ ∀ X : C, Epi (Sigma.desc fun f : P ⟶ X => f) := by
  rw [IsProjectiveEpiSigmaDesc, isSeparator_iff_epi]


-- @@ L38-38 verbatim
end IsProjectiveEpiSigmaDesc


-- @@ L40-51 verbatim
/-- A property of an object in a category with zero morphisms that supplies epimorphism witnesses
and entails projectivity. -/
class HasProjectiveEpiWitnesses {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (P : C)
    extends toProjective : Projective P where
  /-- For each object, the property supplies existential data whose final morphism is an
  epimorphism. -/
  exists_epi : ∀ (X : C), ∃ (n : ℕ) (_ : HasBiproduct (fun _ : Fin n => P))
    (f : biproduct (fun _ : Fin n => P) ⟶ X), Epi f

/-
/-- The projectivity structure carried by an object satisfying this property. -/
-/


-- @@ L53-55 verbatim
end RepresentationTheory.CategoryTheory.ProjectiveEpiProperties

-- Recovered exact-module book alignment.

-- @@ L56-56 verbatim
attribute [source_ref "Chapter9/Definition9.6.2" (role := primary)] _root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses

-- @@ L57-57 verbatim
attribute [source_ref "Chapter9/Definition9.6.2" (role := primary)] _root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.IsProjectiveEpiSigmaDesc

-- @@ L58-58 verbatim
attribute [source_ref "Chapter9/Definition9.6.2" (role := supporting)] _root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses.exists_epi

-- @@ L59-59 verbatim
attribute [source_ref "Chapter9/Definition9.6.2" (role := supporting)] _root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.HasProjectiveEpiWitnesses.toProjective

-- @@ L60-60 verbatim
attribute [source_ref "Chapter9/Definition9.6.2" (role := supporting)] _root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.IsProjectiveEpiSigmaDesc.iff_projective_and_epi_sigma_desc

-- @@ L61-61 verbatim
attribute [source_ref "Chapter9/Definition9.6.2" (role := supporting)] _root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.IsProjectiveEpiSigmaDesc.isSeparator

-- @@ L62-62 verbatim
attribute [source_ref "Chapter9/Definition9.6.2" (role := supporting)] _root_.RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.IsProjectiveEpiSigmaDesc.projective
