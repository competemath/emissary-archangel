/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
import RepresentationTheory.Alignment.Attribute


-- @@ L9-9 verbatim
namespace RepresentationTheory.CategoryTheory.Abelian.ObjectData


-- @@ L11-15 verbatim
/-- A type of data associated with an object of an abelian category. -/
@[source_ref "Chapter8/Definition8.2.1" (role := supporting)]
abbrev AbelianCategoryObjectData {C : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Abelian C] (X : C) :=
  CategoryTheory.ProjectiveResolution X


-- @@ L17-17 verbatim
end RepresentationTheory.CategoryTheory.Abelian.ObjectData
