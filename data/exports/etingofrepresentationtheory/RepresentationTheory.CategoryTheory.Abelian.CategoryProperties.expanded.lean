/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import RepresentationTheory.Alignment.Attribute


-- @@ L11-15 verbatim
/-!
# Abelian category properties

This module defines a proposition associated with a category equipped with an abelian structure.
-/


-- @@ L17-17 verbatim
open CategoryTheory


-- @@ L19-19 verbatim
namespace RepresentationTheory.CategoryTheory.Abelian.CategoryProperties


-- @@ L21-24 verbatim
/-- A proposition associated with a category equipped with an abelian structure. -/
@[source_ref "Chapter7/Definition7.9.4" (role := supporting)]
def AbelianCategoryProperty (C : Type*) [Category C] [Abelian C] : Prop :=
  ∀ (S : ShortComplex C), S.ShortExact → Nonempty S.Splitting


-- @@ L26-26 verbatim
end RepresentationTheory.CategoryTheory.Abelian.CategoryProperties
