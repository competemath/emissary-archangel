/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.Order.KrullDimension
import RepresentationTheory.Alignment.Attribute


-- @@ L14-14 verbatim
universe u v


-- @@ L16-16 verbatim
open CategoryTheory


-- @@ L18-18 verbatim
namespace RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional


-- @@ L20-37 verbatim
/-- A category whose subobject orders are finite-dimensional. -/
class SubobjectFiniteDimensional (C : Type u) [Category.{v} C] extends
    toAbelian : Abelian C,
    toEnoughProjectives : EnoughProjectives C where
  /-- An auxiliary type associated to the category. -/
  Auxiliary : Type
  private [auxiliaryFintype : Fintype Auxiliary]
  private auxiliaryObject : Auxiliary → C
  private simple_auxiliaryObject : ∀ i, Simple (auxiliaryObject i)
  private simple_iso_auxiliaryObject_data :
    ∀ (X : C), Simple X → ∃ i, Nonempty (X ≅ auxiliaryObject i)
  private finiteDimensionalOrder_subobject_data :
    ∀ X : C, FiniteDimensionalOrder (Subobject X)

/-
/-- The category has an abelian category structure. -/
/-- The category has enough projectives. -/
-/


-- @@ L39-39 verbatim
namespace SubobjectFiniteDimensional.Auxiliary


-- @@ L41-44 verbatim
/-- The opaque auxiliary type is finite. -/
instance fintype {C : Type u} [Category.{v} C] [SubobjectFiniteDimensional C] :
    Fintype (SubobjectFiniteDimensional.Auxiliary C) :=
  SubobjectFiniteDimensional.auxiliaryFintype


-- @@ L46-49 verbatim
/-- The object of the category associated to an auxiliary index. -/
def object {C : Type u} [Category.{v} C] [SubobjectFiniteDimensional C]
    (i : SubobjectFiniteDimensional.Auxiliary C) : C :=
  SubobjectFiniteDimensional.auxiliaryObject i


-- @@ L51-55 verbatim
/-- The object associated to an auxiliary index is simple. -/
theorem simple_object {C : Type u} [Category.{v} C] [SubobjectFiniteDimensional C]
    (i : SubobjectFiniteDimensional.Auxiliary C) : Simple (object i) := by
  change Simple (SubobjectFiniteDimensional.auxiliaryObject i)
  exact SubobjectFiniteDimensional.simple_auxiliaryObject i


-- @@ L57-57 verbatim
end SubobjectFiniteDimensional.Auxiliary


-- @@ L59-59 verbatim
namespace SubobjectFiniteDimensional


-- @@ L61-66 verbatim
/-- Every simple object is isomorphic to an object indexed by the auxiliary type. -/
theorem simple_iso_auxiliaryObject {C : Type u} [Category.{v} C]
    [SubobjectFiniteDimensional C] (X : C) (hX : Simple X) :
    ∃ i, Nonempty (X ≅ Auxiliary.object i) := by
  simpa [Auxiliary.object] using
    SubobjectFiniteDimensional.simple_iso_auxiliaryObject_data X hX


-- @@ L68-71 verbatim
/-- Each object's subobject order is finite-dimensional. -/
theorem finiteDimensionalOrder_subobject' {C : Type u} [Category.{v} C]
    [SubobjectFiniteDimensional C] (X : C) : FiniteDimensionalOrder (Subobject X) :=
  SubobjectFiniteDimensional.finiteDimensionalOrder_subobject_data X


-- @@ L73-76 verbatim
/-- The subobjects of any object form a finite-dimensional order. -/
instance finiteDimensionalOrder_subobject {C : Type u} [Category.{v} C]
    [SubobjectFiniteDimensional C] (X : C) : FiniteDimensionalOrder (Subobject X) :=
  SubobjectFiniteDimensional.finiteDimensionalOrder_subobject' X


-- @@ L78-78 verbatim
end SubobjectFiniteDimensional


-- @@ L80-80 verbatim
end RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional


-- @@ L82-83 verbatim
/-- The opaque auxiliary type is finite. -/
alias _root_.RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional.fintype := _root_.RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional.Auxiliary.fintype


-- @@ L85-86 verbatim
/-- The object of the category associated to an auxiliary index. -/
alias _root_.RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional.object := _root_.RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional.Auxiliary.object


-- @@ L88-91 verbatim
/-- The object associated to an auxiliary index is simple. -/
alias _root_.RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional.simple_object := _root_.RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional.Auxiliary.simple_object

-- Recovered exact-module book alignment.

-- @@ L92-92 verbatim
attribute [source_ref "Chapter9/Definition9.6.1" (role := primary)] _root_.RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional

-- @@ L93-93 verbatim
attribute [source_ref "Chapter9/Definition9.6.1" (role := supporting)] _root_.RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional.Auxiliary

-- @@ L94-94 verbatim
attribute [source_ref "Chapter9/Definition9.6.1" (role := supporting)] _root_.RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional.finiteDimensionalOrder_subobject

-- @@ L95-95 verbatim
attribute [source_ref "Chapter9/Definition9.6.1" (role := supporting)] _root_.RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional.finiteDimensionalOrder_subobject'

-- @@ L96-96 verbatim
attribute [source_ref "Chapter9/Definition9.6.1" (role := supporting)] _root_.RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional.fintype

-- @@ L97-97 verbatim
attribute [source_ref "Chapter9/Definition9.6.1" (role := supporting)] _root_.RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional.object

-- @@ L98-98 verbatim
attribute [source_ref "Chapter9/Definition9.6.1" (role := supporting)] _root_.RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional.simple_iso_auxiliaryObject

-- @@ L99-99 verbatim
attribute [source_ref "Chapter9/Definition9.6.1" (role := supporting)] _root_.RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional.simple_object

-- @@ L100-100 verbatim
attribute [source_ref "Chapter9/Definition9.6.1" (role := supporting)] _root_.RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional.toAbelian

-- @@ L101-101 verbatim
attribute [source_ref "Chapter9/Definition9.6.1" (role := supporting)] _root_.RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional.toEnoughProjectives
