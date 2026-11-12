/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import RepresentationTheory.Alignment.Attribute


-- @@ L14-14 verbatim
namespace RepresentationTheory.FieldAlgebraProperties


-- @@ L16-19 verbatim
/-- A property of a ring equipped with an algebra structure over a field. -/
def fieldAlgebraProperty (k : Type*) [Field k]
    (A : Type*) [Ring A] [Algebra k A] : Prop :=
  ∀ x y : A ⧸ Ring.jacobson A, x * y = y * x


-- @@ L21-25 verbatim
/-- A proposition associated with a ring algebra over a field. -/
def fieldAlgebraProperty' (k : Type*) [Field k]
    (A : Type*) [Ring A] [Algebra k A] : Prop :=
  ∀ (M : Type*) [AddCommGroup M] [Module A M] [IsSimpleModule A M] [Module k M]
    [IsScalarTower k A M], Module.finrank k M = 1


-- @@ L27-30 verbatim
/-- The property holds for a commutative ring carrying an algebra structure over a field. -/
theorem fieldAlgebraProperty.commRing (k : Type*) [Field k]
    (A : Type*) [CommRing A] [Algebra k A] : fieldAlgebraProperty k A :=
  fun x y => mul_comm x y


-- @@ L32-34 verbatim
end RepresentationTheory.FieldAlgebraProperties

-- Recovered exact-module book alignment.

-- @@ L35-35 verbatim
attribute [source_ref "Chapter9/Definition9.7.2" (role := primary)] _root_.RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty

-- @@ L36-36 verbatim
attribute [source_ref "Chapter9/Definition9.7.2" (role := primary)] _root_.RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty'

-- @@ L37-37 verbatim
attribute [source_ref "Chapter9/Definition9.7.2" (role := supporting)] _root_.RepresentationTheory.FieldAlgebraProperties.fieldAlgebraProperty.commRing
