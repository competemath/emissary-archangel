/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.LinearAlgebra.DirectSum.Finite
import RepresentationTheory.Alignment.Attribute


-- @@ L10-10 verbatim
/-! # Product modules -/


-- @@ L12-12 verbatim
namespace RepresentationTheory.LinearAlgebra.ProductModules


-- @@ L14-17 verbatim
/-- An auxiliary type constructor taking two type arguments. -/
@[source_ref "Chapter2/Definition2.3.7" (role := supporting),
  source_ref "Chapter2/Discussion_2.1_overview/Derived7" (role := supporting)]
abbrev AuxiliaryBinaryTypeConstructor (V₁ V₂ : Type*) := V₁ × V₂


-- @@ L19-27 verbatim
/-- Scalar multiplication on a pair acts componentwise. -/
@[source_ref "Chapter2/Definition2.3.7" (role := primary)]
theorem smul_prod_mk
    (A : Type*) (V₁ V₂ : Type*) [Ring A]
    [AddCommGroup V₁] [AddCommGroup V₂] [Module A V₁] [Module A V₂]
    (a : A) (v₁ : V₁) (v₂ : V₂) :
    a • ((v₁, v₂) : AuxiliaryBinaryTypeConstructor V₁ V₂) =
      (a • v₁, a • v₂) :=
  rfl


-- @@ L29-29 verbatim
end RepresentationTheory.LinearAlgebra.ProductModules
