/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Lie.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import RepresentationTheory.Alignment.Attribute


-- @@ L10-14 verbatim
/-!
# Duals of Lie modules

The dual-module type and its contragredient Lie action.
-/


-- @@ L16-16 verbatim
set_option linter.style.whitespace false


-- @@ L18-18 verbatim
namespace RepresentationTheory.Algebra.Lie.AuxiliarySingleModuleType


-- @@ L20-25 verbatim
/-- An auxiliary type depending on a Lie algebra and one of its modules. -/
@[nolint unusedArguments, source_ref "Chapter2/Definition2.14.2" (role := supporting)]
abbrev AuxiliaryLieModuleType (k : Type*) (L : Type*) (V : Type*)
    [CommRing k] [LieRing L] [LieAlgebra k L]
    [AddCommGroup V] [Module k V] [LieRingModule L V] [LieModule k L V] :=
  Module.Dual k V


-- @@ L27-29 verbatim
variable (k : Type*) (L : Type*) (V : Type*)
    [CommRing k] [LieRing L] [LieAlgebra k L]
    [AddCommGroup V] [Module k V] [LieRingModule L V] [LieModule k L V]


-- @@ L31-31 verbatim
example : LieRingModule L (AuxiliaryLieModuleType k L V) := inferInstance


-- @@ L33-33 verbatim
example : LieModule k L (AuxiliaryLieModuleType k L V) := inferInstance


-- @@ L35-35 verbatim
variable {k L V}


-- @@ L37-41 verbatim
/-- Evaluating the bracket of a Lie element with an auxiliary element gives the negated evaluation at the bracket of that Lie element with the vector. -/
@[simp, source_ref "Chapter2/Definition2.14.2" (role := primary)]
theorem auxiliary_lie_bracket_apply (x : L) (f : AuxiliaryLieModuleType k L V) (v : V) :
    (⁅x, f⁆ : AuxiliaryLieModuleType k L V) v = -f ⁅x, v⁆ :=
  Module.Dual.lie_apply x v f


-- @@ L43-43 verbatim
end RepresentationTheory.Algebra.Lie.AuxiliarySingleModuleType
