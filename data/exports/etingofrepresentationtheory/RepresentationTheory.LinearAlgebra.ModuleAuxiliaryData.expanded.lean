/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.LinearAlgebra.Span.Basic
import RepresentationTheory.Alignment.Attribute


-- @@ L9-11 verbatim
/-!
# Auxiliary data for modules
-/


-- @@ L13-13 verbatim
namespace RepresentationTheory.LinearAlgebra.ModuleAuxiliaryData


-- @@ L15-20 verbatim
/-- An auxiliary type associated with a module over a ring. -/
@[source_ref "Chapter2/Discussion_2.1_overview/Derived6" (role := supporting),
  source_ref "Chapter2/Definition2.3.4" (role := supporting)]
abbrev ModuleAuxiliaryData (A : Type*) (V : Type*) [Ring A] [AddCommGroup V]
    [Module A V] :=
  Submodule A V


-- @@ L22-26 verbatim
/-- A second auxiliary value associated with a module over a ring. -/
@[source_ref "Chapter2/Definition2.3.4" (role := supporting)]
abbrev moduleAuxiliaryData' (A : Type*) (V : Type*) [Ring A] [AddCommGroup V]
    [Module A V] : ModuleAuxiliaryData A V :=
  ⊥


-- @@ L28-32 verbatim
/-- An auxiliary value associated with a module over a ring. -/
@[source_ref "Chapter2/Definition2.3.4" (role := supporting)]
abbrev moduleAuxiliaryData (A : Type*) (V : Type*) [Ring A] [AddCommGroup V]
    [Module A V] : ModuleAuxiliaryData A V :=
  ⊤


-- @@ L34-34 verbatim
end RepresentationTheory.LinearAlgebra.ModuleAuxiliaryData
