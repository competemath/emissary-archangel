/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import RepresentationTheory.CategoryTheory.QuiverLinearDiagrams
import RepresentationTheory.Alignment.Attribute
import Mathlib.Algebra.Module.Submodule.LinearMap


-- @@ L11-11 verbatim
/-! # Auxiliary quiver-indexed types -/


-- @@ L13-13 verbatim
namespace RepresentationTheory.CategoryTheory.QuiverAuxiliary


-- @@ L15-15 verbatim
open RepresentationTheory.CategoryTheory.QuiverLinearDiagrams


-- @@ L17-25 verbatim
/-- An auxiliary type associated with a commutative semiring and a quiver. -/
@[source_ref "Chapter2/Definition2.8.8" (role := supporting)]
structure AuxiliaryType (k : Type*) (Q : Type*) [CommSemiring k]
    [Quiver Q] (ρ : AuxiliaryQuiverModuleData k Q) where
  /-- Returns the submodule associated with a vertex of the auxiliary type. -/
  carrier : ∀ v, Submodule k (ρ.obj v)
  /-- An arrow map sends an element of the source submodule into the target submodule associated with the auxiliary type. -/
  map_mem : ∀ {v w : Q} (e : v ⟶ w) (x : ρ.obj v),
    x ∈ carrier v → ρ.map e x ∈ carrier w


-- @@ L27-27 verbatim
namespace AuxiliaryType


-- @@ L29-29 verbatim
variable {k Q : Type*} [CommSemiring k] [Quiver Q]

-- @@ L30-30 verbatim
variable {ρ : AuxiliaryQuiverModuleData k Q}


-- @@ L32-37 verbatim
/-- Converts the auxiliary type into its associated quiver-indexed object. -/
@[source_ref "Chapter2/Definition2.8.8" (role := supporting)]
noncomputable def toDiagram (S : AuxiliaryType k Q ρ) :
    AuxiliaryQuiverModuleData k Q where
  obj i := S.carrier i
  map e := LinearMap.restrict (ρ.map e) (fun x hx => S.map_mem e x hx)


-- @@ L39-42 verbatim
/-- At each vertex, the converted auxiliary object's type is the subtype of the corresponding carrier submodule. -/
@[simp] theorem obj_toAuxiliaryObject (S : AuxiliaryType k Q ρ) (i : Q) :
    S.toDiagram.obj i = S.carrier i :=
  rfl


-- @@ L44-44 verbatim
end AuxiliaryType


-- @@ L46-46 verbatim
end RepresentationTheory.CategoryTheory.QuiverAuxiliary
