/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.Combinatorics.Quiver.Basic
import RepresentationTheory.Alignment.Attribute


-- @@ L10-10 verbatim
/-! # Bundled quiver arrows -/


-- @@ L12-12 verbatim
namespace RepresentationTheory.Quiver.Arrows


-- @@ L14-16 verbatim
/-- The type of arrows in a quiver. -/
abbrev Arrow (Q : Type*) [Quiver Q] : Type _ :=
  Σ (source : Q) (target : Q), source ⟶ target


-- @@ L18-18 verbatim
namespace Arrow


-- @@ L20-20 verbatim
variable {Q : Type*} [Quiver Q]


-- @@ L22-23 verbatim
/-- The source vertex of an arrow. -/
def source (h : Arrow Q) : Q := h.1


-- @@ L25-26 verbatim
/-- The target vertex of an arrow. -/
def target (h : Arrow Q) : Q := h.2.1


-- @@ L28-29 verbatim
/-- The morphism underlying an arrow. -/
def hom (h : Arrow Q) : source h ⟶ target h := h.2.2


-- @@ L31-32 verbatim
/-- The source of the arrow built from a morphism is its domain. -/
@[simp] theorem source_mk {i j : Q} (h : i ⟶ j) : source ⟨i, j, h⟩ = i := rfl


-- @@ L34-35 verbatim
/-- The target of the arrow built from a morphism is its codomain. -/
@[simp] theorem target_mk {i j : Q} (h : i ⟶ j) : target ⟨i, j, h⟩ = j := rfl


-- @@ L37-37 verbatim
end Arrow


-- @@ L39-39 verbatim
end RepresentationTheory.Quiver.Arrows


-- @@ L41-43 verbatim
attribute [source_ref "Chapter2/Discussion_quiver_notation" (role := supporting)]
  RepresentationTheory.Quiver.Arrows.Arrow
  RepresentationTheory.Quiver.Arrows.Arrow.hom


-- @@ L45-47 verbatim
attribute [source_ref "Chapter2/Discussion_quiver_notation" (role := primary)]
  RepresentationTheory.Quiver.Arrows.Arrow.source
  RepresentationTheory.Quiver.Arrows.Arrow.target
