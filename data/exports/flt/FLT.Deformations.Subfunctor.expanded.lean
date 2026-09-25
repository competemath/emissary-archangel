/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Subfunctor.Basic


-- @@ L11-16 verbatim
/-!
# Subfunctors

Basic constructions for subfunctors of functors valued in `Type`, including
the subfunctor cut out by a subset of the value at a terminal object.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
universe w v u


-- @@ L22-22 verbatim
open Opposite CategoryTheory


-- @@ L24-24 verbatim
namespace CategoryTheory

-- @@ L25-25 verbatim
namespace Subfunctor


-- @@ L27-27 verbatim
variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w)


-- @@ L29-35 verbatim
/-- The subfunctor defined by pulling back a subset of the terminal component. -/
def ofIsTerminal {X : C} (hX : Limits.IsTerminal X) (s : Set (F.obj X)) :
    Subfunctor F where
  obj U := F.map (hX.from U) ⁻¹' s
  map {U V} i := by
    simp only [← Set.preimage_comp, ← hX.comp_from i, F.map_comp]
    rfl


-- @@ L37-37 verbatim
end Subfunctor

-- @@ L38-38 verbatim
end CategoryTheory
