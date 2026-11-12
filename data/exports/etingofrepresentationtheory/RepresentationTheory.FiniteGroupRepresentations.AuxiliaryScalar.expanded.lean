/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute


-- @@ L10-10 verbatim
namespace RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar


-- @@ L12-20 verbatim
/-- An auxiliary complex scalar attached to a finite-dimensional complex representation of a
finite group. -/
@[source_ref "Chapter5/Definition5.1.4" (role := supporting),
  source_ref "Chapter5/Introduction" (role := supporting)]
noncomputable def auxiliaryRepresentationScalar
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ G V) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ * ∑ g : G, LinearMap.trace ℂ V (ρ (g * g))


-- @@ L22-22 verbatim
end RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar
