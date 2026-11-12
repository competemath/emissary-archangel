/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Lie.Abelian
import Mathlib.Algebra.Lie.OfAssociative
import RepresentationTheory.Algebra.Lie.Module.Predicates
import RepresentationTheory.Alignment.Attribute


-- @@ L11-11 verbatim
/-! # Basic Lie module constructions -/


-- @@ L13-13 verbatim
set_option linter.style.whitespace false


-- @@ L15-15 verbatim
namespace RepresentationTheory.Algebra.Lie.Module.Examples


-- @@ L17-17 verbatim
open RepresentationTheory.Algebra.Lie.Module.Predicates


-- @@ L19-19 verbatim
attribute [local instance 100] LieRing.ofAssociativeRing


-- @@ L21-21 verbatim
variable (k : Type*) [CommRing k] (L : Type*) [LieRing L] [LieAlgebra k L]


-- @@ L23-26 verbatim
/-- A property of the singleton trivial Lie module. -/
@[source_ref "Chapter2/Example2.9.8" (role := primary)]
theorem punitTrivialModuleProperty :
    LieModule.AuxiliaryPredicate k L (TrivialLieModule k L PUnit) := inferInstance


-- @@ L28-32 verbatim
omit [CommRing k] [LieRing L] [LieAlgebra k L] in
/-- The singleton trivial Lie module is a subsingleton. -/
@[source_ref "Chapter2/Example2.9.8" (role := supporting)]
theorem punitTrivialModule_subsingleton :
    Subsingleton (TrivialLieModule k L PUnit) := inferInstanceAs (Subsingleton PUnit)


-- @@ L34-34 verbatim
variable (V : Type*) [AddCommGroup V] [Module k V]


-- @@ L36-39 verbatim
/-- A property of the trivial Lie module. -/
@[source_ref "Chapter2/Example2.9.8" (role := supporting)]
theorem trivialModuleProperty :
    LieModule.AuxiliaryPredicate k L (TrivialLieModule k L V) := inferInstance


-- @@ L41-45 verbatim
omit [CommRing k] [LieAlgebra k L] [Module k V] in
/-- The action bracket on a trivial Lie module is zero. -/
@[source_ref "Chapter2/Example2.9.8" (role := supporting)]
theorem trivialModule_bracket_eq_zero
    (a : L) (v : TrivialLieModule k L V) : ⁅a, v⁆ = 0 := rfl


-- @@ L47-49 verbatim
/-- A property associated with a Lie algebra used as both displayed type parameters. -/
@[source_ref "Chapter2/Example2.9.8" (role := supporting)]
theorem selfProperty : LieModule.AuxiliaryPredicate k L L := inferInstance


-- @@ L51-54 verbatim
/-- The Lie homomorphism from a Lie algebra to its linear endomorphisms induced by the bracket. -/
@[source_ref "Chapter2/Example2.9.8" (role := supporting)]
noncomputable def adjointRepresentation : L →ₗ⁅k⁆ Module.End k L :=
  LieAlgebra.ad k L


-- @@ L56-59 verbatim
/-- The adjoint representation evaluated on two elements is their bracket. -/
@[source_ref "Chapter2/Example2.9.8" (role := primary)]
theorem adjointRepresentation_apply (a b : L) :
    LieAlgebra.ad k L a b = ⁅a, b⁆ := LieAlgebra.ad_apply k L a b


-- @@ L61-65 verbatim
/-- The adjoint map preserves brackets. -/
@[source_ref "Chapter2/Example2.9.8" (role := primary)]
theorem adjointRepresentation_bracket (a b : L) :
    LieAlgebra.ad k L ⁅a, b⁆ = ⁅LieAlgebra.ad k L a, LieAlgebra.ad k L b⁆ :=
  LieHom.map_lie (LieAlgebra.ad k L) a b


-- @@ L67-67 verbatim
end RepresentationTheory.Algebra.Lie.Module.Examples
