/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.AuxiliaryPredicates
import RepresentationTheory.Alignment.Attribute


-- @@ L10-10 verbatim
namespace RepresentationTheory.Module.Auxiliary


-- @@ L12-18 verbatim
/-- An auxiliary uniqueness result for module elements. -/
@[source_ref "Chapter2/Proposition2.2.3" (role := primary)]
theorem auxiliary_unique (k : Type*) {A : Type*} [Field k] [AddCommGroup A] [Module k A]
    [RepresentationTheory.Algebra.AuxiliaryStructure.AuxiliaryStructure k A] {e e' : A}
    (he : RepresentationTheory.Algebra.AuxiliaryStructure.AuxiliaryStructure.auxiliaryPredicate k e)
    (he' : RepresentationTheory.Algebra.AuxiliaryStructure.AuxiliaryStructure.auxiliaryPredicate k e') : e = e' :=
  RepresentationTheory.Algebra.AuxiliaryStructure.AuxiliaryStructure.auxiliaryPredicate_unique k he he'


-- @@ L20-20 verbatim
end RepresentationTheory.Module.Auxiliary
