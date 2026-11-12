/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import RepresentationTheory.Algebra.AuxiliaryStructure


-- @@ L8-12 verbatim
/-!
# Designated identity elements

Two-sided identity elements for an associative bilinear multiplication.
-/


-- @@ L14-14 verbatim
set_option linter.style.whitespace false


-- @@ L16-16 verbatim
namespace RepresentationTheory.Algebra.AuxiliaryStructure.AuxiliaryStructure


-- @@ L18-19 verbatim
variable (k : Type*) {A : Type*} [Field k] [AddCommGroup A] [Module k A]
  [inst : AuxiliaryStructure k A]


-- @@ L21-25 verbatim
/-- An auxiliary predicate on elements of a module equipped with the referenced auxiliary structure. -/
@[source_ref "Chapter2/Definition2.2.2" (role := supporting),
  source_ref "Chapter2/Discussion_2.1_overview/Derived2" (role := supporting)]
def auxiliaryPredicate (e : A) : Prop :=
  ∀ a : A, inst.op e a = a ∧ inst.op a e = a


-- @@ L27-32 verbatim
/-- Two elements satisfying the auxiliary predicate are equal. -/
theorem auxiliaryPredicate_unique {e e' : A} (he : auxiliaryPredicate k e)
    (he' : auxiliaryPredicate k e') : e = e' := by
  have h1 := (he' e).2
  have h2 := (he e').1
  exact h1.symm.trans h2


-- @@ L34-34 verbatim
end RepresentationTheory.Algebra.AuxiliaryStructure.AuxiliaryStructure
