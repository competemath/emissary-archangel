/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Algebra.Opposite
import RepresentationTheory.Alignment.Attribute


-- @@ L10-14 verbatim
/-!
# Actions of rings and algebras

Constructions relating module structures to algebra homomorphisms into linear endomorphisms.
-/


-- @@ L16-16 verbatim
namespace RepresentationTheory.Algebra.ModuleActions


-- @@ L18-22 verbatim
/-- An auxiliary type associated with a ring and an additive commutative group. -/
@[source_ref "Chapter2/Example2.3.3/Derived4" (role := supporting),
  source_ref "Chapter2/Discussion_2.1_overview/Derived5" (role := supporting)]
abbrev RingAddCommGroupAuxiliary (A : Type*) (V : Type*) [Ring A] [AddCommGroup V] :=
  Module A V


-- @@ L24-27 verbatim
/-- A second auxiliary type associated with a ring and an additive commutative group. -/
@[source_ref "Chapter2/Definition2.3.1" (role := supporting)]
abbrev RingAddCommGroupAuxiliary' (A : Type*) (V : Type*) [Ring A] [AddCommGroup V] :=
  Module Aᵐᵒᵖ V


-- @@ L29-29 verbatim
namespace RingAddCommGroupAuxiliary


-- @@ L31-31 verbatim
section Associativity


-- @@ L33-33 verbatim
variable {A V : Type*} [Ring A] [AddCommGroup V]


-- @@ L35-39 verbatim
/-- Scalar multiplication by a product agrees with successive scalar multiplication. -/
@[source_ref "Chapter2/Definition2.3.1" (role := supporting)]
theorem mul_smul [Module A V] (a b : A) (v : V) :
    (a * b) • v = a • (b • v) :=
  SemigroupAction.mul_smul a b v


-- @@ L41-46 verbatim
/-- The action of the opposite of a product is successive action in reversed order. -/
@[source_ref "Chapter2/Definition2.3.1" (role := supporting)]
theorem op_mul_smul [Module Aᵐᵒᵖ V] (a b : A) (v : V) :
    MulOpposite.op (a * b) • v = MulOpposite.op b • (MulOpposite.op a • v) := by
  change (MulOpposite.op b * MulOpposite.op a) • v = _
  exact SemigroupAction.mul_smul _ _ _


-- @@ L48-48 verbatim
end Associativity


-- @@ L50-50 verbatim
section ToAlgHom


-- @@ L52-53 verbatim
variable (k A V : Type*) [CommRing k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]


-- @@ L55-60 verbatim
/-- The scalar action of an algebra defines a homomorphism to linear endomorphisms. -/
@[source_ref "Chapter2/Definition2.3.1" (role := primary),
  source_ref "Chapter2/Discussion_2.1_irreducible_indecomposable/Derived9" (role := supporting),
  source_ref "Chapter2/Discussion_2.1_overview/Derived5" (role := supporting)]
def actionAlgHom : A →ₐ[k] Module.End k V :=
  Algebra.lsmul k k V


-- @@ L62-64 verbatim
/-- Evaluating the action homomorphism at an algebra element gives its scalar action. -/
@[simp]
theorem actionAlgHom_apply (a : A) (v : V) : actionAlgHom k A V a v = a • v := rfl


-- @@ L66-66 verbatim
end ToAlgHom


-- @@ L68-68 verbatim
section OfAlgHom


-- @@ L70-71 verbatim
variable (k A V : Type*) [CommRing k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module k V]


-- @@ L73-77 verbatim
/-- Constructs a module structure from an algebra homomorphism into linear endomorphisms. -/
@[source_ref "Chapter2/Definition2.3.1" (role := primary),
  source_ref "Chapter2/Discussion_2.1_overview/Derived5" (role := supporting)]
abbrev moduleOfAlgHom (ρ : A →ₐ[k] Module.End k V) : Module A V :=
  Module.compHom V ρ.toRingHom


-- @@ L79-82 verbatim
/-- The induced action of an algebra element is its image endomorphism applied to the vector. -/
theorem moduleOfAlgHom_smul_apply (ρ : A →ₐ[k] Module.End k V) (a : A) (v : V) :
    letI := moduleOfAlgHom k A V ρ
    a • v = ρ a v := rfl


-- @@ L84-92 verbatim
/-- The module structure induced by an algebra homomorphism is compatible with the base-ring
action. -/
theorem moduleOfAlgHom_isScalarTower (ρ : A →ₐ[k] Module.End k V) :
    letI := moduleOfAlgHom k A V ρ
    IsScalarTower k A V := by
  letI := moduleOfAlgHom k A V ρ
  refine IsScalarTower.of_algebraMap_smul fun r x => ?_
  rw [moduleOfAlgHom_smul_apply k A V ρ (algebraMap k A r) x, ρ.commutes r,
    Module.algebraMap_end_apply]


-- @@ L94-105 verbatim
/-- The action homomorphism determined by a module structure equals any homomorphism that induces
that structure. -/
@[source_ref "Chapter2/Definition2.3.1" (role := primary),
  source_ref "Chapter2/Discussion_2.1_overview/Derived5" (role := supporting)]
theorem actionAlgHom_eq (ρ : A →ₐ[k] Module.End k V) :
    letI := moduleOfAlgHom k A V ρ
    letI := moduleOfAlgHom_isScalarTower k A V ρ
    actionAlgHom k A V = ρ := by
  letI := moduleOfAlgHom k A V ρ
  letI := moduleOfAlgHom_isScalarTower k A V ρ
  ext a v
  exact (actionAlgHom_apply k A V a v).trans (moduleOfAlgHom_smul_apply k A V ρ a v)


-- @@ L107-107 verbatim
end OfAlgHom


-- @@ L109-109 verbatim
section RoundTrip


-- @@ L111-112 verbatim
variable (k A V : Type*) [CommRing k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]


-- @@ L114-119 verbatim
/-- Reconstructing a module structure from its associated action homomorphism returns the existing
structure. -/
@[source_ref "Chapter2/Definition2.3.1" (role := primary),
  source_ref "Chapter2/Discussion_2.1_overview/Derived5" (role := supporting)]
theorem moduleOfAlgHom_actionAlgHom :
    moduleOfAlgHom k A V (actionAlgHom k A V) = (inferInstance : Module A V) := rfl


-- @@ L121-121 verbatim
end RoundTrip


-- @@ L123-123 verbatim
section RightToAlgHom


-- @@ L125-126 verbatim
variable (k A V : Type*) [CommRing k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module k V] [Module Aᵐᵒᵖ V] [IsScalarTower k Aᵐᵒᵖ V]


-- @@ L128-131 verbatim
/-- The action of the opposite algebra yields an algebra homomorphism into linear endomorphisms. -/
@[source_ref "Chapter2/Definition2.3.1" (role := supporting)]
def oppositeActionAlgHom : Aᵐᵒᵖ →ₐ[k] Module.End k V :=
  actionAlgHom k Aᵐᵒᵖ V


-- @@ L133-137 verbatim
/-- The opposite-action homomorphism evaluates to the given opposite-ring scalar action. -/
@[simp]
theorem oppositeActionAlgHom_apply (a : A) (v : V) :
    oppositeActionAlgHom k A V (MulOpposite.op a) v = MulOpposite.op a • v :=
  rfl


-- @@ L139-139 verbatim
end RightToAlgHom


-- @@ L141-141 verbatim
end RingAddCommGroupAuxiliary


-- @@ L143-143 verbatim
end RepresentationTheory.Algebra.ModuleActions
