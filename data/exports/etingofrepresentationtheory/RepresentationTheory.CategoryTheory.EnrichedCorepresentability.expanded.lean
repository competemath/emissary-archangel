/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
import RepresentationTheory.Alignment.Attribute


-- @@ L9-9 verbatim
open CategoryTheory


-- @@ L11-11 verbatim
namespace RepresentationTheory.CategoryTheory.EnrichedCorepresentability


-- @@ L13-13 verbatim
universe w v u


-- @@ L15-15 verbatim
variable (V : Type v) [Category.{w} V] [MonoidalCategory V]


-- @@ L17-19 verbatim
/-- An auxiliary type operator parameterized by a monoidal category. -/
@[source_ref "Chapter7/Discussion_after_Example7.1.5" (role := supporting)]
abbrev AuxiliaryMonoidalTypeOperator (C : Type u) := CategoryTheory.EnrichedCategory V C


-- @@ L21-25 verbatim
/-- The composition morphism between enriched hom-objects. -/
@[source_ref "Chapter7/Discussion_after_Example7.1.5" (role := primary)]
abbrev enrichedComposition {C : Type u} [CategoryTheory.EnrichedCategory V C]
    (X Y Z : C) :=
  CategoryTheory.eComp V X Y Z


-- @@ L27-27 verbatim
variable {C : Type u} [Category C] [EnrichedOrdinaryCategory V C]


-- @@ L29-33 verbatim
/-- States that a functor from an enriched ordinary category into its enriching category is
enriched corepresentable. -/
@[source_ref "Chapter7/Remark7.5.2" (role := supporting)]
def IsEnrichedCorepresentable (F : Functor C V) : Prop :=
  ∃ X : C, Nonempty (F ≅ eCoyoneda V X)


-- @@ L35-38 verbatim
/-- Characterizes enriched corepresentability by isomorphism with an enriched co-Yoneda functor. -/
theorem isEnrichedCorepresentable_iff (F : Functor C V) :
    IsEnrichedCorepresentable V F ↔ ∃ X : C, Nonempty (F ≅ eCoyoneda V X) :=
  Iff.rfl


-- @@ L40-44 verbatim
/-- The enriched co-Yoneda functor is enriched corepresentable. -/
@[source_ref "Chapter7/Remark7.5.2" (role := primary)]
theorem isEnrichedCorepresentable_eCoyoneda (X : C) :
    IsEnrichedCorepresentable V (eCoyoneda V X) :=
  ⟨X, ⟨Iso.refl _⟩⟩


-- @@ L46-49 verbatim
/-- The enriched co-Yoneda functor has a nonempty type of self-isomorphisms. -/
theorem eCoyoneda_selfIso_nonempty (X : C) :
    Nonempty (eCoyoneda V X ≅ eCoyoneda V X) :=
  ⟨Iso.refl _⟩


-- @@ L51-51 verbatim
end RepresentationTheory.CategoryTheory.EnrichedCorepresentability
