/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.RingTheory.SimpleModule.Basic
import RepresentationTheory.Alignment.Attribute


-- @@ L11-13 verbatim
/-!
# Auxiliary relations and types for module categories
-/


-- @@ L15-15 verbatim
universe v u


-- @@ L17-17 verbatim
open CategoryTheory


-- @@ L19-19 verbatim
namespace RepresentationTheory.ModuleCat.Auxiliary


-- @@ L21-21 verbatim
section


-- @@ L23-23 verbatim
variable (R : Type u) [Ring R] [Small.{v} R]


-- @@ L25-27 verbatim
/-- An auxiliary relation on objects of the category of modules over a small ring. -/
def auxiliaryModuleRelation' (X Y : ModuleCat.{v} R) : Prop :=
  Nontrivial (Abelian.Ext X Y 1)


-- @@ L29-31 verbatim
/-- An auxiliary relation on objects of the category of modules over a small ring. -/
def auxiliaryModuleRelation'' (X Y : ModuleCat.{v} R) : Prop :=
  auxiliaryModuleRelation' R X Y ∨ auxiliaryModuleRelation' R Y X


-- @@ L33-36 verbatim
/-- An auxiliary relation on objects of the category of modules over a small ring. -/
def auxiliaryModuleRelation''' (X Y : ModuleCat.{v} R) : Prop :=
  IsSimpleModule R X ∧ IsSimpleModule R Y ∧
    (auxiliaryModuleRelation'' R X Y ∨ Nonempty (X ≅ Y))


-- @@ L38-40 verbatim
/-- An auxiliary relation on objects of the category of modules over a small ring. -/
def auxiliaryModuleRelation (X Y : ModuleCat.{v} R) : Prop :=
  Relation.EqvGen (auxiliaryModuleRelation''' R) X Y


-- @@ L42-46 verbatim
/-- Establishes the auxiliary module relation between simple module objects joined by an isomorphism. -/
theorem auxiliaryModuleRelation_of_iso {X Y : ModuleCat.{v} R}
    (hX : IsSimpleModule R X) (hY : IsSimpleModule R Y) (e : X ≅ Y) :
    auxiliaryModuleRelation R X Y :=
  Relation.EqvGen.rel _ _ ⟨hX, hY, Or.inr ⟨e⟩⟩


-- @@ L48-53 verbatim
/-- Transfers one auxiliary module relation to another between simple module objects. -/
theorem auxiliaryModuleRelation_of_auxiliaryModuleRelation'' {X Y : ModuleCat.{v} R}
    (hX : IsSimpleModule R X) (hY : IsSimpleModule R Y)
    (h : auxiliaryModuleRelation'' R X Y) :
    auxiliaryModuleRelation R X Y :=
  Relation.EqvGen.rel _ _ ⟨hX, hY, Or.inl h⟩


-- @@ L55-58 verbatim
/-- The auxiliary relation on module objects is an equivalence relation. -/
theorem auxiliaryModuleRelation_equivalence :
    @Equivalence (ModuleCat.{v} R) (auxiliaryModuleRelation R) :=
  Relation.EqvGen.is_equivalence _


-- @@ L60-68 verbatim
/-- Degree-one extensions between simple module objects form a subsingleton when the auxiliary relation does not hold. -/
theorem subsingleton_ext_one_of_not_auxiliaryModuleRelation {S T : ModuleCat.{v} R}
    (hS : IsSimpleModule R S) (hT : IsSimpleModule R T)
    (hST : ¬ auxiliaryModuleRelation R S T) :
    Subsingleton (Abelian.Ext S T 1) := by
  rw [← not_nontrivial_iff_subsingleton]
  intro hnt
  exact hST (auxiliaryModuleRelation_of_auxiliaryModuleRelation'' (R := R) hS hT
    (Or.inl (show auxiliaryModuleRelation' R S T from hnt)))


-- @@ L70-70 verbatim
end


-- @@ L72-72 verbatim
section Blocks


-- @@ L74-74 verbatim
variable (R : Type u) [Ring R] [Small.{v} R]


-- @@ L76-79 verbatim
/-- An auxiliary relation on objects of the category of modules over a ring. -/
def auxiliaryModuleRelationOverRing (M S : ModuleCat.{v} R) : Prop :=
  IsSimpleModule R S ∧ ∃ (N₁ N₂ : Submodule R M) (_ : N₁ ≤ N₂),
    Nonempty ((↥N₂ ⧸ N₁.comap N₂.subtype) ≃ₗ[R] S)


-- @@ L81-83 verbatim
/-- An auxiliary relation on objects of the category of modules over a small ring. -/
def auxiliaryModuleRelation'''' (S M : ModuleCat.{v} R) : Prop :=
  ∀ T : ModuleCat.{v} R, auxiliaryModuleRelationOverRing R M T → auxiliaryModuleRelation R T S


-- @@ L85-87 verbatim
/-- An auxiliary type associated with a ring. -/
def AuxiliaryType : Type (max u (v + 1)) :=
  { X : ModuleCat.{v} R // IsSimpleModule R X }


-- @@ L89-95 verbatim
/-- A setoid on the auxiliary type associated with a small ring. -/
def auxiliaryTypeSetoid : Setoid (AuxiliaryType.{v} R) where
  r X Y := auxiliaryModuleRelation R X.1 Y.1
  iseqv :=
    ⟨fun X => (auxiliaryModuleRelation_equivalence R).refl X.1,
      fun h => (auxiliaryModuleRelation_equivalence R).symm h,
      fun h₁ h₂ => (auxiliaryModuleRelation_equivalence R).trans h₁ h₂⟩


-- @@ L97-99 verbatim
/-- An auxiliary type associated with a small ring. -/
def AuxiliaryModuleType : Type _ :=
  Quotient (auxiliaryTypeSetoid.{v} R)


-- @@ L101-101 verbatim
end Blocks


-- @@ L103-105 verbatim
end RepresentationTheory.ModuleCat.Auxiliary

-- Recovered exact-module book alignment.

-- @@ L106-106 verbatim
attribute [source_ref "Chapter9/Definition9.5.1" (role := primary)] _root_.RepresentationTheory.ModuleCat.Auxiliary.AuxiliaryModuleType

-- @@ L107-107 verbatim
attribute [source_ref "Chapter9/Definition9.5.1" (role := primary)] _root_.RepresentationTheory.ModuleCat.Auxiliary.auxiliaryModuleRelation

-- @@ L108-108 verbatim
attribute [source_ref "Chapter9/Definition9.5.1" (role := primary)] _root_.RepresentationTheory.ModuleCat.Auxiliary.auxiliaryModuleRelation''''

-- @@ L109-109 verbatim
attribute [source_ref "Chapter9/Definition9.5.1" (role := supporting)] _root_.RepresentationTheory.ModuleCat.Auxiliary.AuxiliaryType

-- @@ L110-110 verbatim
attribute [source_ref "Chapter9/Definition9.5.1" (role := supporting)] _root_.RepresentationTheory.ModuleCat.Auxiliary.auxiliaryModuleRelation'

-- @@ L111-111 verbatim
attribute [source_ref "Chapter9/Definition9.5.1" (role := supporting)] _root_.RepresentationTheory.ModuleCat.Auxiliary.auxiliaryModuleRelation''

-- @@ L112-112 verbatim
attribute [source_ref "Chapter9/Definition9.5.1" (role := supporting)] _root_.RepresentationTheory.ModuleCat.Auxiliary.auxiliaryModuleRelation'''

-- @@ L113-113 verbatim
attribute [source_ref "Chapter9/Definition9.5.1" (role := supporting)] _root_.RepresentationTheory.ModuleCat.Auxiliary.auxiliaryModuleRelationOverRing

-- @@ L114-114 verbatim
attribute [source_ref "Chapter9/Definition9.5.1" (role := supporting)] _root_.RepresentationTheory.ModuleCat.Auxiliary.auxiliaryModuleRelation_equivalence

-- @@ L115-115 verbatim
attribute [source_ref "Chapter9/Definition9.5.1" (role := supporting)] _root_.RepresentationTheory.ModuleCat.Auxiliary.auxiliaryModuleRelation_of_auxiliaryModuleRelation''

-- @@ L116-116 verbatim
attribute [source_ref "Chapter9/Definition9.5.1" (role := supporting)] _root_.RepresentationTheory.ModuleCat.Auxiliary.auxiliaryModuleRelation_of_iso

-- @@ L117-117 verbatim
attribute [source_ref "Chapter9/Definition9.5.1" (role := supporting)] _root_.RepresentationTheory.ModuleCat.Auxiliary.auxiliaryTypeSetoid

-- @@ L118-118 verbatim
attribute [source_ref "Chapter9/Definition9.5.1" (role := supporting)] _root_.RepresentationTheory.ModuleCat.Auxiliary.subsingleton_ext_one_of_not_auxiliaryModuleRelation
