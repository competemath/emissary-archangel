/-
Copyright (c) 2026 Dominique Lawson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominique Lawson, Henning Basold, Peter Bruin
-/
module

public import LeanPool.DirectedTopologyLean4.Constructions
public import Mathlib.CategoryTheory.ConcreteCategory.Basic


-- @@ L11-13 verbatim
/-!
# LeanPool.DirectedTopologyLean4.DTop
-/


-- @@ L15-21 verbatim
@[expose] public section

/-
  This file contains the definition of `dTopCat`, the category of directed spaces.
  The structure of this file is based on the approach for the undirected version in Mathlib:
  https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Topology/Category/TopCat/Basic.lean
-/


-- @@ L23-23 verbatim
open DirectedMap

-- @@ L24-24 verbatim
open CategoryTheory


-- @@ L26-26 verbatim
universe u


-- @@ L28-32 verbatim
/-- The category of directed topological spaces. -/
structure dTopCat where
  /-- The underlying type of a directed topological space. -/
  carrier : Type u
  [str : DirectedSpace carrier]


-- @@ L34-34 verbatim
namespace dTopCat


-- @@ L36-36 verbatim
attribute [instance] dTopCat.str


-- @@ L38-38 verbatim
instance : CoeSort dTopCat (Type u) := ⟨dTopCat.carrier⟩


-- @@ L40-40 verbatim
attribute [coe] dTopCat.carrier


-- @@ L42-43 verbatim
/-- Construct a bundled `dTopCat` from the underlying type and the typeclass. -/
def of (X : Type u) [DirectedSpace X] : dTopCat := ⟨X⟩


-- @@ L45-46 verbatim
@[simp]
lemma coe_of (X : Type u) [DirectedSpace X] : (of X : Type u) = X := rfl


-- @@ L48-52 expanded
/-- The type of morphisms in `dTopCat`. -/
@[ext]
structure Hom (X Y : dTopCat.{u}) where
  /-- The underlying `DirectedMap`. -/
  hom' : DirectedMap X Y


-- @@ L54-57 verbatim
instance : Category dTopCat where
  Hom X Y := Hom X Y
  id X := ⟨DirectedMap.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩


-- @@ L59-61 expanded
instance concreteCategory : ConcreteCategory.{u} dTopCat (fun X Y => DirectedMap X Y)
    where
  hom := Hom.hom'
  ofHom f := ⟨f⟩


-- @@ L63-63 verbatim
namespace Hom


-- @@ L65-67 expanded
/-- Turn a morphism in `dTopCat` back into a `DirectedMap`. -/
abbrev hom {X Y : dTopCat.{u}} (f : Hom X Y) : DirectedMap X Y :=
  ConcreteCategory.hom (C := dTopCat) f


-- @@ L69-69 verbatim
end Hom


-- @@ L71-73 expanded
/-- Typecheck a `DirectedMap` as a morphism in `dTopCat`. -/
abbrev ofHom {X Y : Type u} [DirectedSpace X] [DirectedSpace Y] (f : DirectedMap X Y) :
    of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := dTopCat) f


-- @@ L75-76 verbatim
@[simp]
lemma hom_id {X : dTopCat.{u}} : (𝟙 X : X ⟶ X).hom = DirectedMap.id X := rfl


-- @@ L78-79 verbatim
@[simp]
lemma id_app (X : dTopCat.{u}) (x : ↑X) : (𝟙 X : X ⟶ X) x = x := rfl


-- @@ L81-83 verbatim
@[simp]
lemma hom_comp {X Y Z : dTopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl


-- @@ L85-87 verbatim
@[simp]
lemma comp_app {X Y Z : dTopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g : X → Z) x = g (f x) := rfl


-- @@ L89-90 verbatim
@[ext]
lemma hom_ext {X Y : dTopCat} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g := Hom.ext hf


-- @@ L92-94 verbatim
@[ext]
lemma ext {X Y : dTopCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w


-- @@ L96-98 expanded
@[simp]
lemma hom_ofHom {X Y : Type u} [DirectedSpace X] [DirectedSpace Y] (f : DirectedMap X Y) :
    (ofHom f).hom = f :=
  rfl


-- @@ L100-101 verbatim
@[simp]
lemma ofHom_hom {X Y : dTopCat} (f : X ⟶ Y) : ofHom (Hom.hom f) = f := rfl


-- @@ L103-104 verbatim
@[simp]
lemma ofHom_id {X : Type u} [DirectedSpace X] : ofHom (DirectedMap.id X) = 𝟙 (of X) := rfl


-- @@ L106-109 expanded
@[simp]
lemma ofHom_comp {X Y Z : Type u} [DirectedSpace X] [DirectedSpace Y] [DirectedSpace Z]
    (f : DirectedMap X Y) (g : DirectedMap Y Z) : ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl


-- @@ L111-111 verbatim
instance subspaceCoe {X : dTopCat} : CoeTC (Set X) dTopCat := ⟨fun s => dTopCat.of s⟩


-- @@ L113-115 verbatim
/-- The inclusion of a directed subspace into its ambient space. -/
def DirectedSubtypeHom {X : dTopCat} (Y : Set X) : (dTopCat.of Y) ⟶ X :=
  ofHom (DirectedSubtypeInclusion (fun s => s ∈ Y))


-- @@ L117-119 verbatim
/-- The inclusion between two directed subspaces, given a subset relation. -/
def DirectedSubsetHom {X : dTopCat} {Y₀ Y₁ : Set X} (h : Y₀ ⊆ Y₁) : (dTopCat.of Y₀) ⟶ Y₁ :=
  ofHom (DirectedSubsetInclusion h)


-- @@ L121-121 verbatim
end dTopCat
