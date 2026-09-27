/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/
module

public import LeanPool.Polylean.Complexes.Structures.Quiver


-- @@ L10-14 verbatim
/-!
# LeanPool.Polylean.Complexes.Structures.Category

Imported Lean Pool material for `LeanPool.Polylean.Complexes.Structures.Category`.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
namespace LeanPool.Polylean


-- @@ L20-25 expanded
/--
The definition of a `CategoryStruct`, a barebones structure for a category containing none of the axioms (following `mathlib`). -/
class CategoryStruct (Obj : Sort _) extends Quiver Obj where
  /-- The identity morphism at an object. -/
  id : (X : Obj) → (Quiver.hom X X)
  /-- Composition of composable morphisms. -/
  comp : {X Y Z : Obj} → (Quiver.hom X Y) → (Quiver.hom Y Z) → (Quiver.hom X Z)


-- @@ L27-27 verbatim
attribute [reducible] CategoryStruct.id

-- @@ L28-28 verbatim
attribute [reducible] CategoryStruct.comp


-- @@ L30-31 verbatim
/-- Identity morphism notation. -/
notation "𝟙" => CategoryStruct.id -- type as `\b1`

-- @@ L32-33 verbatim
/-- Morphism composition notation. -/
infixr:80 " ≫ " => CategoryStruct.comp -- type as `\gg`

-- @@ L34-35 verbatim
/-- Reverse-order morphism composition notation. -/
infixl:80 " ⊚ " => λ f g => CategoryStruct.comp g f


-- @@ L37-42 expanded
/-- The definition of a Category. -/
class Category (Obj : Sort _) extends CategoryStruct Obj where
  id_comp : {X Y : Obj} → (f : Quiver.hom X Y) → CategoryStruct.comp (CategoryStruct.id X) f = f
  comp_id : {X Y : Obj} → (f : Quiver.hom X Y) → CategoryStruct.comp f (CategoryStruct.id Y) = f
  comp_assoc :
    {W X Y Z : Obj} →
      (f : Quiver.hom W X) →
        (g : Quiver.hom X Y) →
          (h : Quiver.hom Y Z) →
            CategoryStruct.comp (CategoryStruct.comp f g) h =
              CategoryStruct.comp f (CategoryStruct.comp g h)


-- @@ L44-44 verbatim
attribute [simp] Category.id_comp

-- @@ L45-45 verbatim
attribute [simp] Category.comp_id

-- @@ L46-46 verbatim
attribute [simp] Category.comp_assoc


-- @@ L48-48 verbatim
namespace Category


-- @@ L50-55 expanded
/-- A functor is a morphism of categories. -/
structure Functor {C D : Sort _} (𝓒 : Category C) (𝓓 : Category D) extends
    Quiver.PreFunctor 𝓒.toQuiver 𝓓.toQuiver where
  map_id : (X : C) → map (CategoryStruct.id X) = CategoryStruct.id (obj X)
  map_comp :
    {X Y Z : C} →
      (f : Quiver.hom X Y) →
        (g : Quiver.hom Y Z) → map (CategoryStruct.comp f g) = CategoryStruct.comp (map f) (map g)


-- @@ L57-57 verbatim
namespace Functor


-- @@ L59-60 verbatim
/-- Functor notation between categories. -/
infixr:26 " ⥤ " => Functor -- type as `\func`


-- @@ L62-62 verbatim
attribute [simp] map_id

-- @@ L63-63 verbatim
attribute [simp] map_comp


-- @@ L65-68 expanded
/-- The identity functor. -/
@[simp]
protected def id (C : Sort _) [𝓒 : Category C] : Functor 𝓒 𝓒 :=
  -- TODO Use `..` notation : { .. , mapId := λ _ => rfl, mapComp := λ _ _ => rfl }
  
  { obj := id, map := id, map_id := λ _ => rfl, map_comp := λ _ _ => rfl }


-- @@ L70-74 expanded
/-- Composition of functors. -/
def comp {C D E : Sort _} {𝓒 : Category C} {𝓓 : Category D} {𝓔 : Category E} (F : Functor 𝓒 𝓓)
    (G : Functor 𝓓 𝓔) : Functor 𝓒 𝓔 :=
  -- TODO Use `..` notation
  
  { obj := G.obj ∘ F.obj, map := G.map ∘ F.map, map_id := by intro; simp,
    map_comp := by intros; simp }


-- @@ L76-77 verbatim
/-- Functor composition notation. -/
infix:80 " ⋙ " => comp



-- @@ L80-81 expanded
/-- The object map of a composed functor is the composite object map. -/
@[simp]
theorem comp_obj : (Φ.obj ∘ Ψ.obj) = (comp Ψ Φ).obj :=
  rfl


-- @@ L83-84 expanded
/-- Pointwise form of `Category.Functor.comp_obj`. -/
@[simp]
theorem comp_obj' : ∀ x, (Φ.obj (Ψ.obj x)) = (comp Ψ Φ).obj x := λ _ => rfl


-- @@ L86-86 verbatim
end Functor


-- @@ L88-88 verbatim
end Category



-- @@ L91-91 verbatim
namespace Path


-- @@ L93-93 verbatim
variable {C : Sort _} [𝓒 : Category C]


-- @@ L95-98 expanded
/-- Compose the arrows appearing in a category path. -/
def compose {X Y : C} : @Path C 𝓒.toQuiver X Y → (Quiver.hom X Y)
  | .nil => CategoryStruct.id _
  | .cons e p => CategoryStruct.comp e p.compose


-- @@ L100-100 expanded
@[simp]
theorem compose_nil {X : C} : (Path.nil' X).compose = CategoryStruct.id X :=
  rfl


-- @@ L102-107 expanded
/-- Composing an appended path equals composing the two pieces. -/
theorem compose_append {X Y Z : C} :
    {p : Path X Y} → {q : Path Y Z} → (append p q).compose = CategoryStruct.comp p.compose q.compose
  | .nil, _ => by simp
  | .cons _ _, _ => by
    dsimp [append, compose]
    rw [compose_append, Category.comp_assoc]


-- @@ L109-109 verbatim
end Path


-- @@ L111-119 verbatim
/-- Paths in a quiver form a category under concatenation. -/
instance (priority := low) Quiver.PathCategory {V : Sort _} [Quiver V] : Category V where
  hom := Path
  id := Path.nil'
  comp := Path.append

  id_comp := Path.nil_append
  comp_id := Path.append_nil
  comp_assoc := Path.append_assoc


-- @@ L121-121 verbatim
namespace Quiver


-- @@ L123-126 verbatim
/-- Embedding of a `Quiver` into its category of paths. -/
def toPathCategory {V : Sort _} [Q : Quiver V] : Quiver.PreFunctor Q Q.PathCategory.toQuiver where
  obj := id
  map := Quiver.toPath


-- @@ L128-128 verbatim
end Quiver

-- @@ L129-129 verbatim
end LeanPool.Polylean
