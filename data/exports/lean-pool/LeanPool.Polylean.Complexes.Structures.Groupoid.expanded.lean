/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/
module

public import LeanPool.Polylean.Complexes.Structures.Category


-- @@ L10-14 verbatim
/-!
# LeanPool.Polylean.Complexes.Structures.Groupoid

Imported Lean Pool material for `LeanPool.Polylean.Complexes.Structures.Groupoid`.
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
namespace LeanPool.Polylean


-- @@ L20-25 expanded
/--
A `Groupoid` is defined as a `Category` in which every morphism has an inverse satisfying certain conditions. -/
class Groupoid (S : Sort _) extends Category S where
  /-- The inverse of a morphism. -/
  inv : {X Y : S} → (Quiver.hom X Y) → (Quiver.hom Y X)
  inv_comp_id :
    {X Y : S} → (g : Quiver.hom X Y) → CategoryStruct.comp (inv g) g = CategoryStruct.id Y
  comp_inv_id :
    {X Y : S} → (g : Quiver.hom X Y) → CategoryStruct.comp g (inv g) = CategoryStruct.id X


-- @@ L27-27 verbatim
namespace Groupoid


-- @@ L29-29 verbatim
open Category


-- @@ L31-31 verbatim
attribute [simp] inv_comp_id

-- @@ L32-32 verbatim
attribute [simp] comp_inv_id


-- @@ L34-34 expanded
variable {S : Sort _} [G : Groupoid S] {X Y Z : S} (g g' : Quiver.hom X Y) (h h' : Quiver.hom Y Z)


-- @@ L36-37 verbatim
/-- Groupoid inverse notation. -/
postfix:max " ⁻¹ " => Groupoid.inv -- type as `\inv`


-- @@ L39-40 expanded
@[simp]
theorem left_inv_cancel : CategoryStruct.comp g⁻¹ (CategoryStruct.comp g h) = h := by
  rw [← comp_assoc]; simp


-- @@ L42-44 expanded
@[simp]
theorem id_inv : (CategoryStruct.id X)⁻¹ = CategoryStruct.id X :=
  by
  have := left_inv_cancel (CategoryStruct.id X) (CategoryStruct.id X)
  rw [comp_id, comp_id] at this; assumption


-- @@ L46-48 expanded
@[simp]
theorem inv_inv : (g⁻¹)⁻¹ = g := by
  have := left_inv_cancel (g⁻¹) g
  rw [inv_comp_id, comp_id] at this; assumption


-- @@ L50-52 expanded
@[simp]
theorem left_cancel_inv (h : Quiver.hom X Z) :
    CategoryStruct.comp g (CategoryStruct.comp g⁻¹ h) = h :=
  by
  have := left_inv_cancel g⁻¹ h
  rw [inv_inv] at this; assumption


-- @@ L54-56 expanded
@[simp]
theorem inv_comp : (CategoryStruct.comp g h)⁻¹ = CategoryStruct.comp h⁻¹ g⁻¹ :=
  by
  have := left_cancel_inv (CategoryStruct.comp g h)⁻¹ (CategoryStruct.comp h⁻¹ g⁻¹)
  simp at this; assumption


-- @@ L58-60 expanded
@[simp]
theorem left_cancel : CategoryStruct.comp g h = CategoryStruct.comp g h' ↔ h = h' :=
  ⟨fun hyp => by have := congrArg (CategoryStruct.comp g⁻¹ ·) hyp; simp at this; exact this,
    congrArg _⟩


-- @@ L62-64 expanded
@[simp]
theorem right_cancel : CategoryStruct.comp g h = CategoryStruct.comp g' h ↔ g = g' :=
  ⟨fun hyp => by have := congrArg (CategoryStruct.comp · h⁻¹) hyp; simp at this; exact this,
    congrArg (CategoryStruct.comp · h)⟩


-- @@ L66-67 expanded
@[simp]
theorem left_cancel_id : (g = CategoryStruct.comp g e) ↔ CategoryStruct.id Y = e := by
  have := left_cancel g (CategoryStruct.id _) e; simp at this; exact this


-- @@ L69-70 expanded
@[simp]
theorem left_cancel_id' : (CategoryStruct.comp g e = g) ↔ e = CategoryStruct.id Y := by
  have := left_cancel g e (CategoryStruct.id Y); simp at this; exact this


-- @@ L72-73 expanded
@[simp]
theorem right_cancel_id : (g = CategoryStruct.comp e g) ↔ CategoryStruct.id X = e := by
  have := right_cancel (CategoryStruct.id X) e g; simp at this; exact this


-- @@ L75-76 expanded
@[simp]
theorem right_cancel_id' : (CategoryStruct.comp e g = g) ↔ e = CategoryStruct.id X := by
  have := right_cancel e (CategoryStruct.id X) g; simp at this; exact this


-- @@ L78-78 verbatim
end Groupoid



-- @@ L81-81 verbatim
namespace Groupoid


-- @@ L83-85 verbatim
/-- A `Functor` is a morphism of `Groupoid`s. -/
structure Functor {S S' : Sort _} (G : Groupoid S) (G' : Groupoid S')
    extends Category.Functor G.toCategory G'.toCategory


-- @@ L87-87 verbatim
namespace Functor


-- @@ L89-89 verbatim
variable {R S T : Sort _} [F : Groupoid R] [G : Groupoid S] [H : Groupoid T]

-- @@ L90-90 verbatim
variable (Ψ : Groupoid.Functor F G) (Φ : Groupoid.Functor G H)


-- @@ L92-93 expanded
theorem map_id' {X : S} : Φ.map (CategoryStruct.id X) = CategoryStruct.id (Φ.obj X) := by simp_all


-- @@ L95-98 expanded
@[simp]
theorem map_inv {X Y : S} (g : Quiver.hom X Y) : Φ.map g⁻¹ = (Φ.map g)⁻¹ :=
  by
  apply (Groupoid.left_cancel (Φ.map g) _ _).mp
  rw [← Φ.map_comp]
  simp


-- @@ L100-100 verbatim
end Functor


-- @@ L102-102 verbatim
end Groupoid

-- @@ L103-103 verbatim
end LeanPool.Polylean
