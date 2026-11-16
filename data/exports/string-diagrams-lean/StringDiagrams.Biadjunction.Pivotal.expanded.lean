import StringDiagrams.Biadjunction.Trace
import Mathlib.CategoryTheory.Opposites


-- @@ L4-30 verbatim
/-!
# Pivotal structures on bicategories: rotation of 2-morphisms

A pivotal structure `Pivotal B` chooses for every 1-morphism `f : a ⟶ b` a biadjoint
`dual f : b ⟶ a` and a biadjunction `biadj f : f ⊣⊢ dual f` such that *every* 2-morphism
`α : f ⟶ f'` is cyclic for the chosen biadjunctions: its right and left mates agree. The
common mate is the rotation `rotate α : dual f' ⟶ dual f` of `α` (by a half turn, in either
direction). This is the formal content of the rotation invariance of string diagrams:

* `rotate` is a contravariant functor on each hom category (`rotate_id`, `rotate_comp`,
  `rotateFunctor`), and a bijection (`rotateEquiv`);
* rotating back, using the exchanged biadjunctions `(biadj f).symm`, recovers `α`
  (`rightMate_symm_rotate`, `leftMate_symm_rotate`), whichever direction is used;
* rotating twice with the chosen biadjunctions is conjugation by the canonical comparison
  `pivotalIso f : f ≅ dual (dual f)` (`rotate_rotate`), which is therefore natural
  (`pivotalIso_hom_naturality`);
* rotation is compatible with whiskering, up to the canonical comparisons
  `dualCompIso f h : dual (f ≫ h) ≅ dual h ≫ dual f` (`rotate_whiskerRight`,
  `rotate_whiskerLeft`);
* traces are cyclic: `rightTrace (α ≫ β) = rightTrace (β ≫ α)` for all `α : f ⟶ f'`,
  `β : f' ⟶ f` (`Pivotal.rightTrace_comp_comm`, `Pivotal.leftTrace_comp_comm`).

The comparisons `pivotalIso` and `dualCompIso` are defined using the adjunctions in which
`dual f` is a left adjoint (resp. `f ≫ h` is a left adjoint); no condition is imposed on how
the chosen biadjunctions of composites relate to composite biadjunctions, so the natural
isomorphism `pivotalIso` is not asserted to be compatible with composition.
-/


-- @@ L32-32 verbatim
namespace StringDiagrams


-- @@ L34-34 verbatim
open CategoryTheory Bicategory


-- @@ L36-36 verbatim
universe w v u


-- @@ L38-47 verbatim
/-- A pivotal structure on a bicategory: a chosen biadjoint `dual f` of every 1-morphism `f`,
with a biadjunction `biadj f : f ⊣⊢ dual f`, such that every 2-morphism is cyclic for the
chosen biadjunctions. -/
class Pivotal (B : Type u) [Bicategory.{w, v} B] where
  /-- The chosen biadjoint. -/
  dual : ∀ {a b : B}, (a ⟶ b) → (b ⟶ a)
  /-- The chosen biadjunction. -/
  biadj : ∀ {a b : B} (f : a ⟶ b), f ⊣⊢ dual f
  /-- Every 2-morphism is cyclic for the chosen biadjunctions. -/
  isCyclic : ∀ {a b : B} {f f' : a ⟶ b} (α : f ⟶ f'), (biadj f).IsCyclic (biadj f') α


-- @@ L49-49 verbatim
namespace Pivotal


-- @@ L51-51 verbatim
open Biadjunction


-- @@ L53-53 verbatim
variable {B : Type u} [Bicategory.{w, v} B] [Pivotal B] {a b c : B}


-- @@ L55-55 verbatim
section Rotate


-- @@ L57-57 verbatim
variable {f f' f'' : a ⟶ b}


-- @@ L59-62 verbatim
/-- The rotation of a 2-morphism `α : f ⟶ f'`: its (right, equivalently left) mate for the
chosen biadjunctions. -/
def rotate (α : f ⟶ f') : dual f' ⟶ dual f :=
  rightMate (biadj f) (biadj f') α


-- @@ L64-64 verbatim
theorem rotate_eq_rightMate (α : f ⟶ f') : rotate α = rightMate (biadj f) (biadj f') α := rfl


-- @@ L66-67 verbatim
theorem rotate_eq_leftMate (α : f ⟶ f') : rotate α = leftMate (biadj f) (biadj f') α :=
  isCyclic α


-- @@ L69-71 verbatim
@[simp]
theorem rotate_id (f : a ⟶ b) : rotate (𝟙 f) = 𝟙 (dual f) :=
  rightMate_id _


-- @@ L73-75 verbatim
@[simp]
theorem rotate_comp (α : f ⟶ f') (β : f' ⟶ f'') : rotate (α ≫ β) = rotate β ≫ rotate α :=
  rightMate_comp _ _ _ α β


-- @@ L77-79 verbatim
/-- Rotation as a bijection. -/
def rotateEquiv (f f' : a ⟶ b) : (f ⟶ f') ≃ (dual f' ⟶ dual f) :=
  rightMate (biadj f) (biadj f')


-- @@ L81-82 verbatim
@[simp]
theorem rotateEquiv_apply (α : f ⟶ f') : rotateEquiv f f' α = rotate α := rfl


-- @@ L84-85 verbatim
theorem rotate_injective : Function.Injective (rotate : (f ⟶ f') → (dual f' ⟶ dual f)) :=
  (rotateEquiv f f').injective


-- @@ L87-93 verbatim
/-- Rotation as a contravariant functor between hom categories. -/
@[simps]
def rotateFunctor (a b : B) : (a ⟶ b)ᵒᵖ ⥤ (b ⟶ a) where
  obj f := dual f.unop
  map α := rotate α.unop
  map_id _ := rotate_id _
  map_comp _ _ := rotate_comp _ _


-- @@ L95-100 verbatim
/-- Rotating back with the exchanged biadjunctions (in the direction of the right mate)
recovers the original 2-morphism. -/
@[simp]
theorem rightMate_symm_rotate (α : f ⟶ f') :
    rightMate (biadj f').symm (biadj f).symm (rotate α) = α := by
  rw [rotate_eq_leftMate, rightMate_symm_leftMate]


-- @@ L102-107 verbatim
/-- Rotating back with the exchanged biadjunctions (in the direction of the left mate)
recovers the original 2-morphism. -/
@[simp]
theorem leftMate_symm_rotate (α : f ⟶ f') :
    leftMate (biadj f').symm (biadj f).symm (rotate α) = α :=
  leftMate_symm_rightMate _ _ α


-- @@ L109-111 verbatim
/-- The rotation of `α` is cyclic for the exchanged biadjunctions. -/
theorem isCyclic_rotate (α : f ⟶ f') : IsCyclic (biadj f').symm (biadj f).symm (rotate α) :=
  (isCyclic α).rightMate


-- @@ L113-113 verbatim
end Rotate


-- @@ L115-115 verbatim
/-! ## Double rotation -/


-- @@ L117-117 verbatim
section Double


-- @@ L119-122 verbatim
/-- The canonical comparison `f ≅ dual (dual f)`: `f` and `dual (dual f)` are both right
adjoints of `dual f`. -/
def pivotalIso (f : a ⟶ b) : f ≅ dual (dual f) :=
  conjugateIsoEquiv (biadj f).right (biadj (dual f)).left (Iso.refl _)


-- @@ L124-125 verbatim
theorem pivotalIso_hom (f : a ⟶ b) :
    (pivotalIso f).hom = rightMate (biadj (dual f)) (biadj f).symm (𝟙 (dual f)) := rfl


-- @@ L127-131 verbatim
/-- Rotating twice is conjugation by the canonical comparisons `f ≅ dual (dual f)`. -/
theorem rotate_rotate {f f' : a ⟶ b} (α : f ⟶ f') :
    rotate (rotate α) = (pivotalIso f).inv ≫ α ≫ (pivotalIso f').hom := by
  rw [rotate, rightMate_eq_comp' _ (biadj f').symm _ (biadj f).symm, rightMate_symm_rotate]
  rfl


-- @@ L133-136 verbatim
/-- The canonical comparison `f ≅ dual (dual f)` is natural. -/
theorem pivotalIso_hom_naturality {f f' : a ⟶ b} (α : f ⟶ f') :
    α ≫ (pivotalIso f').hom = (pivotalIso f).hom ≫ rotate (rotate α) := by
  rw [rotate_rotate, Iso.hom_inv_id_assoc]


-- @@ L138-138 verbatim
end Double


-- @@ L140-140 verbatim
/-! ## Whiskering -/


-- @@ L142-142 verbatim
section Whisker


-- @@ L144-147 verbatim
/-- The canonical comparison `dual (f ≫ h) ≅ dual h ≫ dual f`: both are right adjoints of
`f ≫ h`. -/
def dualCompIso (f : a ⟶ b) (h : b ⟶ c) : dual (f ≫ h) ≅ dual h ≫ dual f :=
  conjugateIsoEquiv (biadj (f ≫ h)).left ((biadj f).comp (biadj h)).left (Iso.refl _)


-- @@ L149-154 verbatim
/-- Rotation commutes with right whiskering, up to the canonical comparisons. -/
theorem rotate_whiskerRight {f f' : a ⟶ b} (α : f ⟶ f') (h : b ⟶ c) :
    rotate (α ▷ h) = (dualCompIso f' h).hom ≫ dual h ◁ rotate α ≫ (dualCompIso f h).inv := by
  rw [rotate, rightMate_eq_comp' _ ((biadj f).comp (biadj h)) _ ((biadj f').comp (biadj h)),
    rightMate_whiskerRight]
  rfl


-- @@ L156-161 verbatim
/-- Rotation commutes with left whiskering, up to the canonical comparisons. -/
theorem rotate_whiskerLeft (h : c ⟶ a) {f f' : a ⟶ b} (α : f ⟶ f') :
    rotate (h ◁ α) = (dualCompIso h f').hom ≫ rotate α ▷ dual h ≫ (dualCompIso h f).inv := by
  rw [rotate, rightMate_eq_comp' _ ((biadj h).comp (biadj f)) _ ((biadj h).comp (biadj f')),
    rightMate_whiskerLeft]
  rfl


-- @@ L163-163 verbatim
end Whisker


-- @@ L165-165 verbatim
/-! ## Traces -/


-- @@ L167-167 verbatim
section Trace


-- @@ L169-169 verbatim
variable {f f' : a ⟶ b}


-- @@ L171-172 verbatim
/-- The right trace for the chosen biadjunction. -/
abbrev rightTrace (α : f ⟶ f) : 𝟙 a ⟶ 𝟙 a := (biadj f).rightTrace α


-- @@ L174-175 verbatim
/-- The left trace for the chosen biadjunction. -/
abbrev leftTrace (α : f ⟶ f) : 𝟙 b ⟶ 𝟙 b := (biadj f).leftTrace α


-- @@ L177-179 verbatim
theorem rightTrace_comp_comm (α : f ⟶ f') (β : f' ⟶ f) :
    rightTrace (α ≫ β) = rightTrace (β ≫ α) :=
  rightTrace_comp_comm_of_isCyclic_left (isCyclic α) β


-- @@ L181-183 verbatim
theorem leftTrace_comp_comm (α : f ⟶ f') (β : f' ⟶ f) :
    leftTrace (α ≫ β) = leftTrace (β ≫ α) :=
  leftTrace_comp_comm_of_isCyclic_left (isCyclic α) β


-- @@ L185-189 verbatim
/-- The right trace of `α` is the left trace of its rotation, for the exchanged
biadjunction. -/
theorem rightTrace_eq_leftTrace_rotate (α : f ⟶ f) :
    rightTrace α = (biadj f).symm.leftTrace (rotate α) :=
  rightTrace_eq_leftTrace_rightMate _ α


-- @@ L191-195 verbatim
/-- The left trace of `α` is the right trace of its rotation, for the exchanged
biadjunction. -/
theorem leftTrace_eq_rightTrace_rotate (α : f ⟶ f) :
    leftTrace α = (biadj f).symm.rightTrace (rotate α) :=
  leftTrace_eq_rightTrace_rightMate _ α


-- @@ L197-197 verbatim
end Trace


-- @@ L199-199 verbatim
end Pivotal


-- @@ L201-201 verbatim
end StringDiagrams
