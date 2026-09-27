/-
Copyright (c) 2026 Dominique Lawson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominique Lawson, Henning Basold, Peter Bruin
-/
module

public import LeanPool.DirectedTopologyLean4.DirectedPathHomotopy
public import LeanPool.DirectedTopologyLean4.DTop


-- @@ L11-13 verbatim
/-!
# LeanPool.DirectedTopologyLean4.FundamentalCategory
-/


-- @@ L15-21 verbatim
@[expose] public section

/-
  This file contains the definition of the fundamental category of a directed space.
  We follow the structure of the undirected version found at:
  https://leanprover-community.github.io/mathlib_docs/algebraic_topology/fundamental_groupoid/basic.html#fundamental_groupoid
-/


-- @@ L23-23 verbatim
open DirectedMap

-- @@ L24-24 verbatim
open CategoryTheory


-- @@ L26-26 verbatim
universe u v

-- @@ L27-27 verbatim
variable {X : Type u} {Y : Type v} [DirectedSpace X] [DirectedSpace Y] {x₀ x₁ : X}


-- @@ L29-29 verbatim
open scoped unitInterval


-- @@ L31-31 verbatim
noncomputable section


-- @@ L33-33 verbatim
namespace Dipath


-- @@ L35-35 verbatim
namespace Dihomotopy


-- @@ L37-37 verbatim
open Path.Homotopy


-- @@ L39-39 verbatim
section assoc


-- @@ L41-65 verbatim
lemma transAssocReparamAux_directed : DirectedMap.Directed
    ({ toFun := fun t => ⟨transAssocReparamAux t, transAssocReparamAux_mem_I t⟩
       continuous_toFun := Continuous.subtype_mk continuous_transAssocReparamAux _ } :
      C(I, I)) := by
  apply DirectedUnitInterval.directed_of_monotone _
  intros x y hxy
  unfold transAssocReparamAux
  simp only [one_div, ContinuousMap.coe_mk, Subtype.mk_le_mk]
  have hxy' : (x : ℝ) ≤ (y : ℝ) := hxy
  split_ifs with h₀ h₁ h₂ h₃ h₄ h₅
  · linarith
  · linarith
  · push Not at h₂
    have hy_pos : 0 ≤ (y : ℝ) := le_trans (by norm_num) (le_of_lt h₂)
    have h₀' : (x : ℝ) ≤ 4⁻¹ := h₀
    nlinarith
  · linarith
  · linarith
  · push Not at h₅
    have h₃' : (x : ℝ) ≤ 2⁻¹ := h₃
    have h₅' : (2⁻¹ : ℝ) < y := h₅
    nlinarith
  · linarith
  · linarith
  · simp_all


-- @@ L67-72 expanded
/-- The directed self-map of the unit interval used to associate triple concatenations of
dipaths. -/
def transAssocReparamAuxMap : DirectedMap I I
    where
  toFun := fun t => ⟨transAssocReparamAux t, transAssocReparamAux_mem_I t⟩
  continuous_toFun := Continuous.subtype_mk continuous_transAssocReparamAux _
  directed_toFun := transAssocReparamAux_directed


-- @@ L74-83 verbatim
lemma trans_assoc_reparam_directed {x₀ x₁ x₂ x₃ : X} (p : Dipath x₀ x₁) (q : Dipath x₁ x₂)
    (r : Dipath x₂ x₃) :
    (p.trans q).trans r = (p.trans (q.trans r)).reparam
      transAssocReparamAuxMap
      (Subtype.ext transAssocReparamAux_zero)
      (Subtype.ext transAssocReparamAux_one) := by
  ext t
  rw [show (p.trans q).trans r t = (p.toPath.trans q.toPath).trans r.toPath t from rfl,
    trans_assoc_reparam p.toPath q.toPath r.toPath]
  rfl


-- @@ L85-93 verbatim
/-- For any three dipaths `p q r`, `(p.trans q).trans r` is dihomotopic with
`p.trans (q.trans r)`. -/
theorem trans_assoc {x₀ x₁ x₂ x₃ : X} (p : Dipath x₀ x₁) (q : Dipath x₁ x₂) (r : Dipath x₂ x₃) :
    ((p.trans q).trans r).Dihomotopic (p.trans (q.trans r)) := by
  have := Dihomotopic.reparam (p.trans (q.trans r)) transAssocReparamAuxMap
    (Subtype.ext transAssocReparamAux_zero)
    (Subtype.ext transAssocReparamAux_one)
  rw [←trans_assoc_reparam_directed] at this
  exact Relation.EqvGen.symm _ _ this


-- @@ L95-95 verbatim
end assoc


-- @@ L97-97 verbatim
end Dihomotopy


-- @@ L99-104 verbatim
end Dipath

/-
 Definition of the fundamental category and of the functor sending a directed space to its
 fundamental category
-/

-- @@ L105-109 verbatim
/-- The fundamental category of a type, wrapping the underlying element as `as`. -/
@[ext]
structure FundamentalCategory (X : Type u) where
  /-- The underlying element of the type. -/
  as : X


-- @@ L111-111 verbatim
namespace FundamentalCategory


-- @@ L113-119 verbatim
/-- The fundamental-category wrapper is type-equivalent to the underlying type. -/
@[simps]
def equiv (X : Type*) : FundamentalCategory X ≃ X where
  toFun x := x.as
  invFun x := .mk x
  left_inv _ := rfl
  right_inv _ := rfl


-- @@ L121-124 verbatim
@[simp]
lemma isEmpty_iff (X : Type*) :
    IsEmpty (FundamentalCategory X) ↔ IsEmpty X :=
  equiv _ |>.isEmpty_congr


-- @@ L126-128 verbatim
instance (X : Type*) [IsEmpty X] :
    IsEmpty (FundamentalCategory X) :=
  equiv _ |>.isEmpty


-- @@ L130-133 verbatim
@[simp]
lemma nonempty_iff (X : Type*) :
    Nonempty (FundamentalCategory X) ↔ Nonempty X :=
  equiv _ |>.nonempty_congr


-- @@ L135-137 verbatim
instance (X : Type*) [Nonempty X] :
    Nonempty (FundamentalCategory X) :=
  equiv _ |>.nonempty


-- @@ L139-142 verbatim
@[simp]
lemma subsingleton_iff (X : Type*) :
    Subsingleton (FundamentalCategory X) ↔ Subsingleton X :=
  equiv _ |>.subsingleton_congr


-- @@ L144-146 verbatim
instance (X : Type*) [Subsingleton X] :
    Subsingleton (FundamentalCategory X) :=
  equiv _ |>.subsingleton



-- @@ L149-150 verbatim
instance {X : Type u} [Inhabited X] : Inhabited (FundamentalCategory X) :=
  ⟨⟨default⟩⟩


-- @@ L152-152 verbatim
attribute [local instance] Dipath.Dihomotopic.setoid


-- @@ L154-170 verbatim
instance : CategoryTheory.Category (FundamentalCategory X) where
  Hom x y := Dipath.Dihomotopic.Quotient x.as y.as
  id x := ⟦Dipath.refl x.as⟧
  comp {_ _ _} := Dipath.Dihomotopic.Quotient.comp
  id_comp {x _} f :=
    Quotient.inductionOn f fun a =>
      show ⟦(Dipath.refl x.as).trans a⟧ = ⟦a⟧ from
        Quotient.sound (Relation.EqvGen.rel _ _ ⟨Dipath.Dihomotopy.reflTrans a⟩)
  comp_id {_ y} f :=
    Quotient.inductionOn f fun a =>
      show ⟦a.trans (Dipath.refl y.as)⟧ = ⟦a⟧ from
        Quotient.sound (Relation.EqvGen.symm _ _
          (Relation.EqvGen.rel _ _ ⟨Dipath.Dihomotopy.transRefl a⟩))
  assoc {_ _ _ _} f g h :=
    Quotient.inductionOn₃ f g h fun p q r =>
      show ⟦(p.trans q).trans r⟧ = ⟦p.trans (q.trans r)⟧ from
        Quotient.sound (Dipath.Dihomotopy.trans_assoc p q r)


-- @@ L172-173 verbatim
lemma comp_eq (x y z : FundamentalCategory X) (p : x ⟶ y) (q : y ⟶ z) :
    p ≫ q = p.comp q := rfl


-- @@ L175-176 verbatim
lemma id_eq_path_refl (x : FundamentalCategory X) :
    𝟙 x = ⟦Dipath.refl x.as⟧ := rfl


-- @@ L178-186 expanded
/-- The functor on fundamental categories induced by a directed map. -/
@[simps]
def mapFunctor {X Y : Type*} [DirectedSpace X] [DirectedSpace Y] (f : DirectedMap X Y) :
    FundamentalCategory X ⥤ FundamentalCategory Y
    where
  obj x := ⟨f x.as⟩
  map {_ _} p := p.mapFn f
  map_id _ := rfl
  map_comp {_ _ _} p q := Quotient.inductionOn₂ p q fun a b => congrArg _ (Dipath.map_trans a b f)


-- @@ L188-198 verbatim
@[simp]
protected theorem mapFunctor_id (X : Type*) [DirectedSpace X] :
    mapFunctor (DirectedMap.id X) = 𝟭 _ := by
  refine CategoryTheory.Functor.ext ?_ ?_
  · intros; rfl
  · intros x y p
    refine Quotient.inductionOn p fun q => ?_
    change (mapFunctor (DirectedMap.id X)).map ⟦q⟧ =
      eqToHom rfl ≫ (𝟭 (FundamentalCategory X)).map ⟦q⟧ ≫ eqToHom rfl
    simp
    rfl


-- @@ L200-211 expanded
@[simp]
protected theorem mapFunctor_comp {X Y Z : Type*} [DirectedSpace X] [DirectedSpace Y]
    [DirectedSpace Z] (f : DirectedMap X Y) (g : DirectedMap Y Z) :
    mapFunctor (g.comp f) = mapFunctor f ⋙ mapFunctor g :=
  by
  refine CategoryTheory.Functor.ext ?_ ?_
  · intros; rfl
  · intros x y p
    refine Quotient.inductionOn p fun q => ?_
    change
      (mapFunctor (g.comp f)).map ⟦q⟧ =
        eqToHom rfl ≫ (mapFunctor f ⋙ mapFunctor g).map ⟦q⟧ ≫ eqToHom rfl
    simp
    rfl


-- @@ L213-223 verbatim
/-- The fundamental-category functor `dTopCat ⥤ Cat` sending a directed space to its
fundamental category. -/
def fundamentalCategoryFunctor : dTopCat ⥤ CategoryTheory.Cat where
  obj X := Cat.of (FundamentalCategory X)
  map f := (mapFunctor f.hom).toCatHom
  map_id X := by
    apply Cat.Hom.ext
    exact FundamentalCategory.mapFunctor_id X
  map_comp f g := by
    apply Cat.Hom.ext
    exact FundamentalCategory.mapFunctor_comp f.hom g.hom


-- @@ L225-226 verbatim
/-- Notation for the fundamental-category functor `dTopCat ⥤ Cat`. -/
scoped notation "dπ" => FundamentalCategory.fundamentalCategoryFunctor

-- @@ L227-228 verbatim
/-- Notation for the object part of the fundamental-category functor. -/
scoped notation "dπₓ" => FundamentalCategory.fundamentalCategoryFunctor.obj


-- @@ L230-234 verbatim
/-- The underlying functor (not just `Cat.Hom`) induced by a `dTopCat` map. -/
@[reducible]
def fundamentalCategoryMap {X Y : dTopCat} (f : X ⟶ Y) :
    (fundamentalCategoryFunctor.obj X) ⥤ (fundamentalCategoryFunctor.obj Y) :=
  (fundamentalCategoryFunctor.map f).toFunctor


-- @@ L236-237 verbatim
/-- Notation for the underlying functor on fundamental categories induced by a `dTopCat` map. -/
scoped notation "dπₘ" => FundamentalCategory.fundamentalCategoryMap


-- @@ L239-240 verbatim
lemma map_eq {X Y : dTopCat} {x₀ x₁ : X} (f : X ⟶ Y) (p : Dipath.Dihomotopic.Quotient x₀ x₁) :
  (dπₘ f).map p = p.mapFn f.hom := rfl


-- @@ L242-245 verbatim
/-- Help the typechecker by converting a point in the fundamental category back to a point in
the underlying directed space. -/
@[reducible]
def toTop {X : dTopCat} (x : dπₓ X) : X := x.as


-- @@ L247-250 verbatim
/-- Help the typechecker by converting a point in a directed space to a
point in the fundamental category of that space -/
@[reducible]
def fromTop {X : dTopCat} (x : X) : dπₓ X := ⟨x⟩


-- @@ L252-256 verbatim
/-- Help the typechecker by converting an arrow in the fundamental category of
a directed space back to a directed path in that space (i.e., `Dipath.Dihomotopic.Quotient`). -/
@[reducible]
def toPath {X : dTopCat} {x₀ x₁ : dπₓ X} (p : x₀ ⟶ x₁) :
  Dipath.Dihomotopic.Quotient (X := X) x₀.as x₁.as := p


-- @@ L258-262 verbatim
/-- Help the typechecker by convering a directed path in a directed space to an arrow in the
fundamental category of that space. -/
@[reducible]
def fromPath {X : dTopCat} {x₀ x₁ : X} (p : Dipath.Dihomotopic.Quotient x₀ x₁) :
  FundamentalCategory.mk x₀ ⟶ FundamentalCategory.mk x₁ := p


-- @@ L264-264 verbatim
end FundamentalCategory
