/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/

/-
Copyright (c) 2024 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Field.Defs


-- @@ L18-20 verbatim
/-!
# Category instances for `Field`.
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
universe u v


-- @@ L26-26 verbatim
open CategoryTheory


-- @@ L28-33 verbatim
/-- The category of fields. -/
structure FieldCat where
  mk ::
  /-- The underlying type. -/
  carrier : Type u
  [field : Field carrier]


-- @@ L35-35 verbatim
attribute [instance] FieldCat.field


-- @@ L37-37 verbatim
initialize_simps_projections FieldCat (-field)


-- @@ L39-39 verbatim
namespace FieldCat


-- @@ L41-42 verbatim
instance : CoeSort (FieldCat) (Type u) :=
  ⟨FieldCat.carrier⟩


-- @@ L44-44 verbatim
attribute [coe] FieldCat.carrier


-- @@ L46-48 verbatim
/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. This is the preferred way to construct a term of `FieldCat`. -/
abbrev of (R : Type u) [Field R] : FieldCat := ⟨R⟩


-- @@ L50-50 verbatim
lemma coe_of (R : Type u) [Field R] : (of R : Type u) = R := rfl


-- @@ L52-52 verbatim
lemma of_carrier (R : FieldCat.{u}) : of R = R := rfl


-- @@ L54-60 verbatim
variable {R} in
/-- The type of morphisms in `FieldCat`. -/
@[ext]
structure Hom (R S : FieldCat) where
  mk ::
  /-- The underlying ring hom. -/
  hom : R →+* S


-- @@ L62-65 verbatim
instance : Category FieldCat where
  Hom R S := Hom R S
  id R := ⟨RingHom.id R⟩
  comp f g := ⟨g.hom.comp f.hom⟩


-- @@ L67-68 verbatim
instance {R S : FieldCat.{u}} : CoeFun (R ⟶ S) (fun _ ↦ R → S) where
  coe f := f.hom


-- @@ L70-73 verbatim
@[simp]
lemma hom_id {R : FieldCat} : (𝟙 R : R ⟶ R).hom = RingHom.id R := rfl

/- Provided for rewriting. -/

-- @@ L74-75 verbatim
lemma id_apply (R : FieldCat) (r : R) :
    (𝟙 R : R ⟶ R) r = r := by simp


-- @@ L77-81 verbatim
@[simp]
lemma hom_comp {R S T : FieldCat} (f : R ⟶ S) (g : S ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/

-- @@ L82-83 verbatim
lemma comp_apply {R S T : FieldCat} (f : R ⟶ S) (g : S ⟶ T) (r : R) :
    (f ≫ g) r = g (f r) := by simp


-- @@ L85-87 verbatim
@[ext]
lemma hom_ext {R S : FieldCat} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf


-- @@ L89-91 verbatim
/-- Typecheck a `RingHom` as a morphism in `FieldCat`. -/
abbrev ofHom {R S : Type u} [Field R] [Field S] (f : R →+* S) : of R ⟶ of S :=
  ⟨f⟩


-- @@ L93-93 verbatim
lemma hom_ofHom {R S : Type u} [Field R] [Field S] (f : R →+* S) : (ofHom f).hom = f := rfl


-- @@ L95-97 verbatim
@[simp]
lemma ofHom_hom {R S : FieldCat} (f : R ⟶ S) :
    ofHom (Hom.hom f) = f := rfl


-- @@ L99-100 verbatim
@[simp]
lemma ofHom_id {R : Type u} [Field R] : ofHom (RingHom.id R) = 𝟙 (of R) := rfl


-- @@ L102-106 verbatim
@[simp]
lemma ofHom_comp {R S T : Type u} [Field R] [Field S] [Field T]
    (f : R →+* S) (g : S →+* T) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl


-- @@ L108-109 verbatim
lemma ofHom_apply {R S : Type u} [Field R] [Field S]
    (f : R →+* S) (r : R) : ofHom f r = f r := rfl


-- @@ L111-114 verbatim
@[simp]
lemma inv_hom_apply {R S : FieldCat} (e : R ≅ S) (r : R) : e.inv (e.hom r) = r := by
  rw [← comp_apply]
  simp


-- @@ L116-119 verbatim
@[simp]
lemma hom_inv_apply {R S : FieldCat} (e : R ≅ S) (s : S) : e.hom (e.inv s) = s := by
  rw [← comp_apply]
  simp


-- @@ L121-123 verbatim
instance : ConcreteCategory.{u} FieldCat (fun R S ↦ R →+* S) where
  hom := Hom.hom
  ofHom := ofHom


-- @@ L125-132 verbatim
/-- This unification hint helps with problems of the form `(forget ?C).obj R =?= carrier R'`.

An example where this is needed is in applying
`PresheafOfModules.Sheafify.app_eq_of_isLocallyInjective`.
-/
unif_hint forgetObjEqCoe (R R' : FieldCat) where
  R ≟ R' ⊢
  (forget FieldCat).obj R ≟ FieldCat.carrier R'


-- @@ L134-134 verbatim
lemma forget_obj {R : FieldCat} : (forget FieldCat).obj R = R := rfl


-- @@ L136-138 verbatim
lemma forget_map {R S : FieldCat} (f : R ⟶ S) :
    (forget FieldCat).map f = (f.hom : R → S) :=
  rfl


-- @@ L140-141 verbatim
instance {R : FieldCat} : Field ((forget FieldCat).obj R) :=
  (inferInstance : Field R.carrier)


-- @@ L143-146 verbatim
instance hasForgetToSemiRingCat : HasForget₂ FieldCat CommRingCat where
  forget₂ :=
    { obj := fun R ↦ CommRingCat.of R
      map := fun f ↦ CommRingCat.ofHom f.hom }


-- @@ L148-151 verbatim
instance hasForgetToAddCommGrp : HasForget₂ FieldCat RingCat where
  forget₂ :=
    { obj := fun R ↦ RingCat.of R
      map := fun f ↦ RingCat.ofHom f.hom }


-- @@ L153-158 verbatim
/-- Field equivalence are isomorphisms in category of semirings -/
@[simps]
def RingEquiv.toRingCatIso {R S : Type u} [Field R] [Field S] (e : R ≃+* S) :
    of R ≅ of S where
  hom := ⟨e⟩
  inv := ⟨e.symm⟩


-- @@ L160-165 verbatim
instance forgetReflectIsos : (forget FieldCat).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget FieldCat).map f)
    let ff : X →+* Y := f.hom
    let e : X ≃+* Y := { ff, i.toEquiv with }
    exact FieldCat.RingEquiv.toRingCatIso e|>.isIso_hom


-- @@ L167-167 verbatim
end FieldCat
