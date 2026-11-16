/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import SymmMonCoherence.SList.Relations -- Is it really needed?
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic


-- @@ L11-16 verbatim
/-! # Symmetric monoidal structure on SList

In this file, we construct a symmetric monoidal category structure on the category
of symmetric lists.

-/


-- @@ L18-18 verbatim
universe u


-- @@ L20-20 verbatim
namespace CategoryTheory.SList


-- @@ L22-22 verbatim
open FreeSListQuiv


-- @@ L24-24 verbatim
variable {C : Type u}


-- @@ L26-26 verbatim
section append


-- @@ L28-29 expanded
/-- Setup a notation for "singleton" symmetric lists. -/
notation3 "[" c "]~" => (cons c).obj nil


-- @@ L31-43 expanded
/-- The `RecursiveFunctorData` that defines the bifunctor on SList C that appends
symmetric lists to another. -/
abbrev appendRecData : RecursiveFunctorData C (SList C ⥤ SList C)
    where
  nilObj := 𝟭 (SList C)
  consF c := Functor.whiskeringRight _ _ _ |>.obj (cons c)
  swapIso x
    y :=
    NatIso.ofComponents
      (fun F ↦
        (Functor.associator ..) ≪≫
          (Functor.isoWhiskerLeft F <| swapNatIso _ _) ≪≫ (Functor.associator ..).symm)
      (fun {x y} f ↦ by ext; simp [swap_natural])
  swap_inv := by intros; ext; simp
  hexagon := by intros; ext; simp [swap_hexagon]


-- @@ L45-46 verbatim
public def appendFunctor : SList C ⥤ (SList C ⥤ SList C) :=
  appendRecData.functor


-- @@ L48-49 verbatim
public lemma append_nil_eq : appendFunctor.obj (nil : SList C) = 𝟭 (SList C) :=
    RecursiveFunctorData.functor_obj_nil _


-- @@ L51-53 verbatim
public lemma append_cons_eq (x : C) (l : SList C) :
    appendFunctor.obj ((cons x).obj l) = appendFunctor.obj l ⋙ cons x :=
  RecursiveFunctorData.functor_obj_cons _ _ _


-- @@ L55-55 expanded
@[expose]
public def appendNilIso : appendFunctor.obj nil ≅ 𝟭 (SList C) :=
  eqToIso append_nil_eq


-- @@ L57-59 expanded
@[expose]
public def appendConsIso (x : C) (l : SList C) :
    appendFunctor.obj ((cons x).obj l) ≅ appendFunctor.obj l ⋙ cons x :=
  eqToIso <| append_cons_eq x l


-- @@ L61-64 expanded
public lemma append_nil_map {l l' : SList C} (f : l ⟶ l') :
    (appendFunctor.obj nil).map f = appendNilIso.hom.app l ≫ f ≫ appendNilIso.inv.app l' := by
  simpa [appendNilIso] using Functor.congr_hom (append_nil_eq) f


-- @@ L66-71 expanded
public lemma append_map_cons_map (x : C) {l l' : SList C} (f : l ⟶ l') :
    appendFunctor.map ((cons x).map f) =
      (appendConsIso _ _).hom ≫
        Functor.whiskerRight (appendFunctor.map f) (cons x) ≫ (appendConsIso _ _).inv :=
  RecursiveFunctorData.functor_map_cons_map _ _ _


-- @@ L73-82 expanded
public lemma append_map_swap (x y : C) (l : SList C) :
    appendFunctor.map (β~ x y l) =
      (appendConsIso _ _).hom ≫
        (Functor.whiskeringRight _ _ _ |>.obj (cons x)).map (appendConsIso _ _).hom ≫
          (Functor.associator ..).hom ≫
            (Functor.whiskerLeft (appendFunctor.obj l) <| swapNatTrans x y) ≫
              (Functor.associator ..).inv ≫
                (Functor.whiskeringRight _ _ _ |>.obj (cons y)).map (appendConsIso _ _).inv ≫
                  (appendConsIso _ _).inv :=
  by simpa [-RecursiveFunctorData.functor_map_swap] using appendRecData.functor_map_swap x y l


-- @@ L84-91 unexpanded
public lemma append_map_swap_app (x y : C) (l l' : SList C) :
    (appendFunctor.map (β~ x y l)).app l' =
    (appendConsIso x (y ::~ l)).hom.app l' ≫
      (x>~.map ((appendConsIso y l).hom.app l')) ≫
      β~ x y (appendFunctor.obj l |>.obj l') ≫
      (y>~.map ((appendConsIso x l).inv.app l')) ≫
      (appendConsIso y (x ::~ l)).inv.app l' := by
  simpa using congr($(append_map_swap x y l).app l')


-- @@ L93-100 verbatim
@[simp, grind =]
public lemma append_toList (l l' : SList C) :
    ((appendFunctor.obj l).obj l').toList = l.toList ++ l'.toList := by
  cases l with |_ l
  cases l with |_ l
  induction l with
  | nil => simp [← nil_def, append_nil_eq]
  | cons head tail h => simpa [FreeSListQuiv.cons_obj_eq, SList.π_obj_cons, append_cons_eq] using h


-- @@ L102-105 verbatim
@[simp]
public lemma append_length (x y : SList C) :
    ((appendFunctor.obj x).obj y).length = x.length + y.length := by
  simp [length]


-- @@ L107-107 verbatim
end append


-- @@ L109-109 verbatim
section


-- @@ L111-111 verbatim
local notation3 x " ++~ " y => (appendFunctor.obj x).obj y

-- @@ L112-112 verbatim
local notation3 x " ++~ₘ " f => (appendFunctor.obj x).map f

-- @@ L113-115 verbatim
local notation3 f " ₘ++~ " y => (appendFunctor.map f).app y

-- Need to expose it if we want to use somewhere that the monoidal structure is strict

-- @@ L116-120 verbatim
@[expose] public def associator (x y z : SList C) :
    ((x ++~ y) ++~ z) ≅ x ++~ (y ++~ z) :=
  eqToIso <| by
    apply injective_toList
    grind


-- @@ L122-123 expanded
@[expose]
public def leftUnitor (x : SList C) : (nil ++~ x) ≅ x :=
  appendNilIso.app x


-- @@ L125-128 expanded
@[expose]
public def rightUnitor (x : SList C) : (x ++~ nil) ≅ x :=
  eqToIso <| by
    apply injective_toList
    grind


-- @@ L130-137 expanded
public instance : MonoidalCategoryStruct (SList C)
    where
  tensorUnit := nil
  tensorObj x y := x ++~ y
  whiskerLeft x {_ _} f := x ++~ₘ f
  whiskerRight f x := f ₘ++~ x
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor


-- @@ L139-139 verbatim
open MonoidalCategory


-- @@ L141-142 expanded
/-- The isomorphism that defines the unit object for symmetric lists. -/
public lemma unit_eq_nil : 𝟙_ (SList C) = nil :=
  rfl


-- @@ L144-145 expanded
/-- The isomorphism that defines the unit object for symmetric lists. -/
@[expose]
public def unitIsoNil : 𝟙_ (SList C) ≅ nil :=
  eqToIso unit_eq_nil


-- @@ L147-149 verbatim
public instance : IsEmpty (Fin (𝟙_ (SList C)).length) := by
  simp only [unit_eq_nil, length_nil]
  infer_instance


-- @@ L151-152 verbatim
/-- The equality that defines the tensor product for symmetric lists. -/
public lemma tensorObj_eq_append_obj_obj (x y : SList C) : x ⊗ y = x ++~ y := rfl


-- @@ L154-158 verbatim
/-- The isomorphism that defines the tensor product on symmetric lists.
It is usually a bad idea to try to go through this one: prefer phrasing things
in "monoidal language". -/
@[expose] public def tensorObjIsoDef (x y : SList C) : x ⊗ y ≅ x ++~ y :=
  eqToIso <| tensorObj_eq_append_obj_obj _ _


-- @@ L160-163 verbatim
public lemma whiskerLeft_eq (x : SList C) {y z : SList C} (f : y ⟶ z) :
    x ◁ f = (tensorObjIsoDef x y).hom ≫ (x ++~ₘ f) ≫ (tensorObjIsoDef x z).inv := by
  simp [MonoidalCategoryStruct.whiskerLeft, MonoidalCategoryStruct.tensorObj,
    tensorObjIsoDef]


-- @@ L165-168 verbatim
public lemma whiskerRight_eq {x y : SList C} (f : x ⟶ y) (z : SList C) :
    f ▷ z = (tensorObjIsoDef x z).hom ≫ (f ₘ++~ z) ≫ (tensorObjIsoDef y z).inv := by
  simp [MonoidalCategoryStruct.whiskerRight, MonoidalCategoryStruct.tensorObj,
    tensorObjIsoDef]


-- @@ L170-171 verbatim
@[simp, grind =]
public lemma tensorUnit_toList : (𝟙_ (SList C)).toList = [] := by simp [tensorUnit]


-- @@ L173-174 verbatim
@[simp, grind =]
public lemma tensorUnit_length : (𝟙_ (SList C)).length = 0 := by simp [tensorUnit]


-- @@ L176-178 verbatim
@[simp, grind =]
public lemma tensorObj_toList (x y : SList C) : (x ⊗ y).toList = x.toList ++ y.toList :=
  append_toList x y


-- @@ L180-182 verbatim
@[simp, grind =]
public lemma tensorObj_length (x y : SList C) : (x ⊗ y).length = x.length + y.length :=
  append_length x y


-- @@ L184-186 expanded
public lemma tensorObj_cons_eq (x : C) (l l' : SList C) :
    ((cons x).obj l) ⊗ l' = (cons x).obj (l ⊗ l') :=
  Functor.congr_obj (append_cons_eq _ _) l'


-- @@ L188-190 expanded
@[expose]
public def tensorObjConsIso (x : C) (l l' : SList C) :
    ((cons x).obj l) ⊗ l' ≅ (cons x).obj (l ⊗ l') :=
  eqToIso <| tensorObj_cons_eq _ _ _


-- @@ L192-194 verbatim
@[local simp, local grind =] lemma whiskerLeft_id (x y : SList C) : x ◁ 𝟙 y = 𝟙 _ := by
  simp only [whiskerLeft, Functor.map_id]
  rfl


-- @@ L196-199 verbatim
@[local simp, local grind _=_] lemma whiskerLeft_comp (x : SList C) {y z t : SList C}
    (f : y ⟶ z) (g : z ⟶ t) :
    x ◁ (f ≫ g) = x ◁ f ≫ x ◁ g := by
  simp [whiskerLeft]


-- @@ L201-204 verbatim
@[local simp, local grind =] lemma id_whiskerRight (x y : SList C) :
    𝟙 x ▷ y = 𝟙 _ := by
  simp [whiskerRight]
  rfl


-- @@ L206-209 verbatim
@[local simp, local grind _=_] lemma comp_whiskerRight {x y z : SList C}
    (f : x ⟶ y) (g : y ⟶ z) {t : SList C} :
    (f ≫ g) ▷ t = f ▷ t ≫ g ▷ t := by
  simp [whiskerRight]


-- @@ L211-219 expanded
public lemma whiskerLeft_nil {l l' : SList C} (f : l ⟶ l') :
    nil ◁ f = unitIsoNil.inv ▷ _ ≫ (λ_ _).hom ≫ f ≫ (λ_ _).inv ≫ unitIsoNil.hom ▷ _ := by
  simpa [MonoidalCategoryStruct.whiskerLeft, MonoidalCategoryStruct.tensorObj, unit_eq_nil,
    MonoidalCategoryStruct.leftUnitor, leftUnitor, unitIsoNil, appendNilIso, tensorObjConsIso,
    appendConsIso] using Functor.congr_hom append_nil_eq f


-- @@ L221-228 expanded
public lemma whiskerLeft_cons (x : C) (l : SList C) {l' l'' : SList C} (f : l' ⟶ l'') :
    ((cons x).obj l) ◁ f =
      (tensorObjConsIso _ _ _).hom ≫ ((cons x).map (l ◁ f)) ≫ (tensorObjConsIso _ _ _).inv :=
  by
  simpa [MonoidalCategoryStruct.whiskerLeft, MonoidalCategoryStruct.tensorObj, tensorObjConsIso,
    appendConsIso] using Functor.congr_hom (append_cons_eq _ _) f


-- @@ L230-237 expanded
public lemma whiskerRight_cons_map (x : C) {l' l'' : SList C} (f : l' ⟶ l'') (l : SList C) :
    ((cons x).map f) ▷ l =
      (tensorObjConsIso _ _ _).hom ≫ ((cons x).map (f ▷ l)) ≫ (tensorObjConsIso _ _ _).inv :=
  by
  simpa [MonoidalCategoryStruct.whiskerRight, MonoidalCategoryStruct.tensorObj, tensorObjConsIso,
    appendConsIso] using congr_app (append_map_cons_map x f) l


-- @@ L239-247 expanded
public lemma whiskerRight_swap (x y : C) (l : SList C) (l' : SList C) :
    (β~ x y l) ▷ l' =
      (tensorObjConsIso x ((cons y).obj l) l').hom ≫
        ((cons x).map (tensorObjConsIso y l l').hom) ≫
          β~ x y (l ⊗ l') ≫
            ((cons y).map (tensorObjConsIso x l l').inv) ≫
              (tensorObjConsIso y ((cons x).obj l) l').inv :=
  by
  simpa [MonoidalCategoryStruct.whiskerRight, MonoidalCategoryStruct.tensorObj, tensorObjConsIso,
    appendConsIso] using append_map_swap_app x y l l'


-- @@ L249-252 expanded
public lemma rightUnitor_cons (x : C) (l : SList C) :
    ρ_ ((cons x).obj l) = tensorObjConsIso x l (𝟙_ _) ≪≫ ((cons x).mapIso (ρ_ l)) :=
  by
  ext
  simp [MonoidalCategoryStruct.rightUnitor, tensorObjConsIso, rightUnitor, eqToHom_map]


-- @@ L254-254 verbatim
end


-- @@ L256-256 verbatim
open MonoidalCategory


-- @@ L258-264 verbatim
/-- The function `Ψ` is essentially a cast along the equality
`(x ⊗ y).length = x.length + y.length`, followed by the equivalence between
`Fin (n + m)` and `Fin n ⊕ Fin m`, but giving it a name and hiding its
implementation as a cast makes for better automation. -/
@[no_expose] public def Ψ (x y : SList C) :
    Fin x.length ⊕ Fin y.length ≃ Fin (x ⊗ y).length :=
  finSumFinEquiv.trans (Equiv.symm <| finCongr <| tensorObj_length x y)


-- @@ L266-273 verbatim
@[elab_as_elim, cases_eliminator]
public lemma fin_tensor_obj_case {x y : SList C}
    {motive : {x y : SList C} → Fin (x ⊗ y).length → Prop}
    (inl : ∀ (i : Fin x.length), motive (Ψ x y (.inl i)))
    (inr : ∀ (i : Fin y.length), motive (Ψ x y (.inr i)))
    (i : Fin (x ⊗ y).length) : motive i := by
  obtain ⟨i, rfl⟩ := (Ψ _ _).surjective i
  grind


-- @@ L275-277 verbatim
@[simp, grind =]
public lemma Ψ_apply_val_left (x y : SList C) (i : Fin x.length) :
    (Ψ x y (.inl i)).val = i.val := (rfl)


-- @@ L279-281 verbatim
@[simp, grind =]
public lemma Ψ_apply_val_right (x y : SList C) (i : Fin y.length) :
    (Ψ x y (.inr i)).val = x.length + i.val := (rfl)


-- @@ L283-284 verbatim
attribute [local simp, local grind =]
  whiskerLeft_id whiskerLeft_comp id_whiskerRight comp_whiskerRight


-- @@ L286-287 verbatim
lemma tensorHom_def {x y z t : SList C} (f : x ⟶ y) (g : z ⟶ t) :
    f ⊗ₘ g = f ▷ _ ≫ _ ◁ g  := rfl


-- @@ L289-289 verbatim
public section


-- @@ L291-292 verbatim
@[simp, grind =] private lemma toAinf_app_appendIsoDef (l l' : SList C) :
    toAinf.app (tensorObjIsoDef l l').hom = 1 := by simp [tensorObjIsoDef]


-- @@ L294-299 verbatim
@[simp, grind =]
lemma Ainf.shift_zero (x : Ainf.Group) : Ainf.shift 0 x = x := by
  induction x using Ainf.toCoxeterSystem.simple_induction with
  | one => simp
  | simple i => simp [Ainf.shift_simple]
  | mul w i ih_w ih_i => simp [ih_w, ih_i]


-- @@ L301-307 verbatim
lemma toAinf_whiskerLeft (x : SList C) {y y' : SList C} (f : y ⟶ y') :
    toAinf.app (x ◁ f) = Ainf.shift x.length (toAinf.app f) := by
  induction x using SList.cons_induction with
  | nil => simp [whiskerLeft_eq, append_nil_map, appendNilIso]
  | cons head tail ih =>
    simp [whiskerLeft_cons, tensorObjConsIso, ih, Ainf.shift_shift,
      Nat.add_comm]


-- @@ L309-311 expanded
lemma toAinf_appendFunctor_map_cons (x : C) {y y' : SList C} (f : y ⟶ y') (z : SList C) :
    toAinf.app (((cons x).map f) ▷ z) = Ainf.shift 1 (toAinf.app (f ▷ z)) := by
  simp [whiskerRight_cons_map, tensorObjConsIso]


-- @@ L313-316 verbatim
lemma toAinf_appendFunctor_map_swap (x y : C) (l : SList C) (z : SList C) :
    toAinf.app ((β~ x y l) ▷ z) =
    toAinf.app (β~ x y (l ⊗ z)) := by
  simp [whiskerRight_swap, tensorObjConsIso]


-- @@ L318-324 verbatim
lemma toAinf_whiskerRight {x x' : SList C} (f : x ⟶ x') (y : SList C) :
    toAinf.app (f ▷ y) = toAinf.app f := by
  induction f using SList.hom_induction' with
  | comp f g _ _ => grind
  | id x => grind
  | cons head f _ => grind [toAinf_appendFunctor_map_cons]
  | swap x y l => grind [toAinf_appendFunctor_map_swap]


-- @@ L326-326 verbatim
end


-- @@ L328-328 verbatim
section


-- @@ L330-334 verbatim
lemma toPerm_whiskerLeft_apply_left (x : SList C) {y y' : SList C} (f : y ⟶ y')
    (i : ℕ) (hi : i < x.length) :
    (toPerm.app (x ◁ f)) i = i := by
  simp only [toPerm, weight.postComp_app, toAinf_whiskerLeft]
  exact AinfToPerm_shift_apply_lt _ _ _ hi


-- @@ L336-341 verbatim
lemma toPerm_whiskerLeft_apply_right (x : SList C) {y y' : SList C} (f : y ⟶ y')
    (i : ℕ) :
    (toPerm.app (x ◁ f)) (x.length + i) = x.length + (toPerm.app f) i := by
  simp only [toPerm, weight.postComp_app, toAinf_whiskerLeft]
  rw [AinfToPerm_shift_apply_ge _ _ _ (by simp)]
  simp


-- @@ L343-345 verbatim
lemma toPerm_whiskerRight_apply {x x' : SList C} (f : x ⟶ x') (y : SList C) (i : ℕ) :
    (toPerm.app (f ▷ y)) i = (toPerm.app f) i := by
  simp [toPerm, toAinf_whiskerRight]


-- @@ L347-347 verbatim
end


-- @@ L349-354 verbatim
@[simp, grind =] public lemma tensorHom_apply_left {x y z t : SList C} (f : x ⟶ y) (g : z ⟶ t)
    (i : Fin y.length) :
    toEquiv (f ⊗ₘ g) (Ψ y t <| .inl i) = Ψ _ _ (.inl <| toEquiv f i) := by
  ext
  simp [toEquiv_apply_val, tensorHom_def, toPerm_whiskerRight_apply,
    toPerm_whiskerLeft_apply_left]


-- @@ L356-360 verbatim
@[simp, grind =] public lemma tensorHom_apply_right {x y z t : SList C} (f : x ⟶ y) (g : z ⟶ t)
    (i : Fin t.length) : toEquiv (f ⊗ₘ g) (Ψ y t <| .inr i) = Ψ _ _ (.inr <| toEquiv g i) := by
  ext
  simp [toEquiv_apply_val, tensorHom_def, toPerm_whiskerRight_apply,
    toPerm_whiskerLeft_apply_right, toPerm_app_eq_of_lt, length_eq_of_hom f]


-- @@ L362-363 verbatim
lemma id_tensorHom (x : SList C) {y z : SList C} (f : y ⟶ z) :
    𝟙 x ⊗ₘ f = x ◁ f := by simp [tensorHom_def]


-- @@ L365-367 verbatim
lemma tensorHom_id {x y : SList C} (f : x ⟶ y) (z : SList C) :
     f ⊗ₘ (𝟙 z) = f ▷ z := by
  simp [tensorHom_def]


-- @@ L369-373 verbatim
@[simp, grind =] public lemma whiskerLeft_apply_right (x : SList C) {y z : SList C} (f : y ⟶ z)
    (i : Fin z.length) :
    toEquiv (x ◁ f) (Ψ x z <| .inr i) = (Ψ _ _) (.inr (toEquiv f i)) := by
  ext
  simp [← id_tensorHom]


-- @@ L375-379 verbatim
@[simp, grind =] public lemma whiskerLeft_apply_left (x : SList C) {y z : SList C} (f : y ⟶ z)
    (i : Fin x.length) :
    toEquiv (x ◁ f) (Ψ x z <| .inl i) = Ψ _ _ (.inl i) := by
  ext
  simp [← id_tensorHom]


-- @@ L381-385 verbatim
@[simp, grind =] public lemma whiskerRight_apply_left {x y : SList C} (f : x ⟶ y) (z : SList C)
    (i : Fin z.length) :
    toEquiv (f ▷ z) (Ψ y z <| .inr i) = Ψ _ _ (.inr i) := by
  ext
  simp [← tensorHom_id]


-- @@ L387-391 verbatim
@[simp, grind =] public lemma whiskerRight_apply_right {x y : SList C} (f : x ⟶ y) (z : SList C)
    (i : Fin y.length) :
    toEquiv (f ▷ z) (Ψ y z <| .inl i) = Ψ _ _ (.inl (toEquiv f i)) := by
  ext
  simp [← tensorHom_id]


-- @@ L393-396 verbatim
@[simp, grind =] public lemma associator_hom_left_left (x y z : SList C) (i : Fin x.length) :
    toEquiv (α_ x y z).hom (Ψ x (y ⊗ z) <| .inl i) = Ψ (x ⊗ y) z (.inl <| Ψ x y <| .inl i) := by
  ext
  simp [MonoidalCategoryStruct.associator, associator, Ψ]


-- @@ L398-402 verbatim
@[simp, grind =] public lemma associator_hom_right_left (x y z : SList C) (i : Fin y.length) :
    toEquiv (α_ x y z).hom (Ψ x (y ⊗ z) <| .inr <| Ψ y z <| .inl i) =
      Ψ (x ⊗ y) z (.inl <| Ψ x y <| .inr i) := by
  ext
  simp [MonoidalCategoryStruct.associator, associator, Ψ]


-- @@ L404-407 verbatim
@[simp, grind =] public lemma associator_hom_right_right (x y z : SList C) (i : Fin z.length) :
    toEquiv (α_ x y z).hom (Ψ x (y ⊗ z) <| .inr <| Ψ y z <| .inr i) = Ψ (x ⊗ y) z (.inr i) := by
  ext
  simp [MonoidalCategoryStruct.associator, associator, Ψ, Nat.add_assoc]


-- @@ L409-412 verbatim
@[simp, grind =] public lemma associator_inv_left_left (x y z : SList C) (i : Fin x.length) :
    toEquiv (α_ x y z).inv ((Ψ (x ⊗ y) z) (.inl <| Ψ x y <| .inl i)) = Ψ x (y ⊗ z) (.inl i) := by
  ext
  simp [MonoidalCategoryStruct.associator, associator, Ψ]


-- @@ L414-418 verbatim
@[simp, grind =] public lemma associator_inv_left_right (x y z : SList C) (i : Fin y.length) :
    toEquiv (α_ x y z).inv (Ψ (x ⊗ y) z (.inl <| Ψ x y <| .inr i)) =
      Ψ x (y ⊗ z) (.inr <| Ψ y z <| .inl i) := by
  ext
  simp [MonoidalCategoryStruct.associator, associator, Ψ]


-- @@ L420-423 verbatim
@[simp, grind =] public lemma associator_inv_right (x y z : SList C) (i : Fin z.length) :
    toEquiv (α_ x y z).inv (Ψ (x ⊗ y) z <| .inr i) = Ψ x (y ⊗ z) (.inr <| Ψ y z <| .inr i) := by
  ext
  simp [MonoidalCategoryStruct.associator, associator, Ψ, Nat.add_assoc]


-- @@ L425-428 verbatim
@[simp] public lemma toEquiv_leftUnitor_hom (x : SList C) (i : Fin x.length) :
    toEquiv (λ_ x).hom i = Ψ (𝟙_ (SList C)) x (.inr <| i) := by
  ext
  simp [MonoidalCategoryStruct.leftUnitor, leftUnitor, appendNilIso]


-- @@ L430-433 verbatim
@[simp] public lemma toEquiv_leftUnitor_inv (x : SList C) (i : Fin x.length) :
    toEquiv (λ_ x).inv (Ψ (𝟙_ (SList C)) x <| .inr i) = i := by
  ext
  simp [MonoidalCategoryStruct.leftUnitor, leftUnitor, appendNilIso]


-- @@ L435-438 verbatim
@[simp] public lemma toEquiv_rightUnitor_hom (x : SList C) (i : Fin x.length) :
    toEquiv (ρ_ x).hom i = Ψ _ _ (.inl i) := by
  ext
  simp [MonoidalCategoryStruct.rightUnitor, rightUnitor]


-- @@ L440-443 verbatim
@[simp] public lemma toEquiv_rightUnitor_inv (x : SList C) (i : Fin x.length) :
    toEquiv (ρ_ x).inv (Ψ _ _ (.inl i)) = i := by
  ext
  simp [MonoidalCategoryStruct.rightUnitor, rightUnitor]


-- @@ L445-456 verbatim
lemma associator_naturality {x x' y y' z z' : SList C}
    (f : x ⟶ x') (g : y ⟶ y') (h : z ⟶ z') :
    ((f ⊗ₘ g) ⊗ₘ h) ≫ (α_ x' y' z').hom =
    (α_ x y z).hom ≫ (f ⊗ₘ g ⊗ₘ h) := by
  rw [hom_eq_iff_toEquiv_eq]
  ext i
  obtain ⟨i, rfl⟩ := (Ψ _ _).surjective i
  cases i with
  | inl i => simp
  | inr i =>
    obtain ⟨i, rfl⟩ := (Ψ _ _).surjective i
    cases i with simp


-- @@ L458-472 verbatim
lemma pentagon_identity (w x y z : SList C) :
    (α_ w x y).hom ▷ z ≫ (α_ w (x ⊗ y) z).hom ≫ w ◁ (α_ x y z).hom =
    (α_ (w ⊗ x) y z).hom ≫ (α_ w x (y ⊗ z)).hom := by
  rw [hom_eq_iff_toEquiv_eq]
  ext i
  obtain ⟨i, rfl⟩ := (Ψ _ _).surjective i
  cases i with
  | inl i => simp
  | inr i =>
    obtain ⟨i, rfl⟩ := (Ψ _ _).surjective i
    cases i with
      | inl i => simp
      | inr i =>
        obtain ⟨i, rfl⟩ := (Ψ _ _).surjective i
        cases i with simp


-- @@ L474-495 verbatim
public instance : MonoidalCategory (SList C) where
  tensorHom_def f g := rfl
  id_tensorHom_id _ _ := by
    rw [hom_eq_iff_toEquiv_eq]
    ext i
    simp [tensorHom_def]
  associator_naturality f g h := by simpa using associator_naturality f g h
  leftUnitor_naturality f := by
    rw [hom_eq_iff_toEquiv_eq]
    ext i
    simp
  tensorHom_comp_tensorHom _ _ _ _ := by simp [tensorHom]
  rightUnitor_naturality f := by
    rw [hom_eq_iff_toEquiv_eq]
    ext j
    simp
  pentagon x y z t := by simpa using pentagon_identity x y z t
  triangle u v := by
    rw [hom_eq_iff_toEquiv_eq]
    ext j : 1
    obtain ⟨j, rfl⟩ := (Ψ _ _).surjective j
    cases j with simp



-- @@ L498-503 expanded
/-- Giving a name to the isomorphism that translates between `SList.cons` and the
tensor product with a singleton SList. -/
@[expose, simps! -isSimp]
public def consTensSingletonIso (x : C) (l : SList C) : ((cons x).obj l) ≅ (cons x).obj nil ⊗ l :=
  Iso.symm <|
    tensorObjConsIso x nil l ≪≫ (cons x).mapIso (whiskerRightIso unitIsoNil.symm _ ≪≫ λ_ _)


-- @@ L505-509 expanded
public lemma consTensSingletonIso_hom_naturality (x : C) {l l' : SList C} (f : l ⟶ l') :
    (consTensSingletonIso x l).hom ≫ (cons x).obj nil ◁ f =
      ((cons x).map f) ≫ (consTensSingletonIso x l').hom :=
  by
  simp only [consTensSingletonIso_hom, whiskerLeft_cons, Category.assoc, Iso.inv_hom_id_assoc]
  simp_rw [← Functor.map_comp_assoc, ← whisker_exchange, leftUnitor_inv_naturality_assoc]


-- @@ L511-515 expanded
public lemma consTensSingletonIso_inv_naturality (x : C) {l l' : SList C} (f : l ⟶ l') :
    (consTensSingletonIso x l).inv ≫ ((cons x).map f) =
      (cons x).obj nil ◁ f ≫ (consTensSingletonIso x l').inv :=
  by
  simp only [Iso.eq_comp_inv, Category.assoc, ← consTensSingletonIso_hom_naturality]
  simp


-- @@ L517-518 verbatim
/-! Now that we have the monoidal structure, the rest of this file is devoted to extending it to a
symmetric monoidal structure. The construction follows Piceghello’s thesis (chapter 4). -/


-- @@ L520-520 verbatim
section Q

-- @@ L521-521 verbatim
open MonoidalCategory


-- @@ L523-525 expanded
@[reassoc (attr := local simp)]
private lemma cons_cons_hom_inv_id (u v : C) {l l' : SList C} (e : l ≅ l') :
    ((cons u).map ((cons v).map e.hom)) ≫ ((cons u).map ((cons v).map e.inv)) = 𝟙 _ := by
  simp [← Functor.map_comp]


-- @@ L527-529 expanded
@[reassoc (attr := local simp)]
private lemma cons_cons_inv_hom_id (u v : C) {l l' : SList C} (e : l ≅ l') :
    ((cons u).map ((cons v).map e.inv)) ≫ ((cons u).map ((cons v).map e.hom)) = 𝟙 _ := by
  simp [← Functor.map_comp]


-- @@ L531-566 expanded
/-- The natural isomorphism `Q_{x, l₂}(l₁) : (x :: l₁) ⊗ l₂ ≅ l₁ ⊗ (x :: l₂)`.
This corresponds to Lemma 4.25 in Piceghello's thesis.
This is an auxiliary isomorphism for the definition of the general braiding isomorphism.
-/
public def Q (x : C) (l₂ : SList C) : (cons x) ⋙ tensorRight l₂ ≅ tensorRight ((cons x).obj l₂) :=
  recNatIso
    (tensorObjConsIso x nil l₂ ≪≫
      (cons x).mapIso (whiskerRightIso unitIsoNil.symm l₂) ≪≫
        (cons x).mapIso (λ_ l₂) ≪≫ (λ_ ((cons x).obj l₂)).symm ≪≫ whiskerRightIso unitIsoNil _)
    (fun y l₁ prev =>
        -- Inductive step: l₁ = y :: l₁
              -- (x ::~ y ::~ l₁) ⊗ l₂ ≅ (x ::~ l₂) ⊗ y ::~ l₁
        
      tensorObjConsIso x ((cons y).obj l₁) l₂ ≪≫
        (cons x).mapIso (tensorObjConsIso y l₁ l₂) ≪≫
          swapIso x y (l₁ ⊗ l₂) ≪≫
            (cons y).mapIso (tensorObjConsIso x l₁ l₂).symm ≪≫
              (cons y).mapIso prev ≪≫ (tensorObjConsIso y l₁ ((cons x).obj l₂)).symm)
    (fun y z l₁ prev => by
      dsimp at prev ⊢
      simp [whiskerRight_cons_map, whiskerRight_swap,
        reassoc_of% SList.swap_natural x z (tensorObjConsIso y l₁ l₂).hom,
        ← reassoc_of% SList.swap_hexagon x y z (l₁ ⊗ l₂),
        ← reassoc_of% SList.swap_natural x y (tensorObjConsIso z l₁ l₂).hom,
        ← reassoc_of% SList.swap_natural y z prev.hom,
        ← reassoc_of% SList.swap_natural y z (tensorObjConsIso x l₁ l₂).inv])
    (fun c l l' f h h' e => by
      dsimp at h h' e ⊢
      simp only [whiskerRight_cons_map, Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc,
        Iso.map_inv_hom_id_assoc, ← reassoc_of% swap_natural x c (f ▷ l₂), Iso.cancel_iso_hom_left]
      simp_rw [← Functor.map_comp_assoc, ← e]
      simp [whiskerRight_cons_map])


-- @@ L568-576 expanded
@[local simp, reassoc]
public lemma Q_hom_app_nil (x : C) (l₂ : SList C) :
    (Q x l₂).hom.app nil =
      (tensorObjConsIso x nil l₂).hom ≫
        (cons x).map (unitIsoNil.inv ▷ l₂) ≫
          (cons x).map (λ_ l₂).hom ≫ (λ_ ((cons x).obj l₂)).inv ≫ unitIsoNil.hom ▷ _ :=
  by simp [Q]


-- @@ L578-587 expanded
@[local simp, reassoc]
public lemma Q_hom_app_cons (x : C) (l₂ : SList C) (y : C) (l₁ : SList C) :
    (Q x l₂).hom.app ((cons y).obj l₁) =
      (tensorObjConsIso x ((cons y).obj l₁) l₂).hom ≫
        (cons x).map (tensorObjConsIso y l₁ l₂).hom ≫
          β~ x y (l₁ ⊗ l₂) ≫
            (cons y).map (tensorObjConsIso x l₁ l₂).inv ≫
              (cons y).map ((Q x l₂).hom.app l₁) ≫ (tensorObjConsIso y l₁ ((cons x).obj l₂)).inv :=
  by simp [Q]


-- @@ L589-604 expanded
set_option backward.isDefEq.respectTransparency false in
@[local simp, reassoc]
public lemma Q_inv_app_cons (x : C) (l₂ : SList C) (y : C) (l₁ : SList C) :
    (Q x l₂).inv.app ((cons y).obj l₁) =
      (tensorObjConsIso y l₁ ((cons x).obj l₂)).hom ≫
        (cons y).map ((Q x l₂).inv.app l₁) ≫
          (cons y).map (tensorObjConsIso x l₁ l₂).hom ≫
            β~ y x (l₁ ⊗ l₂) ≫
              (cons x).map (tensorObjConsIso y l₁ l₂).inv ≫
                (tensorObjConsIso x ((cons y).obj l₁) l₂).inv :=
  by
  rw [← IsIso.inv_eq_inv]
  simp only [Functor.comp_obj, Functor.flip_obj_obj, curriedTensor_obj_obj, NatIso.inv_inv_app,
    Q_hom_app_cons, IsIso.inv_comp, IsIso.Iso.inv_inv, Category.assoc, IsIso.Iso.inv_hom,
    Iso.cancel_iso_hom_left, IsIso.eq_inv_comp, Iso.map_inv_hom_id_assoc, swap_swap_assoc,
    Iso.map_hom_inv_id_assoc]
  simp [← Functor.map_comp_assoc]


-- @@ L606-620 expanded
set_option backward.isDefEq.respectTransparency false in
public lemma Q_hom_app_naturality (x : C) {l₂ l₂' : SList C} (f : l₂ ⟶ l₂') (l₁ : SList C) :
    ((cons x).obj l₁) ◁ f ≫ (Q x l₂').hom.app l₁ = (Q x l₂).hom.app l₁ ≫ l₁ ◁ ((cons x).map f) := by
  induction l₁ using SList.cons_induction with
  | nil =>
    dsimp
    simp only [whiskerLeft_cons, whiskerLeft_nil, Functor.map_comp, Category.assoc, Q_hom_app_nil,
      Iso.inv_hom_id_assoc, hom_inv_whiskerRight_assoc, Iso.cancel_iso_hom_left]
    simp [← Functor.map_comp_assoc, -Functor.map_comp]
  | cons c l₁ ih =>
    dsimp
    simp only [whiskerLeft_cons, Functor.map_comp, Category.assoc, Q_hom_app_cons,
      Functor.flip_obj_obj, curriedTensor_obj_obj, Iso.inv_hom_id_assoc, Iso.map_inv_hom_id_assoc,
      ← reassoc_of% swap_natural x c (l₁ ◁ f), Iso.cancel_iso_hom_left]
    simp [← Functor.map_comp_assoc, -Functor.map_comp, ← ih, whiskerLeft_cons]


-- @@ L622-661 expanded
/-- This is lemma 4.28 in Piceghello's thesis. -/
lemma Q_cons_Q_cons_swap (x y : C) (l₁ l₂ : SList C) :
    β~ x y (l₂ ⊗ l₁) ≫
        ((cons y).map (tensorObjConsIso x l₂ l₁).inv) ≫
          ((cons y).map ((Q x l₁).hom.app l₂)) ≫
            (tensorObjConsIso y l₂ ((cons x).obj l₁)).inv ≫ ((Q y ((cons x).obj l₁)).hom.app l₂) =
      ((cons x).map (tensorObjConsIso y l₂ l₁).inv) ≫
        ((cons x).map ((Q y l₁).hom.app l₂)) ≫
          (tensorObjConsIso x l₂ ((cons y).obj l₁)).inv ≫
            (Q x ((cons y).obj l₁)).hom.app l₂ ≫ (l₂ ◁ β~ x y l₁) :=
  by
  induction l₂ using SList.cons_induction with
  |
    nil =>
    simp only [Functor.flip_obj_obj, curriedTensor_obj_obj, Q_hom_app_nil, Functor.map_comp,
      Iso.inv_hom_id_assoc, Category.assoc, Iso.map_inv_hom_id_assoc,
      reassoc_of% swap_natural x y (unitIsoNil.inv ▷ l₁), reassoc_of% swap_natural x y (λ_ l₁).hom,
      whiskerLeft_nil, hom_inv_whiskerRight_assoc]
    simp [← Functor.map_comp_assoc, -Functor.map_comp]
  | cons z l₂ ih =>
    dsimp at ih ⊢
    simp only [Q_hom_app_cons, Functor.flip_obj_obj, curriedTensor_obj_obj, Functor.map_comp,
      Iso.inv_hom_id_assoc, Category.assoc, Iso.map_inv_hom_id_assoc] at ih ⊢
    simp only [whiskerLeft_cons, Iso.inv_hom_id_assoc]
    have := swap_natural y z ((Q x l₁).hom.app l₂)
    dsimp at this
    simp only [← reassoc_of% this]
    have := swap_natural y z (tensorObjConsIso x l₂ l₁).inv
    simp only at this
    simp only [← reassoc_of% this]
    have := swap_natural x y (tensorObjConsIso z l₂ l₁).hom
    simp only [reassoc_of% this, reassoc_of% swap_hexagon]
    have := congr((cons z).map $ih)
    simp only [Functor.map_comp] at this
    simp only [reassoc_of% this]
    have := swap_natural x z ((Q y l₁).hom.app l₂)
    simp only [Functor.comp_obj, Functor.flip_obj_obj, curriedTensor_obj_obj] at this
    simp only [← reassoc_of% this]
    have := swap_natural x z (tensorObjConsIso y l₂ l₁).inv
    simp only at this
    simp [reassoc_of% this]


-- @@ L663-663 verbatim
end Q


-- @@ L665-665 verbatim
section


-- @@ L667-697 expanded
set_option backward.isDefEq.respectTransparency false in
/-- The braiding `l₁ ⊗ l₂ ≅ l₂ ⊗ l₁` is built inductively by repeated applications of `Q`.
This corresponds to Lemma 4.29 in Piceghello's thesis.
-/
public def braidNatIso (l₂ : SList C) : tensorRight l₂ ≅ tensorLeft l₂ :=
  recNatIso
    (whiskerRightIso unitIsoNil.symm _ ≪≫ λ_ l₂ ≪≫ (ρ_ l₂).symm ≪≫ whiskerLeftIso _ unitIsoNil)
      -- Inductive step: l₁ = x :: l₁
          -- (x ::~ l₁) ⊗ l₂ ≅ x ::~ (l₁ ⊗ l₂) ≅ x ::~ (l₂ ⊗ l₁) ≅ (x ::~ l₂) ⊗ l₁ ≅ l₂ ⊗ (x ::~ l₁)
      
    (fun x l₁ prev =>
      (tensorObjConsIso x l₁ l₂) ≪≫
        (cons x).mapIso prev ≪≫ (tensorObjConsIso x l₂ l₁).symm ≪≫ (Q x l₁).app l₂)
    (fun y z l₁ prev => by
      -- Compatibility with swap, this is essentially Q_cons_Q_cons_swap with a few extra steps
      
      dsimp
      have := Q_cons_Q_cons_swap y z l₁ l₂
      simp at this ⊢
      simp [← this]
      have := swap_natural y z prev.hom
      simp at this
      simp [← reassoc_of% this, whiskerRight_swap])
    (fun c l l' f h h' e => by
      dsimp at h h' e ⊢
      have := congr((cons c).map $e)
      simp only [Functor.map_comp] at this
      simp [whiskerRight_cons_map, reassoc_of% this, ← Q_hom_app_naturality c f l₂,
        whiskerLeft_cons])


-- @@ L699-703 expanded
lemma braidNatIso_hom_app_nil (l₁ : SList C) :
    ((braidNatIso l₁).hom.app nil) =
      unitIsoNil.inv ▷ _ ≫ (λ_ l₁).hom ≫ (ρ_ l₁).inv ≫ _ ◁ unitIsoNil.hom :=
  by simp [braidNatIso]


-- @@ L705-711 expanded
lemma braidNatIso_hom_cons (x : C) (l₁ l₂ : SList C) :
    (braidNatIso l₁).hom.app ((cons x).obj l₂) =
      (tensorObjConsIso x l₂ l₁).hom ≫
        (cons x).map ((braidNatIso l₁).hom.app l₂) ≫
          (tensorObjConsIso x l₁ l₂).inv ≫ (Q x l₂).hom.app l₁ :=
  by simp [braidNatIso]


-- @@ L713-713 verbatim
end


-- @@ L715-715 verbatim
section

-- @@ L716-716 verbatim
variable {l₁ l₂ : SList C}


-- @@ L718-721 expanded
@[no_expose]
public def Φ (x : C) (l : SList C) : Unit ⊕ Fin l.length ≃ Fin ((cons x).obj l).length :=
  Equiv.trans (Equiv.sumCongr finOneEquiv.symm (.refl _))
    (finSumFinEquiv.trans (finCongr (by simp +arith)))


-- @@ L723-730 expanded
@[elab_as_elim, cases_eliminator]
public lemma fin_cons_obj_case {x : C} {L : SList C}
    {motive : {x : C} → {L : SList C} → Fin ((cons x).obj L).length → Prop}
    (inl : motive (Φ x L (.inl ()))) (inr : ∀ (i : Fin L.length), motive (Φ x L (.inr i)))
    (i : Fin ((cons x).obj L).length) : motive i :=
  by
  obtain ⟨i, rfl⟩ := (Φ _ _).surjective i
  grind


-- @@ L732-735 verbatim
@[simp, grind =]
public lemma Φ_apply_val_right (x : C) (l : SList C) (i : Fin l.length) :
    (Φ x l (.inr i)).val = 1 + i.val :=
  (rfl)


-- @@ L737-739 verbatim
@[simp, grind =]
public lemma Φ_apply_val_left (x : C) (l : SList C) :
    (Φ x l (.inl ())).val = 0 := (rfl)


-- @@ L741-745 expanded
@[local simp, grind =]
public lemma toEquiv_cons_map_Φ_inr (x : C) {l l' : SList C} (f : l ⟶ l') (i : Fin l'.length) :
    toEquiv ((cons x).map f) (Φ _ _ <| .inr i) = (Φ _ _ <| .inr <| (toEquiv f) i) :=
  by
  ext
  simp [toEquiv, Nat.add_comm, toPerm_app_cons_apply_succ, Φ]


-- @@ L747-751 expanded
@[local simp, grind =]
public lemma toEquiv_cons_map_Φ_inl (x : C) {l l' : SList C} (f : l ⟶ l') :
    toEquiv ((cons x).map f) (Φ _ _ <| .inl ()) = (Φ _ _ <| .inl ()) :=
  by
  ext
  simp [toEquiv, Φ]


-- @@ L753-757 verbatim
@[local simp]
public lemma toEquiv_swap_Φ_inl (x y : C) (l : SList C) :
    toEquiv (β~ x y l) (Φ _ _ <| .inl ()) = Φ _ _ (.inr <| Φ _ _ <| .inl ()) := by
  ext
  simp [toEquiv, Φ]


-- @@ L759-764 verbatim
@[local simp]
public lemma toEquiv_swap_Φ_inr_Φ_inl (x y : C) (l : SList C) :
    toEquiv (β~ x y l) (Φ _ _ (.inr <| Φ _ _ <| .inl ())) =
    (Φ _ _ <| .inl ()) := by
  ext
  simp [toEquiv, Φ]


-- @@ L766-771 verbatim
@[local simp, grind =]
public lemma toEquiv_swap_Φ_inr_Φ_inr (x y : C) (l : SList C) (i : Fin l.length) :
    toEquiv (β~ x y l) (Φ _ _ <| .inr <| Φ _ _ <| .inr i) =
    (Φ _ _ <| .inr <| Φ _ _ <| .inr i) := by
  ext
  grind [toEquiv, Φ]


-- @@ L773-778 verbatim
@[local simp, grind =]
public lemma toEquiv_tensorObjConsIso_hom_Φ_inl (x : C) (l : SList C) (l' : SList C) :
    toEquiv (tensorObjConsIso x l l').hom (Φ _ _ <| .inl ()) =
    Ψ _ _ (.inl <| Φ _ _ <| .inl ()) := by
  ext
  simp [tensorObjConsIso]


-- @@ L780-786 verbatim
@[local simp, grind =]
public lemma toEquiv_tensorObjConsIso_hom_Φ_inl_Ψ_inl
    (x : C) (l : SList C) (l' : SList C) (i : Fin l.length) :
    toEquiv (tensorObjConsIso x l l').hom (Φ _ _ <| .inr <| Ψ _ _ <| .inl i) =
    Ψ _ _ (.inl <| Φ _ _ <| .inr i) := by
  ext
  simp [tensorObjConsIso]


-- @@ L788-794 verbatim
@[local simp]
public lemma toEquiv_tensorObjConsIso_hom_Φ_inr
    (x : C) (l : SList C) (l' : SList C) (i : Fin l'.length) :
    toEquiv (tensorObjConsIso x l l').hom (Φ _ _ <| .inr <| Ψ _ _ <| .inr i) =
    Ψ _ _ (.inr i) := by
  ext
  simp +arith [tensorObjConsIso]


-- @@ L796-801 verbatim
@[local simp]
public lemma toEquiv_tensorObjConsIso_inv_Φ_inl (x : C) (l : SList C) (l' : SList C) :
    toEquiv (tensorObjConsIso x l l').inv (Ψ _ _ <| .inl <| Φ _ _ <| .inl ()) =
    (Φ _ _ <| .inl ()) := by
  ext
  simp [tensorObjConsIso]


-- @@ L803-809 verbatim
@[local simp]
public lemma toEquiv_tensorObjConsIso_inv_Φ_inl_Ψ_inl
    (x : C) (l : SList C) (l' : SList C) (i : Fin l.length) :
    toEquiv (tensorObjConsIso x l l').inv (Ψ _ _ <| .inl <| Φ _ _ <| .inr i) =
    (Φ _ _ <| .inr <| Ψ _ _ <| .inl i) := by
  ext
  simp [tensorObjConsIso]


-- @@ L811-817 verbatim
@[local simp]
public lemma toEquiv_tensorObjConsIso_inv_Φ_inr
    (x : C) (l : SList C) (l' : SList C) (i : Fin l'.length) :
    toEquiv (tensorObjConsIso x l l').inv (Ψ _ _ <| .inr i) =
    (Φ _ _ <| .inr <| Ψ _ _ <| .inr i) := by
  ext
  simp +arith [tensorObjConsIso]


-- @@ L819-822 verbatim
@[simp]
public lemma toEquiv_consTensSingletonIso_hom_right (x : C) (l : SList C) (t : Fin l.length) :
    (toEquiv (consTensSingletonIso x l).hom) (Ψ _ _ <| .inr t) = Φ _ _ (.inr t) := by
  simp [consTensSingletonIso]


-- @@ L824-828 verbatim
@[simp]
public lemma toEquiv_consTensSingletonIso_hom_left (x : C) (l : SList C) :
    (toEquiv (consTensSingletonIso x l).hom) (Ψ _ _ (.inl <| Φ _ _ <| .inl ())) =
    (Φ _ _ <| .inl ()) := by
  simp [consTensSingletonIso]


-- @@ L830-833 verbatim
@[simp]
public lemma toEquiv_consTensSingletonIso_inv_right (x : C) (l : SList C) (t : Fin l.length) :
    (toEquiv (consTensSingletonIso x l).inv) (Φ _ _ (.inr t)) = Ψ _ _ (.inr t) := by
  simp [consTensSingletonIso]


-- @@ L835-839 verbatim
@[simp]
public lemma toEquiv_consTensSingletonIso_inv_left (x : C) (l : SList C) :
    (toEquiv (consTensSingletonIso x l).inv) (Φ _ _ <| .inl ()) =
    Ψ _ _ (.inl <| Φ _ _ <| .inl ()) := by
  simp [consTensSingletonIso]


-- @@ L841-861 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma Q_hom_app_left (x : C) (l₂ : SList C) (l : SList C) (i : Fin l.length) :
    toEquiv ((Q x l₂).hom.app l) (Ψ _ _ <| .inl i) =
    Ψ _ _ (.inl <| Φ _ _ (.inr i)) := by
  induction l using SList.cons_induction with
  | nil =>
    simp only [length_nil] at i
    exact Fin.elim0 i
  | cons c l ih =>
    obtain ⟨i, rfl⟩ := (Φ _ _).surjective i
    cases i with
    | inr i =>
      have := ih i
      simp only [Functor.comp_obj, Functor.flip_obj_obj, curriedTensor_obj_obj] at this
      simp [Q_hom_app_cons, this]
    | inl i =>
      obtain rfl : i = () := rfl
      letI U :=(Q x l₂).hom.app l
      dsimp at U
      simp [Q_hom_app_cons]


-- @@ L863-872 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp, grind =]
lemma Q_hom_app_right_Φ_inl (x : C) (l₂ : SList C) (l : SList C) :
    toEquiv ((Q x l₂).hom.app l) (Ψ _ _ (.inr <| Φ _ _ <| .inl ())) =
    Ψ _ _ (.inl <| Φ _ _ <| .inl ()) := by
  induction l using SList.cons_induction with
  | nil => simp [Q_hom_app_nil]
  | cons c l ih =>
    dsimp at ih
    simp [Q_hom_app_cons, ih]


-- @@ L874-883 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp, grind =]
lemma Q_hom_app_right_right (x : C) (l₂ : SList C) (l : SList C) (i : Fin l₂.length) :
    toEquiv ((Q x l₂).hom.app l) (Ψ _ _ <| .inr <| Φ _ _ <| .inr i) =
    Ψ _ _ (.inr i) := by
  induction l using SList.cons_induction with
  | nil => simp [Q_hom_app_nil]
  | cons c l ih =>
    dsimp at ih
    simp [Q_hom_app_cons, ih]


-- @@ L885-923 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The "braiding" morphism we constructed corresponds to the equivalence
```
  Fin (l₁ ⊗ l₂).length
    _ ≃ Fin (l₁.length + l₂.length)
    _ ≃ Fin (l₂.length + l₁.length)
    _ ≃ Fin ((l₂ ⊗ l₁).length)
```. -/
public theorem toEquiv_braidNatIso (l₁ l₂ : SList C) :
    toEquiv (braidNatIso l₁|>.hom.app l₂) =
    ((Ψ l₁ l₂).symm.trans (Equiv.sumComm _ _)).trans (Ψ l₂ l₁) := by
  ext i : 1
  obtain ⟨i, rfl⟩ := (Ψ l₁ l₂).surjective i
  induction l₂ using SList.cons_induction generalizing l₁ with
  | nil =>
    cases i with
    | inl i => simp [braidNatIso_hom_app_nil]
    | inr i =>
      simp only [length_nil] at i
      exact Fin.elim0 i
  | cons t l₂ ih =>
    cases i with
    | inl i =>
      have e₁ := Q_hom_app_left t l₂ l₁ i
      have e₂ := ih l₁ (.inl i)
      simp only [Functor.comp_obj, Functor.flip_obj_obj, curriedTensor_obj_obj] at e₁ e₂
      simp [braidNatIso_hom_cons, e₁, e₂]
    | inr i =>
      obtain ⟨i, rfl⟩ := (Φ _ _).surjective i
      cases i with
      | inr i =>
        have e₁ := Q_hom_app_right_right t l₂ l₁ i
        have e₂ := ih l₁ (.inr i)
        simp only [Functor.comp_obj, Functor.flip_obj_obj, curriedTensor_obj_obj] at e₁ e₂
        simp [braidNatIso_hom_cons, e₁, e₂]
      | inl =>
        have e₁ := Q_hom_app_right_Φ_inl t l₂ l₁
        simp only [Functor.comp_obj, Functor.flip_obj_obj, curriedTensor_obj_obj] at e₁
        simp [braidNatIso_hom_cons, e₁]


-- @@ L925-925 verbatim
@[expose] public abbrev braid (l₁ l₂ : SList C) : l₁ ⊗ l₂ ⟶ l₂ ⊗ l₁ := (braidNatIso l₂|>.hom.app l₁)


-- @@ L927-931 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp, grind =]
public lemma toEquiv_braid_Ψ_left (l₁ l₂ : SList C) (i : Fin l₂.length) :
    (toEquiv (braid l₁ l₂)) (Ψ l₂ l₁ <| .inl i) = (Ψ l₁ l₂) (.inr i) := by
  simp [toEquiv_braidNatIso]


-- @@ L933-937 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp, grind =]
public lemma toEquiv_braid_Ψ_right (l₁ l₂ : SList C) (i : Fin l₁.length) :
    (toEquiv (braid l₁ l₂)) (Ψ l₂ l₁ <| .inr i) = (Ψ l₁ l₂) (.inl i) := by
  simp [toEquiv_braidNatIso]


-- @@ L939-939 verbatim
end


-- @@ L941-946 verbatim
@[simp, grind =]
lemma braid_braid (x y : SList C) : braid x y ≫ braid y x = 𝟙 _ := by
  rw [hom_eq_iff_toEquiv_eq]
  ext i : 1
  obtain ⟨i, rfl⟩ := (Ψ _ _).surjective i
  cases i with simp


-- @@ L948-952 verbatim
@[simps!, expose]
public def braidIso (x y : SList C) :
    x ⊗ y ≅ y ⊗ x where
  hom := braid x y
  inv := braid y x


-- @@ L954-961 verbatim
lemma braid_hexagon_forward (x y z : SList C) :
    (α_ x y z).hom ≫ braid x (y ⊗ z) ≫ (α_ y z x).hom =
    braid x y ▷ z ≫ (α_ y x z).hom ≫ y ◁ braid x z := by
  rw [hom_eq_iff_toEquiv_eq]
  ext j : 1
  cases j using fin_tensor_obj_case with
  | inl j => simp
  | inr j => grind [(Ψ z x).surjective j]


-- @@ L963-970 verbatim
lemma braid_hexagon_reverse (x y z : SList C) :
    (α_ x y z).inv ≫ braid (x ⊗ y) z ≫ (α_ z x y).inv =
    (x ◁ braid y z) ≫ (α_ x z y).inv ≫ (braid x z) ▷ y := by
  rw [hom_eq_iff_toEquiv_eq]
  ext i
  cases i using fin_tensor_obj_case with
  | inl i => grind [(Ψ z x).surjective i]
  | inr i => simp


-- @@ L972-977 verbatim
lemma braid_naturality_left {x y z : SList C} (f : x ⟶ y) :
    (f ▷ z) ≫ braid y z = braid x z ≫ (z ◁ f) := by
  rw [hom_eq_iff_toEquiv_eq]
  ext i
  obtain ⟨i, rfl⟩ := (Ψ _ _).surjective i
  cases i with simp


-- @@ L979-984 verbatim
lemma braid_naturality_right {x y z : SList C} (g : y ⟶ z) :
    (x ◁ g) ≫ braid x z = braid x y ≫ (g ▷ x) := by
  rw [hom_eq_iff_toEquiv_eq]
  ext i
  obtain ⟨i, rfl⟩ := (Ψ _ _).surjective i
  cases i with simp


-- @@ L986-991 verbatim
public instance : SymmetricCategory (SList C) where
  braiding x y := braidIso x y
  braiding_naturality_left f z := by simpa using braid_naturality_left f
  braiding_naturality_right {_ _} _ f := by simpa using braid_naturality_right f
  hexagon_forward x y z := by simpa using braid_hexagon_forward x y z
  hexagon_reverse x y z := by simpa using braid_hexagon_reverse x y z


-- @@ L993-1000 expanded
set_option backward.isDefEq.respectTransparency false in
public lemma braiding_hom_app_nil (l₁ : SList C) :
    (β_ l₁ nil).hom = (_ ◁ unitIsoNil.inv ≫ (ρ_ _).hom ≫ (λ_ _).inv ≫ unitIsoNil.hom ▷ _) :=
  by
  rw [← IsIso.inv_eq_inv, IsIso.Iso.inv_hom]
  simp only [BraidedCategory.braiding, braidIso_inv, braid, IsIso.inv_comp, inv_whiskerRight,
    IsIso.Iso.inv_hom, IsIso.Iso.inv_inv, Category.assoc, inv_whiskerLeft]
  rw [← IsIso.inv_eq_inv]
  simp [braidNatIso_hom_app_nil]


-- @@ L1002-1004 expanded
public lemma braiding_inv_app_nil (l₁ : SList C) :
    (β_ l₁ nil).inv = unitIsoNil.inv ▷ _ ≫ (λ_ _).hom ≫ (ρ_ _).inv ≫ _ ◁ unitIsoNil.hom := by
  simp [BraidedCategory.braiding, braidNatIso_hom_app_nil]


-- @@ L1006-1018 expanded
set_option backward.isDefEq.respectTransparency false in
public lemma braiding_hom_cons_right (x : C) (l₁ l₂ : SList C) :
    (β_ l₁ ((cons x).obj l₂)).hom =
      (Q x l₂).inv.app l₁ ≫
        (tensorObjConsIso x l₁ l₂).hom ≫
          (cons x).map (β_ l₁ l₂).hom ≫ (tensorObjConsIso x l₂ l₁).inv :=
  by
  rw [← IsIso.inv_eq_inv, IsIso.Iso.inv_hom]
  simp only [BraidedCategory.braiding, braidIso_inv, braid, Functor.flip_obj_obj,
    curriedTensor_obj_obj, Functor.comp_obj, braidIso_hom, IsIso.inv_comp, IsIso.Iso.inv_inv,
    IsIso.Iso.inv_hom, Category.assoc, NatIso.inv_inv_app]
  rw [← IsIso.inv_eq_inv]
  simp [braidNatIso_hom_cons, ← Functor.map_comp]


-- @@ L1020-1031 expanded
set_option backward.isDefEq.respectTransparency false in
public lemma braiding_hom_cons_left (x : C) (l₁ l₂ : SList C) :
    (β_ ((cons x).obj l₁) l₂).hom =
      (tensorObjConsIso x l₁ l₂).hom ≫
        (cons x).map (β_ l₁ l₂).hom ≫ (tensorObjConsIso x l₂ l₁).inv ≫ (Q x l₁).hom.app l₂ :=
  by
  rw [SymmetricCategory.braiding_swap_eq_inv_braiding]
  rw [← IsIso.inv_eq_inv, IsIso.Iso.inv_inv, braiding_hom_cons_right]
  simp_rw [IsIso.inv_comp, IsIso.Iso.inv_inv, ← Functor.map_inv, IsIso.Iso.inv_hom]
  simp [SymmetricCategory.braiding_swap_eq_inv_braiding]


-- @@ L1033-1037 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp, grind =]
public lemma toEquiv_braiding_hom_Ψ_left (l₁ l₂ : SList C) (i : Fin l₂.length) :
    toEquiv (β_ l₁ l₂).hom (Ψ l₂ l₁ <| .inl i) = Ψ l₁ l₂ (.inr i) := by
  simp [toEquiv_braidNatIso, BraidedCategory.braiding]


-- @@ L1039-1042 verbatim
@[simp, grind =]
public lemma toEquiv_braiding_hom_Ψ_right (l₁ l₂ : SList C) (i : Fin l₁.length) :
    toEquiv (β_ l₁ l₂).hom (Ψ l₂ l₁ <| .inr i) = Ψ l₁ l₂ (.inl i) := by
  simp [BraidedCategory.braiding]


-- @@ L1044-1044 verbatim
end CategoryTheory.SList
