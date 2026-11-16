/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import SymmMonCoherence.FintypeGrpd
public import SymmMonCoherence.SList.Equivalence
public import Mathlib.CategoryTheory.Elementwise


-- @@ L12-15 verbatim
/-! # Symmetric lists and FintypeGrpd

Symmetric lists on the unit type are equivalent to the groupoid of finite types and bijections,
and the equivalence is symmetric monoidal. -/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
universe v u


-- @@ L21-23 verbatim
namespace CategoryTheory.SList

-- TODO Generalize from Unit to PUnit


-- @@ L25-32 verbatim
/-- The functor from symmetric lists on a unit type to the groupoid
of finite types and bijections. The API for this definition is minimal,
please prefer its equivalent version below (unitEquivalence). -/
@[pp_with_univ]
def toFintypeGrpdFunctor : SList PUnit.{v + 1} ⥤ FintypeGrpd.{u} where
  obj x := .mk <| .of <| ULift <| Fin x.length
  map f := FintypeGrpd.mkHom <| Equiv.symm <|
    Equiv.ulift.trans <| (toEquiv f).trans <| Equiv.ulift.symm


-- @@ L34-39 verbatim
/-- An equivalence `toFintypeGrpdFunctor.obj x ≃ Fin x.length`. Under the hood,
this is an identity, but it is important to insert it in order to help automation. -/
@[pp_with_univ]
irreducible_def toFintypeGrpdFunctor.ι (x : SList PUnit.{v + 1}) :
    Fin x.length ≃ toFintypeGrpdFunctor.{v, u}.obj x :=
  Equiv.ulift.symm


-- @@ L41-44 verbatim
@[simp]
lemma toFintypeGrpdFunctor_card (x : SList PUnit.{v + 1}) :
    Nat.card (toFintypeGrpdFunctor.{v, u}.obj x) = x.length := by
  simp [← Finite.card_eq.mpr ⟨toFintypeGrpdFunctor.ι.{v, u} _⟩]


-- @@ L46-46 verbatim
open toFintypeGrpdFunctor


-- @@ L48-52 verbatim
@[simp]
lemma toFintypeGrpdFunctor_map_ι_symm {x y : SList PUnit.{v + 1}} (f : x ⟶ y) (i : Fin y.length) :
    (toFintypeGrpdFunctor.{v, u}.map f).iso.inv (ι.{v, u} y i) = (ι.{v, u} x) (toEquiv f i) := by
  simp_rw [toFintypeGrpdFunctor.ι_def]
  rfl


-- @@ L54-59 verbatim
@[simp]
lemma toFintypeGrpdFunctor_map_ι {x y : SList PUnit.{v + 1}} (f : x ⟶ y) (i : Fin x.length) :
    (toFintypeGrpdFunctor.{v, u}.map f).iso.hom (ι.{v, u} x i) =
      (ι.{v, u} y) ((toEquiv f).symm i) := by
  simp_rw [toFintypeGrpdFunctor.ι_def]
  rfl


-- @@ L61-61 verbatim
section

-- @@ L62-62 verbatim
open MonoidalCategory


-- @@ L64-66 verbatim
public instance : IsEmpty (toFintypeGrpdFunctor.{v, u}.obj (𝟙_ (SList PUnit.{v + 1}))) := by
  simp only [toFintypeGrpdFunctor, tensorUnit_length]
  infer_instance


-- @@ L68-117 verbatim
public instance : toFintypeGrpdFunctor.{v, u}.Monoidal :=
  letI : toFintypeGrpdFunctor.{v, u}.CoreMonoidal :=
    { εIso := FintypeGrpd.mkIso
        (⟨fun i ↦ IsEmpty.elim inferInstance i,
          fun i ↦ IsEmpty.elim inferInstance i,
          fun i ↦ IsEmpty.elim inferInstance i,
          fun i ↦ IsEmpty.elim inferInstance i⟩)
      μIso X Y := FintypeGrpd.mkIso <|
        FintypeGrpd.tensorObjEquiv _ _ |>.symm.trans <|
          Equiv.sumCongr (ι.{v, u} X).symm (ι.{v, u} Y).symm |>.trans <|
            Ψ .. |>.trans <|
              ι.{v, u} (X ⊗ Y)
      μIso_hom_natural_left {X Y} f Z := by
        ext i
        cases i using FintypeGrpd.tensor_obj_cases with
          obtain ⟨t, rfl⟩ := (ι.{v, u} _).surjective t
        | left t => simp [toEquiv_symm]
        | right t => simp [toEquiv_symm]
      μIso_hom_natural_right X {Y Z} f := by
        ext i
        cases i using FintypeGrpd.tensor_obj_cases with
          obtain ⟨t, rfl⟩ := (ι.{v, u} _).surjective t
        | left t => simp [toEquiv_symm]
        | right t => simp [toEquiv_symm]
      associativity X Y Z := by
        ext i
        cases i using FintypeGrpd.tensor_obj_cases with
        | left i =>
          cases i using FintypeGrpd.tensor_obj_cases with
            obtain ⟨t, rfl⟩ := (ι.{v, u} _).surjective t
          | left t => simp [toEquiv_symm]
          | right t => simp [toEquiv_symm]
        | right i =>
          obtain ⟨i, rfl⟩ := (ι.{v, u} _).surjective i
          simp [toEquiv_symm]
      left_unitality X := by
        ext i
        cases i using FintypeGrpd.tensor_obj_cases with
        | left t => exact IsEmpty.elim inferInstance t
        | right t =>
          obtain ⟨i, rfl⟩ := (ι.{v, u} _).surjective t
          simp [toEquiv_symm]
      right_unitality X := by
        ext i
        cases i using FintypeGrpd.tensor_obj_cases with
        | left t =>
          obtain ⟨i, rfl⟩ := (ι.{v, u} _).surjective t
          simp [toEquiv_symm]
        | right t => exact IsEmpty.elim inferInstance t }
  this.toMonoidal


-- @@ L119-127 verbatim
lemma toFintypeGrpdFunctor_μIso_def (X Y : SList PUnit.{v + 1}) :
    Functor.Monoidal.μIso toFintypeGrpdFunctor.{v, u} X Y =
    (FintypeGrpd.mkIso <|
      FintypeGrpd.tensorObjEquiv _ _ |>.symm.trans <|
        Equiv.sumCongr (ι.{v, u} X).symm (ι.{v, u} Y).symm |>.trans <|
          Ψ .. |>.trans <|
            ι.{v, u} (X ⊗ Y)) := rfl

-- instance : unitEquivalence.functor.Monoidal := inferInstanceAs toFintypeGrpdFunctor.Monoidal


-- @@ L129-129 verbatim
section

-- @@ L130-132 verbatim
variable {X Y : SList PUnit.{v + 1}}
    (l : (toFintypeGrpdFunctor.{v, u}.obj X))
    (r : (toFintypeGrpdFunctor.{v, u}.obj Y))


-- @@ L134-139 verbatim
@[simp]
lemma toFintypeGrpdFunctor_μ_iso_hom_left :
    (Functor.LaxMonoidal.μ toFintypeGrpdFunctor.{v, u} X Y).iso.hom (FintypeGrpd.inl _ _ l) =
    ι.{v, u} _ (Ψ _ _ <| .inl <| (ι.{v, u} _ |>.symm l)) := by
  rw [← Functor.Monoidal.μIso_hom, toFintypeGrpdFunctor_μIso_def]
  simp


-- @@ L141-146 verbatim
@[simp]
lemma toFintypeGrpdFunctor_μ_iso_hom_right :
    (Functor.LaxMonoidal.μ toFintypeGrpdFunctor.{v, u} X Y).iso.hom (FintypeGrpd.inr _ _ r) =
    ι.{v, u} _ (Ψ _ _ <| .inr <| (ι.{v, u} _ |>.symm r)) := by
  rw [← Functor.Monoidal.μIso_hom, toFintypeGrpdFunctor_μIso_def]
  simp


-- @@ L148-154 verbatim
@[simp]
lemma toFintypeGrpdFunctor_μ_iso_inv_left :
    (Functor.LaxMonoidal.μ toFintypeGrpdFunctor.{v, u} X Y).iso.inv
      (ι _ <| Ψ _ _ <| .inl <| (ι _ |>.symm l)) =
    (FintypeGrpd.inl _ _ l) := by
  rw [← Functor.Monoidal.μIso_hom, toFintypeGrpdFunctor_μIso_def]
  simp


-- @@ L156-162 verbatim
@[simp]
lemma toFintypeGrpdFunctor_μ_iso_inv_right :
    (Functor.LaxMonoidal.μ toFintypeGrpdFunctor.{v, u} X Y).iso.inv
      (ι _ <| Ψ _ _ <| .inr (ι _ |>.symm r)) =
    (FintypeGrpd.inr _ _ r) := by
  rw [← Functor.Monoidal.μIso_hom, toFintypeGrpdFunctor_μIso_def]
  simp


-- @@ L164-170 verbatim
@[simp]
lemma toFintypeGrpdFunctor_δ_iso_hom_left :
    (Functor.OplaxMonoidal.δ toFintypeGrpdFunctor.{v, u} X Y).iso.hom
      (ι _ <| Ψ _ _ <| .inl (ι _ |>.symm l)) =
    (FintypeGrpd.inl _ _ l) := by
  rw [← Functor.Monoidal.μIso_inv, toFintypeGrpdFunctor_μIso_def]
  simp


-- @@ L172-178 verbatim
@[simp]
lemma toFintypeGrpdFunctor_δ_iso_hom_right :
    (Functor.OplaxMonoidal.δ toFintypeGrpdFunctor.{v, u} X Y).iso.hom
      (ι _ <| Ψ _ _ <| .inr (ι _ |>.symm r)) =
    (FintypeGrpd.inr _ _ r) := by
  rw [← Functor.Monoidal.μIso_inv, toFintypeGrpdFunctor_μIso_def]
  simp


-- @@ L180-185 verbatim
@[simp]
lemma toFintypeGrpdFunctor_δ_iso_inv_left :
    (Functor.OplaxMonoidal.δ toFintypeGrpdFunctor.{v, u} X Y).iso.inv (FintypeGrpd.inl _ _ l) =
    (ι _ <| Ψ _ _ <| .inl (ι _ |>.symm l)) := by
  rw [← Functor.Monoidal.μIso_inv, toFintypeGrpdFunctor_μIso_def]
  simp


-- @@ L187-192 verbatim
@[simp]
lemma toFintypeGrpdFunctor_δ_iso_inv_right :
    (Functor.OplaxMonoidal.δ toFintypeGrpdFunctor.{v, u} X Y).iso.inv (FintypeGrpd.inr _ _ r) =
    (ι _ <| Ψ _ _ <| .inr <| (ι _ |>.symm r)) := by
  rw [← Functor.Monoidal.μIso_inv, toFintypeGrpdFunctor_μIso_def]
  simp


-- @@ L194-194 verbatim
end


-- @@ L196-213 verbatim
instance : toFintypeGrpdFunctor.{v, u}.Braided where
  braided X Y := by
    ext i
    cases i using FintypeGrpd.tensor_obj_cases with
    | left t =>
      obtain ⟨t, rfl⟩ := (ι _).surjective t
      simp only [coreCategory_comp_iso,
        Iso.trans_hom, ConcreteCategory.comp_apply, toFintypeGrpdFunctor_μ_iso_hom_left,
        Equiv.symm_apply_apply, FintypeGrpd.braiding_iso_hom_inl,
        toFintypeGrpdFunctor_μ_iso_hom_right]
      simp [toEquiv_symm, ← SymmetricCategory.braiding_swap_eq_inv_braiding]
    | right t =>
      obtain ⟨i, rfl⟩ := (ι _).surjective t
      simp only [coreCategory_comp_iso,
        Iso.trans_hom, ConcreteCategory.comp_apply, toFintypeGrpdFunctor_μ_iso_hom_right,
        Equiv.symm_apply_apply, FintypeGrpd.braiding_iso_hom_inr,
        toFintypeGrpdFunctor_μ_iso_hom_left]
      simp [toEquiv_symm, ← SymmetricCategory.braiding_swap_eq_inv_braiding]


-- @@ L215-215 verbatim
section


-- @@ L217-230 verbatim
set_option backward.isDefEq.respectTransparency false in
-- TODO: move this somewhere better
instance
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    [BraidedCategory C] [BraidedCategory D]
    (e : C ≌ D) [e.functor.Braided] [e.inverse.Monoidal] [e.IsMonoidal] : e.inverse.Braided where
  braided X Y := by
    apply e.functor.map_injective
    simp only [Functor.map_comp, Equivalence.fun_inv_map, Functor.comp_obj, Functor.id_obj,
      Equivalence.functor_map_μ_inverse_comp_counitIso_hom_app_tensor_assoc,
      BraidedCategory.braiding_naturality_assoc, Functor.map_braiding, Category.assoc, cancel_epi]
    rw [← IsIso.inv_eq_inv]
    simp [Equivalence.functor_map_μ_inverse_comp_counitIso_hom_app_tensor_assoc]


-- @@ L232-232 verbatim
end


-- @@ L234-236 verbatim
section ofFiniteGrpd

-- TODO: rename

-- @@ L237-239 verbatim
@[pp_with_univ]
noncomputable def ofFinite (X : Type u) [Finite X] : SList PUnit.{v + 1} :=
  listEquiv.symm <| List.replicate (Nat.card X) .unit


-- @@ L241-245 verbatim
lemma ofFinite_length (X : Type*) [Finite X] :
  (ofFinite X).length = Nat.card X := by simp [ofFinite]

/- The equivalence between `Fin (ofFinite X).length` and `X` induced by the
equality of their cardinalities. -/

-- @@ L246-249 verbatim
@[pp_with_univ]
noncomputable irreducible_def ofFinite.ι.{s, t} (X : Type t) [Finite X] :
    X ≃ Fin (ofFinite.{s, t} X).length :=
  Finite.equivFinOfCardEq (ofFinite_length _).symm


-- @@ L251-255 verbatim
noncomputable def ofFiniteHomOfEquiv {X Y : Type*} [Finite X] [Finite Y] (e : X ≃ Y) :
    ofFinite X ⟶ ofFinite Y :=
  liftEquiv
    ((ofFinite.ι _).symm.trans e.symm |>.trans (ofFinite.ι _))
    (fun _ ↦ rfl)


-- @@ L257-257 verbatim
section

-- @@ L258-258 verbatim
variable {X Y Z : Type*} [Finite X] [Finite Y] [Finite Z]


-- @@ L260-263 verbatim
@[simp, grind =]
lemma toEquiv_ofFiniteHomOfEquiv_ι (e : X ≃ Y) (y : Y) :
    toEquiv (ofFiniteHomOfEquiv e) (ofFinite.ι _ y) = ofFinite.ι _ (e.symm y) := by
  simp [ofFiniteHomOfEquiv]


-- @@ L265-268 verbatim
@[simp, grind =]
lemma toEquiv_ofFiniteHomOfEquiv_symm_ι (e : X ≃ Y) (x : X) :
    (toEquiv (ofFiniteHomOfEquiv e)).symm (ofFinite.ι _ x) = ofFinite.ι _ (e x) := by
  simp [ofFiniteHomOfEquiv]


-- @@ L270-276 verbatim
variable (X) in
@[simp, grind =]
lemma ofFiniteHomOfEquiv_refl : ofFiniteHomOfEquiv (.refl X) = 𝟙 _ := by
  rw [hom_eq_iff_toEquiv_eq]
  ext i
  obtain ⟨i, rfl⟩ := (ofFinite.ι X).surjective i
  simp


-- @@ L278-284 verbatim
@[simp, grind =]
lemma ofFiniteHomOfEquiv_trans (e₁ : X ≃ Y) (e₂ : Y ≃ Z) :
    ofFiniteHomOfEquiv (e₁.trans e₂) = ofFiniteHomOfEquiv e₁ ≫ ofFiniteHomOfEquiv e₂ := by
  rw [hom_eq_iff_toEquiv_eq]
  ext i
  obtain ⟨i, rfl⟩ := (ofFinite.ι Z).surjective i
  simp


-- @@ L286-294 verbatim
@[simp, push]
lemma ofFiniteHomOfEquiv_symm (e : X ≃ Y) :
    inv (ofFiniteHomOfEquiv e) = ofFiniteHomOfEquiv e.symm := by
  symm
  apply IsIso.eq_inv_of_inv_hom_id
  rw [hom_eq_iff_toEquiv_eq]
  ext i : 1
  obtain ⟨i, rfl⟩ := (ofFinite.ι Y).surjective i
  simp


-- @@ L296-296 verbatim
end


-- @@ L298-298 verbatim
section


-- @@ L300-302 verbatim
@[simp]
lemma _root_.CategoryTheory.Core.id_iso {C : Type*} [Category* C] (X : Core C) :
    (𝟙 X:).iso = .refl X.of := rfl


-- @@ L304-307 verbatim
@[simp]
lemma _root_.CategoryTheory.Core.comp_iso {C : Type*} [Category* C] {X Y Z : Core C}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).iso = f.iso.trans g.iso := rfl


-- @@ L309-311 verbatim
@[simp, grind =]
lemma _root_.FintypeCat.equivEquivIso_refl (X : FintypeCat) :
    FintypeCat.equivEquivIso (Equiv.refl X) = .refl X := rfl


-- @@ L313-316 verbatim
@[simp, grind =]
lemma _root_.FintypeCat.equivEquivIso_trans {X Y Z : FintypeCat} (e : X ≃ Y) (e' : Y ≃ Z) :
    FintypeCat.equivEquivIso (e.trans e') =
    (FintypeCat.equivEquivIso e).trans (FintypeCat.equivEquivIso e') := rfl


-- @@ L318-321 verbatim
@[simp, grind =]
lemma _root_.FintypeCat.equivEquivIso_apply_symm {X Y : FintypeCat} (e : X ≃ Y) :
    FintypeCat.equivEquivIso (e.symm) =
    (FintypeCat.equivEquivIso e).symm := rfl


-- @@ L323-326 verbatim
@[simp, grind =]
lemma _root_.FintypeCat.equivEquivIso_symm_refl (X : FintypeCat) :
    (FintypeCat.equivEquivIso.symm (Iso.refl X)) =
    Equiv.refl _ := rfl


-- @@ L328-331 verbatim
@[simp, grind =]
lemma _root_.FintypeCat.equivEquivIso_symm_trans {X Y Z : FintypeCat} (e : X ≅ Y) (e' : Y ≅ Z) :
    FintypeCat.equivEquivIso.symm (e.trans e') =
    (FintypeCat.equivEquivIso.symm e).trans (FintypeCat.equivEquivIso.symm e') := rfl


-- @@ L333-336 verbatim
@[simp, grind =]
lemma _root_.FintypeCat.equivEquivIso_symm_apply_symm {X Y : FintypeCat} (e : X ≅ Y) :
    FintypeCat.equivEquivIso.symm e.symm =
    (FintypeCat.equivEquivIso.symm e).symm := rfl


-- @@ L338-340 verbatim
end

-- This is an abbrev so that things check out at reducible transparency.

-- @@ L341-344 verbatim
@[pp_with_univ, simps]
noncomputable abbrev ofFiniteGrpdFunctor : FintypeGrpd.{u} ⥤ SList PUnit.{v + 1} where
  obj X := ofFinite X
  map f := ofFiniteHomOfEquiv (FintypeCat.equivEquivIso.symm f.iso)


-- @@ L346-348 verbatim
instance (X : FintypeGrpd) [IsEmpty X] : IsEmpty (Fin (ofFiniteGrpdFunctor.{u}.obj X).length) := by
  rw [← Equiv.isEmpty_congr (ofFinite.ι _)]
  infer_instance


-- @@ L350-394 verbatim
public noncomputable instance : ofFiniteGrpdFunctor.{v, u}.Monoidal :=
  letI : ofFiniteGrpdFunctor.{v, u}.CoreMonoidal :=
    { εIso :=
        SList.liftEquivIso ((Equiv.equivEmpty _).trans (Equiv.equivEmpty _).symm)
          (fun _ ↦ rfl)
      μIso X Y :=
        SList.liftEquivIso
          (ofFinite.ι _ |>.symm.trans <|
            (FintypeGrpd.tensorObjEquiv X Y).symm.trans <|
            (Equiv.sumCongr (ofFinite.ι _) (ofFinite.ι _)).trans <|
            (Ψ (ofFinite X) (ofFinite Y)))
          (fun _ ↦ rfl)
      μIso_hom_natural_left {X Y} f Z := by
        rw [hom_eq_iff_toEquiv_eq]
        ext i : 1
        obtain ⟨i, rfl⟩ := (ofFinite.ι _).surjective i
        obtain ⟨i, rfl⟩ := (FintypeGrpd.tensorObjEquiv _ _).surjective i
        cases i with simp
      μIso_hom_natural_right X {Y Z} f := by
        rw [hom_eq_iff_toEquiv_eq]
        ext i : 1
        obtain ⟨i, rfl⟩ := (ofFinite.ι _).surjective i
        obtain ⟨i, rfl⟩ := (FintypeGrpd.tensorObjEquiv _ _).surjective i
        cases i with simp
      associativity X Y Z := by
        rw [hom_eq_iff_toEquiv_eq]
        ext i : 1
        obtain ⟨i, rfl⟩ := (ofFinite.ι _).surjective i
        obtain ⟨i, rfl⟩ := (FintypeGrpd.tensorObjEquiv _ _).surjective i
        cases i with
        | inl i => simp
        | inr i =>
          obtain ⟨i, rfl⟩ := (FintypeGrpd.tensorObjEquiv _ _).surjective i
          cases i with simp
      left_unitality X := by
        rw [hom_eq_iff_toEquiv_eq]
        ext i : 1
        obtain ⟨i, rfl⟩ := (ofFinite.ι _).surjective i
        simp
      right_unitality X := by
        rw [hom_eq_iff_toEquiv_eq]
        ext i : 1
        obtain ⟨i, rfl⟩ := (ofFinite.ι _).surjective i
        simp }
  this.toMonoidal


-- @@ L396-403 verbatim
lemma ofFiniteGrpdFunctor_μIso_hom_def (X Y : FintypeGrpd.{u}) :
    (Functor.Monoidal.μIso ofFiniteGrpdFunctor X Y).hom =
    SList.liftEquiv
      (ofFinite.ι _ |>.symm.trans <|
        (FintypeGrpd.tensorObjEquiv X Y).symm.trans <|
        (Equiv.sumCongr (ofFinite.ι _) (ofFinite.ι _)).trans <|
        (Ψ (ofFinite X) (ofFinite Y)))
      (fun _ ↦ rfl) := rfl


-- @@ L405-411 verbatim
lemma ofFiniteGrpdFunctor_μIso_inv_def (X Y : FintypeGrpd.{u}) :
    (Functor.Monoidal.μIso ofFiniteGrpdFunctor X Y).inv =
    SList.liftEquiv
      (Ψ (ofFinite X) (ofFinite Y)|>.symm.trans <|
        (Equiv.sumCongr (ofFinite.ι _).symm (ofFinite.ι _).symm).trans <|
        (FintypeGrpd.tensorObjEquiv X Y).trans <| ofFinite.ι _ )
      (fun _ ↦ rfl) := rfl


-- @@ L413-413 verbatim
section


-- @@ L415-420 verbatim
@[simp, grind =]
lemma toEquiv_ofFiniteGrpdFunctor_μ_left (X Y : FintypeGrpd.{u}) (x : X) :
    toEquiv (Functor.LaxMonoidal.μ ofFiniteGrpdFunctor.{v, u} X Y)
      (ofFinite.ι _ (FintypeGrpd.inl _ _ x)) =
    Ψ _ _ (.inl <| ofFinite.ι _ x) := by
  simp [← Functor.Monoidal.μIso_hom, ofFiniteGrpdFunctor_μIso_hom_def]


-- @@ L422-427 verbatim
@[simp, grind =]
lemma toEquiv_ofFiniteGrpdFunctor_μ_right (X Y : FintypeGrpd.{u}) (y : Y) :
    toEquiv (Functor.LaxMonoidal.μ ofFiniteGrpdFunctor.{v, u} X Y)
      (ofFinite.ι _ <| FintypeGrpd.inr _ _ y) =
    Ψ _ _ (.inr <| ofFinite.ι _ y) := by
  simp [← Functor.Monoidal.μIso_hom, ofFiniteGrpdFunctor_μIso_hom_def]


-- @@ L429-433 verbatim
@[simp, grind =]
lemma toEquiv_ofFiniteGrpdFunctor_δ_left (X Y : FintypeGrpd.{u}) (x : X) :
    toEquiv (Functor.OplaxMonoidal.δ ofFiniteGrpdFunctor.{v, u} X Y)
      (Ψ _ _ <| .inl <| ofFinite.ι _ x) = ofFinite.ι _ (FintypeGrpd.inl _ _ x) := by
  simp [← Functor.Monoidal.μIso_inv, ofFiniteGrpdFunctor_μIso_inv_def]


-- @@ L435-439 verbatim
@[simp, grind =]
lemma toEquiv_ofFiniteGrpdFunctor_δ_right (X Y : FintypeGrpd.{u}) (y : Y) :
    toEquiv (Functor.OplaxMonoidal.δ ofFiniteGrpdFunctor.{v, u} X Y)
      (Ψ _ _ <| .inr <| ofFinite.ι _ y) = ofFinite.ι _ (FintypeGrpd.inr _ _ y) := by
  simp [← Functor.Monoidal.μIso_inv, ofFiniteGrpdFunctor_μIso_inv_def]


-- @@ L441-441 verbatim
end


-- @@ L443-453 verbatim
noncomputable instance : ofFiniteGrpdFunctor.{v, u}.Braided where
  braided X Y := by
    rw [hom_eq_iff_toEquiv_eq]
    ext i : 1
    obtain ⟨i, rfl⟩ := (ofFinite.ι _).surjective i
    obtain ⟨i, rfl⟩ := (FintypeGrpd.tensorObjEquiv _ _).surjective i
    cases i with
    | inl i =>
      simp [← Functor.Monoidal.μIso_hom, ofFiniteGrpdFunctor_μIso_hom_def]
    | inr i =>
      simp [← Functor.Monoidal.μIso_hom, ofFiniteGrpdFunctor_μIso_hom_def]


-- @@ L455-466 verbatim
set_option backward.isDefEq.respectTransparency false in
noncomputable def unitEquivalence.counitIso :
    ofFiniteGrpdFunctor.{v, u} ⋙ toFintypeGrpdFunctor.{v, u} ≅ 𝟭 FintypeGrpd.{u} :=
  NatIso.ofComponents
    (fun _ ↦ FintypeGrpd.mkIso <| (toFintypeGrpdFunctor.ι.{v, u} _).symm.trans
      (ofFinite.ι.{v, u} _).symm)
    (fun {x y} f ↦ by
      ext i
      dsimp at i ⊢
      obtain ⟨i, rfl⟩ := (toFintypeGrpdFunctor.ι _).surjective i
      obtain ⟨i, rfl⟩ := (ofFinite.ι _).surjective i
      simp)


-- @@ L468-492 verbatim
set_option backward.isDefEq.respectTransparency false in
attribute [-simp] Adjunction.rightAdjointLaxMonoidal_μ in -- this declaration causes timeouts here
instance : unitEquivalence.counitIso.{v, u}.hom.IsMonoidal where
  tensor X Y := by
    ext i
    dsimp at i ⊢
    obtain ⟨i, rfl⟩ := (FintypeGrpd.tensorObjEquiv _ _).surjective i
    cases i with
    | inl i =>
      obtain ⟨i, rfl⟩ := (toFintypeGrpdFunctor.ι _).surjective i
      obtain ⟨i, rfl⟩ := (ofFinite.ι _).surjective i
      simp [← Functor.Monoidal.μIso_hom, ofFiniteGrpdFunctor_μIso_hom_def,
        toFintypeGrpdFunctor_μIso_def, unitEquivalence.counitIso]
    | inr i =>
      obtain ⟨i, rfl⟩ := (toFintypeGrpdFunctor.ι _).surjective i
      obtain ⟨i, rfl⟩ := (ofFinite.ι _).surjective i
      simp [← Functor.Monoidal.μIso_hom, ofFiniteGrpdFunctor_μIso_hom_def,
        toFintypeGrpdFunctor_μIso_def, unitEquivalence.counitIso]
  unit := by -- cat_disch works but is a bit slow
    ext i
    grind [IsEmpty.false i]

/- The composition `toFintypeGrpdFunctor ⋙ ofFiniteGrpdFunctor`  is naturally
isomorphic to the identity since both functors are symmetric monoidal.
Note that such an isomorphism, if it exists, must be unique. -/

-- @@ L493-498 verbatim
noncomputable def unitEquivalence.unitIso :
      𝟭 (SList PUnit.{v + 1}) ≅ toFintypeGrpdFunctor.{v, u} ⋙ ofFiniteGrpdFunctor.{v, u} :=
  monoidalLiftNatIso <| fun x ↦
    SList.liftEquivIso
      (Fintype.equivOfCardEq (by simp [ofFinite_length]))
      (fun _ ↦ rfl)


-- @@ L500-502 verbatim
instance : NatTrans.IsMonoidal unitEquivalence.unitIso.hom := by
  dsimp [unitEquivalence.unitIso]
  infer_instance


-- @@ L504-527 unexpanded
noncomputable abbrev unitEquivalence :  SList PUnit.{v + 1} ≌ FintypeGrpd.{u} where
  functor := toFintypeGrpdFunctor.{v, u}
  inverse := ofFiniteGrpdFunctor.{v, u}
  counitIso := unitEquivalence.counitIso.{v, u}
  unitIso := unitEquivalence.unitIso.{v, u}
  functor_unitIso_comp X := by
    /- We restate it as an equality of natural transformations, so that
    we can use the universal property -/
    suffices H : (Functor.leftUnitor _).inv ≫
        Functor.whiskerRight (unitEquivalence.unitIso.hom) toFintypeGrpdFunctor ≫
        (Functor.associator ..).hom ≫
        Functor.whiskerLeft toFintypeGrpdFunctor (unitEquivalence.counitIso.hom) ≫
        (Functor.rightUnitor _).hom = 𝟙 _ by
      simpa using congr($(H).app X)
    apply monoidalNatTrans_ext_app_singleton
    intro c
    simp only [NatTrans.comp_app, Functor.comp_obj, Functor.id_obj, Functor.leftUnitor_inv_app,
      ofFiniteGrpdFunctor_obj, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Category.comp_id, Category.id_comp,
      NatTrans.id_app]
    ext i
    haveI : Subsingleton <| toFintypeGrpdFunctor.{v, u}.obj [c]~ := by
      simp [← Finite.card_le_one_iff_subsingleton]
    subsingleton


-- @@ L529-530 verbatim
instance : toFintypeGrpdFunctor.{v,u}.IsEquivalence :=
  unitEquivalence.isEquivalence_functor


-- @@ L532-533 verbatim
instance : ofFiniteGrpdFunctor.{v,u}.IsEquivalence :=
  unitEquivalence.isEquivalence_inverse


-- @@ L535-535 verbatim
end ofFiniteGrpd


-- @@ L537-537 verbatim
end


-- @@ L539-539 verbatim
section

-- @@ L540-550 verbatim
variable (J : Type u) in
@[pp_with_univ]
def toFintypeGrpdOverFunctor : SList J ⥤ FintypeGrpdOver J where
  obj x := CostructuredArrow.mk (Y := .mk <| .of <| ULift <| Fin x.length)
    (f := fun i ↦ x.toList[(i : ULift (Fin x.length)).down])
  map {x y} f := CostructuredArrow.homMk (FintypeGrpd.mkHom <|
    ((Equiv.ulift.trans (toEquiv f).symm).trans Equiv.ulift.symm)) (by
    ext (i : ULift (Fin x.length))
    cases i with | _ i =>
    change y.toList[(toEquiv f).symm i] = _
    simpa [toEquiv_symm] using SList.getElem_toList_toEquiv (inv f) i |>.symm)


-- @@ L552-552 verbatim
variable {J : Type u}


-- @@ L554-556 verbatim
irreducible_def toFintypeGrpdOverFunctor.ι (x : SList J) :
    Fin x.length ≃ ((toFintypeGrpdOverFunctor J).obj x).left :=
  Equiv.ulift.symm


-- @@ L558-563 verbatim
@[simp, grind =]
lemma toFintypeGrpdOverFunctor.hom_ι (x : SList J) (i : Fin x.length) :
    ((toFintypeGrpdOverFunctor J).obj x).hom (toFintypeGrpdOverFunctor.ι x i) =
    x.toList[i] := by
  rw [ι_def]
  rfl


-- @@ L565-570 verbatim
@[simp]
lemma toFintypeGrpdOverFunctor_map_ι_symm {x y : SList J} (f : x ⟶ y) (i : Fin y.length) :
    ((toFintypeGrpdOverFunctor J).map f).left.iso.inv (toFintypeGrpdOverFunctor.ι y i) =
    (toFintypeGrpdOverFunctor.ι x) (toEquiv f i) := by
  simp_rw [toFintypeGrpdOverFunctor.ι_def]
  rfl


-- @@ L572-577 verbatim
@[simp]
lemma toFintypeGrpdOverFunctor_map_ι {x y : SList J} (f : x ⟶ y) (i : Fin x.length) :
    ((toFintypeGrpdOverFunctor J).map f).left.iso.hom (toFintypeGrpdOverFunctor.ι x i) =
      (toFintypeGrpdOverFunctor.ι y) ((toEquiv f).symm i) := by
  simp_rw [toFintypeGrpdOverFunctor.ι_def]
  rfl


-- @@ L579-579 verbatim
open MonoidalCategory


-- @@ L581-583 verbatim
public instance : IsEmpty ((toFintypeGrpdOverFunctor J).obj (𝟙_ (SList J))).left := by
  dsimp [toFintypeGrpdOverFunctor, tensorUnit_length]
  infer_instance


-- @@ L585-587 verbatim
public instance : IsEmpty ((toFintypeGrpdOverFunctor J).obj (𝟙_ (SList J))).left := by
  dsimp [toFintypeGrpdOverFunctor, tensorUnit_length]
  infer_instance


-- @@ L589-653 verbatim
set_option backward.isDefEq.respectTransparency false in
public instance : (toFintypeGrpdOverFunctor J).Monoidal :=
  letI : (toFintypeGrpdOverFunctor J).CoreMonoidal :=
    { εIso := CostructuredArrow.isoMk (FintypeGrpd.mkIso
        (⟨fun i ↦ IsEmpty.elim inferInstance i,
          fun i ↦ IsEmpty.elim inferInstance i,
          fun i ↦ IsEmpty.elim inferInstance i,
          fun i ↦ IsEmpty.elim inferInstance i⟩)) (by
        ext i
        exact PEmpty.elim i)
      μIso X Y :=
          CostructuredArrow.isoMk (FintypeGrpd.mkIso <|
            FintypeGrpd.tensorObjEquiv _ _ |>.symm.trans <|
            Equiv.sumCongr
              (toFintypeGrpdOverFunctor.ι X).symm
              (toFintypeGrpdOverFunctor.ι Y).symm |>.trans <|
            Ψ .. |>.trans <| toFintypeGrpdOverFunctor.ι (X ⊗ Y)) (by
        ext i
        dsimp at i
        cases i using FintypeGrpd.tensor_obj_cases with
        | left t =>
          obtain ⟨t, rfl⟩ := (toFintypeGrpdOverFunctor.ι _).surjective t
          simp
        | right t =>
          obtain ⟨t, rfl⟩ := (toFintypeGrpdOverFunctor.ι _).surjective t
          simp)
      μIso_hom_natural_left {X Y} f Z := by
        ext i
        dsimp at i
        cases i using FintypeGrpd.tensor_obj_cases with
          obtain ⟨t, rfl⟩ := (toFintypeGrpdOverFunctor.ι _).surjective t
        | left t => simp [toEquiv_symm]
        | right t => simp [toEquiv_symm]
      μIso_hom_natural_right X {Y Z} f := by
        ext i
        cases i using FintypeGrpd.tensor_obj_cases with
          obtain ⟨t, rfl⟩ := (toFintypeGrpdOverFunctor.ι _).surjective t
        | left t => simp [toEquiv_symm]
        | right t => simp [toEquiv_symm]
      associativity X Y Z := by
        ext i
        cases i using FintypeGrpd.tensor_obj_cases with
        | left i =>
          cases i using FintypeGrpd.tensor_obj_cases with
            obtain ⟨t, rfl⟩ := (toFintypeGrpdOverFunctor.ι _).surjective t
          | left t => simp [toEquiv_symm]
          | right t => simp [toEquiv_symm]
        | right i =>
          obtain ⟨i, rfl⟩ := (toFintypeGrpdOverFunctor.ι _).surjective i
          simp [toEquiv_symm]
      left_unitality X := by
        ext i
        cases i using FintypeGrpd.tensor_obj_cases with
        | left t => exact IsEmpty.elim inferInstance t
        | right t =>
          obtain ⟨i, rfl⟩ := (toFintypeGrpdOverFunctor.ι _).surjective t
          simp [toEquiv_symm]
      right_unitality X := by
        ext i
        cases i using FintypeGrpd.tensor_obj_cases with
        | left t =>
          obtain ⟨i, rfl⟩ := (toFintypeGrpdOverFunctor.ι _).surjective t
          simp [toEquiv_symm]
        | right t => exact IsEmpty.elim inferInstance t }
  this.toMonoidal


-- @@ L655-662 verbatim
lemma ofFiniteGrpdOverFunctor_μIso_hom_left_def (X Y : SList J) :
    (Functor.Monoidal.μIso (toFintypeGrpdOverFunctor J) X Y).hom.left =
    (FintypeGrpd.mkIso <|
      FintypeGrpd.tensorObjEquiv _ _ |>.symm.trans <|
      Equiv.sumCongr
        (toFintypeGrpdOverFunctor.ι X).symm
        (toFintypeGrpdOverFunctor.ι Y).symm |>.trans <|
      Ψ .. |>.trans <| toFintypeGrpdOverFunctor.ι (X ⊗ Y)).hom := rfl


-- @@ L664-671 verbatim
lemma ofFiniteGrpdOverFunctor_μIso_inv_left_def (X Y : SList J) :
    (Functor.Monoidal.μIso (toFintypeGrpdOverFunctor J) X Y).inv.left =
    (FintypeGrpd.mkIso <|
      FintypeGrpd.tensorObjEquiv _ _ |>.symm.trans <|
      Equiv.sumCongr
        (toFintypeGrpdOverFunctor.ι X).symm
        (toFintypeGrpdOverFunctor.ι Y).symm |>.trans <|
      Ψ .. |>.trans <| toFintypeGrpdOverFunctor.ι (X ⊗ Y)).inv := rfl


-- @@ L673-673 verbatim
section

-- @@ L674-676 verbatim
variable {X Y : SList J} (x : Fin X.length) (y : Fin Y.length)
    -- (l : ((toFintypeGrpdFunctor J).hom.obj X))
    -- (r : (toFintypeGrpdFunctor.{v, u}.obj Y))


-- @@ L678-685 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma toFintypeGrpdOverFunctor_μ_iso_hom_left :
    (Functor.LaxMonoidal.μ (toFintypeGrpdOverFunctor J) X Y).left.iso.hom
      (FintypeGrpd.inl _ _ (toFintypeGrpdOverFunctor.ι X x)) =
    toFintypeGrpdOverFunctor.ι _ (Ψ _ _ <| .inl <| x) := by
  rw [← Functor.Monoidal.μIso_hom, ofFiniteGrpdOverFunctor_μIso_hom_left_def]
  simp


-- @@ L687-694 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma toFintypeGrpdOverFunctor_μ_iso_hom_right :
    (Functor.LaxMonoidal.μ (toFintypeGrpdOverFunctor J) X Y).left.iso.hom
      (FintypeGrpd.inr _ _ (toFintypeGrpdOverFunctor.ι _ y)) =
    toFintypeGrpdOverFunctor.ι _ (Ψ _ _ <| .inr <| y) := by
  rw [← Functor.Monoidal.μIso_hom, ofFiniteGrpdOverFunctor_μIso_hom_left_def]
  simp


-- @@ L696-703 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma toFintypeGrpdOverFunctor_μ_iso_inv_left :
    (Functor.LaxMonoidal.μ (toFintypeGrpdOverFunctor J) X Y).left.iso.inv
      (toFintypeGrpdOverFunctor.ι _ <| Ψ _ _ <| .inl <| x) =
    (FintypeGrpd.inl _ _ (toFintypeGrpdOverFunctor.ι _ x)) := by
  rw [← Functor.Monoidal.μIso_hom, ofFiniteGrpdOverFunctor_μIso_hom_left_def]
  simp


-- @@ L705-712 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma toFintypeGrpdOverFunctor_μ_iso_inv_right :
    (Functor.LaxMonoidal.μ (toFintypeGrpdOverFunctor J) X Y).left.iso.inv
      (toFintypeGrpdOverFunctor.ι _ <| Ψ _ _ <| .inr y) =
    (FintypeGrpd.inr _ _ <| toFintypeGrpdOverFunctor.ι _ y) := by
  rw [← Functor.Monoidal.μIso_hom, ofFiniteGrpdOverFunctor_μIso_hom_left_def]
  simp


-- @@ L714-721 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma toFintypeGrpdOverFunctor_δ_iso_hom_left :
    (Functor.OplaxMonoidal.δ (toFintypeGrpdOverFunctor J) X Y).left.iso.hom
      (toFintypeGrpdOverFunctor.ι _ <| Ψ _ _ <| .inl x) =
    (FintypeGrpd.inl _ _ (toFintypeGrpdOverFunctor.ι _ x)) := by
  rw [← Functor.Monoidal.μIso_inv, ofFiniteGrpdOverFunctor_μIso_inv_left_def]
  simp


-- @@ L723-730 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma toFintypeGrpdOverFunctor_δ_iso_hom_right :
    (Functor.OplaxMonoidal.δ (toFintypeGrpdOverFunctor J) X Y).left.iso.hom
      (toFintypeGrpdOverFunctor.ι _ <| Ψ _ _ <| .inr y) =
    (FintypeGrpd.inr _ _ (toFintypeGrpdOverFunctor.ι _ y)) := by
  rw [← Functor.Monoidal.μIso_inv, ofFiniteGrpdOverFunctor_μIso_inv_left_def]
  simp


-- @@ L732-739 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma toFintypeGrpdOverFunctor_δ_iso_inv_left :
    (Functor.OplaxMonoidal.δ (toFintypeGrpdOverFunctor J) X Y).left.iso.inv
      (FintypeGrpd.inl _ _ (toFintypeGrpdOverFunctor.ι _ x)) =
    (toFintypeGrpdOverFunctor.ι _ <| Ψ _ _ <| .inl x) := by
  rw [← Functor.Monoidal.μIso_inv, ofFiniteGrpdOverFunctor_μIso_inv_left_def]
  simp


-- @@ L741-748 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma toFintypeGrpdOverFunctor_δ_iso_inv_right :
    (Functor.OplaxMonoidal.δ (toFintypeGrpdOverFunctor J) X Y).left.iso.inv
      (FintypeGrpd.inr _ _ (toFintypeGrpdOverFunctor.ι _ y)) =
    (toFintypeGrpdOverFunctor.ι _ <| Ψ _ _ <| .inr <| y) := by
  rw [← Functor.Monoidal.μIso_inv, ofFiniteGrpdOverFunctor_μIso_inv_left_def]
  simp


-- @@ L750-777 verbatim
set_option backward.isDefEq.respectTransparency false in
instance : (toFintypeGrpdOverFunctor J).Braided where
  braided x y := by
    ext i
    dsimp at i
    cases i with
    | left i =>
      obtain ⟨i, rfl⟩ := (toFintypeGrpdOverFunctor.ι _).surjective i;
      dsimp
      rw [← Functor.Monoidal.μIso_hom, ofFiniteGrpdOverFunctor_μIso_hom_left_def]
      simp only [FintypeGrpd.mkIso_hom_iso_hom_apply, Equiv.trans_apply,
        FintypeGrpd.tensorObjEquiv_symm_inl, Equiv.sumCongr_apply, Sum.map_inl,
        Equiv.symm_apply_apply, toFintypeGrpdOverFunctor_map_ι, toEquiv_symm, IsIso.Iso.inv_hom,
        ← SymmetricCategory.braiding_swap_eq_inv_braiding, toEquiv_braiding_hom_Ψ_left,
        FintypeGrpd.braiding_iso_hom_inl]
      rw [← Functor.Monoidal.μIso_hom, ofFiniteGrpdOverFunctor_μIso_hom_left_def]
      simp
    | right i =>
      obtain ⟨i, rfl⟩ := (toFintypeGrpdOverFunctor.ι _).surjective i;
      dsimp
      rw [← Functor.Monoidal.μIso_hom, ofFiniteGrpdOverFunctor_μIso_hom_left_def]
      simp only [FintypeGrpd.mkIso_hom_iso_hom_apply, Equiv.trans_apply,
        FintypeGrpd.tensorObjEquiv_symm_inr, Equiv.sumCongr_apply, Sum.map_inr,
        Equiv.symm_apply_apply, toFintypeGrpdOverFunctor_map_ι, toEquiv_symm, IsIso.Iso.inv_hom,
        ← SymmetricCategory.braiding_swap_eq_inv_braiding, toEquiv_braiding_hom_Ψ_right,
        FintypeGrpd.braiding_iso_hom_inr]
      rw [← Functor.Monoidal.μIso_hom, ofFiniteGrpdOverFunctor_μIso_hom_left_def]
      simp


-- @@ L779-779 verbatim
end


-- @@ L781-800 verbatim
set_option backward.isDefEq.respectTransparency false in
noncomputable def fullyFaithfulToFintypeGrpdOverFunctor :
    (toFintypeGrpdOverFunctor J).FullyFaithful where
  preimage {X Y} f := SList.liftEquiv
    ((toFintypeGrpdOverFunctor.ι Y).trans <|
      (FintypeCat.equivEquivIso.symm f.left.iso.symm).trans <| (toFintypeGrpdOverFunctor.ι X).symm)
    (fun i ↦ by
      have := congr($(f.w) (f.left.iso.inv (toFintypeGrpdOverFunctor.ι Y i)))
      dsimp at this ⊢
      simp only [Iso.inv_hom_id_apply, toFintypeGrpdOverFunctor.hom_ι, Fin.getElem_fin] at this
      convert this
      simp [toFintypeGrpdOverFunctor, toFintypeGrpdOverFunctor.ι_def])
  preimage_map {X Y} f := by
    rw [hom_eq_iff_toEquiv_eq]
    ext i
    simp
  map_preimage {X Y} f := by
    ext i
    obtain ⟨i, rfl⟩ := (toFintypeGrpdOverFunctor.ι _).surjective i
    simp


-- @@ L802-803 verbatim
instance : (toFintypeGrpdOverFunctor J).Full :=
  fullyFaithfulToFintypeGrpdOverFunctor.full

-- @@ L804-805 verbatim
instance : (toFintypeGrpdOverFunctor J).Faithful :=
  fullyFaithfulToFintypeGrpdOverFunctor.faithful


-- @@ L807-823 verbatim
set_option backward.isDefEq.respectTransparency false in
instance : (toFintypeGrpdOverFunctor J).EssSurj where
  mem_essImage X := by
    classical
    let e := Finite.equivFin X.left.of
    let L₀ : SList J := SList.ofList <| List.ofFn (X.hom ∘ e.symm)
    let hcard₁ : L₀.length = Nat.card X.left.of := by
      simp [L₀]
    let e₁ : Fin L₀.length ≃ X.left.of := (finCongr hcard₁).trans e.symm
    use L₀
    refine ⟨CostructuredArrow.isoMk (FintypeGrpd.mkIso <|
      (toFintypeGrpdOverFunctor.ι _).symm.trans e₁) ?_⟩
    ext i
    dsimp at i
    obtain ⟨i, rfl⟩ := (toFintypeGrpdOverFunctor.ι _).surjective i
    obtain ⟨i, rfl⟩ := e₁.symm.surjective i
    simp [e₁, L₀]


-- @@ L825-825 verbatim
end


-- @@ L827-827 verbatim
end CategoryTheory.SList
