/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import LeanPool.QuasiBorelSpaces.Prod
import LeanPool.QuasiBorelSpaces.Basic



-- @@ L12-18 verbatim
/-!
# Exponentials of Quasi-Borel Spaces

This file defines the exponential object in the category of quasi-borel spaces.

See [HeunenKSY17], Proposition 18.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
open QuasiBorelSpace


-- @@ L24-29 verbatim
/-- The type of morphisms between `QuasiBorelSpace`s. -/
structure QuasiBorelHom (A B : Type*) [QuasiBorelSpace A] [QuasiBorelSpace B] where
  /-- The underlying function. -/
  toFun : A → B
  /-- The underlying function is a morphism. -/
  property : IsHom toFun := by fun_prop


-- @@ L31-31 verbatim
namespace QuasiBorelHom


-- @@ L33-36 verbatim
variable
  {A : Type*} {_ : QuasiBorelSpace A}
  {B : Type*} {_ : QuasiBorelSpace B}
  {C : Type*} {_ : QuasiBorelSpace C}


-- @@ L38-39 verbatim
@[inherit_doc]
infixr:25 " →𝒒 " => QuasiBorelHom


-- @@ L41-45 expanded
instance [QuasiBorelSpace A] [QuasiBorelSpace B] : FunLike (QuasiBorelHom A B) A B
    where
  coe := toFun
  coe_injective f
    g := by
    cases f
    simp_all


-- @@ L47-47 verbatim
namespace Simps


-- @@ L49-50 expanded
/-- A simps projection for function coercion. -/
def coe [QuasiBorelSpace A] [QuasiBorelSpace B] (f : QuasiBorelHom A B) : A → B :=
  f


-- @@ L52-52 verbatim
end Simps


-- @@ L54-54 verbatim
initialize_simps_projections QuasiBorelHom (toFun → coe)


-- @@ L56-57 expanded
@[ext]
lemma ext {f g : QuasiBorelHom A B} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h


-- @@ L59-65 expanded
/-- Copy of a `QuasiBorelHom` with a new `toFun` equal to the old one.
Useful to fix definitional equalities.
-/
protected def copy (f : QuasiBorelHom A B) (f' : A → B) (h : f' = ⇑f) : QuasiBorelHom A B
    where
  toFun := f'
  property := h.symm ▸ f.property


-- @@ L67-68 verbatim
@[simp]
lemma coe_mk {f : A → B} (hf : IsHom f) : ⇑(mk f hf) = f := rfl


-- @@ L70-71 expanded
@[simp]
lemma eta (f : QuasiBorelHom A B) : mk f f.property = f :=
  rfl


-- @@ L73-74 expanded
@[simp]
lemma toFun_eq_coe (f : QuasiBorelHom A B) : toFun f = ⇑f :=
  rfl


-- @@ L76-77 expanded
@[simp, fun_prop]
lemma isHom_coe (f : QuasiBorelHom A B) : IsHom ⇑f :=
  f.property


-- @@ L79-89 expanded
instance : QuasiBorelSpace (QuasiBorelHom A B)
    where
  IsVar φ := IsHom (fun x : ℝ × A ↦ φ x.1 x.2)
  isVar_const f := by fun_prop
  isVar_comp hf
    hφ := by
    rw [← isHom_iff_measurable] at hf
    fun_prop
  isVar_cases' {ix} {φ} hix
    hφ := by
    rw [← isHom_iff_measurable] at hix
    apply isHom_cases (f := fun n (x : _ × _) ↦ (φ n x.1) x.2)
    · fun_prop
    · fun_prop


-- @@ L91-92 expanded
instance : MeasurableSpace (QuasiBorelHom A B) :=
  toMeasurableSpace


-- @@ L94-97 expanded
@[local simp]
lemma isHom_def (φ : ℝ → QuasiBorelHom A B) : IsHom φ ↔ IsHom (fun x : ℝ × A ↦ φ x.1 x.2) :=
  by
  rw [← isVar_iff_isHom]
  rfl


-- @@ L99-105 expanded
@[fun_prop, simp]
lemma isHom_eval : IsHom (fun p : (QuasiBorelHom A B) × A => p.1 p.2) :=
  by
  rw [QuasiBorelSpace.isHom_def]
  simp only [Prod.isHom_iff, isHom_def, and_imp]
  intro φ hφ₁ hφ₂
  apply @hφ₁ fun r ↦ (r, (φ r).2)
  simpa only [Prod.isHom_iff, isHom_id', true_and] using hφ₂


-- @@ L107-112 expanded
@[fun_prop]
lemma isHom_eval' {f : A → QuasiBorelHom B C} (hf : IsHom f) {g : A → B} (hg : IsHom g) :
    IsHom (fun x ↦ f x (g x)) := by
  exact isHom_comp' (f := fun x ↦ x.1 x.2) (g := fun x ↦ (f x, g x)) isHom_eval (by fun_prop)


-- @@ L114-121 verbatim
@[fun_prop]
lemma isHom_mk
    {f : A → B → C} (hf : IsHom (fun x : A × B ↦ f x.1 x.2))
    : IsHom (fun x ↦ mk (f x) (by fun_prop)) := by
  rw [QuasiBorelSpace.isHom_def]
  intro φ hφ
  simp only [isHom_def, coe_mk]
  fun_prop


-- @@ L123-129 expanded
@[simp]
lemma isHom_iff (f : A → QuasiBorelHom B C) : IsHom f ↔ IsHom (fun x : A × B ↦ f x.1 x.2) :=
  by
  apply Iff.intro
  · intro hf
    fun_prop
  · intro hf
    apply isHom_mk hf


-- @@ L131-134 expanded
/-- Currying for `QuasiBorelHom`s. -/
@[simps -fullyApplied]
def curry (f : QuasiBorelHom (A × B) C) : QuasiBorelHom A (QuasiBorelHom B C) where
  toFun x := { toFun y := f (x, y) }


-- @@ L136-139 expanded
/-- Uncurrying for `QuasiBorelHom`s. -/
@[simps -fullyApplied]
def uncurry (f : QuasiBorelHom A (QuasiBorelHom B C)) : QuasiBorelHom (A × B) C where
  toFun x := f x.1 x.2


-- @@ L141-142 expanded
@[simp]
lemma curry_uncurry (f : QuasiBorelHom A (QuasiBorelHom B C)) : curry (uncurry f) = f :=
  rfl


-- @@ L144-145 expanded
@[simp]
lemma uncurry_curry (f : QuasiBorelHom (A × B) C) : uncurry (curry f) = f :=
  rfl


-- @@ L147-150 expanded
/-- The identity morphism. -/
@[simps -fullyApplied]
def id : QuasiBorelHom A A where toFun x := x


-- @@ L152-154 verbatim
@[simp]
lemma eq_id : (.mk fun x : A ↦ x) = id := by
  rfl


-- @@ L156-159 expanded
/-- Morphism composition. -/
@[simps -fullyApplied]
def comp (f : QuasiBorelHom B C) (g : QuasiBorelHom A B) : QuasiBorelHom A C where
  toFun x := f (g x)


-- @@ L161-166 verbatim
@[simp]
lemma eq_comp
    {f : B → C} (hf : IsHom f)
    {g : A → B} (hg : IsHom g)
    : comp (mk f) (mk g) = mk fun x ↦ f (g x) := by
  rfl


-- @@ L168-168 verbatim
end QuasiBorelHom
