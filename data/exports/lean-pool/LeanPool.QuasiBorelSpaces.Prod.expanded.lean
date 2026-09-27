/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import LeanPool.QuasiBorelSpaces.OmegaQuasiBorelSpace
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
import LeanPool.QuasiBorelSpaces.Basic
import Mathlib.MeasureTheory.Measure.Prod



-- @@ L15-22 verbatim
/-!
# Binary Products of Quasi-Borel Spaces

This file defines binary products of quasi-borel spaces by giving a
`QuasiBorelSpace` instance for the `· × ·` type.

See [HeunenKSY17], Proposition 16.
-/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
namespace QuasiBorelSpace.Prod


-- @@ L28-32 verbatim
variable
  {A : Type*} {_ : QuasiBorelSpace A}
  {B : Type*} {_ : QuasiBorelSpace B}
  {C : Type*} {_ : QuasiBorelSpace C}
  {D : Type*} {_ : QuasiBorelSpace D}


-- @@ L34-45 verbatim
instance [QuasiBorelSpace A] [QuasiBorelSpace B] : QuasiBorelSpace (A × B) where
  IsVar φ := IsHom (fun x ↦ Prod.fst (φ x)) ∧ IsHom (fun x ↦ Prod.snd (φ x))
  isVar_const x := by
    simp only [isHom_const', and_self]
  isVar_comp hf := by
    rintro ⟨hφ₁, hφ₂⟩
    refine ⟨isHom_comp' hφ₁ ?_, isHom_comp' hφ₂ ?_⟩ <;>
      simp only [isHom_ofMeasurableSpace, hf]
  isVar_cases' {ix} {φ} hix hφ := by
    refine ⟨isHom_cases (ix := ix) (f := fun n r ↦ (φ n r).1) ?_ (fun n ↦ (hφ n).1),
      isHom_cases (ix := ix) (f := fun n r ↦ (φ n r).2) ?_ (fun n ↦ (hφ n).2)⟩ <;>
      simp only [isHom_ofMeasurableSpace, hix]


-- @@ L47-51 verbatim
@[local simp]
private lemma isHom_def (f : ℝ → A × B)
    : IsHom f ↔ IsHom (fun x ↦ (f x).1) ∧ IsHom (fun x ↦ (f x).2) := by
  rw [← isVar_iff_isHom]
  rfl


-- @@ L53-56 verbatim
@[simp]
lemma isHom_fst : IsHom (Prod.fst : A × B → A) := by
  rw [QuasiBorelSpace.isHom_def]
  simp_all only [isHom_def, implies_true]


-- @@ L58-60 verbatim
@[fun_prop]
lemma isHom_fst' {f : A → B × C} (hf : IsHom f) : IsHom (fun x ↦ (f x).1) :=
  isHom_comp isHom_fst hf


-- @@ L62-65 verbatim
@[simp]
lemma isHom_snd : IsHom (Prod.snd : A × B → B) := by
  rw [QuasiBorelSpace.isHom_def]
  simp_all only [isHom_def, implies_true]


-- @@ L67-69 verbatim
@[fun_prop]
lemma isHom_snd' {f : A → B × C} (hf : IsHom f) : IsHom (fun x ↦ (f x).2) :=
  isHom_comp isHom_snd hf


-- @@ L71-77 verbatim
@[fun_prop]
lemma isHom_mk
    {f : A → B} (hf : IsHom f)
    {g : A → C} (hg : IsHom g)
    : IsHom (fun x ↦ (f x, g x)) := by
  rw [QuasiBorelSpace.isHom_def] at ⊢ hf hg
  simp_all


-- @@ L79-85 verbatim
@[simp]
lemma isHom_iff (f : A → B × C) : IsHom f ↔ IsHom (fun x ↦ (f x).1) ∧ IsHom (fun x ↦ (f x).2) := by
  apply Iff.intro
  · intro hf
    exact ⟨isHom_fst' hf, isHom_snd' hf⟩
  · rintro ⟨h₁, h₂⟩
    exact isHom_mk h₁ h₂


-- @@ L87-97 verbatim
instance
    [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableQuasiBorelSpace A] [MeasurableQuasiBorelSpace B]
    : MeasurableQuasiBorelSpace (A × B) where
  isHom_iff_measurable φ := by
    simp only [isHom_iff, isHom_iff_measurable]
    apply Iff.intro
    · rintro ⟨h₁, h₂⟩
      exact Measurable.prodMk h₁ h₂
    · intro h
      exact ⟨by fun_prop, by fun_prop⟩


-- @@ L99-102 verbatim
@[fun_prop]
lemma isHom_map {f : A → B} {g : C → D} (hf : IsHom f) (hg : IsHom g) : IsHom (Prod.map f g) := by
  simp only [isHom_iff, Prod.map_fst, Prod.map_snd]
  apply And.intro <;> fun_prop


-- @@ L104-109 verbatim
lemma isHom_of_uncurry
    {f : A → B → C} (hf : IsHom (Function.uncurry f))
    {g : D → A} (hg : IsHom g)
    {h : D → B} (hh : IsHom h)
    : IsHom fun x ↦ f (g x) (h x) := by
  exact isHom_comp' (f := Function.uncurry f) (g := fun x ↦ (g x, h x)) hf (by fun_prop)


-- @@ L111-111 verbatim
end QuasiBorelSpace.Prod


-- @@ L113-113 verbatim
namespace OmegaQuasiBorelSpace.Prod


-- @@ L115-115 verbatim
open QuasiBorelSpace

-- @@ L116-116 verbatim
open OmegaCompletePartialOrder


-- @@ L118-118 verbatim
variable {A B : Type*} [OmegaQuasiBorelSpace A] [OmegaQuasiBorelSpace B]


-- @@ L120-128 verbatim
instance : OmegaQuasiBorelSpace (A × B) where
  isHom_ωSup := by
    rw [Prod.isHom_iff]
    constructor <;>
    · apply isHom_ωSup'
      simp only [
        Chain.isHom_iff, Chain.coe_map, Function.comp_apply,
        OrderHom.fst_coe, OrderHom.snd_coe]
      fun_prop


-- @@ L130-130 verbatim
end OmegaQuasiBorelSpace.Prod


-- @@ L132-132 verbatim
namespace QuasiBorelSpace


-- @@ L134-134 verbatim
variable {A B : Type*} [QuasiBorelSpace A] [QuasiBorelSpace B]


-- @@ L136-136 verbatim
namespace Measure


-- @@ L138-149 verbatim
@[fun_prop]
lemma isHom_lintegral
    [MeasurableSpace B] [StandardBorelSpace B] [MeasurableQuasiBorelSpace B]
    {f : A → B → ENNReal} (hf : IsHom fun x : _ × _ ↦ f x.1 x.2)
    (μ : MeasureTheory.Measure B) [MeasureTheory.SFinite μ]
    : IsHom fun x ↦ ∫⁻ y, f x y ∂μ := by
  rw [isHom_def]
  intro φ hφ
  apply isHom_of_measurable
  apply Measurable.lintegral_prod_left
  apply measurable_of_isHom
  fun_prop


-- @@ L151-151 verbatim
end Measure


-- @@ L153-153 verbatim
end QuasiBorelSpace
