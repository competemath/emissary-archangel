/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import LeanPool.QuasiBorelSpaces.OmegaQuasiBorelSpace
import LeanPool.QuasiBorelSpaces.Basic


-- @@ L11-15 verbatim
/-!
# LeanPool.QuasiBorelSpaces.Subtype

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.Subtype`.
-/


-- @@ L17-17 verbatim
@[expose] public section



-- @@ L20-20 verbatim
namespace QuasiBorelSpace.Subtype


-- @@ L22-25 verbatim
variable
  {A : Type*} {_ : QuasiBorelSpace A}
  {B : Type*} {_ : QuasiBorelSpace B}
  {P : A → Prop}


-- @@ L27-27 verbatim
instance [QuasiBorelSpace A] : QuasiBorelSpace (Subtype P) := lift Subtype.val


-- @@ L29-31 verbatim
@[simp]
lemma isHom_def {P : B → Prop} (f : A → Subtype P) : IsHom f ↔ IsHom fun x ↦ (f x).val := by
  rw [isHom_to_lift]


-- @@ L33-43 verbatim
instance
    [MeasurableSpace A] [MeasurableQuasiBorelSpace A]
    : MeasurableQuasiBorelSpace (Subtype P) where
  isHom_iff_measurable φ := by
    apply Iff.intro
    · intro h
      simp only [isHom_to_lift, isHom_iff_measurable] at h
      exact h.subtype_mk
    · intro h
      simp only [isHom_def, isHom_iff_measurable]
      apply h.subtype_val


-- @@ L45-49 verbatim
@[fun_prop]
lemma isHom_mk {P : B → Prop}
    {f : A → B} (hf₁ : IsHom f) (hf₂ : (x : A) → P (f x))
    : IsHom (fun x ↦ Subtype.mk (f x) (hf₂ x)) := by
  simp_all


-- @@ L51-53 verbatim
@[fun_prop]
lemma isHom_val {P : B → Prop} {f : A → Subtype P} (hf : IsHom f) : IsHom (fun x ↦ (f x).val) := by
  rwa [← isHom_def]


-- @@ L55-55 verbatim
end QuasiBorelSpace.Subtype


-- @@ L57-57 verbatim
namespace OmegaQuasiBorelSpace.Subtype


-- @@ L59-59 verbatim
open QuasiBorelSpace

-- @@ L60-60 verbatim
open OmegaCompletePartialOrder


-- @@ L62-65 verbatim
variable
  {I : Type*} {P : I → Prop} [OmegaQuasiBorelSpace I]
  (hP : ∀ (c : OmegaCompletePartialOrder.Chain I),
    (∀ i ∈ c, P i) → P (OmegaCompletePartialOrder.ωSup c))


-- @@ L67-75 verbatim
/-- Constructs an `OmegaQuasiBorelSpace` instance for a `Subtype`. -/
@[reducible] def subtype : OmegaQuasiBorelSpace (Subtype P) where
  toOmegaCompletePartialOrder := OmegaCompletePartialOrder.subtype P hP
  isHom_ωSup := by
    simp only [ωSup, Subtype.isHom_def]
    apply isHom_comp
    · fun_prop
    · simp only [Chain.isHom_iff, Chain.coe_map, OrderHom.Subtype.val_coe, Function.comp_apply]
      fun_prop


-- @@ L77-77 verbatim
end OmegaQuasiBorelSpace.Subtype
