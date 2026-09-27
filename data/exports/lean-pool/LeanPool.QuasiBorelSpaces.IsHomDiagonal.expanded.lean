/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import LeanPool.QuasiBorelSpaces.Sum
import LeanPool.QuasiBorelSpaces.Basic
import LeanPool.QuasiBorelSpaces.Prop


-- @@ L12-16 verbatim
/-!
# LeanPool.QuasiBorelSpaces.IsHomDiagonal

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.IsHomDiagonal`.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
namespace QuasiBorelSpace


-- @@ L22-24 verbatim
variable
  {A : Type*} [QuasiBorelSpace A]
  {B : Type*} [QuasiBorelSpace B]


-- @@ L26-29 verbatim
/-- The class of `QuasiBorelSpace`s where equality is a morphism. -/
class IsHomDiagonal (A : Type*) [QuasiBorelSpace A] where
  /-- Equality is a morphism. -/
  isHom_eq : IsHom (fun x : A × A ↦ x.1 = x.2)


-- @@ L31-31 verbatim
export IsHomDiagonal (isHom_eq)

-- @@ L32-32 verbatim
attribute [simp, fun_prop] isHom_eq


-- @@ L34-37 verbatim
lemma isHom_eq'
    [IsHomDiagonal B] {f g : A → B} (hf : IsHom f) (hg : IsHom g)
    : IsHom fun x ↦ f x = g x := by
  fun_prop


-- @@ L39-43 verbatim
instance
    [Countable A] [MeasurableSpace A]
    [DiscreteQuasiBorelSpace A]
    : IsHomDiagonal A where
  isHom_eq := by simp only [isHom_of_discrete_countable]


-- @@ L45-48 verbatim
instance [IsHomDiagonal A] [IsHomDiagonal B] : IsHomDiagonal (A × B) where
  isHom_eq := by
    simp only [Prod.ext_iff]
    fun_prop


-- @@ L50-62 verbatim
instance [IsHomDiagonal A] [IsHomDiagonal B] : IsHomDiagonal (A ⊕ B) where
  isHom_eq := by
    have {x y : A ⊕ B}
        : x = y
        ↔ x.elim
            (fun x ↦ y.elim (x = ·) (fun _ ↦ False))
            (fun x ↦ y.elim (fun _ ↦ False) (x = ·)) := by
      cases x <;> cases y <;>
        simp only [
          reduceCtorEq, Sum.elim_inr, Sum.elim_inl,
          Sum.inl.inj_iff, Sum.inr.inj_iff]
    simp only [this]
    fun_prop


-- @@ L64-71 verbatim
instance : IsHomDiagonal ℝ where
  isHom_eq := by
    rw [isHom_def]
    intro φ hφ
    simp only [Prod.isHom_iff, isHom_ofMeasurableSpace] at ⊢ hφ
    rcases hφ with ⟨hφ₁, hφ₂⟩
    rw [←measurableSet_setOfPred]
    apply measurableSet_eq_fun <;> fun_prop


-- @@ L73-80 verbatim
instance : IsHomDiagonal ENNReal where
  isHom_eq := by
    rw [isHom_def]
    intro φ hφ
    simp only [Prod.isHom_iff, isHom_ofMeasurableSpace] at ⊢ hφ
    rcases hφ with ⟨hφ₁, hφ₂⟩
    rw [←measurableSet_setOfPred]
    apply measurableSet_eq_fun <;> fun_prop


-- @@ L82-82 verbatim
end QuasiBorelSpace
