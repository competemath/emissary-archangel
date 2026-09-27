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
# LeanPool.QuasiBorelSpaces.ENNReal

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.ENNReal`.
-/


-- @@ L17-17 verbatim
@[expose] public section



-- @@ L20-20 verbatim
namespace QuasiBorelSpace.ENNReal


-- @@ L22-24 verbatim
variable
  {A : Type*} {_ : QuasiBorelSpace A}
  {B : Type*} [Countable B]


-- @@ L26-36 verbatim
@[fun_prop]
lemma isHom_add
    {f : A → ENNReal} (hf : IsHom f)
    {g : A → ENNReal} (hg : IsHom g)
    : IsHom (fun x ↦ f x + g x) := by
  rw [isHom_def] at ⊢ hf hg
  intro φ hφ
  specialize hg hφ
  specialize hf hφ
  simp only [isHom_ofMeasurableSpace] at ⊢ hg hf
  exact Measurable.add hf hg


-- @@ L38-48 verbatim
@[fun_prop]
lemma isHom_mul
    {f : A → ENNReal} (hf : IsHom f)
    {g : A → ENNReal} (hg : IsHom g)
    : IsHom (fun x ↦ f x * g x) := by
  rw [isHom_def] at ⊢ hf hg
  intro φ hφ
  specialize hg hφ
  specialize hf hφ
  simp only [isHom_ofMeasurableSpace] at ⊢ hg hf
  exact Measurable.mul hf hg


-- @@ L50-57 verbatim
@[fun_prop]
lemma isHom_iSup {f : A → B → ENNReal} (hf : ∀ b, IsHom (f · b)) : IsHom fun x ↦ ⨆i, f x i := by
  rw [isHom_def]
  intro φ hφ
  apply isHom_of_measurable
  apply Measurable.iSup fun b ↦ ?_
  apply measurable_of_isHom
  fun_prop


-- @@ L59-59 verbatim
end QuasiBorelSpace.ENNReal


-- @@ L61-61 verbatim
namespace OmegaQuasiBorelSpace.ENNReal


-- @@ L63-63 verbatim
open QuasiBorelSpace


-- @@ L65-69 verbatim
/-- ωQBS structure on `ENNReal` -/
noncomputable instance : OmegaQuasiBorelSpace ENNReal where
  isHom_ωSup := by
    change IsHom fun c : OmegaCompletePartialOrder.Chain ENNReal ↦ ⨆ n, c n
    fun_prop


-- @@ L71-71 verbatim
end OmegaQuasiBorelSpace.ENNReal
