/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import LeanPool.InfinitaryLogic.Lomega1omega.Operations

-- @@ L9-23 verbatim
/-!
# The first-order image inside `Lω₁ω`

`IsFirstOrder φ` says `φ` is `toLω` of an ordinary first-order formula — i.e. it contains no
infinitary node.

The point of the API is the **exact constructor equations**, especially

* `isFirstOrder_imp_iff` / `isFirstOrder_all_iff` — structural, both directions;
* `not_isFirstOrder_iInf` / `not_isFirstOrder_iSup` — the two negative facts.

Without these, every consumer that needs "this fragment contains no infinitary formula" re-does the
same `cases … <;> simp [toLω]` inversion. With them the HF fragment's closure fields become
one-liners.
-/


-- @@ L25-25 verbatim
@[expose] public section


-- @@ L27-27 verbatim
namespace FirstOrder.Language


-- @@ L29-29 verbatim
universe u v u'


-- @@ L31-31 verbatim
variable {L : Language.{u, v}} {α : Type u'} {n : ℕ}


-- @@ L33-35 verbatim
/-- `φ` is the `toLω`-image of a first-order formula: it has no infinitary node. -/
def BoundedFormulaω.IsFirstOrder (φ : L.BoundedFormulaω α n) : Prop :=
  ∃ φ₀ : L.BoundedFormula α n, φ₀.toLω = φ


-- @@ L37-37 verbatim
namespace BoundedFormulaω


-- @@ L39-53 verbatim
@[simp] theorem isFirstOrder_imp_iff {φ ψ : L.BoundedFormulaω α n} :
    (φ.imp ψ).IsFirstOrder ↔ φ.IsFirstOrder ∧ ψ.IsFirstOrder := by
  constructor
  · rintro ⟨φ₀, hφ₀⟩
    cases φ₀ with
    | imp a b =>
      rw [BoundedFormula.toLω] at hφ₀
      cases hφ₀
      exact ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
    | falsum => exact absurd hφ₀ (by simp [BoundedFormula.toLω])
    | equal => exact absurd hφ₀ (by simp [BoundedFormula.toLω])
    | rel => exact absurd hφ₀ (by simp [BoundedFormula.toLω])
    | all => exact absurd hφ₀ (by simp [BoundedFormula.toLω])
  · rintro ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
    exact ⟨a.imp b, rfl⟩


-- @@ L55-69 verbatim
@[simp] theorem isFirstOrder_all_iff {φ : L.BoundedFormulaω α (n + 1)} :
    φ.all.IsFirstOrder ↔ φ.IsFirstOrder := by
  constructor
  · rintro ⟨φ₀, hφ₀⟩
    cases φ₀ with
    | all a =>
      rw [BoundedFormula.toLω] at hφ₀
      cases hφ₀
      exact ⟨a, rfl⟩
    | falsum => exact absurd hφ₀ (by simp [BoundedFormula.toLω])
    | equal => exact absurd hφ₀ (by simp [BoundedFormula.toLω])
    | rel => exact absurd hφ₀ (by simp [BoundedFormula.toLω])
    | imp => exact absurd hφ₀ (by simp [BoundedFormula.toLω])
  · rintro ⟨a, rfl⟩
    exact ⟨a.all, rfl⟩


-- @@ L71-75 verbatim
/-- **No infinitary conjunction is first-order.**  This is the fact HF's closure fields need. -/
@[simp] theorem not_isFirstOrder_iInf (φs : ℕ → L.BoundedFormulaω α n) :
    ¬ (BoundedFormulaω.iInf φs).IsFirstOrder := by
  rintro ⟨φ₀, hφ₀⟩
  cases φ₀ <;> exact absurd hφ₀ (by simp [BoundedFormula.toLω])


-- @@ L77-81 verbatim
/-- **No infinitary disjunction is first-order.** -/
@[simp] theorem not_isFirstOrder_iSup (φs : ℕ → L.BoundedFormulaω α n) :
    ¬ (BoundedFormulaω.iSup φs).IsFirstOrder := by
  rintro ⟨φ₀, hφ₀⟩
  cases φ₀ <;> exact absurd hφ₀ (by simp [BoundedFormula.toLω])


-- @@ L83-83 verbatim
end BoundedFormulaω


-- @@ L85-85 verbatim
end FirstOrder.Language
