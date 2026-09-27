/-
Copyright (c) 2026 Scott Harper, Peiran Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Harper, Peiran Wu
-/
module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Finset

-- @@ L17-19 verbatim
/-!
# LeanPool.OrderPQ.MonoidHom
-/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-25 verbatim
lemma Set.nat_card_range_of_injective {α β : Type*} (f : α → β) (hf : Function.Injective f) :
    Nat.card (range f) = Nat.card α :=
  Eq.symm <| Nat.card_congr <| Equiv.ofInjective f hf


-- @@ L27-27 verbatim
namespace MonoidHom


-- @@ L29-35 verbatim
@[to_additive]
lemma nat_card_range_of_injective
    {α β : Type*} [Group α] [Group β]
    {f : α →* β} (hf : Function.Injective f) :
    Nat.card (range f) = Nat.card α := by
  convert Set.nat_card_range_of_injective f hf using 1
  exact Nat.card_congr (Set.equivOfEq (MonoidHom.coe_range f))


-- @@ L37-37 verbatim
end MonoidHom


-- @@ L39-39 verbatim
section OfGenerator


-- @@ L41-41 verbatim
variable {α β : Type*} [Group α] [Group β]


-- @@ L43-43 verbatim
section Lemmas


-- @@ L45-48 verbatim
@[to_additive]
theorem zpow_eq_self_iff_modEq {x : α} {n : ℤ} : x ^ n = x ↔ n ≡ 1 [ZMOD orderOf x] := by
  convert zpow_eq_zpow_iff_modEq .. using 2
  exact zpow_one x |>.symm


-- @@ L50-51 verbatim
lemma Int.modEq_of_modEq_dvd {n m a b : ℤ} (h : m ∣ n) : a ≡ b [ZMOD n] → a ≡ b [ZMOD m] :=
  Int.modEq_iff_dvd.mpr ∘ Int.dvd_trans h ∘ Int.modEq_iff_dvd.mp


-- @@ L53-55 verbatim
@[to_additive]
lemma Subgroup.nat_card_top : Nat.card (⊤ : Subgroup α) = Nat.card α :=
  Nat.card_congr (Equiv.Set.univ α)


-- @@ L57-57 verbatim
end Lemmas


-- @@ L59-59 verbatim
variable {x : α} (hx : ∀ a : α, a ∈ Subgroup.zpowers x)

-- @@ L60-60 verbatim
include hx


-- @@ L62-65 verbatim
@[to_additive]
lemma MonoidHom.eq_of_apply_eq (f₁ f₂ : α →* β) (h2 : f₁ x = f₂ x) : f₁ = f₂ := by
  ext y
  rw [← (hx y).choose_spec, map_zpow, map_zpow, h2]


-- @@ L67-69 verbatim
@[to_additive]
lemma MulEquiv.eq_of_apply_eq (f₁ f₂ : α ≃* β) (h2 : f₁ x = f₂ x) : f₁ = f₂ :=
  MulEquiv.toMonoidHom_injective <| MonoidHom.eq_of_apply_eq hx _ _ h2


-- @@ L71-73 verbatim
@[to_additive]
private lemma orderOf_eq_nat_card : orderOf x = Nat.card α :=
  Nat.card_zpowers x ▸ (Subgroup.eq_top_iff' _).mpr hx ▸ Subgroup.nat_card_top


-- @@ L75-75 verbatim
variable {y : β} (hy : orderOf y ∣ Nat.card α)

-- @@ L76-76 verbatim
include hy


-- @@ L78-89 verbatim
@[to_additive]
private noncomputable def MonoidHom.ofGeneratorAndImage : α →* β where
  toFun a := y ^ (hx a).choose
  map_one' := by
    have hx' := (hx 1).choose_spec
    simp only [← orderOf_dvd_iff_zpow_eq_one, orderOf_eq_nat_card hx] at hx' ⊢
    exact Int.dvd_trans (Int.ofNat_dvd.mpr hy) hx'
  map_mul' a1 a2 := by
    have h := (hx (a1 * a2)).choose_spec
    nth_rewrite 3 [← (hx a1).choose_spec, ← (hx a2).choose_spec] at h
    rw [← zpow_add, zpow_eq_zpow_iff_modEq] at h ⊢
    exact Int.modEq_of_modEq_dvd (Int.ofNat_dvd.mpr hy) (orderOf_eq_nat_card hx ▸ h)


-- @@ L91-97 verbatim
@[to_additive]
lemma MonoidHom.exists_of_generator_and_image : ∃ f : α →* β, f x = y := by
  use MonoidHom.ofGeneratorAndImage hx hy
  change y ^ (hx x).choose = y
  have h := (hx x).choose_spec
  rw [zpow_eq_self_iff_modEq] at h ⊢
  exact Int.modEq_of_modEq_dvd (Int.ofNat_dvd.mpr hy) (orderOf_eq_nat_card hx ▸ h)


-- @@ L99-99 verbatim
end OfGenerator
