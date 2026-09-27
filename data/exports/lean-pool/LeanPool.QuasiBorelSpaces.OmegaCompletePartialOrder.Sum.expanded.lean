/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import LeanPool.QuasiBorelSpaces.OmegaCompletePartialOrder.Chain.Sum
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Inv
import Mathlib.Tactic.Measurability.Init
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded



-- @@ L16-20 verbatim
/-!
# ωCPO instance for coproducts

This file provides the `OmegaCompletePartialOrder` instance for `Sum α β`.
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
namespace OmegaCompletePartialOrder.Sum


-- @@ L26-26 verbatim
variable {α β : Type*} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]


-- @@ L28-52 verbatim
@[simps! -isSimp]
noncomputable instance instSumLeanPool : OmegaCompletePartialOrder (Sum α β) where
  ωSup c := Sum.map ωSup ωSup (Chain.Sum.distrib c)
  le_ωSup c i := by
    cases c using Chain.Sum.distrib_cases with
    | inl c =>
      simp only [Chain.Sum.inl_coe, Chain.Sum.distrib_inl, Sum.map_inl, ge_iff_le,
        Sum.inl_le_inl_iff]
      apply le_ωSup
    | inr c =>
      simp only [Chain.Sum.inr_coe, Chain.Sum.distrib_inr, Sum.map_inr, ge_iff_le,
        Sum.inr_le_inr_iff]
      apply le_ωSup
  ωSup_le c x hx := by
    cases c using Chain.Sum.distrib_cases with
    | inl c =>
      cases x with
      | inl x =>
        simp_all
      | inr x => simp only [Chain.Sum.inl_coe, ge_iff_le, Sum.not_inl_le_inr, forall_const] at hx
    | inr c =>
      cases x with
      | inl x => simp only [Chain.Sum.inr_coe, ge_iff_le, Sum.not_inr_le_inl, forall_const] at hx
      | inr x =>
        simp_all


-- @@ L54-56 verbatim
@[simp]
lemma ωSup_inl (c : Chain α) : ωSup (Chain.Sum.inl c : Chain (α ⊕ β)) = .inl (ωSup c) := by
  simp only [ωSup, Chain.Sum.distrib_inl, Sum.map_inl]


-- @@ L58-60 verbatim
@[simp]
lemma ωSup_inr (c : Chain β) : ωSup (Chain.Sum.inr c : Chain (α ⊕ β)) = .inr (ωSup c) := by
  simp only [ωSup, Chain.Sum.distrib_inr, Sum.map_inr]


-- @@ L62-62 verbatim
end OmegaCompletePartialOrder.Sum
