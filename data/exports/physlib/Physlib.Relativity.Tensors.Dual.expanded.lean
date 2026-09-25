/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.MetricTensor
public import Physlib.Relativity.Tensors.Contraction.UnitTensorContraction

-- @@ L10-53 verbatim
/-!

# Dual tensors

## i. Overview

The metric tensor identifies a tensor with the one obtained by dualising the color of a single
index: contracting slot `i` of `t` against `metricTensor (S.τ (c i))` returns a tensor of color
`Function.update c i (S.τ (c i))`, leaving every other slot alone. This is the raising and lowering
of a named index, `T^{μν} ↦ T_{μ}{}^{ν}`. `toDualMapAtIndex i` is that contraction, `crossToSlot`
against the metric, at every rank and every named slot.

A metric contracted against the metric at the dual color collapses to the unit tensor, in both
orders. So the contraction back against `metricTensor (c i)`, `fromDualMapAtIndex i`, inverts it,
and the two assemble into the linear equivalence `toDualAtIndex i`: the two color assignments
carry the same information. Dualising the same index twice returns the original tensor, up to the
reindexing of the colors.

## ii. Key results

- `TensorSpecies.Tensor.toDualMapAtIndex` : dualise the color of the index `i` by contracting with
    the metric tensor.
- `TensorSpecies.Tensor.fromDualMapAtIndex` : the returning contraction, against the metric tensor
    at `c i`.
- `TensorSpecies.Tensor.toDualMapAtIndex_toDualMapAtIndex` : dualising the index `i` twice returns
    the original tensor.
- `TensorSpecies.Tensor.toDualMapAtIndex_equivariant` : dualising an index commutes with the
    `G`-action.
- `TensorSpecies.Tensor.toDualAtIndex` : raising and lowering the index `i` as a linear
    equivalence.

## iii. Table of contents

- A. Dualising a named index
- B. Contracting a metric against its dual
- C. Dualising twice
- D. The returning contraction
- E. Equivariance
- F. Raising and lowering as an equivalence

## iv. References

* None.
-/


-- @@ L55-55 verbatim
@[expose] public section


-- @@ L57-57 verbatim
namespace TensorSpecies


-- @@ L59-63 verbatim
variable {k : Type} [RCLike k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Module.Basis (basisIdx c) k (V c)}
    {S : TensorSpecies k C G V basisIdx rep b}


-- @@ L65-65 verbatim
namespace Tensor


-- @@ L67-71 verbatim
/-!

## A. Dualising a named index

-/


-- @@ L73-78 verbatim
/-- The linear map between `S.Tensor c` and `S.Tensor (Function.update c i (S.τ (c i)))`
  formed by contracting the index `i` with the metric tensor. -/
noncomputable def toDualMapAtIndex : {n : ℕ} → {c : Fin n → C} → (i : Fin n) →
    S.Tensor c →ₗ[k] S.Tensor (Function.update c i (S.τ (c i)))
  | 0, _, i => i.elim0
  | _ + 1, c, i => crossToSlot i (0 : Fin 2) rfl (metricTensor (S := S) (S.τ (c i)))


-- @@ L80-84 verbatim
/-!

## B. Contracting a metric against its dual

-/


-- @@ L86-94 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The metric tensor at `S.τ c` contracted with the metric tensor at `c` is the unit tensor
  at `c`. -/
lemma crossToEnd_dual_metricTensor_metricTensor {c : C} :
    crossToEnd (Fin.last 1) (0 : Fin 2) (S.τ_τ_apply c) (metricTensor (S := S) (S.τ c))
        (metricTensor (S := S) c) =
      permT (id : Fin 2 → Fin 2) (IsReindexing.unitTensor_pair rfl) (unitTensor (S := S) c) := by
  rw [crossToEnd_two, contrT_dual_metricTensor_metricTensor, permT_permT]
  exact permT_congr rfl rfl


-- @@ L96-105 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The metric tensor at `c` contracted with the metric tensor at `S.τ c` is the unit tensor
  at `S.τ c`. -/
lemma crossToEnd_metricTensor_metricTensor_eq_dual_unit {c : C} :
    crossToEnd (Fin.last 1) (0 : Fin 2) rfl (metricTensor (S := S) c)
        (metricTensor (S := S) (S.τ c)) =
      permT (id : Fin 2 → Fin 2) (IsReindexing.unitTensor_pair (S.τ_τ_apply c))
        (unitTensor (S := S) (S.τ c)) := by
  rw [crossToEnd_two, contrT_metricTensor_metricTensor_eq_dual_unit, permT_permT]
  exact permT_congr (by decide) rfl


-- @@ L107-111 verbatim
/-!

## C. Dualising twice

-/


-- @@ L113-133 verbatim
/-- Dualising the index `i` twice returns the original tensor, up to the reindexing of the
  colors. -/
lemma toDualMapAtIndex_toDualMapAtIndex {n : ℕ} {c : Fin n → C}
    (i : Fin n) (t : S.Tensor c) :
    toDualMapAtIndex (S := S) i (toDualMapAtIndex (S := S) i t) =
      permT (id : Fin n → Fin n)
        (IsReindexing.update_update_of_eq i (by simp [τ_τ_apply])) t := by
  cases n with
  | zero => exact i.elim0
  | succ nA =>
    -- Both metrics enter at literal colors, matched by `S.τ_τ_apply`, so neither is transported.
    have key := crossToSlot_raise_lower_round_trip (S := S) i (he := rfl) (ha := rfl)
      (hb := S.τ_τ_apply (c i)) (M := metricTensor (S := S) (S.τ (c i)))
      (M' := metricTensor (S := S) (c i))
      (hM := crossToEnd_dual_metricTensor_metricTensor) (t := t)
    -- The second dualisation reads its metric at the composite color the first one left behind.
    rw [toDualMapAtIndex, toDualMapAtIndex,
      metricTensor_congr (by simp [Function.update_self, τ_τ_apply] :
        S.τ (Function.update c i (S.τ (c i)) i) = c i)]
    erw [crossToSlot_permT_right_id, key, permT_permT]
    exact permT_congr (by funext j; simp) rfl


-- @@ L135-139 verbatim
/-!

## D. The returning contraction

-/


-- @@ L141-147 verbatim
/-- The linear map between `S.Tensor (Function.update c i (S.τ (c i)))` and `S.Tensor c`
  formed by contracting the index `i` with the metric tensor. It is the inverse of
  `toDualMapAtIndex`. -/
noncomputable def fromDualMapAtIndex : {n : ℕ} → {c : Fin n → C} → (i : Fin n) →
    S.Tensor (Function.update c i (S.τ (c i))) →ₗ[k] S.Tensor c
  | 0, _, i => i.elim0
  | _ + 1, c, i => crossToSlotInv i rfl (S.τ_τ_apply (c i)) (metricTensor (S := S) (c i))


-- @@ L149-156 verbatim
@[simp]
lemma fromDualMapAtIndex_toDualMapAtIndex {n : ℕ} {c : Fin n → C} (i : Fin n) (t : S.Tensor c) :
    fromDualMapAtIndex (S := S) i (toDualMapAtIndex (S := S) i t) = t := by
  cases n with
  | zero => exact i.elim0
  | succ nA =>
    exact crossToSlotInv_crossToSlot i rfl rfl (S.τ_τ_apply (c i)) _ _
      crossToEnd_dual_metricTensor_metricTensor t


-- @@ L158-166 verbatim
@[simp]
lemma toDualMapAtIndex_fromDualMapAtIndex {n : ℕ} {c : Fin n → C} (i : Fin n)
    (t : S.Tensor (Function.update c i (S.τ (c i)))) :
    toDualMapAtIndex (S := S) i (fromDualMapAtIndex (S := S) i t) = t := by
  cases n with
  | zero => exact i.elim0
  | succ nA =>
    exact crossToSlot_crossToSlotInv i rfl rfl (S.τ_τ_apply (c i)) _ _
      crossToEnd_dual_metricTensor_metricTensor crossToEnd_metricTensor_metricTensor_eq_dual_unit t


-- @@ L168-172 verbatim
/-!

## E. Equivariance

-/


-- @@ L174-183 verbatim
/-- Dualising the index `i` commutes with the action of `G`. -/
@[simp]
lemma toDualMapAtIndex_equivariant {n : ℕ} {c : Fin n → C} (i : Fin n) (g : G) (t : S.Tensor c) :
    toDualMapAtIndex (S := S) i (g • t) = g • toDualMapAtIndex (S := S) i t := by
  cases n with
  | zero => exact i.elim0
  | succ nA =>
    rw [toDualMapAtIndex]
    conv_lhs => rw [← metricTensor_invariant (S := S) g]
    exact crossToSlot_equivariant i (0 : Fin 2) _ g _ t


-- @@ L185-189 verbatim
/-!

## F. Raising and lowering as an equivalence

-/


-- @@ L191-199 verbatim
/-- The linear equivalence between `S.Tensor c` and `S.Tensor (Function.update c i (S.τ (c i)))`
  formed by contracting the index `i` with the metric tensor. -/
noncomputable def toDualAtIndex : {n : ℕ} → {c : Fin n → C} → (i : Fin n) →
    S.Tensor c ≃ₗ[k] S.Tensor (Function.update c i (S.τ (c i)))
  | 0, _, i => i.elim0
  | _ + 1, c, i =>
    crossToSlotEquiv i rfl rfl (S.τ_τ_apply (c i)) (metricTensor (S := S) (S.τ (c i)))
      (metricTensor (S := S) (c i)) crossToEnd_dual_metricTensor_metricTensor
      crossToEnd_metricTensor_metricTensor_eq_dual_unit


-- @@ L201-206 verbatim
@[simp]
lemma toDualAtIndex_apply {n : ℕ} {c : Fin n → C} (i : Fin n) (t : S.Tensor c) :
    toDualAtIndex (S := S) i t = toDualMapAtIndex (S := S) i t := by
  cases n with
  | zero => exact i.elim0
  | succ nA => rfl


-- @@ L208-214 verbatim
@[simp]
lemma toDualAtIndex_symm_apply {n : ℕ} {c : Fin n → C} (i : Fin n)
    (t : S.Tensor (Function.update c i (S.τ (c i)))) :
    (toDualAtIndex (S := S) i).symm t = fromDualMapAtIndex (S := S) i t := by
  cases n with
  | zero => exact i.elim0
  | succ nA => rfl


-- @@ L216-216 verbatim
end Tensor


-- @@ L218-218 verbatim
open Tensor


-- @@ L220-220 verbatim
end TensorSpecies
