/-
Copyright (c) 2022 Yaël Dillies, Ella Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Ella Yu
-/

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Combinatorics.Additive.Convolution

public import Mathlib.Data.Finset.Density
public meta import Mathlib.Tactic.Basic
public meta import Mathlib.Tactic.ToAdditive
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity.Finset


-- @@ L19-43 verbatim
/-!
# Additive energy

This file defines the additive energy of two finsets of a group. This is a central quantity in
additive combinatorics.

## Main declarations

* `Finset.addEnergy'`: The additive energy of two finsets in an additive group.
* `Finset.mulEnergy'`: The multiplicative energy of two finsets in a group.

## Notation

The following notations are defined in the `Combinatorics.Additive` scope:
* `E[s, t]` for `Finset.addEnergy' s t`.
* `Eₘ[s, t]` for `Finset.mulEnergy' s t`.
* `E[s]` for `E[s, s]`.
* `Eₘ[s]` for `Eₘ[s, s]`.

## TODO

It's possibly interesting to have
`(s ×ˢ s) ×ˢ t ×ˢ t).filter (fun x : (G × G) × G × G ↦ x.1.1 * x.2.1 = x.1.2 * x.2.2)`
(whose density in `G × G × G` is `mulEnergy' s t`) as a standalone definition.
-/


-- @@ L45-45 verbatim
public section


-- @@ L47-47 verbatim
open scoped BigOperators Pointwise



-- @@ L50-50 verbatim
variable {G : Type*} [Fintype G] [DecidableEq G]


-- @@ L52-52 verbatim
namespace Finset

-- @@ L53-53 verbatim
section Group

-- @@ L54-54 verbatim
variable [Group G] {s s₁ s₂ t t₁ t₂ : Finset G}


-- @@ L56-67 verbatim
/-- The multiplicative energy `Eₘ[s, t]` of two finsets `s` and `t` in a group is the number of
quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ * b₁ = a₂ * b₂`.

The notation `Eₘ[s, t]` is available in scope `Combinatorics.Additive`. -/
@[expose, to_additive
/-- The additive energy `E[s, t]` of two finsets `s` and `t` in a group is the number of quadruples
`(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ + b₁ = a₂ + b₂`.

The notation `E[s, t]` is available in scope `Combinatorics.Additive`. -/]
public
def mulEnergy' (s t : Finset G) : ℚ≥0 :=
  #{x ∈ ((s ×ˢ s) ×ˢ t ×ˢ t) | x.1.1 * x.2.1 = x.1.2 * x.2.2} / Fintype.card G ^ 3


-- @@ L69-71 verbatim
/-- The multiplicative energy of two finsets `s` and `t` in a group is the number of quadruples
`(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ * b₁ = a₂ * b₂`. -/
scoped[Combinatorics.Additive'] notation3:max "Eₘ[" s ", " t "]" => Finset.mulEnergy' s t


-- @@ L73-75 verbatim
/-- The additive energy of two finsets `s` and `t` in a group is the number of quadruples
`(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ + b₁ = a₂ + b₂`. -/
scoped[Combinatorics.Additive'] notation3:max "E[" s ", " t "]" => Finset.addEnergy' s t


-- @@ L77-79 verbatim
/-- The multiplicative energy of a finset `s` in a group is the number of quadruples
`(a₁, a₂, b₁, b₂) ∈ s × s × s × s` such that `a₁ * b₁ = a₂ * b₂`. -/
scoped[Combinatorics.Additive'] notation3:max "Eₘ[" s "]" => Finset.mulEnergy' s s


-- @@ L81-83 verbatim
/-- The additive energy of a finset `s` in a group is the number of quadruples
`(a₁, a₂, b₁, b₂) ∈ s × s × s × s` such that `a₁ + b₁ = a₂ + b₂`. -/
scoped[Combinatorics.Additive'] notation3:max "E[" s "]" => Finset.addEnergy' s s


-- @@ L85-85 verbatim
open scoped Combinatorics.Additive'
















-- @@ L101-101 verbatim
variable (s t)


-- @@ L103-105 verbatim
@[to_additive (attr := simp)]
public
lemma mulEnergy'_empty_left : Eₘ[∅, t] = 0 := by simp [mulEnergy']

-- @@ L106-108 verbatim
@[to_additive (attr := simp)]
public
lemma mulEnergy'_empty_right : Eₘ[s, ∅] = 0 := by simp [mulEnergy']


-- @@ L110-110 verbatim
variable {s t}










-- @@ L120-129 verbatim
public
lemma addEnergy'_eq_card_filter {G : Type*} [Fintype G] [DecidableEq G] [AddGroup G]
    (s t : Finset G) :
    E[s, t] =
      #{x ∈ ((s ×ˢ t) ×ˢ s ×ˢ t) | x.1.1 + x.1.2 = x.2.1 + x.2.2} / Fintype.card G ^ 3 := by
  unfold addEnergy'
  congr 2
  exact card_equiv (.prodProdProdComm _ _ _ _) (by simp [and_and_and_comm])

-- TODO: Why does `to_additive` fail here?



-- @@ L132-154 verbatim
public
lemma addEnergy'_eq_sum_sq' {G : Type*} [Fintype G] [DecidableEq G] [AddGroup G] (s t : Finset G) :
    E[s, t] = (∑ a ∈ s + t, s.addConvolution t a ^ 2) / Fintype.card G ^ 3 := by
  simp_rw [addEnergy'_eq_card_filter, sq, addConvolution, ← card_product]
  let f := fun x ↦ {ab ∈ s ×ˢ t | ab.1 + ab.2 = x}
  have hd : (↑(s + t) : Set G).PairwiseDisjoint (fun x ↦ f x ×ˢ f x) := by
    intro x _ y _ hxy
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro z hzx hzy
    simp only [mem_product, mem_filter, f] at hzx hzy
    exact hxy (hzx.1.2.symm.trans hzy.1.2)
  rw [← Finset.card_disjiUnion (s + t) (fun x ↦ f x ×ˢ f x) hd]
  congr 2
  congr 1
  ext z
  rw [Finset.mem_filter, Finset.mem_disjiUnion]
  simp only [mem_product, f, mem_filter]
  constructor
  · rintro ⟨⟨hab, hcs, hdt⟩, heq⟩
    exact ⟨z.1.1 + z.1.2, add_mem_add hab.1 hab.2, ⟨hab, rfl⟩, ⟨hcs, hdt⟩, heq.symm⟩
  · rintro ⟨a, _, ⟨hab, hlab⟩, hcd, hcd_eq⟩
    exact ⟨⟨hab, hcd.1, hcd.2⟩, hlab.trans hcd_eq.symm⟩








-- @@ L162-177 verbatim
public
lemma card_sq_le_card_mul_addEnergy' {G : Type*} [Fintype G] [DecidableEq G] [AddGroup G]
    (s t u : Finset G) :
    {xy ∈ s ×ˢ t | xy.1 + xy.2 ∈ u}.dens ^ 2 ≤ u.dens * E[s, t] := by
  simp only [dens, Fintype.card_prod, Nat.cast_mul, addEnergy'_eq_sum_sq', Nat.cast_sum,
    Nat.cast_pow]
  field_simp
  norm_cast
  calc
    _ = (∑ c ∈ u, #{xy ∈ s ×ˢ t | xy.1 + xy.2 = c}) ^ 2 := by
        rw [← sum_card_fiberwise_eq_card_filter]
    _ ≤ #u * ∑ c ∈ u, #{xy ∈ s ×ˢ t | xy.1 + xy.2 = c} ^ 2 := by
        simpa using sum_mul_sq_le_sq_mul_sq (R := ℕ) _ 1 _
    _ ≤ #u * ∑ c ∈ s + t, #{xy ∈ s ×ˢ t | xy.1 + xy.2 = c} ^ 2 := by
        refine mul_le_mul_right (sum_le_sum_of_ne_zero ?_) _
        aesop (add simp [filter_eq_empty_iff]) (add safe add_mem_add)




-- @@ L181-181 verbatim
end Group


-- @@ L183-183 verbatim
end Finset
