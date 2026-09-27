/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import LeanPool.MisereGames.Form.Birthday
public import LeanPool.MisereGames.GameForm


-- @@ L11-13 verbatim
/-!
Misere combinatorial games.
-/


-- @@ L15-15 verbatim
namespace MisereGames


-- @@ L17-17 verbatim
open NatOrdinal Order Set


-- @@ L19-19 verbatim
universe u


-- @@ L21-21 verbatim
public section


-- @@ L23-23 verbatim
namespace GameForm


-- @@ L25-25 verbatim
open Form


-- @@ L27-32 verbatim
@[simp]
theorem birthday_eq_zero {x : GameForm} : birthday x = 0 ↔ x = 0 := by
  rw [birthday, iSup_eq_zero_iff, GameForm.ext_iff]
  simp only [succ_eq_add_one, add_one_ne_zero, Subtype.forall, IsOption.iff_mem_union, mem_union,
             imp_false, not_or, forall_and, moves_zero (G := GameForm), eq_empty_iff_forall_notMem,
             Player.forall]


-- @@ L34-38 expanded
/-- The finite set of game forms born by day `n`. -/
noncomputable def birthdayFinset : ℕ → Finset GameForm.{u}
  | 0 => {0}
  | n + 1 =>
    ((birthdayFinset n).powerset ×ˢ (birthdayFinset n).powerset).map
      ⟨fun a =>
        OfSets.ofSets (Player.cases a.1 a.2)
          (by
            first
            | done
            | trivial
            | assumption
            | aesop
            |
              fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                where `h` is a proof that sets are valid"),
        fun a b hab => by aesop⟩


-- @@ L40-47 expanded
theorem mem_birthdayFinset_succ {x : GameForm} {n : ℕ} :
    x ∈ birthdayFinset (n + 1) ↔
      ∃ l r,
        (l ⊆ birthdayFinset n ∧ r ⊆ birthdayFinset n) ∧
          OfSets.ofSets (Player.cases l r)
              (by
                first
                | done
                | trivial
                | assumption
                | aesop
                |
                  fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                    where `h` is a proof that sets are valid") =
            x :=
  by
  simp only [birthdayFinset, Finset.mem_map, Finset.mem_product, Finset.mem_powerset, Prod.exists]
  constructor
  · rintro ⟨l, r, h, rfl⟩
    exact ⟨l, r, h, rfl⟩
  · rintro ⟨l, r, h, rfl⟩
    exact ⟨l, r, h, rfl⟩


-- @@ L49-50 verbatim
@[simp]
theorem birthdayFinset_zero : birthdayFinset 0 = {0} := by rfl


-- @@ L52-69 verbatim
@[simp]
theorem mem_birthdayFinset {x : GameForm} {n : ℕ} : x ∈ birthdayFinset n ↔ birthday x ≤ n := by
  induction n generalizing x with
  | zero =>
    simp [birthdayFinset_zero, birthday_eq_zero]
  | succ n IH =>
    simp_rw [mem_birthdayFinset_succ, birthday_le_iff, Finset.subset_iff, Nat.cast_add_one,
      ← succ_eq_add_one, lt_succ_iff, IH]
    constructor
    · aesop
    · rintro ⟨hl, hr⟩
      have hxl : xᴸ ⊆ birthdayFinset n := fun y hy => (IH (x := y)).2 (hl y hy)
      have hxr : xᴿ ⊆ birthdayFinset n := fun y hy => (IH (x := y)).2 (hr y hy)
      classical
      have := Set.fintypeSubset _ hxl
      have := Set.fintypeSubset _ hxr
      use xᴸ.toFinset, xᴿ.toFinset
      simp_all


-- @@ L71-71 verbatim
end GameForm


-- @@ L73-73 verbatim
end


-- @@ L75-75 verbatim
end MisereGames
