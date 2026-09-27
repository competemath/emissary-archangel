/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Basic


-- @@ L11-13 verbatim
/-!
# Maximum absolute value of a tuple of integers
-/


-- @@ L15-15 verbatim
@[expose] public section



-- @@ L18-18 verbatim
open Finset


-- @@ L20-20 verbatim
variable {n : ℕ}


-- @@ L22-24 verbatim
/-- The maximum absolute value of a tuple of integers (0 if empty). -/
def maxAbs (a : Fin n → ℤ) : ℕ :=
  univ.sup fun i ↦ (a i).natAbs


-- @@ L26-26 verbatim
lemma maxAbs_zero {a : Fin 0 → ℤ} : maxAbs a = 0 := by simp [maxAbs]


-- @@ L28-28 verbatim
lemma maxAbs_one {a : Fin 1 → ℤ} : maxAbs a = (a 0).natAbs := by simp [maxAbs]


-- @@ L30-30 verbatim
variable {a : Fin n → ℤ}


-- @@ L32-35 verbatim
lemma maxAbs_eq_foldr : maxAbs a = (List.ofFn fun i ↦ (a i).natAbs).foldr max 0 := by
  rw [← Nat.bot_eq_zero, List.foldr_sup_eq_sup_toFinset, maxAbs,
    ← (fun i ↦ (a i).natAbs).id_comp, ← sup_image]
  congr; ext; simp


-- @@ L37-39 verbatim
lemma maxAbs_eq_of_forall_le {i : Fin n} (hi : ∀ j, (a j).natAbs ≤ (a i).natAbs) :
    maxAbs a = (a i).natAbs :=
  le_antisymm (Finset.sup_le (by simp_all)) (le_sup (f := fun i ↦ (a i).natAbs) (mem_univ _))
