/-
Copyright (c) 2026 Alexander Loitzl, Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl, Martin Dvorak
-/
module

public import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Attr.Core


-- @@ L11-16 verbatim
/-!
# List repetition utilities

Defines `nTimes` (notation `l ^+^ n`), the `n`-fold repetition of a list,
together with basic rewriting lemmas about it.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
variable {α : Type _}


-- @@ L22-24 verbatim
/-- `nTimes l n` (notation `l ^+^ n`) is the concatenation of `n` copies of the list `l`. -/
def nTimes (l : List α) (n : ℕ) : List α :=
  (List.replicate n l).flatten


-- @@ L26-27 verbatim
@[inherit_doc]
infixl:69 " ^+^ " => nTimes


-- @@ L29-29 verbatim
variable {l : List α} {n : ℕ}


-- @@ L31-31 expanded
lemma nTimes_succ_l : nTimes l n.succ = l ++ nTimes l n := by simp [nTimes, List.replicate_succ]


-- @@ L33-33 expanded
lemma nTimes_succ_r : nTimes l n.succ = nTimes l n ++ l := by simp [nTimes, List.replicate_succ']


-- @@ L35-37 expanded
lemma nTimes_map {β : Type _} {f : α → β} : nTimes (l.map f) n = (nTimes l n).map f := by
  simp [nTimes]
    -- not used anywhere, just for fun


-- @@ L38-43 expanded
lemma nTimes_add {m : ℕ} : nTimes l (m + n) = nTimes l m ++ nTimes l n := by
  induction n with
  | zero => exact (nTimes l m).append_nil.symm
  | succ _ ih =>
    rw [Nat.add_succ, nTimes_succ_r, nTimes_succ_r, ih, List.append_assoc]
      -- not used anywhere, just for fun


-- @@ L44-47 expanded
lemma nTimes_mul {m : ℕ} : nTimes l (m * n) = nTimes (nTimes l m) n := by
  induction n with
  | zero => rfl
  | succ _ ih => rw [Nat.mul_succ, nTimes_add, ih, nTimes_succ_r]

