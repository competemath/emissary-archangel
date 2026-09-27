/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/
module

public import Mathlib.Tactic.Simps
public import Mathlib.Tactic.ToAdditive


-- @@ L11-13 verbatim
/-!
# LeanPool.Polylean.ConjInvLength.LengthBound
-/


-- @@ L15-15 verbatim
@[expose] public section


-- @@ L17-17 verbatim
namespace LeanPool.Polylean

-- @@ L18-24 verbatim
/-- The four generators used for words in the conjugation-invariant length example. -/
inductive Letter where
  | α : Letter
  | β : Letter
  | α! : Letter
  | β! : Letter
  deriving DecidableEq, Repr, Hashable, Inhabited


-- @@ L26-26 verbatim
namespace Letter


-- @@ L28-33 verbatim
/-- Render a letter as a string. -/
def toString : Letter → String
| α => "α"
| β => "β"
| α! => "alpha!"
| β! => "beta!"


-- @@ L35-35 verbatim
instance : ToString Letter := ⟨Letter.toString⟩


-- @@ L37-42 verbatim
/-- The formal inverse of a letter. -/
def inv : Letter → Letter
  | α => α!
  | β  => β!
  | α! => α
  | β! => β


-- @@ L44-44 verbatim
end Letter


-- @@ L46-46 verbatim
@[inline] instance letInv : Inv Letter := ⟨Letter.inv⟩



-- @@ L49-49 verbatim
open Letter


-- @@ L51-52 verbatim
/-- A word is a list of letters. -/
abbrev Word := List Letter


-- @@ L54-54 verbatim
namespace Word


-- @@ L56-57 verbatim
/-- Render a word by concatenating its rendered letters. -/
def toString (w : Word) := w.foldl (fun x y => s!"{x}{y}") ""


-- @@ L59-59 verbatim
instance : ToString Word := ⟨Word.toString⟩


-- @@ L61-64 verbatim
/-- Repeated concatenation of a word. -/
def pow : Word → Nat → Word
  | _, 0 => []
  | w, Nat.succ m => w ++ (pow w m)


-- @@ L66-67 verbatim
instance : Pow Word Nat where
  pow w n := w.pow n


-- @@ L69-72 verbatim
end Word

-- The code below (with better termination) is due to Mario Carneiro
-- split a word into parts before and after each occurrence of a letter `l`

-- @@ L73-79 verbatim
/-- All splits of a word around occurrences of a letter, with length witnesses. -/
def splits (l : Letter) : (w : Word) → List {p : Word × Word // p.1.length + p.2.length < w.length}
  | [] => []
  | x :: ys =>
    let tailSplits := (splits l ys).map fun ⟨(fst, snd), h⟩ =>
      ⟨(x :: fst, snd), by simp [Nat.succ_add, Nat.succ_lt_succ h]⟩
    if x = l then ⟨([], ys), by simp⟩ :: tailSplits else tailSplits


-- @@ L81-94 verbatim
/-- A recursively computed conjugation-invariant length candidate. -/
def length : Word → Nat
  | [] => 0
  | x :: ys =>
    let base := 1 + (length ys)
    let derived := (splits x⁻¹ ys).map fun ⟨(fst, snd), h⟩ =>
      have h : fst.length + snd.length < ys.length + 1 := Nat.lt_trans h (Nat.lt_succ_self _)
      have _ : snd.length < ys.length + 1  := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h
      have _ : fst.length < ys.length + 1 := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) h
      length fst + length snd
    derived.foldl min base -- minimum of base and elements of derived
termination_by l => l.length

-- For proofs


-- @@ L96-96 verbatim
namespace Word


-- @@ L98-99 verbatim
/-- Conjugate a word by a letter. -/
def conj : Word → Letter → Word := fun w l => [l] ++ w ++ [l⁻¹]


-- @@ L101-101 verbatim
end Word


-- @@ L103-104 verbatim
instance : Pow Word Letter where
  pow w l := w.conj l

-- @@ L105-105 verbatim
end LeanPool.Polylean
