/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import LeanPool.MisereGames.Ruleset.Strip


-- @@ L10-12 verbatim
/-!
Misere combinatorial games.
-/


-- @@ L14-14 verbatim
namespace MisereGames


-- @@ L16-16 verbatim
open GameForm

-- @@ L17-17 verbatim
open Form


-- @@ L19-19 verbatim
public section


-- @@ L21-38 verbatim
/-!
# Shove

Shove is played on a horizontal strip of squares, each square either empty or
occupied by a Left or Right piece (see `Strip.Piece`). On their turn a player
chooses one of their pieces and moves it, together with *everything* to the
left of it (not even necessarily adjacent), one square to the left. Pieces can
fall off the left side of the strip and are removed.

In terms of the shared `Strip` primitive `shiftDown`, a Shove move pushing the
piece at position `n` is `shiftDown b 0 n`: the whole prefix `0 .. n` shifts
left and the piece at position `0` falls off. So `Shove` is exactly the `Strip`
ruleset whose shift anchor `start` is always `0`.

The stride theory developed in `CombinatorialGames.Ruleset.Strip` then
immediately gives that the misère quotient of `Shove` is isomorphic to `ℤ`
(`Shove.equivInt`).
-/


-- @@ L40-46 verbatim
/--
A `Shove` position is a strip board (a function from positions to pieces with
finite support).
-/
structure Shove where
  /-- The underlying strip board. -/
  toBoard : Strip.Board


-- @@ L48-48 verbatim
namespace Shove


-- @@ L50-51 verbatim
/-- The piece at position `n`. -/
@[expose] def board (s : Shove) (n : ℕ) : Strip.Piece := s.toBoard.board n


-- @@ L53-66 verbatim
/--
`Shove` is the `Strip` ruleset whose shift always starts at position `0`:
pushing the piece at position `n` shifts the entire prefix `0 .. n` to the
left, dropping the piece that falls off.
-/
instance : Strip Shove where
  toBoard := Shove.toBoard
  ofBoard := Shove.mk
  toBoard_ofBoard _ := rfl
  push s n := ⟨s.toBoard.shiftDownB 0 n⟩
  start _ _ := 0
  start_le _ _ := Nat.zero_le _
  start_lt := by intro _ _ h; exact h
  push_eq _ _ := rfl


-- @@ L68-69 verbatim
/-- The `GameForm` of a Shove position. -/
protected noncomputable def toGameForm : Shove → GameForm := Strip.toGameForm


-- @@ L71-74 verbatim
/-- The misère quotient of `Shove` is isomorphic to `ℤ`. -/
protected noncomputable def equivInt :
    MisereQuotient (ClosedUnderAdd.closure (Ruleset.Forms Shove)) ≃ ℤ :=
  Strip.equivInt Shove


-- @@ L76-80 verbatim
protected theorem le_iff_equiv_ge
    (a b : MisereQuotient (ClosedUnderAdd.closure (Ruleset.Forms Shove))) :
    a ≤ b ↔
    MisereQuotient.stridedEquivInt a ≥ MisereQuotient.stridedEquivInt b :=
  Strip.le_iff_equiv_ge Shove a b


-- @@ L82-82 verbatim
end Shove


-- @@ L84-84 verbatim
end


-- @@ L86-86 verbatim
end MisereGames
