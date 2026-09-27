/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import LeanPool.TwoColoringOneRound.LowerBound.Defs

public import LeanPool.TwoColoringOneRound.LowerBound.N1000000Data
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Finset


-- @@ L19-21 verbatim
/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000AvailFrom
-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-25 verbatim
namespace Distributed2Coloring.LowerBound


-- @@ L27-27 verbatim
namespace N1000000AvailFrom


-- @@ L29-29 verbatim
open Distributed2Coloring.LowerBound.N1000000Data


-- @@ L31-32 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev n : Nat := N1000000Data.n

-- @@ L33-34 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev SymN := Sym n


-- @@ L36-39 verbatim
/-- Symbols `≥ s` inside `Fin n`. -/
@[implicit_reducible]
def AvailFrom (s : Nat) : Type :=
  { x : SymN // s ≤ x.1 }


-- @@ L41-43 verbatim
noncomputable instance (s : Nat) : Fintype (AvailFrom (s := s)) := by
  dsimp [AvailFrom]
  infer_instance


-- @@ L45-69 verbatim
theorem card_availFrom (s : Nat) : Fintype.card (AvailFrom (s := s)) = n - s := by
  classical
  let e : Fin (n - s) ≃ AvailFrom (s := s) :=
    { toFun := fun i =>
        let xVal : Nat := s + i.1
        have hx : xVal < n := by
          have hi : i.1 < n - s := i.2
          simpa [xVal, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            (Nat.add_lt_of_lt_sub hi)
        ⟨⟨xVal, hx⟩, Nat.le_add_right _ _⟩
      invFun := fun x =>
        ⟨x.1.1 - s, by
          have hxlt : x.1.1 < n := x.1.2
          have : x.1.1 - s < n - s := Nat.sub_lt_sub_right x.2 hxlt
          simpa using this⟩
      left_inv := by
        intro i
        simp_all
      right_inv := by
        intro x
        apply Subtype.ext
        apply Fin.ext
        dsimp
        exact Nat.add_sub_of_le x.2 }
  simpa using (Fintype.card_congr e).symm


-- @@ L71-71 verbatim
end N1000000AvailFrom


-- @@ L73-73 verbatim
end Distributed2Coloring.LowerBound
