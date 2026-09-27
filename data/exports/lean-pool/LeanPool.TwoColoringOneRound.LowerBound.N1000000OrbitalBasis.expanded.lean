/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import LeanPool.TwoColoringOneRound.LowerBound.N1000000PairTransitivity
public import LeanPool.TwoColoringOneRound.LowerBound.N1000000StructureConstants
public import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Finset


-- @@ L20-22 verbatim
/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000OrbitalBasis
-/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
namespace Distributed2Coloring.LowerBound


-- @@ L28-28 verbatim
namespace N1000000OrbitalBasis


-- @@ L30-30 verbatim
open scoped BigOperators

-- @@ L31-31 verbatim
open scoped Matrix


-- @@ L33-33 verbatim
open Distributed2Coloring.LowerBound.Correlation

-- @@ L34-34 verbatim
open Distributed2Coloring.LowerBound.N1000000Data

-- @@ L35-35 verbatim
open Distributed2Coloring.LowerBound.N1000000PairTransitivity

-- @@ L36-36 verbatim
open Distributed2Coloring.LowerBound.N1000000StructureConstants

-- @@ L37-37 verbatim
open Distributed2Coloring.LowerBound.N1000000Witness


-- @@ L39-40 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev n : Nat := N1000000Data.n

-- @@ L41-42 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Q := ℚ

-- @@ L43-44 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev SymN := Sym n

-- @@ L45-46 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev V := Vertex n

-- @@ L47-48 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev G := Correlation.G n

-- @@ L49-50 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Mask := Distributed2Coloring.LowerBound.Mask

-- @@ L51-52 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev DirIdx := N1000000StructureConstants.DirIdx


-- @@ L54-55 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev i0 : Fin 3 := ⟨0, by decide⟩

-- @@ L56-57 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev i1 : Fin 3 := ⟨1, by decide⟩

-- @@ L58-59 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev i2 : Fin 3 := ⟨2, by decide⟩


-- @@ L61-62 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev s0 : SymN := ⟨0, by decide⟩

-- @@ L63-64 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev s1 : SymN := ⟨1, by decide⟩

-- @@ L65-66 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev s2 : SymN := ⟨2, by decide⟩


-- @@ L68-72 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def baseTuple : Tuple 3 n
  | ⟨0, _⟩ => s0
  | ⟨1, _⟩ => s1
  | ⟨2, _⟩ => s2


-- @@ L74-76 verbatim
theorem baseTuple_injective : Function.Injective baseTuple := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp only [baseTuple] at hij <;> cases hij <;> rfl


-- @@ L78-80 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def baseVertex : V :=
  ⟨baseTuple, baseTuple_injective⟩


-- @@ L82-84 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def baseSet : Finset SymN :=
  insert s0 (insert s1 (insert s2 ∅))


-- @@ L86-87 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def outside (x : SymN) : Prop := x ∉ baseSet


-- @@ L89-92 verbatim
instance : DecidablePred outside := by
  intro x
  unfold outside
  infer_instance


-- @@ L94-98 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev OutsideSym := { x : SymN // outside x }

-- The directed orbital basis matrices, in the `N[k][a][d]` convention:
-- `A_d[u,v] = 1` iff the directed overlap mask of the ordered pair `(v,u)` is `maskAt d`.

-- @@ L99-101 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def A (d : DirIdx) : Matrix V V Q :=
  fun u v => if dirMask v u = maskAt d then 1 else 0


-- @@ L103-106 verbatim
@[simp] theorem A_apply (d : DirIdx) (u v : V) :
    A d u v = (if dirMask v u = maskAt d then 1 else 0) := rfl

-- The symmetric orbital basis element corresponding to a directed type `d`.

-- @@ L107-114 verbatim
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
def ASymm (d : DirIdx) : Matrix V V Q :=
  if h : tTr[d.1]! = d.1 then
    A d
  else
    A d + A ⟨tTr[d.1]!, by
      -- `tTr` is a permutation of the 34 indices.
      fin_cases d <;> decide⟩


-- @@ L116-116 verbatim
end N1000000OrbitalBasis


-- @@ L118-118 verbatim
end Distributed2Coloring.LowerBound
