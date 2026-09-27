/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageSummaryTypes
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD


-- @@ L14-14 verbatim
/-! # Lightweight state for finite coverage search -/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage


-- @@ L20-21 verbatim
/-- One assigned centre and its eight-bit target-row mask. -/
abbrev RowAssignment := Vertex × UInt64


-- @@ L23-28 verbatim
/-- Packed state recording which unordered pairs have occurred once or twice. -/
structure PairState where
  /-- Pairs that have occurred in at least one assigned row. -/
  seenOnce : UInt64
  /-- Pairs that have occurred in at least two assigned rows. -/
  seenTwice : UInt64


-- @@ L30-31 verbatim
/-- The empty pair-occurrence state. -/
def PairState.empty : PairState := ⟨0, 0⟩


-- @@ L33-35 verbatim
/-- Whether adding a row preserves pair sparsity. -/
def PairState.compatible (state : PairState) (pairMask : UInt64) : Bool :=
  (state.seenTwice &&& pairMask) == 0


-- @@ L37-40 verbatim
/-- Update pair occurrences after accepting one row. -/
def PairState.add (state : PairState) (pairMask : UInt64) : PairState :=
  ⟨state.seenOnce ||| pairMask,
    state.seenTwice ||| (state.seenOnce &&& pairMask)⟩


-- @@ L42-45 verbatim
/-- Packed byte counters for the number of assigned rows selecting each target. -/
structure ColumnState where
  /-- Eight one-byte column counters. -/
  counts : UInt64


-- @@ L47-48 verbatim
/-- The empty column-count state. -/
def ColumnState.empty : ColumnState := ⟨0⟩


-- @@ L50-55 verbatim
/-- Packed increments contributed by one target-row mask. -/
def columnIncrements (row : UInt64) : UInt64 :=
  (List.finRange 8).foldl (fun result target =>
    if bitSetB row target.val then
      result + (1 <<< UInt64.ofNat (8 * target.val))
    else result) 0


-- @@ L57-59 verbatim
/-- Update packed column counts after accepting one row. -/
def ColumnState.add (state : ColumnState) (row : UInt64) : ColumnState :=
  ⟨state.counts + columnIncrements row⟩


-- @@ L61-63 verbatim
/-- Read one packed column counter. -/
def ColumnState.count (state : ColumnState) (target : Vertex) : Nat :=
  ((state.counts >>> UInt64.ofNat (8 * target.val)) &&& 255).toNat


-- @@ L65-67 verbatim
/-- Number of remaining rows that can still select a target. -/
def remainingColumnCapacity (remaining : List Vertex) (target : Vertex) : Nat :=
  (remaining.filter (· ≠ target)).length


-- @@ L69-73 verbatim
/-- Fast packed check that every column can still finish with exactly four entries. -/
def ColumnState.feasible (state : ColumnState) (remaining : List Vertex) : Bool :=
  (List.finRange 8).all fun target =>
    decide (state.count target ≤ 4) &&
      decide (4 ≤ state.count target + remainingColumnCapacity remaining target)


-- @@ L75-79 verbatim
/-- Whether a target is selected by an assigned row. -/
def selectedByAssignmentsB
    (assignments : List RowAssignment) (centre target : Vertex) : Bool :=
  assignments.any fun assignment =>
    (assignment.1 == centre) && bitSetB assignment.2 target.val


-- @@ L81-84 verbatim
/-- Number of assigned rows selecting one target, computed from the semantic prefix. -/
def assignmentColumnCount
    (assignments : List RowAssignment) (target : Vertex) : Nat :=
  (assignments.filter fun assignment => bitSetB assignment.2 target.val).length


-- @@ L86-92 verbatim
/-- Semantic check that every column can still finish with exactly four entries. -/
def columnFeasibleB
    (assignments : List RowAssignment) (remaining : List Vertex) : Bool :=
  (List.finRange 8).all fun target =>
    decide (assignmentColumnCount assignments target ≤ 4) &&
      decide (4 ≤ assignmentColumnCount assignments target +
        remainingColumnCapacity remaining target)


-- @@ L94-100 verbatim
/-- Full semantic check that a packed pattern extends the assigned partial table. -/
def patternExtendsAssignmentsB
    (assignments : List RowAssignment) (summary : PatternSummary) : Bool :=
  (List.finRange 8).all fun centre =>
    (List.finRange 8).all fun target =>
      !bitSetB summary.mask (varIndex centre target) ||
        selectedByAssignmentsB assignments centre target


-- @@ L102-108 verbatim
/-- Full semantic check that an exact-table code equals all assigned rows. -/
def hardEqualsAssignmentsB
    (assignments : List RowAssignment) (summary : HardSummary) : Bool :=
  (List.finRange 8).all fun centre =>
    (List.finRange 8).all fun target =>
      bitSetB summary.code (varIndex centre target) ==
        selectedByAssignmentsB assignments centre target


-- @@ L110-112 verbatim
/-- Add one row to a packed 64-bit incidence-table prefix. -/
def addRowCode (code row : UInt64) (centre : Vertex) : UInt64 :=
  code ||| ((row &&& 255) <<< UInt64.ofNat (8 * centre.val))


-- @@ L114-114 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage
