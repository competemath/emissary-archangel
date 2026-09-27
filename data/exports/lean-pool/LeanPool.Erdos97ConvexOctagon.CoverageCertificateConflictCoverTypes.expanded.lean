/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoveragePairRowIndexMasks
public import LeanPool.Erdos97ConvexOctagon.FiniteModel
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD


-- @@ L15-15 verbatim
/-! # Types and local audit for repeated-pair row-mask covers -/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage


-- @@ L21-30 verbatim
/-- Repeated pairs and legal rows that they soundly reject at one search centre. -/
structure ConflictCover where
  /-- Search centre for which the row-index mask is valid. -/
  centre : Nat
  /-- Repeated-pair bits sufficient to justify the rejected rows. -/
  requiredPairs : UInt64
  /-- Masked rows, each of which contains one of the required pairs. -/
  incompatibleRows : UInt64
  /-- Short list of pair bits whose row-mask union is `incompatibleRows`. -/
  pairIndices : List Nat


-- @@ L32-40 verbatim
/-- Audit the short pair list and its precomputed row-mask union. -/
def ConflictCover.validB (cover : ConflictCover) : Bool :=
  if _hcentre : cover.centre < 8 then
    let masks := pairRowIndexMasks.getD cover.centre #[]
    cover.pairIndices.all (fun index =>
      index < 64 && bitSetB cover.requiredPairs index) &&
      cover.pairIndices.foldl (fun rows index =>
        rows ||| masks.getD index 0) 0 == cover.incompatibleRows
  else false


-- @@ L42-42 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage
