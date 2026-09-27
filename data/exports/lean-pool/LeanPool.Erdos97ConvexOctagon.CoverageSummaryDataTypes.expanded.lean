/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageDataTypes
public import LeanPool.Erdos97ConvexOctagon.CoverageSummaryTypes


-- @@ L11-11 verbatim
/-! # Lightweight coverage-summary data validation -/


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
namespace Erdos97Octagon.RawIncidence


-- @@ L17-23 verbatim
/-- Check a pattern summary against one eight-bucket data shard. -/
def PatternSummary.validAgainstB
    (buckets : Array (List PatternEntry)) (summary : PatternSummary) : Bool :=
  match (buckets.getD (summary.origin % 8) []).find?
      (fun entry => entry.origin == summary.origin) with
  | some entry => entry.mask == summary.mask && entry.validB
  | none => false


-- @@ L25-31 verbatim
/-- Check an exact-table summary against one eight-bucket data shard. -/
def HardSummary.validAgainstB
    (buckets : Array (List HardEntry)) (summary : HardSummary) : Bool :=
  match (buckets.getD (summary.origin % 8) []).find?
      (fun entry => entry.origin == summary.origin) with
  | some entry => entry.code == summary.code && entry.validB
  | none => false


-- @@ L33-33 verbatim
end Erdos97Octagon.RawIncidence
