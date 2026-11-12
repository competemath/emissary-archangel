/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.YoungDiagram.PartitionFormulas
import RepresentationTheory.Alignment.Attribute


-- @@ L11-11 verbatim
namespace RepresentationTheory.PartitionFinrank


-- @@ L13-13 verbatim
noncomputable section


-- @@ L15-21 verbatim
/-- The finrank of the partition-indexed subtype equals the cardinality of an auxiliary type. -/
theorem finrank_eq_card_auxiliaryType (n : ℕ) (la : Nat.Partition n) :
    Module.finrank ℂ (RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la) =
      Nat.card
        (RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.AuxiliaryPartitionSource
          n la) :=
  RepresentationTheory.YoungDiagram.PartitionFormulas.finrank_auxiliary_subtype_eq_card n la


-- @@ L23-31 verbatim
/-- The finrank of the partition-indexed subtype equals the factorial divided by its Young diagram hook-length product. -/
theorem finrank_eq_factorial_div_hookLengthProduct (n : ℕ) (la : Nat.Partition n) :
    Module.finrank ℂ (RepresentationTheory.PartitionAuxiliary.partitionSubmodule n la) =
      n.factorial /
        RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.YoungDiagram.auxiliaryDiagramStatistic
          (RepresentationTheory.YoungDiagram.PartitionConstructions.auxiliaryYoungDiagramOfPartition
            la) := by
  rw [finrank_eq_card_auxiliaryType,
    RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.Partition.auxiliaryCard_eq_factorial_div_hookLengthProduct]


-- @@ L33-33 verbatim
end


-- @@ L35-37 verbatim
end RepresentationTheory.PartitionFinrank

-- Recovered exact-module book alignment.

-- @@ L38-38 verbatim
attribute [source_ref "Chapter5/Theorem5.17.1" (role := primary)] _root_.RepresentationTheory.PartitionFinrank.finrank_eq_factorial_div_hookLengthProduct

-- @@ L39-39 verbatim
attribute [source_ref "Chapter5/Theorem5.17.1" (role := supporting)] _root_.RepresentationTheory.PartitionFinrank.finrank_eq_card_auxiliaryType
