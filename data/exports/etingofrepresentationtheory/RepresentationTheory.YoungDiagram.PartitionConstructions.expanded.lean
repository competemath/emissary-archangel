/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute


-- @@ L10-10 verbatim
/-! # Auxiliary partition constructions -/


-- @@ L12-12 verbatim
namespace RepresentationTheory.YoungDiagram.PartitionConstructions


-- @@ L14-17 verbatim
/-- Assigns an auxiliary Young diagram to each partition of a natural number. -/
noncomputable def auxiliaryYoungDiagramOfPartition {n : ℕ} (μ : Nat.Partition n) : YoungDiagram :=
  YoungDiagram.ofRowLens (μ.parts.sort (· ≥ ·))
    (List.sortedGE_iff_pairwise.mpr (Multiset.pairwise_sort (s := μ.parts) (r := (· ≥ ·))))


-- @@ L19-25 verbatim
/-- An auxiliary natural-valued function of two partitions of the same natural number. -/
@[source_ref "Chapter5/Definition5.14.2" (role := supporting)]
noncomputable def auxiliaryPartitionPairNat (n : ℕ) (mu la : Nat.Partition n) : ℕ :=
  Nat.card { T : SemistandardYoungTableau (auxiliaryYoungDiagramOfPartition mu) //
    ∀ k : ℕ, ((auxiliaryYoungDiagramOfPartition mu).cells.filter
      (fun c => T c.1 c.2 = k)).card =
      (la.parts.sort (· ≥ ·)).getD k 0 }


-- @@ L27-27 verbatim
end RepresentationTheory.YoungDiagram.PartitionConstructions
