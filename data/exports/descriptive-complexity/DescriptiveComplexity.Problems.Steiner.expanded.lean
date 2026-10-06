/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Steiner.Defs
import DescriptiveComplexity.Problems.Steiner.Reductions
import DescriptiveComplexity.Problems.Steiner.Membership
import DescriptiveComplexity.Problems.CliqueFamily


-- @@ L11-30 verbatim
/-!
# Steiner Tree is NP-complete

Umbrella file for `DescriptiveComplexity.SteinerTree`, the node-weighted Steiner tree
with unit weights (defined in `DescriptiveComplexity.Problems.Steiner.Defs`), deriving
NP-completeness from

* `DescriptiveComplexity.steinerTree_sigmaSODefinable`
  (`DescriptiveComplexity.Problems.Steiner.Membership`): membership, by guessing the
  chosen set, a root, an order certifying connectivity, and the threshold
  injection;
* `DescriptiveComplexity.vertexCover_ordered_fo_reduction_steinerTree`
  (`DescriptiveComplexity.Problems.Steiner.Reductions`): hardness, from the NP-hardness
  of Vertex Cover (`DescriptiveComplexity.Problems.CliqueFamily`), and so ultimately
  from the Cook–Levin theorem, with no machine model anywhere.

As with any complexity-theoretic statement, these results are about finite
structures only
(`DescriptiveComplexity.ComplexityClass.mem_congr_finite`/`hard_congr_finite`).
-/


-- @@ L32-32 verbatim
namespace DescriptiveComplexity


-- @@ L34-34 verbatim
open FirstOrder


-- @@ L36-38 verbatim
/-- Steiner Tree is in NP: it is `Σ₁`-definable. -/
theorem steinerTree_mem_NP : SteinerTree ∈ NP :=
  steinerTree_sigmaSODefinable


-- @@ L40-43 verbatim
/-- Steiner Tree is NP-hard: Vertex Cover, which is NP-hard, ordered-FO-reduces
to it by the edge-incidence structure with a root. -/
theorem steinerTree_NP_hard : NP.Hard SteinerTree :=
  NP.hard_of_orderedReduction vertexCover_ordered_fo_reduction_steinerTree vertexCover_NP_hard


-- @@ L45-50 verbatim
/-- **Steiner Tree is NP-complete**, derived from the first-order reductions
of this library and the Cook–Levin theorem.
Registered in the Lax archive as
[`Lax799700.Steiner.steinerTree_NP_complete`](https://laxarchive.org/lax-799700/Lax799700.Steiner.html#s-Lax799700.Steiner.steinerTree_NP_complete). -/
theorem steinerTree_NP_complete : NP.Complete SteinerTree :=
  ⟨steinerTree_mem_NP, steinerTree_NP_hard⟩


-- @@ L52-52 verbatim
/-! ### The edge-weighted variant -/


-- @@ L54-56 verbatim
/-- The edge-weighted Steiner Tree is in NP: it is `Σ₁`-definable. -/
theorem edgeSteinerTree_mem_NP : EdgeSteinerTree ∈ NP :=
  edgeSteinerTree_sigmaSODefinable


-- @@ L58-62 verbatim
/-- The edge-weighted Steiner Tree is NP-hard: Vertex Cover, which is NP-hard,
ordered-FO-reduces to it. -/
theorem edgeSteinerTree_NP_hard : NP.Hard EdgeSteinerTree :=
  NP.hard_of_orderedReduction vertexCover_ordered_fo_reduction_edgeSteinerTree
    vertexCover_NP_hard


-- @@ L64-69 verbatim
/-- **The edge-weighted Steiner Tree is NP-complete** – Karp's original
reading of the problem.
Registered in the Lax archive as
[`Lax799700.Steiner.edgeSteinerTree_NP_complete`](https://laxarchive.org/lax-799700/Lax799700.Steiner.html#s-Lax799700.Steiner.edgeSteinerTree_NP_complete). -/
theorem edgeSteinerTree_NP_complete : NP.Complete EdgeSteinerTree :=
  ⟨edgeSteinerTree_mem_NP, edgeSteinerTree_NP_hard⟩


-- @@ L71-71 verbatim
end DescriptiveComplexity
