/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/
module

public import LeanPool.Wallace.ConcreteFusionRun
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init


-- @@ L12-17 verbatim
/-!
# The full free-Abelian group theorem

This module applies the unconditional fusion construction to the generic topological results in
`Wallace.FullTopology`.  The resulting theorem has no hypotheses.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
namespace Wallace


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
open TriangularPreprocess

-- @@ L26-26 verbatim
open Filter Topology


-- @@ L28-34 verbatim
/-- The fully constructed character package on the canonical free Abelian group of rank
continuum. -/
def continuumFullSeparationPackage : SeparationPackage ContinuumIndex :=
  GlobalAssembly.separationPackage
    ConcreteFusionRun.blockSize ConcreteFusionRun.blockSize_pos
    ConcreteFusionRun.independenceBound
    ConcreteFusionRun.hasLocalSeparatingCharacters


-- @@ L36-36 verbatim
end


-- @@ L38-38 verbatim
end Wallace
