/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.HadwigerNelsonBounds.PartsGadgetMiddleData0
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.SimpleGraph.Init
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD


-- @@ L15-15 verbatim
/-! Aggregation of the generated `Middle` certificate. -/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
namespace HadwigerNelsonBounds


-- @@ L21-28 verbatim
/-- The checked `Middle` contradiction tree. -/
def partsGadgetMiddleCertificate : PartsGadgetCertificate := {
  roots := [⟨5, 0⟩, ⟨31, 3⟩, ⟨18, 1⟩]
  nodeCount := 17
  nodes := #[
    partsGadgetMiddleChunk0,
  ]
}


-- @@ L30-30 verbatim
end HadwigerNelsonBounds
