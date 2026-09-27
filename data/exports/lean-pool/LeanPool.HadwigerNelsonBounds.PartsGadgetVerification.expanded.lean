/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.HadwigerNelsonBounds.PartsGadgetMiddleData
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.SimpleGraph.Init
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD


-- @@ L15-15 verbatim
/-! Kernel verification of the two normalized second-stage coloring trees. -/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
namespace HadwigerNelsonBounds


-- @@ L21-24 verbatim
/-- The middle-color normalized second-stage certificate checks by reduction. -/
theorem partsGadgetMiddleCertificate_verifies :
    partsGadgetMiddleCertificate.Verifies := by
  decide


-- @@ L26-26 verbatim
end HadwigerNelsonBounds
