/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.HadwigerNelsonBounds.PartsGadgetHardCasesData0
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.SimpleGraph.Init
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD


-- @@ L15-15 verbatim
/-! Kernel checks for hard-case certificate group 0. -/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
namespace HadwigerNelsonBounds


-- @@ L21-23 verbatim
theorem partsGadgetHardCertificate0_verifies :
    partsGadgetHardCertificate0.Verifies := by
  decide


-- @@ L25-27 verbatim
theorem partsGadgetHardCertificate1_verifies :
    partsGadgetHardCertificate1.Verifies := by
  decide


-- @@ L29-31 verbatim
theorem partsGadgetHardCertificate2_verifies :
    partsGadgetHardCertificate2.Verifies := by
  decide


-- @@ L33-35 verbatim
theorem partsGadgetHardCertificate3_verifies :
    partsGadgetHardCertificate3.Verifies := by
  decide


-- @@ L37-37 verbatim
end HadwigerNelsonBounds
