/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData08
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD


-- @@ L14-14 verbatim
/-! # Bounded coverage-certificate computation facts -/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage


-- @@ L20-23 verbatim
/-- Root audit for fixed branch (2, 7). -/
theorem coverageBranchRoot_2_07 :
    branchClaimRootValidB 2 7 (.patternThree 2) = true := by
  decide +kernel


-- @@ L25-28 verbatim
/-- Node audit for fixed branch (5, 14), starting at 64. -/
theorem coverageBranchNodes_5_14_00064 :
    nodeClaimChunkValidB branchClaims5Row14 64 64 = true := by
  decide +kernel


-- @@ L30-33 verbatim
/-- Node audit for fixed branch (5, 14), starting at 128. -/
theorem coverageBranchNodes_5_14_00128 :
    nodeClaimChunkValidB branchClaims5Row14 128 64 = true := by
  decide +kernel


-- @@ L35-38 verbatim
/-- Node audit for fixed branch (5, 14), starting at 192. -/
theorem coverageBranchNodes_5_14_00192 :
    nodeClaimChunkValidB branchClaims5Row14 192 64 = true := by
  decide +kernel


-- @@ L40-43 verbatim
/-- Node audit for fixed branch (5, 14), starting at 256. -/
theorem coverageBranchNodes_5_14_00256 :
    nodeClaimChunkValidB branchClaims5Row14 256 64 = true := by
  decide +kernel


-- @@ L45-45 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage
