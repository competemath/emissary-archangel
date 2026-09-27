/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData07
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
/-- Root audit for fixed branch (1, 23). -/
theorem coverageBranchRoot_1_23 :
    branchClaimRootValidB 1 23 (.patternThree 179) = true := by
  decide +kernel


-- @@ L25-28 verbatim
/-- Root audit for fixed branch (5, 8). -/
theorem coverageBranchRoot_5_08 :
    branchClaimRootValidB 5 8 (.search branchClaims5Row8) = true := by
  decide +kernel


-- @@ L30-33 verbatim
/-- Root audit for fixed branch (5, 9). -/
theorem coverageBranchRoot_5_09 :
    branchClaimRootValidB 5 9 (.search branchClaims5Row9) = true := by
  decide +kernel


-- @@ L35-38 verbatim
/-- Node audit for fixed branch (5, 7), starting at 64. -/
theorem coverageBranchNodes_5_07_00064 :
    nodeClaimChunkValidB branchClaims5Row7 64 35 = true := by
  decide +kernel


-- @@ L40-43 verbatim
/-- Node audit for fixed branch (5, 8), starting at 0. -/
theorem coverageBranchNodes_5_08_00000 :
    nodeClaimChunkValidB branchClaims5Row8 0 64 = true := by
  decide +kernel


-- @@ L45-48 verbatim
/-- Node audit for fixed branch (5, 8), starting at 64. -/
theorem coverageBranchNodes_5_08_00064 :
    nodeClaimChunkValidB branchClaims5Row8 64 25 = true := by
  decide +kernel


-- @@ L50-53 verbatim
/-- Node audit for fixed branch (5, 9), starting at 0. -/
theorem coverageBranchNodes_5_09_00000 :
    nodeClaimChunkValidB branchClaims5Row9 0 64 = true := by
  decide +kernel


-- @@ L55-55 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage
