/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData00
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
/-- Root audit for fixed branch (0, 1). -/
theorem coverageBranchRoot_0_01 :
    branchClaimRootValidB 0 1 (.patternTwo 0) = true := by
  decide +kernel


-- @@ L25-28 verbatim
/-- Root audit for fixed branch (4, 19). -/
theorem coverageBranchRoot_4_19 :
    branchClaimRootValidB 4 19 (.patternTwo 0) = true := by
  decide +kernel


-- @@ L30-33 verbatim
/-- Root audit for fixed branch (1, 6). -/
theorem coverageBranchRoot_1_06 :
    branchClaimRootValidB 1 6 (.search branchClaims1Row6) = true := by
  decide +kernel


-- @@ L35-38 verbatim
/-- Root audit for fixed branch (1, 7). -/
theorem coverageBranchRoot_1_07 :
    branchClaimRootValidB 1 7 (.search branchClaims1Row7) = true := by
  decide +kernel


-- @@ L40-43 verbatim
/-- Node audit for fixed branch (1, 6), starting at 0. -/
theorem coverageBranchNodes_1_06_00000 :
    nodeClaimChunkValidB branchClaims1Row6 0 64 = true := by
  decide +kernel


-- @@ L45-48 verbatim
/-- Node audit for fixed branch (1, 6), starting at 64. -/
theorem coverageBranchNodes_1_06_00064 :
    nodeClaimChunkValidB branchClaims1Row6 64 57 = true := by
  decide +kernel


-- @@ L50-53 verbatim
/-- Node audit for fixed branch (1, 7), starting at 0. -/
theorem coverageBranchNodes_1_07_00000 :
    nodeClaimChunkValidB branchClaims1Row7 0 64 = true := by
  decide +kernel


-- @@ L55-58 verbatim
/-- Node audit for fixed branch (1, 7), starting at 64. -/
theorem coverageBranchNodes_1_07_00064 :
    nodeClaimChunkValidB branchClaims1Row7 64 51 = true := by
  decide +kernel


-- @@ L60-60 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage
