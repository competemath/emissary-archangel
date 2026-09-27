/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData12
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
/-- Root audit for fixed branch (3, 34). -/
theorem coverageBranchRoot_3_34 :
    branchClaimRootValidB 3 34 (.patternThree 6) = true := by
  decide +kernel


-- @@ L25-28 verbatim
/-- Root audit for fixed branch (6, 5). -/
theorem coverageBranchRoot_6_05 :
    branchClaimRootValidB 6 5 (.search branchClaims6Row5) = true := by
  decide +kernel


-- @@ L30-33 verbatim
/-- Root audit for fixed branch (6, 6). -/
theorem coverageBranchRoot_6_06 :
    branchClaimRootValidB 6 6 (.search branchClaims6Row6) = true := by
  decide +kernel


-- @@ L35-38 verbatim
/-- Root audit for fixed branch (6, 7). -/
theorem coverageBranchRoot_6_07 :
    branchClaimRootValidB 6 7 (.search branchClaims6Row7) = true := by
  decide +kernel


-- @@ L40-43 verbatim
/-- Node audit for fixed branch (6, 5), starting at 0. -/
theorem coverageBranchNodes_6_05_00000 :
    nodeClaimChunkValidB branchClaims6Row5 0 40 = true := by
  decide +kernel


-- @@ L45-48 verbatim
/-- Node audit for fixed branch (6, 6), starting at 0. -/
theorem coverageBranchNodes_6_06_00000 :
    nodeClaimChunkValidB branchClaims6Row6 0 35 = true := by
  decide +kernel


-- @@ L50-53 verbatim
/-- Node audit for fixed branch (6, 7), starting at 0. -/
theorem coverageBranchNodes_6_07_00000 :
    nodeClaimChunkValidB branchClaims6Row7 0 64 = true := by
  decide +kernel


-- @@ L55-58 verbatim
/-- Node audit for fixed branch (6, 7), starting at 64. -/
theorem coverageBranchNodes_6_07_00064 :
    nodeClaimChunkValidB branchClaims6Row7 64 39 = true := by
  decide +kernel


-- @@ L60-60 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage
