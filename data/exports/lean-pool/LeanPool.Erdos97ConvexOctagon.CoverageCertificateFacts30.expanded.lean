/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData04
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
/-- Root audit for fixed branch (0, 30). -/
theorem coverageBranchRoot_0_30 :
    branchClaimRootValidB 0 30 (.patternTwo 0) = true := by
  decide +kernel


-- @@ L25-28 verbatim
/-- Root audit for fixed branch (6, 20). -/
theorem coverageBranchRoot_6_20 :
    branchClaimRootValidB 6 20 (.patternThree 1) = true := by
  decide +kernel


-- @@ L30-33 verbatim
/-- Root audit for fixed branch (3, 3). -/
theorem coverageBranchRoot_3_03 :
    branchClaimRootValidB 3 3 (.search branchClaims3Row3) = true := by
  decide +kernel


-- @@ L35-38 verbatim
/-- Root audit for fixed branch (3, 4). -/
theorem coverageBranchRoot_3_04 :
    branchClaimRootValidB 3 4 (.search branchClaims3Row4) = true := by
  decide +kernel


-- @@ L40-43 verbatim
/-- Node audit for fixed branch (3, 2), starting at 64. -/
theorem coverageBranchNodes_3_02_00064 :
    nodeClaimChunkValidB branchClaims3Row2 64 52 = true := by
  decide +kernel


-- @@ L45-48 verbatim
/-- Node audit for fixed branch (3, 3), starting at 0. -/
theorem coverageBranchNodes_3_03_00000 :
    nodeClaimChunkValidB branchClaims3Row3 0 64 = true := by
  decide +kernel


-- @@ L50-53 verbatim
/-- Node audit for fixed branch (3, 3), starting at 64. -/
theorem coverageBranchNodes_3_03_00064 :
    nodeClaimChunkValidB branchClaims3Row3 64 31 = true := by
  decide +kernel


-- @@ L55-58 verbatim
/-- Node audit for fixed branch (3, 4), starting at 0. -/
theorem coverageBranchNodes_3_04_00000 :
    nodeClaimChunkValidB branchClaims3Row4 0 64 = true := by
  decide +kernel


-- @@ L60-60 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage
