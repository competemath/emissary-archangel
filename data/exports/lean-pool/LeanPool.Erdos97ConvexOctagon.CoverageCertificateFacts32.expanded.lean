/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData05
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
/-- Root audit for fixed branch (0, 32). -/
theorem coverageBranchRoot_0_32 :
    branchClaimRootValidB 0 32 (.patternTwo 0) = true := by
  decide +kernel


-- @@ L25-28 verbatim
/-- Root audit for fixed branch (6, 22). -/
theorem coverageBranchRoot_6_22 :
    branchClaimRootValidB 6 22 (.patternThree 1) = true := by
  decide +kernel


-- @@ L30-33 verbatim
/-- Root audit for fixed branch (3, 10). -/
theorem coverageBranchRoot_3_10 :
    branchClaimRootValidB 3 10 (.search branchClaims3Row10) = true := by
  decide +kernel


-- @@ L35-38 verbatim
/-- Node audit for fixed branch (3, 6), starting at 64. -/
theorem coverageBranchNodes_3_06_00064 :
    nodeClaimChunkValidB branchClaims3Row6 64 33 = true := by
  decide +kernel


-- @@ L40-43 verbatim
/-- Node audit for fixed branch (3, 10), starting at 0. -/
theorem coverageBranchNodes_3_10_00000 :
    nodeClaimChunkValidB branchClaims3Row10 0 64 = true := by
  decide +kernel


-- @@ L45-48 verbatim
/-- Node audit for fixed branch (3, 10), starting at 64. -/
theorem coverageBranchNodes_3_10_00064 :
    nodeClaimChunkValidB branchClaims3Row10 64 64 = true := by
  decide +kernel


-- @@ L50-53 verbatim
/-- Node audit for fixed branch (3, 10), starting at 128. -/
theorem coverageBranchNodes_3_10_00128 :
    nodeClaimChunkValidB branchClaims3Row10 128 17 = true := by
  decide +kernel


-- @@ L55-55 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage
