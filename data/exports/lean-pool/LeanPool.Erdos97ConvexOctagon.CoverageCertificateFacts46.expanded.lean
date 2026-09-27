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
/-- Root audit for fixed branch (1, 21). -/
theorem coverageBranchRoot_1_21 :
    branchClaimRootValidB 1 21 (.patternThree 1) = true := by
  decide +kernel


-- @@ L25-28 verbatim
/-- Root audit for fixed branch (5, 4). -/
theorem coverageBranchRoot_5_04 :
    branchClaimRootValidB 5 4 (.search branchClaims5Row4) = true := by
  decide +kernel


-- @@ L30-33 verbatim
/-- Root audit for fixed branch (5, 5). -/
theorem coverageBranchRoot_5_05 :
    branchClaimRootValidB 5 5 (.search branchClaims5Row5) = true := by
  decide +kernel


-- @@ L35-38 verbatim
/-- Node audit for fixed branch (3, 32), starting at 256. -/
theorem coverageBranchNodes_3_32_00256 :
    nodeClaimChunkValidB branchClaims3Row32 256 12 = true := by
  decide +kernel


-- @@ L40-43 verbatim
/-- Node audit for fixed branch (5, 4), starting at 0. -/
theorem coverageBranchNodes_5_04_00000 :
    nodeClaimChunkValidB branchClaims5Row4 0 64 = true := by
  decide +kernel


-- @@ L45-48 verbatim
/-- Node audit for fixed branch (5, 4), starting at 64. -/
theorem coverageBranchNodes_5_04_00064 :
    nodeClaimChunkValidB branchClaims5Row4 64 50 = true := by
  decide +kernel


-- @@ L50-53 verbatim
/-- Node audit for fixed branch (5, 5), starting at 0. -/
theorem coverageBranchNodes_5_05_00000 :
    nodeClaimChunkValidB branchClaims5Row5 0 64 = true := by
  decide +kernel


-- @@ L55-55 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage
