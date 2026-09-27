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
/-- Root audit for fixed branch (0, 3). -/
theorem coverageBranchRoot_0_03 :
    branchClaimRootValidB 0 3 (.patternTwo 0) = true := by
  decide +kernel


-- @@ L25-28 verbatim
/-- Root audit for fixed branch (4, 21). -/
theorem coverageBranchRoot_4_21 :
    branchClaimRootValidB 4 21 (.patternTwo 0) = true := by
  decide +kernel


-- @@ L30-33 verbatim
/-- Root audit for fixed branch (1, 16). -/
theorem coverageBranchRoot_1_16 :
    branchClaimRootValidB 1 16 (.search branchClaims1Row16) = true := by
  decide +kernel


-- @@ L35-38 verbatim
/-- Node audit for fixed branch (1, 9), starting at 64. -/
theorem coverageBranchNodes_1_09_00064 :
    nodeClaimChunkValidB branchClaims1Row9 64 64 = true := by
  decide +kernel


-- @@ L40-43 verbatim
/-- Node audit for fixed branch (1, 9), starting at 128. -/
theorem coverageBranchNodes_1_09_00128 :
    nodeClaimChunkValidB branchClaims1Row9 128 16 = true := by
  decide +kernel


-- @@ L45-48 verbatim
/-- Node audit for fixed branch (1, 16), starting at 0. -/
theorem coverageBranchNodes_1_16_00000 :
    nodeClaimChunkValidB branchClaims1Row16 0 64 = true := by
  decide +kernel


-- @@ L50-53 verbatim
/-- Node audit for fixed branch (1, 16), starting at 64. -/
theorem coverageBranchNodes_1_16_00064 :
    nodeClaimChunkValidB branchClaims1Row16 64 28 = true := by
  decide +kernel


-- @@ L55-55 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage
