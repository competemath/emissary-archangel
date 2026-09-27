/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData01
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
/-- Root audit for fixed branch (0, 10). -/
theorem coverageBranchRoot_0_10 :
    branchClaimRootValidB 0 10 (.patternTwo 0) = true := by
  decide +kernel


-- @@ L25-28 verbatim
/-- Root audit for fixed branch (4, 28). -/
theorem coverageBranchRoot_4_28 :
    branchClaimRootValidB 4 28 (.patternTwo 0) = true := by
  decide +kernel


-- @@ L30-33 verbatim
/-- Root audit for fixed branch (1, 32). -/
theorem coverageBranchRoot_1_32 :
    branchClaimRootValidB 1 32 (.search branchClaims1Row32) = true := by
  decide +kernel


-- @@ L35-38 verbatim
/-- Node audit for fixed branch (1, 31), starting at 128. -/
theorem coverageBranchNodes_1_31_00128 :
    nodeClaimChunkValidB branchClaims1Row31 128 64 = true := by
  decide +kernel


-- @@ L40-43 verbatim
/-- Node audit for fixed branch (1, 31), starting at 192. -/
theorem coverageBranchNodes_1_31_00192 :
    nodeClaimChunkValidB branchClaims1Row31 192 29 = true := by
  decide +kernel


-- @@ L45-48 verbatim
/-- Node audit for fixed branch (1, 31), starting at 221. -/
theorem coverageBranchNodes_1_31_00221 :
    nodeClaimChunkValidB branchClaims1Row31 221 29 = true := by
  decide +kernel


-- @@ L50-53 verbatim
/-- Node audit for fixed branch (1, 32), starting at 0. -/
theorem coverageBranchNodes_1_32_00000 :
    nodeClaimChunkValidB branchClaims1Row32 0 64 = true := by
  decide +kernel


-- @@ L55-55 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage
