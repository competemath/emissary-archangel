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
/-- Root audit for fixed branch (0, 9). -/
theorem coverageBranchRoot_0_09 :
    branchClaimRootValidB 0 9 (.patternTwo 0) = true := by
  decide +kernel


-- @@ L25-28 verbatim
/-- Root audit for fixed branch (4, 27). -/
theorem coverageBranchRoot_4_27 :
    branchClaimRootValidB 4 27 (.patternTwo 0) = true := by
  decide +kernel


-- @@ L30-33 verbatim
/-- Root audit for fixed branch (1, 31). -/
theorem coverageBranchRoot_1_31 :
    branchClaimRootValidB 1 31 (.search branchClaims1Row31) = true := by
  decide +kernel


-- @@ L35-38 verbatim
/-- Node audit for fixed branch (1, 30), starting at 192. -/
theorem coverageBranchNodes_1_30_00192 :
    nodeClaimChunkValidB branchClaims1Row30 192 64 = true := by
  decide +kernel


-- @@ L40-43 verbatim
/-- Node audit for fixed branch (1, 30), starting at 256. -/
theorem coverageBranchNodes_1_30_00256 :
    nodeClaimChunkValidB branchClaims1Row30 256 19 = true := by
  decide +kernel


-- @@ L45-48 verbatim
/-- Node audit for fixed branch (1, 31), starting at 0. -/
theorem coverageBranchNodes_1_31_00000 :
    nodeClaimChunkValidB branchClaims1Row31 0 64 = true := by
  decide +kernel


-- @@ L50-53 verbatim
/-- Node audit for fixed branch (1, 31), starting at 64. -/
theorem coverageBranchNodes_1_31_00064 :
    nodeClaimChunkValidB branchClaims1Row31 64 64 = true := by
  decide +kernel


-- @@ L55-55 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage
