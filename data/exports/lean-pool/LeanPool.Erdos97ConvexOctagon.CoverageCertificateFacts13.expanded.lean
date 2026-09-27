/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData02
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
/-- Root audit for fixed branch (0, 13). -/
theorem coverageBranchRoot_0_13 :
    branchClaimRootValidB 0 13 (.patternTwo 0) = true := by
  decide +kernel


-- @@ L25-28 verbatim
/-- Root audit for fixed branch (4, 31). -/
theorem coverageBranchRoot_4_31 :
    branchClaimRootValidB 4 31 (.patternTwo 0) = true := by
  decide +kernel


-- @@ L30-33 verbatim
/-- Root audit for fixed branch (2, 1). -/
theorem coverageBranchRoot_2_01 :
    branchClaimRootValidB 2 1 (.search branchClaims2Row1) = true := by
  decide +kernel


-- @@ L35-38 verbatim
/-- Root audit for fixed branch (2, 2). -/
theorem coverageBranchRoot_2_02 :
    branchClaimRootValidB 2 2 (.search branchClaims2Row2) = true := by
  decide +kernel


-- @@ L40-43 verbatim
/-- Node audit for fixed branch (1, 34), starting at 64. -/
theorem coverageBranchNodes_1_34_00064 :
    nodeClaimChunkValidB branchClaims1Row34 64 41 = true := by
  decide +kernel


-- @@ L45-48 verbatim
/-- Node audit for fixed branch (2, 1), starting at 0. -/
theorem coverageBranchNodes_2_01_00000 :
    nodeClaimChunkValidB branchClaims2Row1 0 64 = true := by
  decide +kernel


-- @@ L50-53 verbatim
/-- Node audit for fixed branch (2, 1), starting at 64. -/
theorem coverageBranchNodes_2_01_00064 :
    nodeClaimChunkValidB branchClaims2Row1 64 46 = true := by
  decide +kernel


-- @@ L55-58 verbatim
/-- Node audit for fixed branch (2, 2), starting at 0. -/
theorem coverageBranchNodes_2_02_00000 :
    nodeClaimChunkValidB branchClaims2Row2 0 64 = true := by
  decide +kernel


-- @@ L60-60 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage
