/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData03
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
/-- Root audit for fixed branch (0, 20). -/
theorem coverageBranchRoot_0_20 :
    branchClaimRootValidB 0 20 (.patternTwo 0) = true := by
  decide +kernel


-- @@ L25-28 verbatim
/-- Root audit for fixed branch (5, 3). -/
theorem coverageBranchRoot_5_03 :
    branchClaimRootValidB 5 3 (.patternThree 180) = true := by
  decide +kernel


-- @@ L30-33 verbatim
/-- Root audit for fixed branch (2, 17). -/
theorem coverageBranchRoot_2_17 :
    branchClaimRootValidB 2 17 (.search branchClaims2Row17) = true := by
  decide +kernel


-- @@ L35-38 verbatim
/-- Root audit for fixed branch (2, 18). -/
theorem coverageBranchRoot_2_18 :
    branchClaimRootValidB 2 18 (.search branchClaims2Row18) = true := by
  decide +kernel


-- @@ L40-43 verbatim
/-- Node audit for fixed branch (2, 17), starting at 0. -/
theorem coverageBranchNodes_2_17_00000 :
    nodeClaimChunkValidB branchClaims2Row17 0 64 = true := by
  decide +kernel


-- @@ L45-48 verbatim
/-- Node audit for fixed branch (2, 17), starting at 64. -/
theorem coverageBranchNodes_2_17_00064 :
    nodeClaimChunkValidB branchClaims2Row17 64 60 = true := by
  decide +kernel


-- @@ L50-53 verbatim
/-- Node audit for fixed branch (2, 18), starting at 0. -/
theorem coverageBranchNodes_2_18_00000 :
    nodeClaimChunkValidB branchClaims2Row18 0 64 = true := by
  decide +kernel


-- @@ L55-58 verbatim
/-- Node audit for fixed branch (2, 18), starting at 64. -/
theorem coverageBranchNodes_2_18_00064 :
    nodeClaimChunkValidB branchClaims2Row18 64 64 = true := by
  decide +kernel


-- @@ L60-60 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage
