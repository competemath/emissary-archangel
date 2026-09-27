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
/-- Root audit for fixed branch (0, 24). -/
theorem coverageBranchRoot_0_24 :
    branchClaimRootValidB 0 24 (.patternTwo 0) = true := by
  decide +kernel


-- @@ L25-28 verbatim
/-- Root audit for fixed branch (5, 22). -/
theorem coverageBranchRoot_5_22 :
    branchClaimRootValidB 5 22 (.patternThree 1) = true := by
  decide +kernel


-- @@ L30-33 verbatim
/-- Root audit for fixed branch (2, 29). -/
theorem coverageBranchRoot_2_29 :
    branchClaimRootValidB 2 29 (.search branchClaims2Row29) = true := by
  decide +kernel


-- @@ L35-38 verbatim
/-- Root audit for fixed branch (2, 30). -/
theorem coverageBranchRoot_2_30 :
    branchClaimRootValidB 2 30 (.search branchClaims2Row30) = true := by
  decide +kernel


-- @@ L40-43 verbatim
/-- Node audit for fixed branch (2, 28), starting at 64. -/
theorem coverageBranchNodes_2_28_00064 :
    nodeClaimChunkValidB branchClaims2Row28 64 32 = true := by
  decide +kernel


-- @@ L45-48 verbatim
/-- Node audit for fixed branch (2, 29), starting at 0. -/
theorem coverageBranchNodes_2_29_00000 :
    nodeClaimChunkValidB branchClaims2Row29 0 64 = true := by
  decide +kernel


-- @@ L50-53 verbatim
/-- Node audit for fixed branch (2, 29), starting at 64. -/
theorem coverageBranchNodes_2_29_00064 :
    nodeClaimChunkValidB branchClaims2Row29 64 39 = true := by
  decide +kernel


-- @@ L55-58 verbatim
/-- Node audit for fixed branch (2, 30), starting at 0. -/
theorem coverageBranchNodes_2_30_00000 :
    nodeClaimChunkValidB branchClaims2Row30 0 64 = true := by
  decide +kernel


-- @@ L60-60 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage
