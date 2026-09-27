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
/-- Root audit for fixed branch (0, 23). -/
theorem coverageBranchRoot_0_23 :
    branchClaimRootValidB 0 23 (.patternTwo 0) = true := by
  decide +kernel


-- @@ L25-28 verbatim
/-- Root audit for fixed branch (5, 21). -/
theorem coverageBranchRoot_5_21 :
    branchClaimRootValidB 5 21 (.patternThree 1) = true := by
  decide +kernel


-- @@ L30-33 verbatim
/-- Root audit for fixed branch (2, 27). -/
theorem coverageBranchRoot_2_27 :
    branchClaimRootValidB 2 27 (.search branchClaims2Row27) = true := by
  decide +kernel


-- @@ L35-38 verbatim
/-- Root audit for fixed branch (2, 28). -/
theorem coverageBranchRoot_2_28 :
    branchClaimRootValidB 2 28 (.search branchClaims2Row28) = true := by
  decide +kernel


-- @@ L40-43 verbatim
/-- Node audit for fixed branch (2, 26), starting at 64. -/
theorem coverageBranchNodes_2_26_00064 :
    nodeClaimChunkValidB branchClaims2Row26 64 34 = true := by
  decide +kernel


-- @@ L45-48 verbatim
/-- Node audit for fixed branch (2, 27), starting at 0. -/
theorem coverageBranchNodes_2_27_00000 :
    nodeClaimChunkValidB branchClaims2Row27 0 64 = true := by
  decide +kernel


-- @@ L50-53 verbatim
/-- Node audit for fixed branch (2, 27), starting at 64. -/
theorem coverageBranchNodes_2_27_00064 :
    nodeClaimChunkValidB branchClaims2Row27 64 26 = true := by
  decide +kernel


-- @@ L55-58 verbatim
/-- Node audit for fixed branch (2, 28), starting at 0. -/
theorem coverageBranchNodes_2_28_00000 :
    nodeClaimChunkValidB branchClaims2Row28 0 64 = true := by
  decide +kernel


-- @@ L60-60 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage
