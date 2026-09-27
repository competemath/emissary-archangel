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
/-- Root audit for fixed branch (0, 17). -/
theorem coverageBranchRoot_0_17 :
    branchClaimRootValidB 0 17 (.patternTwo 0) = true := by
  decide +kernel


-- @@ L25-28 verbatim
/-- Root audit for fixed branch (5, 0). -/
theorem coverageBranchRoot_5_00 :
    branchClaimRootValidB 5 0 (.patternThree 1) = true := by
  decide +kernel


-- @@ L30-33 verbatim
/-- Root audit for fixed branch (2, 9). -/
theorem coverageBranchRoot_2_09 :
    branchClaimRootValidB 2 9 (.search branchClaims2Row9) = true := by
  decide +kernel


-- @@ L35-38 verbatim
/-- Root audit for fixed branch (2, 10). -/
theorem coverageBranchRoot_2_10 :
    branchClaimRootValidB 2 10 (.search branchClaims2Row10) = true := by
  decide +kernel


-- @@ L40-43 verbatim
/-- Node audit for fixed branch (2, 9), starting at 0. -/
theorem coverageBranchNodes_2_09_00000 :
    nodeClaimChunkValidB branchClaims2Row9 0 64 = true := by
  decide +kernel


-- @@ L45-48 verbatim
/-- Node audit for fixed branch (2, 9), starting at 64. -/
theorem coverageBranchNodes_2_09_00064 :
    nodeClaimChunkValidB branchClaims2Row9 64 64 = true := by
  decide +kernel


-- @@ L50-53 verbatim
/-- Node audit for fixed branch (2, 9), starting at 128. -/
theorem coverageBranchNodes_2_09_00128 :
    nodeClaimChunkValidB branchClaims2Row9 128 54 = true := by
  decide +kernel


-- @@ L55-58 verbatim
/-- Node audit for fixed branch (2, 10), starting at 0. -/
theorem coverageBranchNodes_2_10_00000 :
    nodeClaimChunkValidB branchClaims2Row10 0 15 = true := by
  decide +kernel


-- @@ L60-60 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage
