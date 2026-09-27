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
/-- Root audit for fixed branch (0, 15). -/
theorem coverageBranchRoot_0_15 :
    branchClaimRootValidB 0 15 (.patternTwo 0) = true := by
  decide +kernel


-- @@ L25-28 verbatim
/-- Root audit for fixed branch (4, 33). -/
theorem coverageBranchRoot_4_33 :
    branchClaimRootValidB 4 33 (.patternTwo 0) = true := by
  decide +kernel


-- @@ L30-33 verbatim
/-- Root audit for fixed branch (2, 5). -/
theorem coverageBranchRoot_2_05 :
    branchClaimRootValidB 2 5 (.search branchClaims2Row5) = true := by
  decide +kernel


-- @@ L35-38 verbatim
/-- Root audit for fixed branch (2, 6). -/
theorem coverageBranchRoot_2_06 :
    branchClaimRootValidB 2 6 (.search branchClaims2Row6) = true := by
  decide +kernel


-- @@ L40-43 verbatim
/-- Node audit for fixed branch (2, 4), starting at 64. -/
theorem coverageBranchNodes_2_04_00064 :
    nodeClaimChunkValidB branchClaims2Row4 64 50 = true := by
  decide +kernel


-- @@ L45-48 verbatim
/-- Node audit for fixed branch (2, 5), starting at 0. -/
theorem coverageBranchNodes_2_05_00000 :
    nodeClaimChunkValidB branchClaims2Row5 0 64 = true := by
  decide +kernel


-- @@ L50-53 verbatim
/-- Node audit for fixed branch (2, 5), starting at 64. -/
theorem coverageBranchNodes_2_05_00064 :
    nodeClaimChunkValidB branchClaims2Row5 64 61 = true := by
  decide +kernel


-- @@ L55-58 verbatim
/-- Node audit for fixed branch (2, 6), starting at 0. -/
theorem coverageBranchNodes_2_06_00000 :
    nodeClaimChunkValidB branchClaims2Row6 0 64 = true := by
  decide +kernel


-- @@ L60-60 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage
