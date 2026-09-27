/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData12
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
/-- Root audit for fixed branch (3, 33). -/
theorem coverageBranchRoot_3_33 :
    branchClaimRootValidB 3 33 (.patternThree 6) = true := by
  decide +kernel


-- @@ L25-28 verbatim
/-- Root audit for fixed branch (6, 2). -/
theorem coverageBranchRoot_6_02 :
    branchClaimRootValidB 6 2 (.search branchClaims6Row2) = true := by
  decide +kernel


-- @@ L30-33 verbatim
/-- Root audit for fixed branch (6, 3). -/
theorem coverageBranchRoot_6_03 :
    branchClaimRootValidB 6 3 (.search branchClaims6Row3) = true := by
  decide +kernel


-- @@ L35-38 verbatim
/-- Root audit for fixed branch (6, 4). -/
theorem coverageBranchRoot_6_04 :
    branchClaimRootValidB 6 4 (.search branchClaims6Row4) = true := by
  decide +kernel


-- @@ L40-43 verbatim
/-- Node audit for fixed branch (6, 1), starting at 64. -/
theorem coverageBranchNodes_6_01_00064 :
    nodeClaimChunkValidB branchClaims6Row1 64 1 = true := by
  decide +kernel


-- @@ L45-48 verbatim
/-- Node audit for fixed branch (6, 2), starting at 0. -/
theorem coverageBranchNodes_6_02_00000 :
    nodeClaimChunkValidB branchClaims6Row2 0 52 = true := by
  decide +kernel


-- @@ L50-53 verbatim
/-- Node audit for fixed branch (6, 3), starting at 0. -/
theorem coverageBranchNodes_6_03_00000 :
    nodeClaimChunkValidB branchClaims6Row3 0 42 = true := by
  decide +kernel


-- @@ L55-58 verbatim
/-- Node audit for fixed branch (6, 4), starting at 0. -/
theorem coverageBranchNodes_6_04_00000 :
    nodeClaimChunkValidB branchClaims6Row4 0 51 = true := by
  decide +kernel


-- @@ L60-60 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage
