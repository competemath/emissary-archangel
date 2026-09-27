/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData05
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
/-- Root audit for fixed branch (1, 0). -/
theorem coverageBranchRoot_1_00 :
    branchClaimRootValidB 1 0 (.patternThree 1) = true := by
  decide +kernel


-- @@ L25-28 verbatim
/-- Root audit for fixed branch (6, 34). -/
theorem coverageBranchRoot_6_34 :
    branchClaimRootValidB 6 34 (.patternThree 6) = true := by
  decide +kernel


-- @@ L30-33 verbatim
/-- Root audit for fixed branch (3, 24). -/
theorem coverageBranchRoot_3_24 :
    branchClaimRootValidB 3 24 (.search branchClaims3Row24) = true := by
  decide +kernel


-- @@ L35-38 verbatim
/-- Node audit for fixed branch (3, 23), starting at 256. -/
theorem coverageBranchNodes_3_23_00256 :
    nodeClaimChunkValidB branchClaims3Row23 256 41 = true := by
  decide +kernel


-- @@ L40-43 verbatim
/-- Node audit for fixed branch (3, 24), starting at 0. -/
theorem coverageBranchNodes_3_24_00000 :
    nodeClaimChunkValidB branchClaims3Row24 0 64 = true := by
  decide +kernel


-- @@ L45-48 verbatim
/-- Node audit for fixed branch (3, 24), starting at 64. -/
theorem coverageBranchNodes_3_24_00064 :
    nodeClaimChunkValidB branchClaims3Row24 64 64 = true := by
  decide +kernel


-- @@ L50-53 verbatim
/-- Node audit for fixed branch (3, 24), starting at 128. -/
theorem coverageBranchNodes_3_24_00128 :
    nodeClaimChunkValidB branchClaims3Row24 128 64 = true := by
  decide +kernel


-- @@ L55-55 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage
