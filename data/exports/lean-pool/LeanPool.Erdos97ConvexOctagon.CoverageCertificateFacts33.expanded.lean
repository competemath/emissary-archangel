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
/-- Root audit for fixed branch (0, 33). -/
theorem coverageBranchRoot_0_33 :
    branchClaimRootValidB 0 33 (.patternTwo 0) = true := by
  decide +kernel


-- @@ L25-28 verbatim
/-- Root audit for fixed branch (6, 29). -/
theorem coverageBranchRoot_6_29 :
    branchClaimRootValidB 6 29 (.patternThree 6) = true := by
  decide +kernel


-- @@ L30-33 verbatim
/-- Root audit for fixed branch (3, 11). -/
theorem coverageBranchRoot_3_11 :
    branchClaimRootValidB 3 11 (.search branchClaims3Row11) = true := by
  decide +kernel


-- @@ L35-38 verbatim
/-- Root audit for fixed branch (3, 12). -/
theorem coverageBranchRoot_3_12 :
    branchClaimRootValidB 3 12 (.search branchClaims3Row12) = true := by
  decide +kernel


-- @@ L40-43 verbatim
/-- Node audit for fixed branch (3, 11), starting at 0. -/
theorem coverageBranchNodes_3_11_00000 :
    nodeClaimChunkValidB branchClaims3Row11 0 64 = true := by
  decide +kernel


-- @@ L45-48 verbatim
/-- Node audit for fixed branch (3, 11), starting at 64. -/
theorem coverageBranchNodes_3_11_00064 :
    nodeClaimChunkValidB branchClaims3Row11 64 49 = true := by
  decide +kernel


-- @@ L50-53 verbatim
/-- Node audit for fixed branch (3, 12), starting at 0. -/
theorem coverageBranchNodes_3_12_00000 :
    nodeClaimChunkValidB branchClaims3Row12 0 64 = true := by
  decide +kernel


-- @@ L55-58 verbatim
/-- Node audit for fixed branch (3, 12), starting at 64. -/
theorem coverageBranchNodes_3_12_00064 :
    nodeClaimChunkValidB branchClaims3Row12 64 43 = true := by
  decide +kernel


-- @@ L60-60 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage
