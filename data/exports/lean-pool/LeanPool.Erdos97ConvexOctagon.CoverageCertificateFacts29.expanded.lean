/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData04
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
/-- Root audit for fixed branch (0, 29). -/
theorem coverageBranchRoot_0_29 :
    branchClaimRootValidB 0 29 (.patternTwo 0) = true := by
  decide +kernel


-- @@ L25-28 verbatim
/-- Root audit for fixed branch (6, 19). -/
theorem coverageBranchRoot_6_19 :
    branchClaimRootValidB 6 19 (.patternThree 6) = true := by
  decide +kernel


-- @@ L30-33 verbatim
/-- Root audit for fixed branch (3, 1). -/
theorem coverageBranchRoot_3_01 :
    branchClaimRootValidB 3 1 (.search branchClaims3Row1) = true := by
  decide +kernel


-- @@ L35-38 verbatim
/-- Root audit for fixed branch (3, 2). -/
theorem coverageBranchRoot_3_02 :
    branchClaimRootValidB 3 2 (.search branchClaims3Row2) = true := by
  decide +kernel


-- @@ L40-43 verbatim
/-- Node audit for fixed branch (2, 34), starting at 128. -/
theorem coverageBranchNodes_2_34_00128 :
    nodeClaimChunkValidB branchClaims2Row34 128 34 = true := by
  decide +kernel


-- @@ L45-48 verbatim
/-- Node audit for fixed branch (3, 1), starting at 0. -/
theorem coverageBranchNodes_3_01_00000 :
    nodeClaimChunkValidB branchClaims3Row1 0 64 = true := by
  decide +kernel


-- @@ L50-53 verbatim
/-- Node audit for fixed branch (3, 1), starting at 64. -/
theorem coverageBranchNodes_3_01_00064 :
    nodeClaimChunkValidB branchClaims3Row1 64 47 = true := by
  decide +kernel


-- @@ L55-58 verbatim
/-- Node audit for fixed branch (3, 2), starting at 0. -/
theorem coverageBranchNodes_3_02_00000 :
    nodeClaimChunkValidB branchClaims3Row2 0 64 = true := by
  decide +kernel


-- @@ L60-60 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage
