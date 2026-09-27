/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData00
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
/-- Root audit for fixed branch (0, 5). -/
theorem coverageBranchRoot_0_05 :
    branchClaimRootValidB 0 5 (.patternTwo 0) = true := by
  decide +kernel


-- @@ L25-28 verbatim
/-- Root audit for fixed branch (4, 23). -/
theorem coverageBranchRoot_4_23 :
    branchClaimRootValidB 4 23 (.patternTwo 0) = true := by
  decide +kernel


-- @@ L30-33 verbatim
/-- Root audit for fixed branch (1, 19). -/
theorem coverageBranchRoot_1_19 :
    branchClaimRootValidB 1 19 (.search branchClaims1Row19) = true := by
  decide +kernel


-- @@ L35-38 verbatim
/-- Root audit for fixed branch (1, 26). -/
theorem coverageBranchRoot_1_26 :
    branchClaimRootValidB 1 26 (.search branchClaims1Row26) = true := by
  decide +kernel


-- @@ L40-43 verbatim
/-- Node audit for fixed branch (1, 18), starting at 64. -/
theorem coverageBranchNodes_1_18_00064 :
    nodeClaimChunkValidB branchClaims1Row18 64 42 = true := by
  decide +kernel


-- @@ L45-48 verbatim
/-- Node audit for fixed branch (1, 19), starting at 0. -/
theorem coverageBranchNodes_1_19_00000 :
    nodeClaimChunkValidB branchClaims1Row19 0 64 = true := by
  decide +kernel


-- @@ L50-53 verbatim
/-- Node audit for fixed branch (1, 19), starting at 64. -/
theorem coverageBranchNodes_1_19_00064 :
    nodeClaimChunkValidB branchClaims1Row19 64 53 = true := by
  decide +kernel


-- @@ L55-58 verbatim
/-- Node audit for fixed branch (1, 26), starting at 0. -/
theorem coverageBranchNodes_1_26_00000 :
    nodeClaimChunkValidB branchClaims1Row26 0 64 = true := by
  decide +kernel


-- @@ L60-60 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage
