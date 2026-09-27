/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData06
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
/-- Root audit for fixed branch (1, 3). -/
theorem coverageBranchRoot_1_03 :
    branchClaimRootValidB 1 3 (.patternThree 178) = true := by
  decide +kernel


-- @@ L25-28 verbatim
/-- Root audit for fixed branch (3, 26). -/
theorem coverageBranchRoot_3_26 :
    branchClaimRootValidB 3 26 (.search branchClaims3Row26) = true := by
  decide +kernel


-- @@ L30-33 verbatim
/-- Node audit for fixed branch (3, 25), starting at 320. -/
theorem coverageBranchNodes_3_25_00320 :
    nodeClaimChunkValidB branchClaims3Row25 320 21 = true := by
  decide +kernel


-- @@ L35-38 verbatim
/-- Node audit for fixed branch (3, 26), starting at 0. -/
theorem coverageBranchNodes_3_26_00000 :
    nodeClaimChunkValidB branchClaims3Row26 0 64 = true := by
  decide +kernel


-- @@ L40-43 verbatim
/-- Node audit for fixed branch (3, 26), starting at 64. -/
theorem coverageBranchNodes_3_26_00064 :
    nodeClaimChunkValidB branchClaims3Row26 64 64 = true := by
  decide +kernel


-- @@ L45-48 verbatim
/-- Node audit for fixed branch (3, 26), starting at 128. -/
theorem coverageBranchNodes_3_26_00128 :
    nodeClaimChunkValidB branchClaims3Row26 128 64 = true := by
  decide +kernel


-- @@ L50-50 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage
