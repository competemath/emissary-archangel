/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData10
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
/-- Root audit for fixed branch (3, 8). -/
theorem coverageBranchRoot_3_08 :
    branchClaimRootValidB 3 8 (.patternThree 4) = true := by
  decide +kernel


-- @@ L25-28 verbatim
/-- Root audit for fixed branch (5, 26). -/
theorem coverageBranchRoot_5_26 :
    branchClaimRootValidB 5 26 (.search branchClaims5Row26) = true := by
  decide +kernel


-- @@ L30-33 verbatim
/-- Node audit for fixed branch (5, 25), starting at 223. -/
theorem coverageBranchNodes_5_25_00223 :
    nodeClaimChunkValidB branchClaims5Row25 223 31 = true := by
  decide +kernel


-- @@ L35-38 verbatim
/-- Node audit for fixed branch (5, 26), starting at 0. -/
theorem coverageBranchNodes_5_26_00000 :
    nodeClaimChunkValidB branchClaims5Row26 0 64 = true := by
  decide +kernel


-- @@ L40-43 verbatim
/-- Node audit for fixed branch (5, 26), starting at 64. -/
theorem coverageBranchNodes_5_26_00064 :
    nodeClaimChunkValidB branchClaims5Row26 64 64 = true := by
  decide +kernel


-- @@ L45-48 verbatim
/-- Node audit for fixed branch (5, 26), starting at 128. -/
theorem coverageBranchNodes_5_26_00128 :
    nodeClaimChunkValidB branchClaims5Row26 128 64 = true := by
  decide +kernel


-- @@ L50-50 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage
