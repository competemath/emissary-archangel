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
/-- Root audit for fixed branch (3, 14). -/
theorem coverageBranchRoot_3_14 :
    branchClaimRootValidB 3 14 (.patternThree 4) = true := by
  decide +kernel


-- @@ L25-28 verbatim
/-- Root audit for fixed branch (5, 28). -/
theorem coverageBranchRoot_5_28 :
    branchClaimRootValidB 5 28 (.search branchClaims5Row28) = true := by
  decide +kernel


-- @@ L30-33 verbatim
/-- Node audit for fixed branch (5, 27), starting at 384. -/
theorem coverageBranchNodes_5_27_00384 :
    nodeClaimChunkValidB branchClaims5Row27 384 8 = true := by
  decide +kernel


-- @@ L35-38 verbatim
/-- Node audit for fixed branch (5, 28), starting at 0. -/
theorem coverageBranchNodes_5_28_00000 :
    nodeClaimChunkValidB branchClaims5Row28 0 64 = true := by
  decide +kernel


-- @@ L40-43 verbatim
/-- Node audit for fixed branch (5, 28), starting at 64. -/
theorem coverageBranchNodes_5_28_00064 :
    nodeClaimChunkValidB branchClaims5Row28 64 32 = true := by
  decide +kernel


-- @@ L45-48 verbatim
/-- Node audit for fixed branch (5, 28), starting at 96. -/
theorem coverageBranchNodes_5_28_00096 :
    nodeClaimChunkValidB branchClaims5Row28 96 32 = true := by
  decide +kernel


-- @@ L50-50 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage
