/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData13
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
/-- Root audit for fixed branch (4, 6). -/
theorem coverageBranchRoot_4_06 :
    branchClaimRootValidB 4 6 (.patternTwo 0) = true := by
  decide +kernel


-- @@ L25-28 verbatim
/-- Root audit for fixed branch (6, 17). -/
theorem coverageBranchRoot_6_17 :
    branchClaimRootValidB 6 17 (.search branchClaims6Row17) = true := by
  decide +kernel


-- @@ L30-33 verbatim
/-- Node audit for fixed branch (6, 16), starting at 64. -/
theorem coverageBranchNodes_6_16_00064 :
    nodeClaimChunkValidB branchClaims6Row16 64 54 = true := by
  decide +kernel


-- @@ L35-38 verbatim
/-- Node audit for fixed branch (6, 17), starting at 0. -/
theorem coverageBranchNodes_6_17_00000 :
    nodeClaimChunkValidB branchClaims6Row17 0 64 = true := by
  decide +kernel


-- @@ L40-43 verbatim
/-- Node audit for fixed branch (6, 17), starting at 64. -/
theorem coverageBranchNodes_6_17_00064 :
    nodeClaimChunkValidB branchClaims6Row17 64 64 = true := by
  decide +kernel


-- @@ L45-48 verbatim
/-- Node audit for fixed branch (6, 17), starting at 128. -/
theorem coverageBranchNodes_6_17_00128 :
    nodeClaimChunkValidB branchClaims6Row17 128 43 = true := by
  decide +kernel


-- @@ L50-50 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage
