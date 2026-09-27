/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData14
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
/-- Root audit for fixed branch (4, 12). -/
theorem coverageBranchRoot_4_12 :
    branchClaimRootValidB 4 12 (.patternTwo 0) = true := by
  decide +kernel


-- @@ L25-28 verbatim
/-- Root audit for fixed branch (6, 27). -/
theorem coverageBranchRoot_6_27 :
    branchClaimRootValidB 6 27 (.search branchClaims6Row27) = true := by
  decide +kernel


-- @@ L30-33 verbatim
/-- Node audit for fixed branch (6, 27), starting at 0. -/
theorem coverageBranchNodes_6_27_00000 :
    nodeClaimChunkValidB branchClaims6Row27 0 64 = true := by
  decide +kernel


-- @@ L35-38 verbatim
/-- Node audit for fixed branch (6, 27), starting at 64. -/
theorem coverageBranchNodes_6_27_00064 :
    nodeClaimChunkValidB branchClaims6Row27 64 64 = true := by
  decide +kernel


-- @@ L40-43 verbatim
/-- Node audit for fixed branch (6, 27), starting at 128. -/
theorem coverageBranchNodes_6_27_00128 :
    nodeClaimChunkValidB branchClaims6Row27 128 64 = true := by
  decide +kernel


-- @@ L45-48 verbatim
/-- Node audit for fixed branch (6, 27), starting at 192. -/
theorem coverageBranchNodes_6_27_00192 :
    nodeClaimChunkValidB branchClaims6Row27 192 32 = true := by
  decide +kernel


-- @@ L50-50 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage
