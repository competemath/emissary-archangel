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
/-- Root audit for fixed branch (3, 29). -/
theorem coverageBranchRoot_3_29 :
    branchClaimRootValidB 3 29 (.patternThree 6) = true := by
  decide +kernel


-- @@ L25-28 verbatim
/-- Root audit for fixed branch (6, 1). -/
theorem coverageBranchRoot_6_01 :
    branchClaimRootValidB 6 1 (.search branchClaims6Row1) = true := by
  decide +kernel


-- @@ L30-33 verbatim
/-- Node audit for fixed branch (5, 34), starting at 320. -/
theorem coverageBranchNodes_5_34_00320 :
    nodeClaimChunkValidB branchClaims5Row34 320 64 = true := by
  decide +kernel


-- @@ L35-38 verbatim
/-- Node audit for fixed branch (5, 34), starting at 384. -/
theorem coverageBranchNodes_5_34_00384 :
    nodeClaimChunkValidB branchClaims5Row34 384 6 = true := by
  decide +kernel


-- @@ L40-43 verbatim
/-- Node audit for fixed branch (6, 1), starting at 0. -/
theorem coverageBranchNodes_6_01_00000 :
    nodeClaimChunkValidB branchClaims6Row1 0 32 = true := by
  decide +kernel


-- @@ L45-48 verbatim
/-- Node audit for fixed branch (6, 1), starting at 32. -/
theorem coverageBranchNodes_6_01_00032 :
    nodeClaimChunkValidB branchClaims6Row1 32 32 = true := by
  decide +kernel


-- @@ L50-50 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage
