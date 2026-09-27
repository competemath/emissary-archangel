/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData11
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
/-- Root audit for fixed branch (3, 18). -/
theorem coverageBranchRoot_3_18 :
    branchClaimRootValidB 3 18 (.patternThree 5) = true := by
  decide +kernel


-- @@ L25-28 verbatim
/-- Node audit for fixed branch (5, 31), starting at 192. -/
theorem coverageBranchNodes_5_31_00192 :
    nodeClaimChunkValidB branchClaims5Row31 192 64 = true := by
  decide +kernel


-- @@ L30-33 verbatim
/-- Node audit for fixed branch (5, 31), starting at 256. -/
theorem coverageBranchNodes_5_31_00256 :
    nodeClaimChunkValidB branchClaims5Row31 256 64 = true := by
  decide +kernel


-- @@ L35-38 verbatim
/-- Node audit for fixed branch (5, 31), starting at 320. -/
theorem coverageBranchNodes_5_31_00320 :
    nodeClaimChunkValidB branchClaims5Row31 320 32 = true := by
  decide +kernel


-- @@ L40-43 verbatim
/-- Node audit for fixed branch (5, 31), starting at 352. -/
theorem coverageBranchNodes_5_31_00352 :
    nodeClaimChunkValidB branchClaims5Row31 352 32 = true := by
  decide +kernel


-- @@ L45-45 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage
