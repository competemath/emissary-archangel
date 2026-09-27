/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData15
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
/-- Root audit for fixed branch (4, 17). -/
theorem coverageBranchRoot_4_17 :
    branchClaimRootValidB 4 17 (.patternTwo 0) = true := by
  decide +kernel


-- @@ L25-28 verbatim
/-- Node audit for fixed branch (6, 32), starting at 128. -/
theorem coverageBranchNodes_6_32_00128 :
    nodeClaimChunkValidB branchClaims6Row32 128 64 = true := by
  decide +kernel


-- @@ L30-33 verbatim
/-- Node audit for fixed branch (6, 32), starting at 192. -/
theorem coverageBranchNodes_6_32_00192 :
    nodeClaimChunkValidB branchClaims6Row32 192 64 = true := by
  decide +kernel


-- @@ L35-38 verbatim
/-- Node audit for fixed branch (6, 32), starting at 256. -/
theorem coverageBranchNodes_6_32_00256 :
    nodeClaimChunkValidB branchClaims6Row32 256 1 = true := by
  decide +kernel


-- @@ L40-40 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage
