/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData09
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
/-- Root audit for fixed branch (3, 0). -/
theorem coverageBranchRoot_3_00 :
    branchClaimRootValidB 3 0 (.patternThree 1) = true := by
  decide +kernel


-- @@ L25-28 verbatim
/-- Node audit for fixed branch (5, 24), starting at 64. -/
theorem coverageBranchNodes_5_24_00064 :
    nodeClaimChunkValidB branchClaims5Row24 64 64 = true := by
  decide +kernel


-- @@ L30-33 verbatim
/-- Node audit for fixed branch (5, 24), starting at 128. -/
theorem coverageBranchNodes_5_24_00128 :
    nodeClaimChunkValidB branchClaims5Row24 128 64 = true := by
  decide +kernel


-- @@ L35-38 verbatim
/-- Node audit for fixed branch (5, 24), starting at 192. -/
theorem coverageBranchNodes_5_24_00192 :
    nodeClaimChunkValidB branchClaims5Row24 192 25 = true := by
  decide +kernel


-- @@ L40-43 verbatim
/-- Node audit for fixed branch (5, 24), starting at 217. -/
theorem coverageBranchNodes_5_24_00217 :
    nodeClaimChunkValidB branchClaims5Row24 217 25 = true := by
  decide +kernel


-- @@ L45-45 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage
