/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData04
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
/-- Root audit for fixed branch (0, 27). -/
theorem coverageBranchRoot_0_27 :
    branchClaimRootValidB 0 27 (.patternTwo 0) = true := by
  decide +kernel


-- @@ L25-28 verbatim
/-- Root audit for fixed branch (5, 33). -/
theorem coverageBranchRoot_5_33 :
    branchClaimRootValidB 5 33 (.patternThree 3) = true := by
  decide +kernel


-- @@ L30-33 verbatim
/-- Root audit for fixed branch (2, 33). -/
theorem coverageBranchRoot_2_33 :
    branchClaimRootValidB 2 33 (.search branchClaims2Row33) = true := by
  decide +kernel


-- @@ L35-38 verbatim
/-- Node audit for fixed branch (2, 32), starting at 64. -/
theorem coverageBranchNodes_2_32_00064 :
    nodeClaimChunkValidB branchClaims2Row32 64 64 = true := by
  decide +kernel


-- @@ L40-43 verbatim
/-- Node audit for fixed branch (2, 32), starting at 128. -/
theorem coverageBranchNodes_2_32_00128 :
    nodeClaimChunkValidB branchClaims2Row32 128 64 = true := by
  decide +kernel


-- @@ L45-48 verbatim
/-- Node audit for fixed branch (2, 32), starting at 192. -/
theorem coverageBranchNodes_2_32_00192 :
    nodeClaimChunkValidB branchClaims2Row32 192 27 = true := by
  decide +kernel


-- @@ L50-53 verbatim
/-- Node audit for fixed branch (2, 33), starting at 0. -/
theorem coverageBranchNodes_2_33_00000 :
    nodeClaimChunkValidB branchClaims2Row33 0 64 = true := by
  decide +kernel


-- @@ L55-55 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage
