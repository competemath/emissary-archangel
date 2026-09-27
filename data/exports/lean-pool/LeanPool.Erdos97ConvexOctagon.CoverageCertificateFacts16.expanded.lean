/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.Erdos97ConvexOctagon.CoverageCertificateData02
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
/-- Root audit for fixed branch (0, 16). -/
theorem coverageBranchRoot_0_16 :
    branchClaimRootValidB 0 16 (.patternTwo 0) = true := by
  decide +kernel


-- @@ L25-28 verbatim
/-- Root audit for fixed branch (4, 34). -/
theorem coverageBranchRoot_4_34 :
    branchClaimRootValidB 4 34 (.patternTwo 0) = true := by
  decide +kernel


-- @@ L30-33 verbatim
/-- Root audit for fixed branch (2, 8). -/
theorem coverageBranchRoot_2_08 :
    branchClaimRootValidB 2 8 (.search branchClaims2Row8) = true := by
  decide +kernel


-- @@ L35-38 verbatim
/-- Node audit for fixed branch (2, 6), starting at 64. -/
theorem coverageBranchNodes_2_06_00064 :
    nodeClaimChunkValidB branchClaims2Row6 64 45 = true := by
  decide +kernel


-- @@ L40-43 verbatim
/-- Node audit for fixed branch (2, 8), starting at 0. -/
theorem coverageBranchNodes_2_08_00000 :
    nodeClaimChunkValidB branchClaims2Row8 0 64 = true := by
  decide +kernel


-- @@ L45-48 verbatim
/-- Node audit for fixed branch (2, 8), starting at 64. -/
theorem coverageBranchNodes_2_08_00064 :
    nodeClaimChunkValidB branchClaims2Row8 64 64 = true := by
  decide +kernel


-- @@ L50-53 verbatim
/-- Node audit for fixed branch (2, 8), starting at 128. -/
theorem coverageBranchNodes_2_08_00128 :
    nodeClaimChunkValidB branchClaims2Row8 128 36 = true := by
  decide +kernel


-- @@ L55-55 verbatim
end Erdos97Octagon.RawIncidence.StaticDirectCoverage
