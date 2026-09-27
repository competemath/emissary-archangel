/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Uniformization.TriangleUniformizationGluing
import all LeanPool.HopfProblem.Uniformization.CuspUniformization1
import all LeanPool.HopfProblem.Uniformization.TriangleUniformizationGluing


-- @@ L13-17 verbatim
/-!
# Hopf problem: uniformization · cusp uniformization 3

Supporting definitions and proofs for this stage of the six-sphere construction.
-/



-- @@ L20-20 verbatim
open Set Function Filter Manifold Topology


-- @@ L22-25 verbatim
open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane


-- @@ L27-27 verbatim
universe u v


-- @@ L29-29 verbatim
noncomputable section


-- @@ L31-31 verbatim
namespace Mathoverflow1973


-- @@ L33-33 verbatim
local infixr:80 " ≫ₚ " => Path.trans


-- @@ L35-35 verbatim
local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f


-- @@ L37-40 verbatim
/-- A branch of the normalized logarithm centered at a nonzero point. -/
public
def CuspUniformization.localLog (z0 z : ℂ) : ℂ :=
  logarithm z0 + logarithm (z / z0)


-- @@ L42-49 verbatim
private theorem CuspUniformization.localLog_contDiffAt_of_mem_slitPlane {z0 z : ℂ}
    (hz : z / z0 ∈ Complex.slitPlane) : ContDiffAt ℂ ω (localLog z0) z := by
  change
    ContDiffAt ℂ ω (fun w : ℂ => logarithm z0 + Complex.log (w / z0) / (2 * Real.pi * Complex.I))
      z
  exact
    contDiffAt_const.add
      (((Complex.contDiffAt_log hz).comp z (contDiffAt_id.div_const z0)).div_const _)


-- @@ L51-53 verbatim
private theorem CuspUniformization.localLog_contDiffAt {z0 : ℂ} (hz0 : z0 ≠ 0) :
    ContDiffAt ℂ ω (localLog z0) z0 :=
  localLog_contDiffAt_of_mem_slitPlane (by simp [hz0])


-- @@ L55-58 verbatim
private theorem CuspUniformization.exponential_localLog {z0 z : ℂ} (hz0 : z0 ≠ 0) (hz : z ≠ 0) :
    exponential (localLog z0 z) = z := by
  rw [localLog, exponential_add, exponential_logarithm hz0,
    exponential_logarithm (div_ne_zero hz hz0), mul_div_cancel₀ _ hz0]


-- @@ L60-64 verbatim
public
theorem CuspUniformization.logarithm_eq_localLog_add_int {z0 z : ℂ} (hz0 : z0 ≠ 0) (hz : z ≠ 0) :
    ∃ n : ℤ, logarithm z = localLog z0 z + n := by
  apply (exponential_eq_iff (logarithm z) (localLog z0 z)).mp
  rw [exponential_logarithm hz, exponential_localLog hz0 hz]


-- @@ L66-66 verbatim
end Mathoverflow1973


-- @@ L68-68 verbatim
end
