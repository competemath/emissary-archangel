/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonCutoffs
public import LeanPool.NavierStokesAndEuler.ForMathlib.SobolevThreeDimensional
import Mathlib.Algebra.Order.Ring.Star


-- @@ L13-19 verbatim
/-!
# Homogeneous Sobolev bounds for smooth square-integrable functions

Spatial cutoffs extend the compactly supported Sobolev inequality to a smooth
function whose value and derivative belong to `L²`. The derivative of the
cutoff contributes an error tending to zero; Fatou's lemma passes to the limit.
-/


-- @@ L21-21 verbatim
@[expose] public section




-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
open MeasureTheory Filter

-- @@ L28-28 verbatim
open scoped ContDiff ENNReal Topology


-- @@ L30-30 verbatim
namespace NavierStokesR3.RieszTestOperators


-- @@ L32-32 verbatim
open ProblemStatement ComparisonCutoffs


-- @@ L34-34 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


-- @@ L36-41 verbatim
/-- The product rule with a uniformly bounded spatial cutoff. -/
theorem norm_fderiv_cutoff_smul_le {f : Space → E} (hf : ContDiff ℝ 1 f)
    {R : ℝ} (hR : 0 < R) (x : Space) :
    ‖fderiv ℝ (fun y => cutoff R y • f y) x‖ ≤
      ‖fderiv ℝ f x‖ + (derivativeConstant 1 / R) * ‖f x‖ :=
  NavierStokesAndEuler.SobolevThreeDimensional.norm_fderiv_cutoff_smul_le hf hR x


-- @@ L43-49 verbatim
/-- The cutoff derivative has a vanishing `L²` error. -/
theorem eLpNorm_fderiv_cutoff_smul_le {f : Space → E} (hf : ContDiff ℝ 1 f)
    {R : ℝ} (hR : 0 < R) :
    eLpNorm (fderiv ℝ (fun y => cutoff R y • f y)) 2 volume ≤
      eLpNorm (fderiv ℝ f) 2 volume +
        ENNReal.ofReal (derivativeConstant 1 / R) * eLpNorm f 2 volume :=
  NavierStokesAndEuler.SobolevThreeDimensional.eLpNorm_fderiv_cutoff_smul_le hf hR


-- @@ L51-59 verbatim
/-- The homogeneous `H¹ → L⁶` inequality without a support assumption.
Only the function itself must have finite `L²` norm for this extended-norm
inequality; the right side may be infinite. -/
theorem smooth_eLpNorm_six_le {f : Space → E} (hf : ContDiff ℝ 1 f)
    (h2 : MemLp f 2 volume) :
    eLpNorm f 6 volume ≤
      (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Space) 2 : ℝ≥0∞) *
        eLpNorm (fderiv ℝ f) 2 volume :=
  NavierStokesAndEuler.SobolevThreeDimensional.eLpNorm_six_le hf h2


-- @@ L61-66 verbatim
/-- A smooth function with square-integrable value and derivative belongs to
`L⁶`, with no support hypothesis. -/
theorem smooth_memLp_six {f : Space → E} (hf : ContDiff ℝ 1 f)
    (h2 : MemLp f 2 volume) (hD2 : MemLp (fderiv ℝ f) 2 volume) :
    MemLp f 6 volume :=
  NavierStokesAndEuler.SobolevThreeDimensional.memLp_six hf h2 hD2


-- @@ L68-74 verbatim
/-- The real-valued homogeneous Sobolev bound when both `L²` norms are finite. -/
theorem smooth_eLpNorm_six_toReal_le {f : Space → E} (hf : ContDiff ℝ 1 f)
    (h2 : MemLp f 2 volume) (hD2 : MemLp (fderiv ℝ f) 2 volume) :
    (eLpNorm f 6 volume).toReal ≤
      (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Space) 2 : ℝ) *
        (eLpNorm (fderiv ℝ f) 2 volume).toReal :=
  NavierStokesAndEuler.SobolevThreeDimensional.toReal_eLpNorm_six_le hf h2 hD2


-- @@ L76-76 verbatim
end NavierStokesR3.RieszTestOperators
