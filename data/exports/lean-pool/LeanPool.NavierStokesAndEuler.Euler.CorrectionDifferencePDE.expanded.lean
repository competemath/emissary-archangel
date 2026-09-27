/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionDifference
public import LeanPool.NavierStokesAndEuler.Euler.EulerCorrectionEquation
import LeanPool.NavierStokesAndEuler.Euler.MildEquationBridge

import Mathlib.Analysis.Calculus.Deriv.Add


-- @@ L14-14 verbatim
/-! The exact viscosity-difference equation of two genuine nonlinear mild corrections. -/


-- @@ L16-16 verbatim
section


-- @@ L18-19 verbatim
/-! Every actual continued mild correction obeys the literal viscous PDE with its genuine coercive
pressure. -/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
namespace EulerCorrectionContinuation


-- @@ L27-28 verbatim
open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCorrectionOperators
  EulerQuadraticSource EulerMildEquationBridge EulerSobolevHeatGenerator EulerVolterraConvolution

-- @@ L29-29 verbatim
open scoped Topology


-- @@ L31-31 verbatim
variable (period : ℝ) [Fact (0 < period)]


-- @@ L33-56 verbatim
/-- The literal PDE follows at every interior time from any actual correction mild solution. -/
theorem correction_mild_hasDerivAt {q : ℕ} (hq : 6 ≤ q) (ν : ℝ) (hν : 0 < ν)
    {T S : ℝ} (hT : 0 ≤ T) (hTS : T ≤ S)
    (D : CorrectionData period q (Icc (0 : ℝ) S))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (hsol : ∀ t, e t = quadraticDuhamel period ν hν hT hTS (D.coefficients period hq) 0 e t)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => value period (extendPath T hT e r))
      (ν • laplacianEvaluation period (q+1) (by omega) (e ⟨t,ht.1.le,ht.2.le⟩) -
        value period (D.rawSource period hq (timeInclusion hTS ⟨t,ht.1.le,ht.2.le⟩) (e
            ⟨t,ht.1.le,ht.2.le⟩)) -
        (D.metric.coefficient (timeInclusion hTS ⟨t,ht.1.le,ht.2.le⟩)).operator
          (value period (D.pressure period hq (timeInclusion hTS ⟨t,ht.1.le,ht.2.le⟩) (e
              ⟨t,ht.1.le,ht.2.le⟩)))) t := by
  let F := ((D.coefficients period hq).comp (timeInclusion hTS)).apply
  have hF : Continuous (fun p : Icc (0 : ℝ) T × SobolevSpace period (q+1) => F p.1 p.2) :=
    ((D.coefficients period hq).comp (timeInclusion hTS)).continuous
  have hp := viscous_mild_hasDerivAt period (by omega : 2 ≤ q) ν hν T hT 0 F hF e hsol t ht
  change HasDerivAt _ (ν • laplacianEvaluation period (q+1) _ (e ⟨t,ht.1.le,ht.2.le⟩) +
    value period ((D.coefficients period hq).apply (timeInclusion hTS ⟨t,ht.1.le,ht.2.le⟩) (e
        ⟨t,ht.1.le,ht.2.le⟩))) t at hp
  rw [D.source_value period hq] at hp
  convert hp using 1
  abel


-- @@ L58-58 verbatim
end EulerCorrectionContinuation


-- @@ L60-60 verbatim
end

-- @@ L61-61 verbatim
end


-- @@ L63-63 verbatim
end


-- @@ L65-65 verbatim
@[expose] public section


-- @@ L67-67 verbatim
noncomputable section


-- @@ L69-69 verbatim
namespace EulerCorrectionDifferencePDE


-- @@ L71-73 verbatim
open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCorrectionOperators
  EulerQuadraticSource EulerCorrectionContinuation EulerCorrectionDifference EulerSobolevTransport
   EulerSobolevHeatGenerator EulerVolterraConvolution

-- @@ L74-74 verbatim
open scoped Topology


-- @@ L76-76 verbatim
variable (period : ℝ) [Fact (0 < period)]


-- @@ L78-81 verbatim
/-- The existing Sobolev normed-group instance, fixed explicitly for difference-equation
elaboration. -/
local instance differenceSobolevGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) :=
    inferInstance

-- @@ L82-85 verbatim
/-- The existing real Sobolev module instance, fixed explicitly for difference-equation elaboration.
-/
local instance differenceSobolevSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) :=
    inferInstance


-- @@ L87-99 verbatim
/-- The literal right side of the viscosity-difference equation, including its genuine pressure
difference. -/
def differenceRhs {q : ℕ} {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (hq : 6 ≤ q) (ν μ : ℝ) (t : T)
    (u v : SobolevSpace period (q + 1)) : LiftL2 period :=
  ν • laplacianEvaluation period (q+1) (by omega) (u-v) +
    (ν-μ) • laplacianEvaluation period (q+1) (by omega) v -
    value period (transportBilinear period hq (velocityComponents D.κ D.direction)
      (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound) (D.approximation
          t+u) (u-v)) -
    value period (differenceRemainder period D hq t u v) -
    (D.metric.coefficient t).operator (value period (D.pressure period hq t u)-value period
        (D.pressure period hq t v))


-- @@ L101-108 verbatim
/-- Exact vector subtraction for a bilinear evolution with two viscosities. -/
theorem vector_difference_identity {H : Type*} [AddCommGroup H] [Module ℝ H]
    (ν μ : ℝ) (a b ru rv top rem pu pv : H) (hraw : ru - rv = top + rem) :
    ν • (a-b)+(ν-μ) • b-top-rem-(pu-pv) =
      (ν • a-ru-pu)-(μ • b-rv-pv) := by
  have hr : ru=rv+(top+rem) := (sub_eq_iff_eq_add.mp hraw).trans (add_comm _ _)
  rw [hr,smul_sub,sub_smul]
  abel


-- @@ L110-129 verbatim
/-- The exposed difference equation is exactly the subtraction of the two actual PDE right sides. -/
theorem differenceRhs_eq_sub {q : ℕ} {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (hq : 6 ≤ q) (ν μ : ℝ) (t : T)
    (u v : SobolevSpace period (q + 1)) :
    differenceRhs period D hq ν μ t u v =
      (ν • laplacianEvaluation period (q+1) (by omega) u-value period (D.rawSource period hq t u) -
        (D.metric.coefficient t).operator (value period (D.pressure period hq t u))) -
      (μ • laplacianEvaluation period (q+1) (by omega) v-value period (D.rawSource period hq t v) -
        (D.metric.coefficient t).operator (value period (D.pressure period hq t v))) := by
  have hraw := congrArg (valueOperator period q) (rawSource_sub period D hq t u v)
  change value period (D.rawSource period hq t u)-value period (D.rawSource period hq t v) =
    value period (transportBilinear period hq (velocityComponents D.κ D.direction)
      (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound)
      (D.approximation t+u) (u-v))+value period (differenceRemainder period D hq t u v) at hraw
  have hlap := (laplacianEvaluation period (q+1) (by omega)).map_sub u v
  have hp := (D.metric.coefficient t).operator.map_sub
    (value period (D.pressure period hq t u)) (value period (D.pressure period hq t v))
  unfold differenceRhs
  rw [hlap,hp]
  exact vector_difference_identity ν μ _ _ _ _ _ _ _ _ hraw


-- @@ L131-145 verbatim
/-- Subtracting two actual mild correction equations gives the literal transport-pressure-heat
difference equation. -/
theorem correction_difference_hasDerivAt {q : ℕ} (hq : 6 ≤ q) (ν μ : ℝ) (hν : 0 < ν) (hμ : 0 < μ)
    (T : ℝ) (hT : 0 ≤ T) (D : CorrectionData period q (Icc (0 : ℝ) T))
    (u v : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (hu : ∀ t, u t = quadraticDuhamel period ν hν hT le_rfl (D.coefficients period hq) 0 u t)
    (hv : ∀ t, v t = quadraticDuhamel period μ hμ hT le_rfl (D.coefficients period hq) 0 v t)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun s => value period (extendPath T hT u s)-value period (extendPath T hT v s))
      (differenceRhs period D hq ν μ ⟨t,ht.1.le,ht.2.le⟩ (u ⟨t,ht.1.le,ht.2.le⟩) (v
          ⟨t,ht.1.le,ht.2.le⟩)) t := by
  have hu' := correction_mild_hasDerivAt period hq ν hν hT le_rfl D u hu t ht
  have hv' := correction_mild_hasDerivAt period hq μ hμ hT le_rfl D v hv t ht
  apply (hu'.sub hv').congr_deriv
  exact (differenceRhs_eq_sub period D hq ν μ ⟨t,ht.1.le,ht.2.le⟩ _ _).symm


-- @@ L147-147 verbatim
end EulerCorrectionDifferencePDE
