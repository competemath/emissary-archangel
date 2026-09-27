/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.LiftedWeakDerivative
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SmoothLimit


-- @@ L12-12 verbatim
/-! Exact ordinary derivatives of the raw covering field of a smooth cylinder representative. -/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
namespace EulerCylinderSmoothOrbit


-- @@ L21-22 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerMetricTransport EulerTransportDerivatives EulerLiftedWeakDerivative

-- @@ L23-23 verbatim
open scoped ContDiff


-- @@ L25-26 verbatim
variable (P : ℝ) [Fact (0 < P)]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]


-- @@ L28-32 verbatim
omit [Fact (0 < P)] [NormedAddCommGroup V] [NormedSpace ℝ V] in
theorem coverField_eq_local (f : LiftDomain P → V) :
    (fun z : LiftTangent => f (z.1,(z.2 : AddCircle P))) = localFieldLift P f 0 := by
  funext z
  simp only [localFieldLift, Prod.fst_zero, Prod.snd_zero, zero_add]


-- @@ L34-39 verbatim
omit [Fact (0 < P)] in
theorem coverField_fderiv (f : LiftDomain P → V) (z : LiftTangent) :
    fderiv ℝ (fun y : LiftTangent => f (y.1,(y.2 : AddCircle P))) z =
      fieldFDeriv P f (z.1,(z.2 : AddCircle P)) := by
  rw [coverField_eq_local]
  exact (fderiv_localFieldLift_cover P f z).symm


-- @@ L41-46 verbatim
omit [Fact (0 < P)] in
theorem coverField_contDiff (f : LiftDomain P → V)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift P f x)) :
    ContDiff ℝ ∞ (fun z : LiftTangent => f (z.1,(z.2 : AddCircle P))) := by
  rw [coverField_eq_local]
  exact hf 0


-- @@ L48-57 verbatim
omit [Fact (0 < P)] in
/-- The raw spatial derivative is exactly the spatial restriction of the cylinder derivative. -/
theorem coverField_spatial_fderiv (f : LiftDomain P → V)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift P f x)) (x : Space) (θ : ℝ) :
    fderiv ℝ (fun y : Space => f (y,(θ : AddCircle P))) x =
      (fieldFDeriv P f (x,(θ : AddCircle P))).comp (ContinuousLinearMap.inl ℝ Space ℝ) := by
  have hi : HasFDerivAt (fun y : Space => (y,θ)) (ContinuousLinearMap.inl ℝ Space ℝ) x :=
    (hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const θ x)
  have hd := ((coverField_contDiff P f hf).differentiable (by simp) (x,θ)).hasFDerivAt.comp x hi
  simpa only [Function.comp_def, coverField_fderiv] using hd.fderiv


-- @@ L59-59 verbatim
end EulerCylinderSmoothOrbit
