/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevEmbedding
import LeanPool.NavierStokesAndEuler.Euler.ClassicalPressureCurl
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.MollifierUniform


-- @@ L13-13 verbatim
/-! Actual continuous representatives and point evaluation as bounded linear maps on cylinder H3. -/


-- @@ L15-15 verbatim
@[expose] public section



-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-20 verbatim
namespace EulerSobolevPointEvaluation


-- @@ L22-23 verbatim
open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerMollifierUniform EulerClassicalPressureCurl

-- @@ L24-24 verbatim
open scoped Topology


-- @@ L26-26 verbatim
variable (period : ℝ) [Fact (0 < period)]


-- @@ L28-30 verbatim
/-- The actual continuous representative of a genuine cylinder H3 field. -/
def representative (u : SobolevSpace period 3) : LiftDomain period → Vector3 :=
  Classical.choose (exists_continuous_representative period (value period u) (toJet period u))


-- @@ L32-36 verbatim
/-- The chosen representative is actually continuous. -/
theorem representative_continuous (u : SobolevSpace period 3) : Continuous (representative period
    u) :=
  (Classical.choose_spec (exists_continuous_representative period (value period u) (toJet period
      u))).1


-- @@ L38-42 verbatim
/-- The chosen representative agrees almost everywhere with the actual L² field. -/
theorem representative_ae (u : SobolevSpace period 3) :
    (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] representative period u :=
  (Classical.choose_spec (exists_continuous_representative period (value period u) (toJet period
      u))).2


-- @@ L44-50 verbatim
/-- Continuous representatives of the same actual L² field agree pointwise. -/
theorem representative_eq (u : SobolevSpace period 3) (g : LiftDomain period → Vector3)
    (hg : Continuous g) (hrep : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure
        period] g) :
    representative period u = g :=
  MeasureTheory.Measure.eq_of_ae_eq ((representative_ae period u).symm.trans hrep)
    (representative_continuous period u) hg


-- @@ L52-62 verbatim
/-- The actual representative obeys the pointwise H3 evaluation bound at every point. -/
theorem representative_bound (u : SobolevSpace period 3) (x : LiftDomain period) :
    ‖representative period u x‖ ≤ sobolevEmbeddingConstant period 3*‖u‖ := by
  have hb : ∀ᵐ y ∂liftMeasure period, ‖representative period u y‖ ≤ sobolevEmbeddingConstant period
      3*‖u‖ := by
    filter_upwards [value_ae_bound period (le_refl 3) u,representative_ae period u] with y hy he
    rwa [← he]
  have hc : IsClosed {y | ‖representative period u y‖ ≤ sobolevEmbeddingConstant period 3*‖u‖} :=
    isClosed_le (representative_continuous period u).norm continuous_const
  have hx := MeasureTheory.Measure.dense_of_ae hb x
  rwa [hc.closure_eq] at hx


-- @@ L64-72 verbatim
/-- Addition of actual H3 fields gives pointwise addition of their continuous representatives. -/
theorem representative_add (u v : SobolevSpace period 3) :
    representative period (u+v) = fun x => representative period u x+representative period v x := by
  apply representative_eq period (u+v) _ ((representative_continuous period u).add
      (representative_continuous period v))
  filter_upwards [Lp.coeFn_add (value period u) (value period v),representative_ae period
      u,representative_ae period v] with x ha hu hv
  change (value period u+value period v) x = _
  simpa only [Pi.add_apply,hu,hv] using ha


-- @@ L74-81 verbatim
/-- Scalar multiplication of actual H3 fields gives pointwise scalar multiplication of their
continuous representatives. -/
theorem representative_smul (c : ℝ) (u : SobolevSpace period 3) :
    representative period (c • u) = fun x => c • representative period u x := by
  apply representative_eq period (c • u) _ ((representative_continuous period u).const_smul c)
  filter_upwards [Lp.coeFn_smul c (value period u),representative_ae period u] with x hs hu
  change (c • value period u) x = _
  simpa only [Pi.smul_apply,hu] using hs


-- @@ L83-89 verbatim
/-- Evaluation of the actual continuous representative is a bounded linear map on cylinder H3. -/
def pointEvaluation (x : LiftDomain period) : SobolevSpace period 3 →L[ℝ] Vector3 :=
  ({ toFun := fun u => representative period u x
     map_add' := fun u v => congrFun (representative_add period u v) x
     map_smul' := fun c u => congrFun (representative_smul period c u) x } :
    SobolevSpace period 3 →ₗ[ℝ] Vector3).mkContinuous (sobolevEmbeddingConstant period 3)
      (fun u => representative_bound period u x)


-- @@ L91-95 verbatim
/-- The bounded evaluation operator returns the value of every actual continuous representative. -/
theorem pointEvaluation_eq (x : LiftDomain period) (u : SobolevSpace period 3)
    (g : LiftDomain period → Vector3) (hg : Continuous g)
    (hrep : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g) :
    pointEvaluation period x u = g x := congrFun (representative_eq period u g hg hrep) x


-- @@ L97-97 verbatim
end EulerSobolevPointEvaluation
