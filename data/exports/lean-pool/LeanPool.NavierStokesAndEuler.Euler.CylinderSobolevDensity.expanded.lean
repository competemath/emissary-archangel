/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevOperators
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.MollifierRepresentative


-- @@ L12-12 verbatim
/-! Smooth mollifications are dense in every actual complete cylinder Sobolev space. -/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
namespace EulerCylinderSobolevSpace


-- @@ L21-22 verbatim
open MeasureTheory EulerLiftedGradientSpace EulerMetricTransport EulerSpatialSobolevInverse
  EulerCylinderSobolev EulerCylinderMollifier EulerMollifierRepresentative

-- @@ L23-23 verbatim
open scoped Topology ContDiff


-- @@ L25-25 verbatim
variable (period : ℝ) [Fact (0 < period)]


-- @@ L27-30 verbatim
/-- Actual smooth convolution lifted to the complete Sobolev space. -/
def sobolevMollifier (q n : ℕ) : SobolevSpace period q →L[ℝ] SobolevSpace period q :=
  liftOperator period q (mollifierOperator period n)
    (fun a f => (mollify_translation period n a f).symm)


-- @@ L32-35 verbatim
/-- Every derivative coordinate is mollified by the same actual convolution. -/
@[simp]
theorem sobolevMollifier_apply {q : ℕ} (n : ℕ) (u : SobolevSpace period q) (w : SobolevWord q) :
    (sobolevMollifier period q n u).val w = mollify period n (u.val w) := rfl


-- @@ L37-42 verbatim
/-- The smooth convolution is contractive in every complete Sobolev norm. -/
theorem sobolevMollifier_bound {q : ℕ} (n : ℕ) (u : SobolevSpace period q) :
    ‖sobolevMollifier period q n u‖ ≤ ‖u‖ := by
  exact (liftOperator_bound period (mollifierOperator period n) _ u).trans
    ((mul_le_mul_of_nonneg_right (mollifierOperator_norm_le period n) (norm_nonneg u)).trans_eq
        (one_mul _))


-- @@ L44-50 verbatim
/-- The same genuine smooth convolutions converge in the complete Sobolev topology. -/
theorem sobolevMollifier_tendsto {q : ℕ} (u : SobolevSpace period q) :
    Filter.Tendsto (fun n => sobolevMollifier period q n u) Filter.atTop (𝓝 u) := by
  rw [tendsto_subtype_rng]
  apply tendsto_pi_nhds.mpr
  intro w
  exact mollify_tendsto period (u.val w)


-- @@ L52-58 verbatim
/-- Every Sobolev mollification has the concrete smooth convolution as an almost-everywhere
representative. -/
theorem sobolevMollifier_representative {q : ℕ} (n : ℕ) (u : SobolevSpace period q) :
    (value period (sobolevMollifier period q n u) : LiftDomain period → Vector3) =ᵐ[liftMeasure
        period]
      smoothMollifier period n (value period u) :=
  mollify_ae_smoothMollifier period n (value period u)


-- @@ L60-69 verbatim
/-- The smooth representative of a Sobolev mollifier has exactly the expected classical derivative
coordinates. -/
theorem sobolevMollifier_word_ae {q k : ℕ} (hk : k ≤ q) (n : ℕ) (u : SobolevSpace period q)
    (w : Fin k → Fin 4) :
    (word period (sobolevMollifier period q n u) hk w : LiftDomain period → Vector3) =ᵐ[liftMeasure
        period]
      iteratedFieldDerivative period w (smoothMollifier period n (value period u)) := by
  have h := smoothMollifier_word_ae period hk (value period u) (toJet period u) n w
  rw [toJet_word period u hk] at h
  exact h


-- @@ L71-80 verbatim
/-- Fields with actual smooth cylinder representatives are dense in the complete Sobolev space. -/
theorem smooth_representatives_dense (q : ℕ) :
    Dense {u : SobolevSpace period q | ∃ g : LiftDomain period → Vector3,
      (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g ∧
        ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)} := by
  intro u
  apply mem_closure_of_tendsto (sobolevMollifier_tendsto period u)
  exact Filter.Eventually.of_forall fun n =>
    ⟨smoothMollifier period n (value period u), sobolevMollifier_representative period n u,
      smoothMollifier_smooth period n (value period u)⟩


-- @@ L82-82 verbatim
end EulerCylinderSobolevSpace
