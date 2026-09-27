/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderField
public import LeanPool.NavierStokesAndEuler.Euler.CylinderFieldReflection


-- @@ L12-12 verbatim
/-! Literal joint parity is equivalent to parity of an actual cylinder-path witness. -/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
namespace EulerPacketCylinderField.Field


-- @@ L21-22 verbatim
open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace EulerCylinderSmoothOrbit
  EulerMetricTransport EulerCylinderFieldReflection EulerPacketProfileRecursion


-- @@ L24-24 verbatim
variable {P T : ℝ} [Fact (0 < P)] {raw : VectorField} (G : Field P T raw)


-- @@ L26-35 verbatim
theorem reflection_eq_of_raw_parity (c : ℝ) (t : Icc (0 : ℝ) T)
    (h : ∀ x θ, raw (t, (-x, -θ)) = c • raw (t, (x, θ))) :
    reflection P (G.path t) = c • G.path t := by
  apply reflection_of_representative P (G.path t) (pointField P G.path G.orbit t)
    (pointField_ae P G.path G.orbit t) c
  rintro ⟨x,z⟩
  obtain ⟨θ,hθ⟩ := QuotientAddGroup.mk_surjective z
  have he := h x θ
  rw [G.raw_eq t (-x) (-θ), G.raw_eq t x θ] at he
  simpa only [AddCircle.coe_neg,hθ,Prod.neg_mk] using he


-- @@ L37-44 verbatim
theorem raw_parity_of_reflection (c : ℝ) (t : Icc (0 : ℝ) T)
    (h : reflection P (G.path t) = c • G.path t) (x : Space) (θ : ℝ) :
    raw (t,(-x,-θ)) = c • raw (t,(x,θ)) := by
  have he := representative_of_reflection P (G.path t) (pointField P G.path G.orbit t)
    (pointField_ae P G.path G.orbit t)
    (smoothField_continuous P _ (pointField_smooth P G.path G.orbit t)) c h (x,(θ : AddCircle P))
  rw [G.raw_eq t (-x) (-θ), G.raw_eq t x θ]
  simpa only [AddCircle.coe_neg,Prod.neg_mk] using he


-- @@ L46-50 verbatim
theorem reflection_neg_of_raw_odd (t : Icc (0 : ℝ) T)
    (h : ∀ x θ, raw (t, (-x, -θ)) = -raw (t, (x, θ))) :
    reflection P (G.path t) = -G.path t := by
  have he := G.reflection_eq_of_raw_parity (-1) t (by simpa only [neg_one_smul] using h)
  simpa only [neg_one_smul] using he


-- @@ L52-56 verbatim
theorem raw_odd_of_reflection_neg (t : Icc (0 : ℝ) T)
    (h : reflection P (G.path t) = -G.path t) (x : Space) (θ : ℝ) :
    raw (t,(-x,-θ)) = -raw (t,(x,θ)) := by
  have he := G.raw_parity_of_reflection (-1) t (by simpa only [neg_one_smul] using h) x θ
  simpa only [neg_one_smul] using he


-- @@ L58-58 verbatim
end EulerPacketCylinderField.Field
