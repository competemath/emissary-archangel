/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldBounds
public import LeanPool.NavierStokesAndEuler.Euler.CylinderPotentialWeight
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderTimeWeight
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevLinear


-- @@ L14-14 verbatim
/-! Actual time-profile multiplication of raw cylinder witnesses and their same-radius bounds. -/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
namespace EulerContinuousTimeWeight


-- @@ L23-23 verbatim
open ContinuousLinearMap


-- @@ L25-33 verbatim
theorem weight_norm_of_pointwise {K E : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : C(K, ℝ)) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ t, |g t| ≤ C) : ‖weight (E := E) g‖ ≤ C := by
  apply opNorm_le_bound _ hC
  intro p
  apply (ContinuousMap.norm_le _ (mul_nonneg hC (norm_nonneg p))).mpr
  intro t
  rw [weight_apply,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul (hg t) (p.norm_coe_le_norm t) (norm_nonneg _) hC


-- @@ L35-35 verbatim
end EulerContinuousTimeWeight


-- @@ L37-37 verbatim
namespace EulerPacketCylinderField.Field


-- @@ L39-42 verbatim
open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSmoothOrbit EulerCylinderSobolev EulerLpCylinderTranslation
  EulerLpCylinderRectangular EulerContinuousTimeWeight EulerCylinderPotential
  EulerParameterWordGevrey EulerGevrey EulerPacketProfileRecursion

-- @@ L43-43 verbatim
open scoped ContDiff


-- @@ L45-45 verbatim
variable {P T : ℝ} [Fact (0 < P)] {raw : VectorField} (G : Field P T raw)


-- @@ L47-57 verbatim
/-- Weighted, constructed using `ofLifted`. -/
def weighted (hT : 0 ≤ T) (g : C(Icc (0 : ℝ) T, ℝ)) :
    Field P T (fun z => g (projIcc 0 T hT z.1) • raw z) :=
  ofLifted (weight g G.path) (weighted_orbit P g G.path G.orbit)
    (fun t x => g t • pointField P G.path G.orbit t x)
    (fun t => (EulerMetricTransport.smoothField_continuous P _
      (pointField_smooth P G.path G.orbit t)).const_smul (g t))
    (fun t => by
      filter_upwards [Lp.coeFn_smul (g t) (G.path t),pointField_ae P G.path G.orbit t] with x hs hp
      exact hs.trans (congrArg (g t • ·) hp))
    (fun t x θ => by rw [projIcc_of_mem hT t.property,G.raw_eq])


-- @@ L59-62 verbatim
/-- Normalized, given by `G.weighted hT (reciprocal g hg)`. -/
def normalized (hT : 0 ≤ T) (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t) :
    Field P T (fun z => (g (projIcc 0 T hT z.1))⁻¹ • raw z) :=
  G.weighted hT (reciprocal g hg)


-- @@ L64-65 verbatim
@[simp] theorem weighted_path (hT : 0 ≤ T) (g : C(Icc (0 : ℝ) T, ℝ)) :
    (G.weighted hT g).path = weight g G.path := rfl


-- @@ L67-68 verbatim
@[simp] theorem normalized_path (hT : 0 ≤ T) (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t) :
    (G.normalized hT g hg).path = normalize g hg G.path := rfl


-- @@ L70-72 verbatim
theorem derivative_weighted_path (hT : 0 ≤ T) (g : C(Icc (0 : ℝ) T, ℝ)) (i : Fin 4) :
    ((G.weighted hT g).derivative i).path = ((G.derivative i).weighted hT g).path :=
  derivativePath_weight P g G.path G.orbit i


-- @@ L74-77 verbatim
theorem derivative_normalized_path (hT : 0 ≤ T) (g : C(Icc (0 : ℝ) T, ℝ))
    (hg : ∀ t, 0 < g t) (i : Fin 4) :
    ((G.normalized hT g hg).derivative i).path = ((G.derivative i).normalized hT g hg).path :=
  G.derivative_weighted_path hT (reciprocal g hg) i


-- @@ L79-79 verbatim
variable {G}


-- @@ L81-93 verbatim
theorem WordBound.weighted {q d : ℕ} {R A : ℝ} (hG : G.WordBound q R A d)
    (hT : 0 ≤ T) (g : C(Icc (0 : ℝ) T, ℝ)) (C : ℝ) (hC : 0 ≤ C) (hg : ∀ t, |g t| ≤ C) :
    (G.weighted hT g).WordBound q R (C*A) d := by
  intro n
  have he : (fun a : LiftTangent => pathTranslate P a (G.weighted hT g).path) =
      weight g ∘ (fun a : LiftTangent => pathTranslate P a G.path) :=
    funext (fun a => translate_weight P g a G.path)
  rw [he]
  have h := block_comp_clm_le standardDirection q (weight g)
    (fun a : LiftTangent => pathTranslate P a G.path) G.orbit n 0
  have hn := h.trans (mul_le_mul_of_nonneg_right (weight_norm_of_pointwise g C hC hg)
    (block_nonneg standardDirection q (fun a : LiftTangent => pathTranslate P a G.path) n 0))
  exact hn.trans ((mul_le_mul_of_nonneg_left (hG n) hC).trans_eq (by ring))


-- @@ L95-95 verbatim
end EulerPacketCylinderField.Field
