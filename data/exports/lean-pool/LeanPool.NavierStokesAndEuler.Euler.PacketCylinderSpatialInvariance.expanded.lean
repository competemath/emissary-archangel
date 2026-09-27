/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderField


-- @@ L11-11 verbatim
/-! Actual spatial jets outside a closed support and for angle-independent fields. -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-18 verbatim
namespace EulerPacketCylinderField


-- @@ L20-21 verbatim
open Set Filter ContinuousLinearMap EulerSmoothLimit EulerPacketPointJets
    EulerPacketProfileRecursion

-- @@ L22-22 verbatim
open scoped Topology ContDiff


-- @@ L24-28 verbatim
/-- Precisely the spatial parts of the jet that occur in the packet nonlinearities. -/
structure AngleIndependentJet (J : ℝ → VectorJet) : Prop where
  value : ∀ θ, (J θ).1 = (J 0).1
  spatial : ∀ θ v, (J θ).2 (spatialInjection v) = (J 0).2 (spatialInjection v)
  angular : ∀ θ, (J θ).2 angleDirection = 0


-- @@ L30-30 verbatim
namespace AngleIndependentJet


-- @@ L32-35 verbatim
theorem zero : AngleIndependentJet (fun _ => (0 : VectorJet)) where
  value _ := rfl
  spatial _ _ := rfl
  angular _ := rfl


-- @@ L37-48 verbatim
theorem add {J K : ℝ → VectorJet} (hJ : AngleIndependentJet J) (hK : AngleIndependentJet K) :
    AngleIndependentJet (fun θ => J θ+K θ) where
  value θ := by
    change (J θ).1+(K θ).1 = (J 0).1+(K 0).1
    rw [hJ.value,hK.value]
  spatial θ v := by
    change (J θ).2 (spatialInjection v)+(K θ).2 (spatialInjection v) =
      (J 0).2 (spatialInjection v)+(K 0).2 (spatialInjection v)
    rw [hJ.spatial,hK.spatial]
  angular θ := by
    change (J θ).2 angleDirection+(K θ).2 angleDirection = 0
    rw [hJ.angular,hK.angular,add_zero]


-- @@ L50-50 verbatim
end AngleIndependentJet


-- @@ L52-52 verbatim
variable {P T : ℝ} [Fact (0 < P)] {raw : VectorField}


-- @@ L54-63 verbatim
theorem raw_fderiv_zero_outside (S : Set Space) (hS : IsClosed S)
    (h : ∀ (t : Icc (0 : ℝ) T) x, x ∉ S → ∀ θ : ℝ, raw (t,(x,θ)) = 0)
    (t : Icc (0 : ℝ) T) (x : Space) (hx : x ∉ S) (θ : ℝ) :
    fderiv ℝ (fun y : Space × ℝ => raw (t,y)) (x,θ) = 0 := by
  have hn : {y : Space × ℝ | y.1 ∉ S} ∈ 𝓝 (x,θ) :=
    (hS.isOpen_compl.preimage continuous_fst).mem_nhds hx
  have he : (fun y : Space × ℝ => raw (t,y)) =ᶠ[𝓝 (x,θ)] fun _ => (0 : Space) := by
    filter_upwards [hn] with y hy
    exact h t y.1 hy y.2
  simpa only [fderiv_const_apply] using he.fderiv_eq (𝕜 := ℝ)


-- @@ L65-76 verbatim
theorem slicedJet_angleIndependent_of_support (s : Set ℝ) (S : Set Space) (hS : IsClosed S)
    (h : ∀ (t : Icc (0 : ℝ) T) x, x ∉ S → ∀ θ : ℝ, raw (t,(x,θ)) = 0)
    (t : Icc (0 : ℝ) T) (x : Space) (hx : x ∉ S) :
    AngleIndependentJet (fun θ => slicedJet s raw (t,(x,θ))) where
  value θ := by
    change raw (t,(x,θ)) = raw (t,(x,0))
    rw [h t x hx θ,h t x hx 0]
  spatial θ v := by
    rw [slicedJet_space,slicedJet_space,raw_fderiv_zero_outside S hS h t x hx θ,
      raw_fderiv_zero_outside S hS h t x hx 0]
  angular θ := by
    rw [slicedJet_angle,raw_fderiv_zero_outside S hS h t x hx θ,zero_apply]


-- @@ L78-90 verbatim
theorem Field.raw_fderiv_of_angleIndependent (G : Field P T raw)
    (h : ∀ (t : Icc (0 : ℝ) T) x θ, raw (t, (x, θ)) = raw (t, (x, 0)))
    (t : Icc (0 : ℝ) T) (x : Space) (θ : ℝ) :
    fderiv ℝ (fun y : Space × ℝ => raw (t,y)) (x,θ) =
      (fderiv ℝ (fun y : Space => raw (t,(y,0))) x).comp (ContinuousLinearMap.fst ℝ Space ℝ) := by
  have hg : ContDiff ℝ ∞ (fun y : Space => raw (t,(y,0))) :=
    (G.raw_smooth t).comp (contDiff_id.prodMk contDiff_const)
  have hd := (hg.differentiable (by simp) x).hasFDerivAt.comp (x,θ)
    (ContinuousLinearMap.fst ℝ Space ℝ).hasFDerivAt
  have he : (fun y : Space × ℝ => raw (t,y)) = fun y => raw (t,(y.1,0)) :=
    funext (fun y => h t y.1 y.2)
  rw [he]
  exact hd.fderiv


-- @@ L92-103 verbatim
theorem Field.slicedJet_angleIndependent (G : Field P T raw) (s : Set ℝ)
    (h : ∀ (t : Icc (0 : ℝ) T) x θ, raw (t, (x, θ)) = raw (t, (x, 0)))
    (t : Icc (0 : ℝ) T) (x : Space) :
    AngleIndependentJet (fun θ => slicedJet s raw (t,(x,θ))) where
  value θ := h t x θ
  spatial θ v := by
    rw [slicedJet_space,slicedJet_space,G.raw_fderiv_of_angleIndependent h t x θ,
      G.raw_fderiv_of_angleIndependent h t x 0]
  angular θ := by
    rw [slicedJet_angle,G.raw_fderiv_of_angleIndependent h t x θ]
    change (fderiv ℝ (fun y : Space => raw (t,(y,0))) x) 0 = 0
    exact map_zero _


-- @@ L105-105 verbatim
end EulerPacketCylinderField
