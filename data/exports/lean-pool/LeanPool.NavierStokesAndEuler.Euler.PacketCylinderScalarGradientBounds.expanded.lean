/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderScalarGradient
import LeanPool.NavierStokesAndEuler.Euler.CylinderConstantMapBounds
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevFiniteSum


-- @@ L13-13 verbatim
/-! The actual scalar pressure gradient uses one external word and keeps the same radius. -/


-- @@ L15-15 verbatim
@[expose] public section



-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-20 verbatim
namespace EulerPacketCylinderField


-- @@ L22-24 verbatim
open Set Finset EulerLiftedGradientSpace EulerLpCylinderTranslation
  EulerCylinderConstantMap EulerCylinderScalarPrimitive EulerCylinderSmoothOrbit
  EulerCylinderSobolev EulerParameterWordGevrey EulerGevrey EulerPacketProfileRecursion

-- @@ L25-25 verbatim
open scoped ContDiff


-- @@ L27-27 verbatim
variable {P : ℝ} [Fact (0 < P)]


-- @@ L29-29 verbatim
section Path


-- @@ L31-33 verbatim
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
  (p : C(K, CylinderL2 P ℝ))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))


-- @@ L35-38 verbatim
/-- Scalar gradient path, given by `∑ i : Fin 3, pathMap P (gradientComponent i) (derivativePath
P (pathMap P scalarEmbed p) i.succ)`. -/
def scalarGradientPath : C(K,LiftL2 P) := ∑ i : Fin 3,
  pathMap P (gradientComponent i) (derivativePath P (pathMap P scalarEmbed p) i.succ)


-- @@ L40-46 verbatim
include hp in
theorem scalarGradientPath_orbit :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (scalarGradientPath p)) := by
  simp only [scalarGradientPath,map_sum]
  exact ContDiff.sum (fun i _ => pathMap_orbit_contDiff P (gradientComponent i) _
    (derivativePath_orbit P (pathMap P scalarEmbed p)
      (pathMap_orbit_contDiff P scalarEmbed p hp) i.succ))


-- @@ L48-81 verbatim
include hp in
theorem scalarGradientPath_block_bound (q n : ℕ) (a : LiftTangent) :
    block standardDirection q
        (fun b : LiftTangent => pathTranslate P b (scalarGradientPath p)) n a ≤
      3 * block standardDirection q (fun b : LiftTangent => pathTranslate P b p) (n+1) a := by
  let u := pathMap P scalarEmbed p
  have hu : ContDiff ℝ ∞ (fun b : LiftTangent => pathTranslate P b u) :=
    pathMap_orbit_contDiff P scalarEmbed p hp
  let v := fun i : Fin 3 => pathMap P (gradientComponent i) (derivativePath P u i.succ)
  have hv (i : Fin 3) : ContDiff ℝ ∞ (fun b : LiftTangent => pathTranslate P b (v i)) :=
    pathMap_orbit_contDiff P (gradientComponent i) _ (derivativePath_orbit P u hu i.succ)
  have hb (i : Fin 3) :
      block standardDirection q (fun b : LiftTangent => pathTranslate P b (v i)) n a ≤
        block standardDirection q (fun b : LiftTangent => pathTranslate P b p) (n+1) a := by
    have h₁ := pathMap_block_bound P standardDirection q (gradientComponent i)
      (derivativePath P u i.succ) (derivativePath_orbit P u hu i.succ) n a
    have h₂ := h₁.trans (mul_le_mul_of_nonneg_right (gradientComponent_norm i)
      (block_nonneg standardDirection q
        (fun b : LiftTangent => pathTranslate P b (derivativePath P u i.succ)) n a))
    simp only [one_mul] at h₂
    have h₃ := h₂.trans (derivativePath_block_bound P u hu i.succ q n a)
    have h₄ := pathMap_block_bound P standardDirection q scalarEmbed p hp (n+1) a
    rw [scalarEmbed_norm,one_mul] at h₄
    exact h₃.trans h₄
  have hfun :
      (fun b : LiftTangent => pathTranslate P b (scalarGradientPath p)) =
        ∑ i : Fin 3, (fun b : LiftTangent => pathTranslate P b (v i)) := by
    funext b
    simp only [scalarGradientPath,map_sum,Finset.sum_apply,v,u]
  rw [hfun]
  have h := block_finset_sum_le standardDirection q univ
    (fun i : Fin 3 => fun b : LiftTangent => pathTranslate P b (v i)) (fun i _ => hv i) n a
  exact h.trans ((sum_le_sum (fun i _ => hb i)).trans_eq (by
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]))


-- @@ L83-94 verbatim
include hp in
theorem scalarGradientPath_majorant (q : ℕ) (R A : ℝ) (d : ℕ)
    (hb : ∀ n, block standardDirection q (fun b : LiftTangent => pathTranslate P b p) n 0 ≤
      A * majorant R d n) (n : ℕ) :
    block standardDirection q
        (fun b : LiftTangent => pathTranslate P b (scalarGradientPath p)) n 0 ≤
      (3*A) * majorant R (d+1) n := by
  have h := (scalarGradientPath_block_bound p hp q n 0).trans
    (mul_le_mul_of_nonneg_left (hb (n+1)) (by norm_num : (0 : ℝ) ≤ 3))
  exact h.trans_eq (by
    simp only [majorant,show n+1+d=n+(d+1) by omega]
    ring)


-- @@ L96-96 verbatim
end Path


-- @@ L98-98 verbatim
section Field


-- @@ L100-103 verbatim
variable {T : ℝ} (raw : ScalarField) (p : C(Icc (0 : ℝ) T, CylinderL2 P ℝ))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
  (he : ∀ (t : Icc (0 : ℝ) T) x θ,
    raw (t, (x, θ)) = scalarPointField P p hp t (x, (θ : AddCircle P)))


-- @@ L105-106 verbatim
theorem scalarGradientField_path :
    (scalarGradientField raw p hp he).path = scalarGradientPath p := rfl


-- @@ L108-112 verbatim
theorem scalarGradientField_block_bound (q n : ℕ) (a : LiftTangent) :
    block standardDirection q
        (fun b : LiftTangent => pathTranslate P b (scalarGradientField raw p hp he).path) n a ≤
      3 * block standardDirection q (fun b : LiftTangent => pathTranslate P b p) (n+1) a :=
  scalarGradientPath_block_bound p hp q n a


-- @@ L114-120 verbatim
theorem scalarGradientField_majorant (q : ℕ) (R A : ℝ) (d : ℕ)
    (hb : ∀ n, block standardDirection q (fun b : LiftTangent => pathTranslate P b p) n 0 ≤
      A * majorant R d n) (n : ℕ) :
    block standardDirection q
        (fun b : LiftTangent => pathTranslate P b (scalarGradientField raw p hp he).path) n 0 ≤
      (3*A) * majorant R (d+1) n :=
  scalarGradientPath_majorant p hp q R A d hb n


-- @@ L122-122 verbatim
end Field


-- @@ L124-124 verbatim
end EulerPacketCylinderField
