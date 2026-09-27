/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderCoefficientData
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldAdvection
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Bounds


-- @@ L14-14 verbatim
/-! Norm-one coefficient constructions used by the actual slow and fast packet terms. -/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
namespace EulerPacketCylinderField


-- @@ L23-25 verbatim
open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerLiftedGradientSpace
  EulerMeanCoefficients EulerCylinderScalarPrimitive EulerBoundedFieldCalculus
  EulerPacketPointJets EulerPacketProfileRecursion EulerGevrey

-- @@ L26-26 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L28-36 verbatim
private theorem mapped_derivative_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) (f : Space → E) (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (a : Space) : ‖iteratedFDeriv ℝ n (L ∘ f) a‖ ≤ ‖iteratedFDeriv ℝ n f a‖ := by
  have h := ContinuousLinearMap.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (E := Space)
    L (hf.contDiffAt (x := a)) (n := n) (by simp)
  exact h.trans (by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hL (norm_nonneg (iteratedFDeriv ℝ n f a)))


-- @@ L38-45 verbatim
theorem normalComponentMap_norm : ‖normalComponentMap‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro m
  rw [one_mul]
  apply opNorm_le_bound _ (norm_nonneg m)
  intro v
  rw [normalComponentMap_apply,scalarEmbed,toSpanSingleton_apply,norm_smul,unitVector_norm,mul_one]
  exact norm_inner_le_norm m v


-- @@ L47-58 verbatim
private theorem mapCoefficientPath_norm_le
    {K E F : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) : ‖mapCoefficientPath (K := K) L‖ ≤ ‖L‖ := by
  apply opNorm_le_bound _ (norm_nonneg L)
  intro A
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg L) (norm_nonneg A))).mpr
  intro t
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg L) (norm_nonneg A))).mpr
  intro x
  exact (L.le_opNorm (A t x)).trans (mul_le_mul_of_nonneg_left
    (((A t).norm_coe_le_norm x).trans (A.norm_coe_le_norm t)) (norm_nonneg L))


-- @@ L60-60 verbatim
namespace VectorCoefficient


-- @@ L62-62 verbatim
variable {T : ℝ} {raw : VectorField} (N : VectorCoefficient T raw)


-- @@ L64-68 verbatim
/-- Normal matrix, bundling `path`, `orbit`, `raw_eq`. -/
def normalMatrix : MatrixCoefficient T (fun z => normalComponentMap (raw z)) where
  path := normalComponentPath N.path
  orbit := normalComponentPath_orbit N.path N.orbit
  raw_eq t x θ := by rw [N.raw_eq]; rfl


-- @@ L70-86 verbatim
theorem normalMatrix_bound (Rc C : ℝ)
    (hN : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath N.path) a‖ ≤ C * majorant Rc 0 n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath N.normalMatrix.path) a‖ ≤ C*majorant Rc 0 n := by
  have he : translateCoefficientPath N.normalMatrix.path =
      (mapCoefficientPath (K := Icc (0 : ℝ) T) normalComponentMap) ∘ translateCoefficientPath
          N.path := by
    funext b
    apply ContinuousMap.ext
    intro t
    apply BoundedContinuousFunction.ext
    intro x
    rfl
  rw [he]
  exact (mapped_derivative_le (mapCoefficientPath (K := Icc (0 : ℝ) T) normalComponentMap)
    ((mapCoefficientPath_norm_le normalComponentMap).trans normalComponentMap_norm)
    _ N.orbit n a).trans (hN n a)


-- @@ L88-88 verbatim
end VectorCoefficient


-- @@ L90-90 verbatim
namespace MatrixCoefficient


-- @@ L92-92 verbatim
variable {T : ℝ} {raw : Domain → Space →L[ℝ] Space} (K : MatrixCoefficient T raw)


-- @@ L94-118 verbatim
theorem adjoint_bound (Rc C : ℝ)
    (hK : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath K.path) a‖ ≤ C * majorant Rc 0 n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath K.adjoint.path) a‖ ≤ C*majorant Rc 0 n := by
  let A : (Space →L[ℝ] Space) →L[ℝ] (Space →L[ℝ] Space) :=
    EulerTransverseGramInverse.realAdjoint
  have hA : ‖A‖ ≤ 1 := by
    apply opNorm_le_bound _ zero_le_one
    intro v
    change ‖v.adjoint‖ ≤ 1*‖v‖
    rw [LinearIsometryEquiv.norm_map,one_mul]
  have he : translateCoefficientPath K.adjoint.path =
      (mapCoefficientPath (K := Icc (0 : ℝ) T) A) ∘ translateCoefficientPath K.path := by
    funext b
    apply ContinuousMap.ext
    intro t
    apply BoundedContinuousFunction.ext
    intro x
    rfl
  rw [he]
  have hm := mapped_derivative_le
    (mapCoefficientPath (K := Icc (0 : ℝ) T) A)
    ((mapCoefficientPath_norm_le A).trans hA)
    (translateCoefficientPath K.path) K.orbit n a
  exact hm.trans (hK n a)


-- @@ L120-120 verbatim
end MatrixCoefficient

-- @@ L121-121 verbatim
end EulerPacketCylinderField
