/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderJetOperations
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderCoefficientBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderWeightedLinear
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldWeight
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldUnique


-- @@ L14-14 verbatim
/-! Same-radius normalized bounds for the literal slow and fast packet jet expressions. -/


-- @@ L16-16 verbatim
section


-- @@ L18-18 verbatim
/-! Products of actual normalized fields use only the pointwise ratio of their time profiles. -/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
namespace EulerPacketCylinderField


-- @@ L26-27 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderPathProduct EulerPacketProfileRecursion

-- @@ L28-28 verbatim
open scoped ContDiff


-- @@ L30-34 verbatim
/-- Product profile ratio, given by `⟨fun t => g t*h t/b t,(g.continuous.mul h.continuous).div
b.continuous (fun t => (hb t).ne')⟩`. -/
def productProfileRatio {K : Type*} [TopologicalSpace K]
    (g h b : C(K, ℝ)) (hb : ∀ t, 0 < b t) : C(K,ℝ) :=
  ⟨fun t => g t*h t/b t,(g.continuous.mul h.continuous).div b.continuous (fun t => (hb t).ne')⟩


-- @@ L36-38 verbatim
@[simp] theorem productProfileRatio_apply {K : Type*} [TopologicalSpace K]
    (g h b : C(K, ℝ)) (hb : ∀ t, 0 < b t) (t : K) :
    productProfileRatio g h b hb t = g t*h t/b t := rfl


-- @@ L40-45 verbatim
theorem productProfileRatio_abs_le {K : Type*} [TopologicalSpace K]
    (g h b : C(K, ℝ)) (hg : ∀ t, 0 ≤ g t) (hh : ∀ t, 0 ≤ h t)
    (hb : ∀ t, 0 < b t) (C : ℝ) (hC : ∀ t, g t * h t ≤ C * b t) (t : K) :
    |productProfileRatio g h b hb t| ≤ C := by
  rw [productProfileRatio_apply,abs_of_nonneg (div_nonneg (mul_nonneg (hg t) (hh t)) (hb t).le)]
  exact (div_le_iff₀ (hb t)).mpr (hC t)


-- @@ L47-47 verbatim
namespace Field


-- @@ L49-51 verbatim
variable {P T : ℝ} [Fact (0 < P)] {raw raw' : VectorField}
  (G : Field P T raw) (H : Field P T raw') (hT : 0 ≤ T)
  (g h b : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t) (hh : ∀ t, 0 < h t) (hb : ∀ t, 0 < b t)


-- @@ L53-65 verbatim
theorem normalized_bilinear_path (L : Space →L[ℝ] Space →L[ℝ] Space) :
    ((G.bilinear H L).normalized hT b hb).path =
      (((G.normalized hT g hg).bilinear (H.normalized hT h hh) L).weighted hT
        (productProfileRatio g h b hb)).path := by
  apply path_eq_of_raw_eq
  intro t x θ
  change productProfileRatio g h b hb (projIcc 0 T hT t) •
    L ((g (projIcc 0 T hT t))⁻¹ • raw (t,(x,θ))) ((h (projIcc 0 T hT t))⁻¹ • raw' (t,(x,θ))) =
      (b (projIcc 0 T hT t))⁻¹ • L (raw (t,(x,θ))) (raw' (t,(x,θ)))
  rw [projIcc_of_mem hT t.property]
  simp only [productProfileRatio_apply,map_smul,smul_apply,smul_smul]
  congr 1
  field_simp [(hg t).ne',(hh t).ne',(hb t).ne']


-- @@ L67-79 verbatim
theorem normalized_scalarProduct_path (L : Space →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) :
    ((G.scalarProduct H L hL).normalized hT b hb).path =
      (((G.normalized hT g hg).scalarProduct (H.normalized hT h hh) L hL).weighted hT
        (productProfileRatio g h b hb)).path := by
  apply path_eq_of_raw_eq
  intro t x θ
  change productProfileRatio g h b hb (projIcc 0 T hT t) •
    (L ((g (projIcc 0 T hT t))⁻¹ • raw (t,(x,θ))) • ((h (projIcc 0 T hT t))⁻¹ • raw' (t,(x,θ)))) =
      (b (projIcc 0 T hT t))⁻¹ • (L (raw (t,(x,θ))) • raw' (t,(x,θ)))
  rw [projIcc_of_mem hT t.property]
  simp only [productProfileRatio_apply,map_smul,smul_eq_mul,smul_smul]
  congr 1
  field_simp [(hg t).ne',(hh t).ne',(hb t).ne']


-- @@ L81-102 verbatim
theorem normalized_spatialTransport_path :
    ((G.spatialTransport H).normalized hT b hb).path =
      (((G.normalized hT g hg).spatialTransport (H.normalized hT h hh)).weighted hT
        (productProfileRatio g h b hb)).path := by
  apply path_eq_of_raw_eq
  intro t x θ
  have hd : fderiv ℝ
      (fun y : LiftTangent => (h (projIcc 0 T hT t))⁻¹ • raw' (t,y)) (x,θ) =
        (h t)⁻¹ • fderiv ℝ (fun y : LiftTangent => raw' (t,y)) (x,θ) := by
    rw [projIcc_of_mem hT t.property]
    exact (((H.raw_smooth t).differentiable (by simp) (x,θ)).hasFDerivAt.const_smul (h t)⁻¹).fderiv
  change productProfileRatio g h b hb (projIcc 0 T hT t) •
    fderiv ℝ (fun y : LiftTangent => (h (projIcc 0 T hT t))⁻¹ • raw' (t,y)) (x,θ)
      ((g (projIcc 0 T hT t))⁻¹ • raw (t,(x,θ)),0) =
        (b (projIcc 0 T hT t))⁻¹ • fderiv ℝ (fun y : LiftTangent => raw' (t,y)) (x,θ) (raw
            (t,(x,θ)),0)
  rw [hd,projIcc_of_mem hT t.property]
  have ha : ((g t)⁻¹ • raw (t,(x,θ)),(0 : ℝ)) = (g t)⁻¹ • (raw (t,(x,θ)),(0 : ℝ)) := by simp
  rw [ha]
  simp only [productProfileRatio_apply,smul_apply,map_smul,smul_smul]
  congr 1
  field_simp [(hg t).ne',(hh t).ne',(hb t).ne']


-- @@ L104-104 verbatim
variable {G H g h b hg hh hb}


-- @@ L106-117 verbatim
theorem WordBound.normalized_bilinear {R A B : ℝ} {d e : ℕ}
    (hG : (G.normalized hT g hg).WordBound 6 R A d)
    (hH : (H.normalized hT h hh).WordBound 6 R B e)
    (L : Space →L[ℝ] Space →L[ℝ] Space) (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (C : ℝ) (hC : 0 ≤ C) (hprofile : ∀ t, |productProfileRatio g h b hb t| ≤ C) :
    ((G.bilinear H L).normalized hT b hb).WordBound 6 R
      (C*(9*productBlockConstant P*‖L‖*A*B)) (d+e) := by
  have hbound := (hG.bilinear hH L hR hA hB).weighted hT (productProfileRatio g h b hb) C hC
      hprofile
  unfold WordBound at *
  rw [G.normalized_bilinear_path H hT g h b hg hh hb L]
  exact hbound


-- @@ L119-130 verbatim
theorem WordBound.normalized_scalarProduct {R A B : ℝ} {d e : ℕ}
    (hG : (G.normalized hT g hg).WordBound 6 R A d)
    (hH : (H.normalized hT h hh).WordBound 6 R B e)
    (L : Space →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (C : ℝ) (hC : 0 ≤ C) (hprofile : ∀ t, |productProfileRatio g h b hb t| ≤ C) :
    ((G.scalarProduct H L hL).normalized hT b hb).WordBound 6 R
      (C*(3*productBlockConstant P*A*B)) (d+e) := by
  have hbound := (hG.scalarProduct hH L hL hR hA hB).weighted hT (productProfileRatio g h b hb) C
      hC hprofile
  unfold WordBound at *
  rw [G.normalized_scalarProduct_path H hT g h b hg hh hb L hL]
  exact hbound


-- @@ L132-143 verbatim
theorem WordBound.normalized_spatialTransport {R A B : ℝ} {d e : ℕ}
    (hG : (G.normalized hT g hg).WordBound 6 R A d)
    (hH : (H.normalized hT h hh).WordBound 6 R B e)
    (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (C : ℝ) (hC : 0 ≤ C) (hprofile : ∀ t, |productProfileRatio g h b hb t| ≤ C) :
    ((G.spatialTransport H).normalized hT b hb).WordBound 6 R
      (C*(9*productBlockConstant P*A*B)) (d+e+1) := by
  have hbound := (hG.spatialTransport hH hR hA hB).weighted hT (productProfileRatio g h b hb) C hC
      hprofile
  unfold WordBound at *
  rw [G.normalized_spatialTransport_path H hT g h b hg hh hb]
  exact hbound


-- @@ L145-145 verbatim
end Field

-- @@ L146-146 verbatim
end EulerPacketCylinderField


-- @@ L148-148 verbatim
end

-- @@ L149-149 verbatim
end


-- @@ L151-151 verbatim
end


-- @@ L153-153 verbatim
@[expose] public section


-- @@ L155-155 verbatim
noncomputable section


-- @@ L157-157 verbatim
namespace EulerPacketCylinderField


-- @@ L159-161 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerPacketPointJets EulerPacketProfileRecursion EulerCylinderPathProduct
  EulerCylinderScalarPrimitive EulerMeanCoefficients EulerParameterWordGevrey EulerGevrey

-- @@ L162-162 verbatim
open scoped ContDiff


-- @@ L164-164 verbatim
namespace SpatialJetField


-- @@ L166-169 verbatim
variable {P T : ℝ} [Fact (0 < P)] {J K : Domain → VectorJet}
  (G : SpatialJetField P T J) (H : SpatialJetField P T K) (hT : 0 ≤ T)
  (g h b : C(Icc (0 : ℝ) T, ℝ))
  (hg : ∀ t, 0 < g t) (hh : ∀ t, 0 < h t) (hb : ∀ t, 0 < b t)


-- @@ L171-189 verbatim
theorem slowAdvection_normalized_bound
    {inverse : Domain → Space →L[ℝ] Space} (F : MatrixCoefficient T inverse)
    {R A B : ℝ} {d e : ℕ}
    (hG : (G.field.normalized hT g hg).WordBound 6 R A d)
    (hH : (H.field.normalized hT h hh).WordBound 6 R B e)
    (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
    (hRF : sobolevCoefficientRadius (Fin 4) Rc ≤ R)
    (hF : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath F.path) a‖ ≤ C * majorant Rc 0 n)
    (c : ℝ) (hc : 0 ≤ c) (hprofile : ∀ t, |productProfileRatio g h b hb t| ≤ c) :
    ((slowAdvection F G H).normalized hT b hb).WordBound 6 R
      (c*(9*productBlockConstant P*(3*sobolevCoefficientAmplitude (Fin 4) 6 Rc C*A)*B))
      (d+e+1) := by
  have hm := Field.WordBound.normalized_multiply hT hG F Rc C hRc hC hA hRF hF
  have ham : 0 ≤ 3*sobolevCoefficientAmplitude (Fin 4) 6 Rc C*A :=
    mul_nonneg (mul_nonneg (by norm_num)
      (sobolevCoefficientAmplitude_nonneg 6 Rc C hRc hC)) hA
  have hs := Field.WordBound.normalized_spatialTransport hT hm hH hR ham hB c hc hprofile
  exact hs.of_path_eq _ rfl


-- @@ L191-213 verbatim
theorem fastAdvection_normalized_bound
    {normal : VectorField} (N : VectorCoefficient T normal)
    {R A B : ℝ} {d e : ℕ}
    (hG : (G.field.normalized hT g hg).WordBound 6 R A d)
    (hH : (H.field.normalized hT h hh).WordBound 6 R B e)
    (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
    (hRN : sobolevCoefficientRadius (Fin 4) Rc ≤ R)
    (hN : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath N.path) a‖ ≤ C * majorant Rc 0 n)
    (c : ℝ) (hc : 0 ≤ c) (hprofile : ∀ t, |productProfileRatio g h b hb t| ≤ c) :
    ((fastAdvection N G H).normalized hT b hb).WordBound 6 R
      (c*(3*productBlockConstant P*(3*sobolevCoefficientAmplitude (Fin 4) 6 Rc C*A)*B))
      (d+e+1) := by
  have hm := Field.WordBound.normalized_multiply hT hG N.normalMatrix Rc C hRc hC hA hRN
    (N.normalMatrix_bound Rc C hN)
  have hd := Field.WordBound.normalized_derivative hT hH 0
  have ham : 0 ≤ 3*sobolevCoefficientAmplitude (Fin 4) 6 Rc C*A :=
    mul_nonneg (mul_nonneg (by norm_num)
      (sobolevCoefficientAmplitude_nonneg 6 Rc C hRc hC)) hA
  have hs := Field.WordBound.normalized_scalarProduct hT hm hd scalarProject
    (le_of_eq scalarProject_norm) hR ham hB c hc hprofile
  have he := hs.of_path_eq ((fastAdvection N G H).normalized hT b hb) rfl
  simpa only [Nat.add_assoc] using he


-- @@ L215-215 verbatim
end SpatialJetField


-- @@ L217-217 verbatim
namespace Field


-- @@ L219-220 verbatim
variable {P T : ℝ} [Fact (0 < P)] (hT : 0 ≤ T)
  (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t)


-- @@ L222-233 verbatim
theorem WordBound.normalized_slowPressure
    {inverse : Domain → Space →L[ℝ] Space} (F : MatrixCoefficient T inverse)
    (p : ScalarField) (G : Field P T (pressureGradient p))
    {q d : ℕ} {R A : ℝ} (hG : (G.normalized hT g hg).WordBound q R A d)
    (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hRF : sobolevCoefficientRadius (Fin 4) Rc ≤ R)
    (hF : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath F.path) a‖ ≤ C * majorant Rc 0 n) :
    ((slowPressure F p G).normalized hT g hg).WordBound q R
      (3*sobolevCoefficientAmplitude (Fin 4) q Rc C*A) d := by
  have hm := WordBound.normalized_multiply hT hG F.adjoint Rc C hRc hC hA hRF
    (F.adjoint_bound Rc C hF)
  exact hm.of_path_eq _ rfl


-- @@ L235-250 verbatim
theorem WordBound.normalized_linearPart
    {strain : Domain → Space →L[ℝ] Space} (M : MatrixCoefficient T strain)
    {raw raw_t : VectorField} (G : Field P T raw) (H : Field P T raw_t)
    (hTpos : 0 < T) (hd : TimeDerivative hTpos.le G H)
    (s : Set ℝ) (hs : s = Icc (0 : ℝ) T)
    {q d : ℕ} {R A B : ℝ}
    (hG : (G.normalized hT g hg).WordBound q R A d)
    (hH : (H.normalized hT g hg).WordBound q R B d)
    (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hRM : sobolevCoefficientRadius (Fin 4) Rc ≤ R)
    (hM : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath M.path) a‖ ≤ C * majorant Rc 0 n) :
    ((linearPart M G H hTpos hd s hs).normalized hT g hg).WordBound q R
      (B+3*sobolevCoefficientAmplitude (Fin 4) q Rc C*A) d := by
  have hm := WordBound.normalized_multiply hT hG M Rc C hRc hC hA hRM hM
  have ha := WordBound.normalized_add hT hH hm
  exact ha.of_path_eq _ rfl


-- @@ L252-252 verbatim
end Field

-- @@ L253-253 verbatim
end EulerPacketCylinderField
