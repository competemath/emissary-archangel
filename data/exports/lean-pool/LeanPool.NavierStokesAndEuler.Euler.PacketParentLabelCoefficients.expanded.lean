/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.MeanClassicalWordBounds
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import Mathlib.Algebra.Order.Star.Real
public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevEmbedding
public import LeanPool.NavierStokesAndEuler.Euler.MeanSmoothRepresentative
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevBlocks
import LeanPool.NavierStokesAndEuler.Euler.Foundations.SobolevDerivativeNorm
import LeanPool.NavierStokesAndEuler.Euler.GevreyFixedShift
import LeanPool.NavierStokesAndEuler.Euler.MeanSpatialEvaluation
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder


-- @@ L19-21 verbatim
/-! The physical-label estimate (21) supplies the multiplier inputs in (H1).
The displacement, velocity and acceleration are the actual L² fields.  The
identity part of the deformation is never asserted to lie in L². -/


-- @@ L23-23 verbatim
section


-- @@ L25-29 verbatim
/-! Source (21) controls actual ordered physical-label derivatives in a fixed
Sobolev norm.  This file converts those genuine L² blocks to uniform spatial
coefficient bounds.  The embedding constant is independent of the external
order; only the one derivative from displacement to deformation enlarges
the coefficient radius. -/


-- @@ L31-31 verbatim
@[expose] public section


-- @@ L33-33 verbatim
noncomputable section


-- @@ L35-35 verbatim
namespace EulerPacketParentLabelBounds


-- @@ L37-40 verbatim
open Set MeasureTheory Finset ContinuousLinearMap EulerSmoothLimit
  EulerMeanSolenoidal EulerMeanSmoothRepresentative EulerMeanClassicalWordBounds
  EulerParameterWordGevrey EulerSobolevPointEvaluation EulerCylinderSobolevSpace EulerGevrey
  EulerOperatorGevreyCalculus

-- @@ L41-41 verbatim
open scoped ContDiff


-- @@ L43-44 verbatim
/-- Direction, given by `EuclideanSpace.single i 1`. -/
def direction (i : Fin 3) : Space := EuclideanSpace.single i 1


-- @@ L46-47 verbatim
/-- Embedding cost, given by `sobolevEmbeddingConstant 1 3`. -/
def embeddingCost : ℝ := sobolevEmbeddingConstant 1 3


-- @@ L49-50 verbatim
theorem embeddingCost_nonneg : 0 ≤ embeddingCost :=
  sobolevEmbeddingConstant_nonneg 1 3


-- @@ L52-55 verbatim
theorem tensor_le_wordSum {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Space → V) (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n f x‖ ≤ wordSum direction f n x :=
  EulerSobolevDerivativeNorm.multilinear_norm_le_coordinate_sum 3 n _


-- @@ L57-64 verbatim
theorem representative_norm_le_base (u : L2) (hu : SmoothOrbit u) (q : ℕ)
    (hq : 3 ≤ q) (x : Space) :
    ‖representative u hu x‖ ≤
      embeddingCost*baseSize direction q (fun a : Space => translation a u) 0 := by
  apply (EulerMeanSmoothRepresentative.representative_bound u hu x).trans
  apply mul_le_mul_of_nonneg_left _ embeddingCost_nonneg
  apply le_trans _ (baseSize_mono direction _ 0 hq)
  exact sum_le_sum (fun k _ => tensor_le_wordSum (fun a : Space => translation a u) k 0)


-- @@ L66-84 verbatim
/-- Fixed H³ evaluation is applied after each external word, without a
tensor-coordinate norm equivalence depending on the word length. -/
theorem representative_tensor_le_block (u : L2) (hu : SmoothOrbit u)
    (q : ℕ) (hq : 3 ≤ q) (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (representative u hu) x‖ ≤
      embeddingCost*block direction q (fun a : Space => translation a u) n 0 := by
  apply (tensor_le_wordSum (representative u hu) n x).trans
  unfold wordSum block
  rw [mul_sum]
  apply sum_le_sum
  intro w _
  rw [representative_word direction u hu w x]
  have h := representative_norm_le_base (ordinaryWord direction u w)
    (ordinaryWord_smooth direction u hu w) q hq x
  have he : (fun a : Space => translation a (ordinaryWord direction u w)) =
      wordDerivative direction (fun a : Space => translation a u) w :=
    funext (ordinaryWord_translation direction u hu w)
  rw [he] at h
  exact h


-- @@ L86-95 verbatim
/-- The bound applies to the actual continuous representative, not merely
to a field chosen by the Sobolev reconstruction. -/
theorem field_tensor_le_block (u : L2) (hu : SmoothOrbit u)
    (f : Space → Space) (hf : Continuous f) (hrep : (u : Space → Space) =ᵐ[volume] f)
    (q : ℕ) (hq : 3 ≤ q) (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n f x‖ ≤
      embeddingCost*block direction q (fun a : Space => translation a u) n 0 := by
  have he := representative_unique u hu f hf hrep
  rw [← he]
  exact representative_tensor_le_block u hu q hq n x


-- @@ L97-104 verbatim
theorem field_tensor_gevrey (u : L2) (hu : SmoothOrbit u)
    (f : Space → Space) (hf : Continuous f) (hrep : (u : Space → Space) =ᵐ[volume] f)
    (q : ℕ) (hq : 3 ≤ q) (R A : ℝ)
    (hb : ∀ n, block direction q (fun a : Space => translation a u) n 0 ≤ A*majorant R 0 n)
    (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n f x‖ ≤ (embeddingCost*A)*majorant R 0 n :=
  (field_tensor_le_block u hu f hf hrep q hq n x).trans
    ((mul_le_mul_of_nonneg_left (hb n) embeddingCost_nonneg).trans_eq (by ring))


-- @@ L106-119 verbatim
/-- Differentiating the parent particle map once costs a fixed coefficient
radius factor four and a single polynomial amplitude factor R. -/
theorem gradient_gevrey (u : L2) (hu : SmoothOrbit u)
    (f : Space → Space) (hf : Continuous f) (hrep : (u : Space → Space) =ᵐ[volume] f)
    (q : ℕ) (hq : 3 ≤ q) (R A : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (hb : ∀ n, block direction q (fun a : Space => translation a u) n 0 ≤ A*majorant R 0 n)
    (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (fderiv ℝ f) x‖ ≤ (embeddingCost*A*R)*majorant (4*R) 0 n := by
  rw [norm_iteratedFDeriv_fderiv]
  have h := field_tensor_gevrey u hu f hf hrep q hq R A hb (n+1) x
  have hs := majorant_one_le_radius_four R hR n
  change majorant R 0 (n+1) ≤ R*majorant (4*R) 0 n at hs
  exact h.trans ((mul_le_mul_of_nonneg_left hs (mul_nonneg embeddingCost_nonneg hA)).trans_eq (by
      ring))


-- @@ L121-138 verbatim
/-- Label normalization by a contraction does not enlarge positive spatial
derivatives.  This applies to the source scaling a=ℓ y. -/
theorem gradient_scaled_gevrey (u : L2) (hu : SmoothOrbit u)
    (f : Space → Space) (hf : ContDiff ℝ ∞ f) (hrep : (u : Space → Space) =ᵐ[volume] f)
    (q : ℕ) (hq : 3 ≤ q) (R A : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (hb : ∀ n, block direction q (fun a : Space => translation a u) n 0 ≤ A*majorant R 0 n)
    (L : Space →L[ℝ] Space) (hL : ‖L‖ ≤ 1) (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ f (L y)) x‖ ≤
      (embeddingCost*A*R)*majorant (4*R) 0 n := by
  change ‖iteratedFDeriv ℝ n (fderiv ℝ f ∘ L) x‖ ≤ _
  rw [L.iteratedFDeriv_comp_right (hf.fderiv_right (m := ∞) (by simp)) x (by simp)]
  have hc := (iteratedFDeriv ℝ n (fderiv ℝ f) (L x)).norm_compContinuousLinearMap_le
    (fun _ : Fin n => L)
  simp only [prod_const,card_univ,Fintype.card_fin] at hc
  apply hc.trans
  apply le_trans _ (gradient_gevrey u hu f hf.continuous hrep q hq R A hR hA hb n (L x))
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg L) hL)
    (norm_nonneg (iteratedFDeriv ℝ n (fderiv ℝ f) (L x)))


-- @@ L140-153 verbatim
/-- The actual deformation is identity plus the derivative of the L²
displacement.  The identity is kept out of the spatial L² datum. -/
theorem deformation_scaled_gevrey (u : L2) (hu : SmoothOrbit u)
    (f : Space → Space) (hf : ContDiff ℝ ∞ f) (hrep : (u : Space → Space) =ᵐ[volume] f)
    (q : ℕ) (hq : 3 ≤ q) (R A : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (hb : ∀ n, block direction q (fun a : Space => translation a u) n 0 ≤ A*majorant R 0 n)
    (L : Space →L[ℝ] Space) (hL : ‖L‖ ≤ 1) (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (fun y => ContinuousLinearMap.id ℝ Space+fderiv ℝ f (L y)) x‖ ≤
      (1+embeddingCost*A*R)*majorant (4*R) 0 n :=
  add_bound (fun _ : Space => ContinuousLinearMap.id ℝ Space) (fun y => fderiv ℝ f (L y))
    contDiff_const ((hf.fderiv_right (m := ∞) (by simp)).comp L.contDiff)
    (4*R) 1 (embeddingCost*A*R) 0
    (const_bound (ContinuousLinearMap.id ℝ Space) (4*R) 1 (by positivity) norm_id_le)
    (gradient_scaled_gevrey u hu f hf hrep q hq R A hR hA hb L hL) n x


-- @@ L155-155 verbatim
end EulerPacketParentLabelBounds


-- @@ L157-157 verbatim
end

-- @@ L158-158 verbatim
end


-- @@ L160-160 verbatim
end


-- @@ L162-162 verbatim
@[expose] public section


-- @@ L164-164 verbatim
noncomputable section


-- @@ L166-166 verbatim
namespace EulerPacketParentLabelBounds


-- @@ L168-170 verbatim
open MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanSmoothRepresentative EulerMeanClassicalWordBounds EulerParameterWordGevrey
  EulerGevrey EulerOperatorGevreyCalculus

-- @@ L171-171 verbatim
open scoped ContDiff


-- @@ L173-174 verbatim
/-- Coefficient radius, given by `max 1024 (4*K)`. -/
def coefficientRadius (K : ℝ) : ℝ := max 1024 (4*K)

-- @@ L175-176 verbatim
/-- Gradient amplitude, given by `embeddingCost*K^2`. -/
def gradientAmplitude (K : ℝ) : ℝ := embeddingCost*K^2

-- @@ L177-178 verbatim
/-- Frame amplitude, given by `1+gradientAmplitude K`. -/
def frameAmplitude (K : ℝ) : ℝ := 1+gradientAmplitude K


-- @@ L180-180 verbatim
theorem coefficientRadius_lower (K : ℝ) : 1024 ≤ coefficientRadius K := le_max_left _ _

-- @@ L181-182 verbatim
theorem coefficientRadius_nonneg (K : ℝ) : 0 ≤ coefficientRadius K :=
  (by norm_num : (0 : ℝ) ≤ 1024).trans (coefficientRadius_lower K)

-- @@ L183-184 verbatim
theorem gradientAmplitude_nonneg (K : ℝ) : 0 ≤ gradientAmplitude K :=
  mul_nonneg embeddingCost_nonneg (sq_nonneg K)

-- @@ L185-186 verbatim
theorem frameAmplitude_nonneg (K : ℝ) : 0 ≤ frameAmplitude K :=
  add_nonneg zero_le_one (gradientAmplitude_nonneg K)


-- @@ L188-192 verbatim
/-- An actual scalar label scaling with 0≤ℓ≤1 is a linear contraction. -/
theorem labelScaling_norm_le (ℓ : ℝ) (hℓ : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1) :
    ‖ℓ • ContinuousLinearMap.id ℝ Space‖ ≤ 1 := by
  rw [norm_smul,Real.norm_of_nonneg hℓ]
  exact (mul_le_mul_of_nonneg_left norm_id_le hℓ).trans (by simpa only [mul_one] using hℓ1)


-- @@ L194-201 verbatim
theorem source_block_bound (u : L2) (hu : SmoothOrbit u) (K : ℝ)
    (hb : ∀ n, classicalBlockSize direction 6 u hu n ≤ K ^ (n + 1) * (n.factorial : ℝ) ^ 2)
    (n : ℕ) : block direction 6 (fun a : Space => translation a u) n 0 ≤ K*majorant K 0 n := by
  have h := hb n
  rw [classicalBlockSize_eq] at h
  convert h using 1
  simp only [majorant,Nat.add_zero,pow_succ]
  ring


-- @@ L203-217 verbatim
/-- A velocity or acceleration in the literal physical-label H⁶ word norm
gives its actual spatial Jacobian at one polynomial coefficient radius. -/
theorem source_gradient_bound (u : L2) (hu : SmoothOrbit u)
    (f : Space → Space) (hf : ContDiff ℝ ∞ f) (hrep : (u : Space → Space) =ᵐ[volume] f)
    (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ n, classicalBlockSize direction 6 u hu n ≤ K ^ (n + 1) * (n.factorial : ℝ) ^ 2)
    (L : Space →L[ℝ] Space) (hL : ‖L‖ ≤ 1) (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ f (L y)) x‖ ≤
      gradientAmplitude K*majorant (coefficientRadius K) 0 n := by
  have h := gradient_scaled_gevrey u hu f hf hrep 6 (by omega) K K hK hK
    (source_block_bound u hu K hb) L hL n x
  have hr := majorant_radius_mono (4*K) (coefficientRadius K) (by positivity) (le_max_right _ _) 0 n
  have he : embeddingCost*K*K = gradientAmplitude K := by unfold gradientAmplitude; ring
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_left hr (gradientAmplitude_nonneg K))


-- @@ L219-234 verbatim
/-- The parent displacement bound gives the full deformation, including
its constant identity, without making the identity an L² datum. -/
theorem source_deformation_bound (u : L2) (hu : SmoothOrbit u)
    (f : Space → Space) (hf : ContDiff ℝ ∞ f) (hrep : (u : Space → Space) =ᵐ[volume] f)
    (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ n, classicalBlockSize direction 6 u hu n ≤ K ^ (n + 1) * (n.factorial : ℝ) ^ 2)
    (L : Space →L[ℝ] Space) (hL : ‖L‖ ≤ 1) (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (fun y => ContinuousLinearMap.id ℝ Space+fderiv ℝ f (L y)) x‖ ≤
      frameAmplitude K*majorant (coefficientRadius K) 0 n := by
  have h := deformation_scaled_gevrey u hu f hf hrep 6 (by omega) K K hK hK
    (source_block_bound u hu K hb) L hL n x
  have hr := majorant_radius_mono (4*K) (coefficientRadius K) (by positivity) (le_max_right _ _) 0 n
  have he : 1+embeddingCost*K*K = frameAmplitude K := by
      unfold frameAmplitude gradientAmplitude; ring
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_left hr (frameAmplitude_nonneg K))


-- @@ L236-236 verbatim
end EulerPacketParentLabelBounds
