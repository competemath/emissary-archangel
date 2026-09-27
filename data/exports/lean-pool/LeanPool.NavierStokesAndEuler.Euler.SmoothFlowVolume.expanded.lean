/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowJacobian
import LeanPool.NavierStokesAndEuler.Euler.Foundations.DeformationVolume
public import LeanPool.NavierStokesAndEuler.Euler.LinearFundamentalPath
public import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.MeanValue


-- @@ L16-17 verbatim
/-! The actual flow of a trace-free smooth bounded velocity preserves its
Jacobian determinant and Haar volume, in every finite dimension. -/


-- @@ L19-19 verbatim
section


-- @@ L21-22 verbatim
/-! Jacobi's formula in every finite dimension, and determinant preservation
for the actual linear evolution with trace-free coefficient. -/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-28 verbatim
namespace EulerLinearEvolutionDeterminant


-- @@ L30-30 verbatim
open Set Matrix EulerVolterraConvolution EulerLinearDuhamel

-- @@ L31-31 verbatim
open scoped Matrix.Norms.Elementwise


-- @@ L33-36 verbatim
private def determinantRows (ι : Type*) [Fintype ι] [DecidableEq ι] :
    ContinuousMultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ where
  toMultilinearMap := Matrix.detRowAlternating.toMultilinearMap
  cont := continuous_id.matrix_det


-- @@ L38-58 verbatim
theorem matrixJacobi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F M : ℝ → Matrix ι ι ℝ) (S : Set ℝ) (t : ℝ)
    (hF : HasDerivWithinAt F (M t * F t) S t) :
    HasDerivWithinAt (fun s => (F s).det) ((M t).trace * (F t).det) S t := by
  have h := (determinantRows ι).hasFDerivAt (F t) |>.comp_hasDerivWithinAt t hF
  have he : (determinantRows ι).linearDeriv (F t) (M t * F t) =
      (M t).trace * (F t).det := by
    calc
      _ = ∑ i, ((F t).updateRow i ((M t * F t) i)).det :=
        (determinantRows ι).linearDeriv_apply (fun i j => F t i j)
          (fun i j => (M t * F t) i j)
      _ = _ := ?_
    rw [Matrix.trace, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    have hr : (M t * F t) i = ∑ j, M t i j • F t j := by
      funext j
      simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hr, Matrix.det_updateRow_sum]
    rfl
  exact h.congr_deriv he


-- @@ L60-60 verbatim
section Operators


-- @@ L62-62 verbatim
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]


-- @@ L64-67 verbatim
private def operatorCoordinates :
    (E →L[ℝ] E) →L[ℝ] Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  ((LinearMap.toMatrix (Module.finBasis ℝ E) (Module.finBasis ℝ E)).toLinearMap.comp
    (ContinuousLinearMap.coeLM ℝ)).toContinuousLinearMap


-- @@ L69-72 verbatim
private theorem operatorCoordinates_comp (A B : E →L[ℝ] E) :
    operatorCoordinates (A.comp B) = operatorCoordinates A * operatorCoordinates B := by
  exact LinearMap.toMatrix_comp (Module.finBasis ℝ E) (Module.finBasis ℝ E)
    (Module.finBasis ℝ E) A.toLinearMap B.toLinearMap


-- @@ L74-76 verbatim
private theorem operatorCoordinates_det (A : E →L[ℝ] E) :
    (operatorCoordinates A).det = A.det :=
  LinearMap.det_toMatrix (Module.finBasis ℝ E) A.toLinearMap


-- @@ L78-80 verbatim
private theorem operatorCoordinates_trace (A : E →L[ℝ] E) :
    (operatorCoordinates A).trace = LinearMap.trace ℝ E A.toLinearMap :=
  (LinearMap.trace_eq_matrix_trace ℝ (Module.finBasis ℝ E) A.toLinearMap).symm


-- @@ L82-97 verbatim
/-- The finite-dimensional Jacobi formula does not assume invertibility. -/
theorem operatorJacobi (F M : ℝ → (E →L[ℝ] E)) (S : Set ℝ) (t : ℝ)
    (hF : HasDerivWithinAt F ((M t).comp (F t)) S t) :
    HasDerivWithinAt (fun s => (F s).det)
      (LinearMap.trace ℝ E (M t).toLinearMap * (F t).det) S t := by
  have hc := ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ)
    (E := E →L[ℝ] E)
    (F := Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (x := F t) (operatorCoordinates (E := E))
  have hm := HasFDerivAt.comp_hasDerivWithinAt (𝕜 := ℝ)
    (F := E →L[ℝ] E)
    (E := Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) t hc hF
  have hm' := hm.congr_deriv (operatorCoordinates_comp (M t) (F t))
  have h := matrixJacobi (fun s => operatorCoordinates (F s))
    (fun s => operatorCoordinates (M s)) S t hm'
  simpa only [operatorCoordinates_det, operatorCoordinates_trace] using h


-- @@ L99-99 verbatim
end Operators


-- @@ L101-101 verbatim
end EulerLinearEvolutionDeterminant


-- @@ L103-103 verbatim
namespace EulerLinearDuhamel.Evolution


-- @@ L105-105 verbatim
open Set EulerVolterraConvolution EulerLinearEvolutionDeterminant


-- @@ L107-108 verbatim
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {T : ℝ} {hT : 0 ≤ T} {B : C(Icc (0 : ℝ) T, E →L[ℝ] E)}


-- @@ L110-125 verbatim
theorem det_forward_eq_initial (U : Evolution T hT B)
    (htrace : ∀ t, LinearMap.trace ℝ E (B t).toLinearMap = 0)
    (t : Icc (0 : ℝ) T) : (U.forward t).det = (U.forward ⟨0,le_rfl,hT⟩).det := by
  have hd : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun r => (extendPath T hT U.forward r).det) 0 (Icc 0 T) s := by
    intro s hs
    have hF := U.derivative ⟨s,hs⟩
    have h := operatorJacobi (extendPath T hT U.forward) (extendPath T hT B)
      (Icc 0 T) s (by
        simpa only [extendPath, projIcc_of_mem hT hs] using hF)
    simpa only [extendPath, projIcc_of_mem hT hs, htrace, zero_mul] using h
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0) hd
    (fun s hs => by simp) (convex_Icc (0 : ℝ) T)
    (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩) t.property
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero, extendPath,
    projIcc_of_mem hT t.property, projIcc_of_mem hT ⟨le_rfl,hT⟩] using h


-- @@ L127-127 verbatim
end EulerLinearDuhamel.Evolution


-- @@ L129-129 verbatim
namespace EulerLinearDuhamel


-- @@ L131-131 verbatim
open Set


-- @@ L133-133 verbatim
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]


-- @@ L135-141 verbatim
theorem constructedEvolution_det_one (T : ℝ) (hT : 0 ≤ T)
    (B : C(Icc (0 : ℝ) T, E →L[ℝ] E))
    (htrace : ∀ t, LinearMap.trace ℝ E (B t).toLinearMap = 0)
    (t : Icc (0 : ℝ) T) : ((constructedEvolution T hT B).forward t).det = 1 := by
  rw [(constructedEvolution T hT B).det_forward_eq_initial htrace t,
    constructedEvolution_initial]
  exact LinearMap.det_id


-- @@ L143-143 verbatim
end EulerLinearDuhamel


-- @@ L145-145 verbatim
end

-- @@ L146-146 verbatim
end


-- @@ L148-148 verbatim
end


-- @@ L150-150 verbatim
@[expose] public section


-- @@ L152-152 verbatim
noncomputable section


-- @@ L154-154 verbatim
namespace EulerSmoothBanachFlow


-- @@ L156-156 verbatim
open Set MeasureTheory EulerLinearDuhamel


-- @@ L158-160 verbatim
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (T : ℝ) (hT : 0 ≤ T) (A : SmoothTimeField (Icc (0 : ℝ) T) E E)
  (hdiv : ∀ t x, LinearMap.trace ℝ E (fderiv ℝ (A.field t : E → E) x).toLinearMap = 0)


-- @@ L162-169 verbatim
include hdiv in
theorem jacobianEvolution_det_one (t : Icc (0 : ℝ) T) (x : E) :
    ((jacobianEvolution T hT A x).forward t).det = 1 := by
  apply constructedEvolution_det_one
  intro s
  change LinearMap.trace ℝ E (A.derivativeField s (pathFamily T hT A x s)).toLinearMap = 0
  rw [A.derivativeField_eq]
  exact hdiv s _


-- @@ L171-175 verbatim
include hdiv in
theorem forward_det_one (t : Icc (0 : ℝ) T) (x : E) :
    (fderiv ℝ (fun y => (flowData T hT A).forward t y) x).det = 1 := by
  rw [forward_fderiv]
  exact jacobianEvolution_det_one T hT A hdiv t x


-- @@ L177-178 verbatim
variable [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]


-- @@ L180-187 verbatim
include hdiv in
theorem forward_measurePreserving (t : Icc (0 : ℝ) T) :
    MeasurePreserving ((flowData T hT A).forward t) μ μ := by
  apply EulerDeformationVolume.measurePreserving_of_det_one μ
    ((flowData T hT A).forward t) (fun x => (jacobianEvolution T hT A x).forward t)
    (forward_hasFDerivAt_label T hT A t)
  · exact ((flowData T hT A).flowHomeomorph 0 t).bijective
  · exact jacobianEvolution_det_one T hT A hdiv t


-- @@ L189-195 verbatim
include hdiv in
theorem backward_measurePreserving (t : Icc (0 : ℝ) T) :
    MeasurePreserving ((flowData T hT A).backward t) μ μ := by
  let e := (flowData T hT A).flowHomeomorph 0 t
  have hm : MeasurePreserving e.toMeasurableEquiv μ μ :=
    forward_measurePreserving T hT A hdiv μ t
  exact MeasurePreserving.symm e.toMeasurableEquiv hm


-- @@ L197-197 verbatim
end EulerSmoothBanachFlow
