/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.MeasureTheory.Function.Holder
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.CylinderMollifier


-- @@ L12-12 verbatim
/-! Set integration as a bounded functional on L², and its commutation with Bochner averages. -/


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-18 verbatim
namespace EulerSetIntegralL2


-- @@ L20-20 verbatim
open MeasureTheory

-- @@ L21-21 verbatim
open scoped ENNReal NNReal Topology


-- @@ L23-24 verbatim
variable {X V : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]


-- @@ L26-29 verbatim
/-- Integration on a finite-measure set as a genuine bounded linear map on L². -/
def setIntegralL2 (s : Set X) (hs : MeasurableSet s) (hμs : μ s ≠ ⊤) : Lp V 2 μ →L[ℝ] V :=
  (ContinuousLinearMap.lsmul ℝ ℝ).lpPairing μ 2 2
    (indicatorConstLp 2 hs hμs (1 : ℝ))


-- @@ L31-43 verbatim
theorem setIntegralL2_apply (s : Set X) (hs : MeasurableSet s) (hμs : μ s ≠ ⊤)
    (f : Lp V 2 μ) : setIntegralL2 s hs hμs f = ∫ x in s, f x ∂μ := by
  rw [setIntegralL2, ContinuousLinearMap.lpPairing_eq_integral]
  calc
    _ = ∫ x, s.indicator (fun y => f y) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := (1 : ℝ))] with
          x hx
      rw [hx]
      by_cases hxs : x ∈ s
      · simp [hxs]
      · simp [hxs]
    _ = _ := integral_indicator hs


-- @@ L45-52 verbatim
/-- Bochner averaging of L² elements commutes with integration on every finite-measure set. -/
theorem setIntegral_integral_L2 {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    (s : Set X) (hs : MeasurableSet s) (hμs : μ s ≠ ⊤)
    (F : Y → Lp V 2 μ) (hF : Integrable F ν) :
    (∫ x in s, (∫ y, F y ∂ν) x ∂μ) = ∫ y, ∫ x in s, F y x ∂μ ∂ν := by
  rw [← setIntegralL2_apply s hs hμs,
    ← (setIntegralL2 s hs hμs).integral_comp_comm hF]
  simp_rw [setIntegralL2_apply]


-- @@ L54-54 verbatim
section Cylinder


-- @@ L56-56 verbatim
open EulerLiftedGradientSpace EulerCylinderCoordinates EulerCylinderMollifier EulerSobolev


-- @@ L58-58 verbatim
variable (period : ℝ) [Fact (0 < period)]


-- @@ L60-63 verbatim
omit [Fact (0 < period)] in
theorem euclideanCover_neg (y : Domain 4) : euclideanCover period (-y) = -euclideanCover period y
    := by
  simp [euclideanCover, coveringMap, map_neg]


-- @@ L65-81 verbatim
/-- The Bochner L² mollifier and the classical convolution have the same iterated finite-set
integrals. -/
theorem mollify_setIntegral (n : ℕ) (f : LiftL2 period) (s : Set (LiftDomain period))
    (hs : MeasurableSet s) (hμs : liftMeasure period s ≠ ⊤) :
    (∫ x in s, mollify period n f x ∂liftMeasure period) =
      ∫ y : Domain 4, ∫ x in s, mollifierKernel n y • f (x - euclideanCover period y)
        ∂liftMeasure period := by
  rw [mollify_eq_integral, setIntegral_integral_L2 s hs hμs _ (kernel_orbit_integrable period n f)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul (mollifierKernel n y) (orbit period f (-y))),
    ae_restrict_of_ae (translation_ae period (euclideanCover period (-y)) f)] with x hx hy
  rw [hx]
  change mollifierKernel n y • (translation period (euclideanCover period (-y)) f) x = _
  rw [hy, euclideanCover_neg, sub_eq_add_neg]


-- @@ L83-83 verbatim
end Cylinder


-- @@ L85-85 verbatim
end EulerSetIntegralL2
