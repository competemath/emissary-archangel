import Submission.MorseLemma2D


-- @@ L3-12 verbatim
/-!
# Smoothness of the radial Hadamard parameter integrals

This file discharges the analytic hypothesis left explicit in
`MorseLemma2D`.  The key input is a reusable fixed-interval theorem: a
jointly smooth scalar integrand has a smooth parameter integral.  We prove it
from mathlib's first-derivative-under-the-integral theorem and induct on the
finite differentiability order; no smoothness assumption on the resulting
integral is introduced.
-/


-- @@ L14-14 verbatim
noncomputable section


-- @@ L16-16 verbatim
open Set Filter Function Metric MeasureTheory

-- @@ L17-17 verbatim
open scoped Topology ContDiff RealInnerProductSpace Interval


-- @@ L19-19 verbatim
namespace Submission


-- @@ L21-21 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)


-- @@ L23-23 verbatim
namespace MorseIntegralSmooth


-- @@ L25-28 verbatim
/-- Restriction of the total derivative of a jointly defined function to its
parameter-space directions. -/
def parameterFDeriv (F : E₂ → ℝ → ℝ) (x : E₂) (t : ℝ) : E₂ →L[ℝ] ℝ :=
  (fderiv ℝ F.uncurry (x, t)).comp (ContinuousLinearMap.inl ℝ E₂ ℝ)


-- @@ L30-32 verbatim
lemma parameterFDeriv_apply (F : E₂ → ℝ → ℝ) (x : E₂) (t : ℝ) (v : E₂) :
    parameterFDeriv F x t v = fderiv ℝ F.uncurry (x, t) (v, 0) := by
  rfl


-- @@ L34-42 verbatim
/-- Smoothness of the partial derivative, including its dependence on the
integration variable. -/
lemma contDiff_parameterFDeriv_apply {F : E₂ → ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F.uncurry) (v : E₂) :
    ContDiff ℝ ∞ (fun p : E₂ × ℝ => parameterFDeriv F p.1 p.2 v) := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ F.uncurry) :=
    hF.fderiv_right (by simp)
  have hv : ContDiff ℝ ∞ (fun _ : E₂ × ℝ => (v, (0 : ℝ))) := contDiff_const
  simpa [parameterFDeriv_apply] using hD.clm_apply hv


-- @@ L44-52 verbatim
lemma continuous_parameterFDeriv {F : E₂ → ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F.uncurry) :
    Continuous (fun p : E₂ × ℝ => parameterFDeriv F p.1 p.2) := by
  have hD : Continuous (fderiv ℝ F.uncurry) :=
    hF.continuous_fderiv (by simp)
  let R : ((E₂ × ℝ) →L[ℝ] ℝ) →L[ℝ] (E₂ →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ E₂ (E₂ × ℝ) ℝ).flip
      (ContinuousLinearMap.inl ℝ E₂ ℝ)
  exact R.continuous.comp hD


-- @@ L54-94 verbatim
/-- A jointly `C∞` scalar integrand may be differentiated under the fixed
interval integral.  Compactness of a closed parameter ball times `[0,1]`
supplies the local uniform derivative bound required by the dominated
convergence theorem. -/
theorem hasFDerivAt_intervalIntegral {F : E₂ → ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F.uncurry) (x₀ : E₂) :
    HasFDerivAt (fun x => ∫ t in (0 : ℝ)..1, F x t)
      (∫ t in (0 : ℝ)..1, parameterFDeriv F x₀ t) x₀ := by
  let K : Set (E₂ × ℝ) := closedBall x₀ 1 ×ˢ Icc 0 1
  have hK : IsCompact K := (isCompact_closedBall x₀ 1).prod isCompact_Icc
  have hcontD : Continuous (fun p : E₂ × ℝ => ‖parameterFDeriv F p.1 p.2‖) :=
    (continuous_parameterFDeriv hF).norm
  obtain ⟨M, hM⟩ := hK.bddAbove_image hcontD.continuousOn
  have hbound : ∀ p ∈ K, ‖parameterFDeriv F p.1 p.2‖ ≤ M := by
    intro p hp
    exact hM (mem_image_of_mem _ hp)
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := ball x₀ 1) (bound := fun _ => M) (ball_mem_nhds x₀ zero_lt_one)
  · filter_upwards with x
    exact (hF.continuous.uncurry_left x).aestronglyMeasurable
  · exact (hF.continuous.uncurry_left x₀).intervalIntegrable 0 1
  · exact ((continuous_parameterFDeriv hF).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards with t ht x hx
    have htI : t ∈ Icc (0 : ℝ) 1 := by
      rw [uIoc_of_le zero_le_one] at ht
      exact ⟨ht.1.le, ht.2⟩
    exact hbound (x, t)
      ⟨Metric.mem_closedBall.mpr (Metric.mem_ball.mp hx).le, htI⟩
  · exact continuous_const.intervalIntegrable 0 1
  · filter_upwards with t _ x _
    have hsection : HasFDerivAt (fun y : E₂ => F y t)
        (parameterFDeriv F x t) x := by
      have htotal : HasFDerivAt F.uncurry (fderiv ℝ F.uncurry (x, t)) (x, t) :=
        (hF.differentiable (by simp)).differentiableAt.hasFDerivAt
      have hc : HasFDerivAt (fun y : E₂ => F y t)
          ((fderiv ℝ F.uncurry (x, t)).comp
            (ContinuousLinearMap.inl ℝ E₂ ℝ)) x := by
        exact htotal.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)
      exact hc
    exact hsection


-- @@ L96-101 verbatim
lemma fderiv_intervalIntegral {F : E₂ → ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F.uncurry) :
    fderiv ℝ (fun x => ∫ t in (0 : ℝ)..1, F x t) =
      fun x => ∫ t in (0 : ℝ)..1, parameterFDeriv F x t := by
  funext x
  exact (hasFDerivAt_intervalIntegral hF x).fderiv


-- @@ L103-138 verbatim
/-- Finite-order core of smooth parameter integration.  The induction stays
in scalar codomain by applying the derivative to a fixed direction, while
finite dimensionality reconstructs the bundled derivative. -/
theorem contDiff_intervalIntegral_nat (n : ℕ) {F : E₂ → ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F.uncurry) :
    ContDiff ℝ n (fun x => ∫ t in (0 : ℝ)..1, F x t) := by
  induction n generalizing F with
  | zero =>
      change ContDiff ℝ (0 : ℕ∞ω) (fun x => ∫ t in (0 : ℝ)..1, F x t)
      exact contDiff_zero.mpr <|
        intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          (μ := MeasureTheory.volume) hF.continuous 0 1
  | succ n ih =>
      rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp,
        contDiff_succ_iff_fderiv_apply]
      have hd : Differentiable ℝ (fun x => ∫ t in (0 : ℝ)..1, F x t) :=
        fun x => (hasFDerivAt_intervalIntegral hF x).differentiableAt
      refine ⟨hd, ?_, ?_⟩
      · simp
      · intro v
        rw [fderiv_intervalIntegral hF]
        let Fv : E₂ → ℝ → ℝ := fun x t => parameterFDeriv F x t v
        have hFv : ContDiff ℝ ∞ Fv.uncurry := by
          change ContDiff ℝ ∞ (fun p : E₂ × ℝ => parameterFDeriv F p.1 p.2 v)
          exact contDiff_parameterFDeriv_apply hF v
        have hphi (x : E₂) : IntervalIntegrable
            (fun t => parameterFDeriv F x t) MeasureTheory.volume 0 1 :=
          ((continuous_parameterFDeriv hF).comp
            (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
        have heq :
            (fun x : E₂ => (∫ t in (0 : ℝ)..1, parameterFDeriv F x t) v) =
              fun x => ∫ t in (0 : ℝ)..1, parameterFDeriv F x t v := by
          funext x
          exact ContinuousLinearMap.intervalIntegral_apply (hphi x) v
        rw [heq]
        exact ih hFv


-- @@ L140-146 verbatim
/-- A jointly smooth scalar integrand has a smooth integral over `[0,1]`. -/
theorem contDiff_intervalIntegral {F : E₂ → ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F.uncurry) :
    ContDiff ℝ ∞ (fun x => ∫ t in (0 : ℝ)..1, F x t) := by
  rw [contDiff_infty]
  intro n
  exact contDiff_intervalIntegral_nat n hF


-- @@ L148-163 verbatim
private lemma contDiff_radialHessian_eval {f : E₂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (u v : E₂) :
    ContDiff ℝ ∞ (fun p : E₂ × ℝ =>
      iteratedFDeriv ℝ 2 f (p.2 • p.1) ![u, v]) := by
  have hinf : (∞ : ℕ∞ω) + 2 = ∞ := by
    rw [show (2 : ℕ∞ω) = 1 + 1 by norm_num, ← add_assoc,
      ENat.coe_top_add_one, ENat.coe_top_add_one]
  have hHess : ContDiff ℝ ∞ (iteratedFDeriv ℝ 2 f) :=
    hf.iteratedFDeriv_right (hinf.le)
  have hrad : ContDiff ℝ ∞ (fun p : E₂ × ℝ => p.2 • p.1) := by
    fun_prop
  have hcomp : ContDiff ℝ ∞ (fun p : E₂ × ℝ =>
      iteratedFDeriv ℝ 2 f (p.2 • p.1)) := hHess.comp hrad
  let ev : (E₂ [×2]→L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E₂) ℝ ![u, v]
  exact ev.contDiff.comp hcomp


-- @@ L165-176 verbatim
/-- The first radial Hessian coefficient is globally smooth. -/
theorem contDiff_integratedHadamardA {f : E₂ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (HadamardQuadraticData.integratedHadamardA f) := by
  change ContDiff ℝ ∞ (fun x : E₂ => ∫ t in (0 : ℝ)..1,
    (1 - t) * iteratedFDeriv ℝ 2 f (t • x)
      ![HadamardQuadraticData.e₀, HadamardQuadraticData.e₀])
  apply contDiff_intervalIntegral
  change ContDiff ℝ ∞ (fun p : E₂ × ℝ =>
    (1 - p.2) * iteratedFDeriv ℝ 2 f (p.2 • p.1)
      ![HadamardQuadraticData.e₀, HadamardQuadraticData.e₀])
  exact (contDiff_const.sub contDiff_snd).mul
    (contDiff_radialHessian_eval hf _ _)


-- @@ L178-196 verbatim
/-- The mixed radial Hessian coefficient is globally smooth. -/
theorem contDiff_integratedHadamardB {f : E₂ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (HadamardQuadraticData.integratedHadamardB f) := by
  change ContDiff ℝ ∞ (fun x : E₂ => ∫ t in (0 : ℝ)..1,
    (1 - t) *
      ((iteratedFDeriv ℝ 2 f (t • x)
          ![HadamardQuadraticData.e₀, HadamardQuadraticData.e₁] +
        iteratedFDeriv ℝ 2 f (t • x)
          ![HadamardQuadraticData.e₁, HadamardQuadraticData.e₀]) / 2))
  apply contDiff_intervalIntegral
  change ContDiff ℝ ∞ (fun p : E₂ × ℝ =>
    (1 - p.2) *
      ((iteratedFDeriv ℝ 2 f (p.2 • p.1)
          ![HadamardQuadraticData.e₀, HadamardQuadraticData.e₁] +
        iteratedFDeriv ℝ 2 f (p.2 • p.1)
          ![HadamardQuadraticData.e₁, HadamardQuadraticData.e₀]) / 2))
  exact (contDiff_const.sub contDiff_snd).mul
    (((contDiff_radialHessian_eval hf _ _).add
      (contDiff_radialHessian_eval hf _ _)).div_const 2)


-- @@ L198-209 verbatim
/-- The second radial Hessian coefficient is globally smooth. -/
theorem contDiff_integratedHadamardC {f : E₂ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (HadamardQuadraticData.integratedHadamardC f) := by
  change ContDiff ℝ ∞ (fun x : E₂ => ∫ t in (0 : ℝ)..1,
    (1 - t) * iteratedFDeriv ℝ 2 f (t • x)
      ![HadamardQuadraticData.e₁, HadamardQuadraticData.e₁])
  apply contDiff_intervalIntegral
  change ContDiff ℝ ∞ (fun p : E₂ × ℝ =>
    (1 - p.2) * iteratedFDeriv ℝ 2 f (p.2 • p.1)
      ![HadamardQuadraticData.e₁, HadamardQuadraticData.e₁])
  exact (contDiff_const.sub contDiff_snd).mul
    (contDiff_radialHessian_eval hf _ _)


-- @@ L211-211 verbatim
end MorseIntegralSmooth


-- @@ L213-213 verbatim
namespace HadamardQuadraticData


-- @@ L215-223 verbatim
/-- The explicit radial-integral quadratic data attached to an arbitrary
smooth critical function.  Unlike `integratedHadamardData`, this constructor
has no parameter-integral smoothness hypotheses. -/
def integratedHadamardDataOfContDiff {f : E₂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hcrit : fderiv ℝ f 0 = 0) : HadamardQuadraticData f :=
  integratedHadamardData hf hcrit
    (MorseIntegralSmooth.contDiff_integratedHadamardA hf).contDiffAt
    (MorseIntegralSmooth.contDiff_integratedHadamardB hf).contDiffAt
    (MorseIntegralSmooth.contDiff_integratedHadamardC hf).contDiffAt


-- @@ L225-234 verbatim
/-- End-to-end two-dimensional Morse lemma for an arbitrary smooth function,
with the three former parameter-integral assumptions discharged. -/
theorem morseLemma2D_integrated_of_contDiff {g : E₂ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hcrit : fderiv ℝ g 0 = 0)
    (hdet : integratedHadamardDet g ≠ 0) :
    Nonempty (LocalMorseNormalForm g) :=
  morseLemma2D_integrated hg hcrit
    (MorseIntegralSmooth.contDiff_integratedHadamardA hg).contDiffAt
    (MorseIntegralSmooth.contDiff_integratedHadamardB hg).contDiffAt
    (MorseIntegralSmooth.contDiff_integratedHadamardC hg).contDiffAt hdet


-- @@ L236-236 verbatim
end HadamardQuadraticData


-- @@ L238-238 verbatim
end Submission
