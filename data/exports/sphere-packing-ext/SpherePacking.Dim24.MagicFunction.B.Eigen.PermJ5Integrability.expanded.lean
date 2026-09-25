module
public import SpherePacking.Dim24.MagicFunction.B.Eigen.PermJ5KernelSetup
import SpherePacking.Dim24.MagicFunction.B.Defs.PsiSDecay
import SpherePacking.ForMathlib.IntegrablePowMulExp
import SpherePacking.ForMathlib.GaussianRexpIntegral
import SpherePacking.ForMathlib.IntegralProd
import SpherePacking.Contour.PermJ5Kernel


-- @@ L9-17 verbatim
/-!
# Integrability of the `PermJ5` kernel

This file proves integrability of the kernel appearing in the `perm_J₅` Fourier permutation
argument, together with supporting Gaussian integral bounds needed to apply Fubini.

## Main statements
* `PermJ5.integrable_kernel`
-/


-- @@ L19-19 verbatim
open scoped Real

-- @@ L20-20 verbatim
open Complex


-- @@ L22-22 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L24-24 verbatim
namespace SpherePacking.Dim24.BFourier

-- @@ L25-25 verbatim
open MeasureTheory Set Filter

-- @@ L26-26 verbatim
open scoped RealInnerProductSpace


-- @@ L28-28 verbatim
noncomputable section



-- @@ L31-31 verbatim
namespace PermJ5


-- @@ L33-33 verbatim
open MeasureTheory Set

-- @@ L34-34 verbatim
open SpherePacking.Integration (μIciOne)


-- @@ L36-38 expanded
lemma integral_gaussian_rexp (s : ℝ) (hs : 0 < s) :
    (∫ x : EuclideanSpace ℝ (Fin 24), Real.exp (-π * (‖x‖ ^ 2) / s)) = s ^ 12 := by
  simpa using SpherePacking.ForMathlib.integral_gaussian_rexp_even (k := 12) (s := s) hs


-- @@ L40-47 expanded
lemma kernel_norm_eq (w : EuclideanSpace ℝ (Fin 24)) (x : EuclideanSpace ℝ (Fin 24)) (s : ℝ) :
    ‖kernel w (x, s)‖ =
      (‖ψS' ((Complex.I : ℂ) * (s : ℂ))‖ * ‖(s ^ (-12 : ℤ) : ℂ)‖) * Real.exp (-π * (‖x‖ ^ 2) / s) :=
  by
  -- Use the generic norm computation for the standard kernel shape.
  simpa [kernel, J5Change.g] using
    (SpherePacking.Contour.permJ5_kernel_norm_eq_of (ψS' := ψS') (k := 12) (w := w) (x := x) (s :=
      s))


-- @@ L49-91 expanded
lemma integrable_kernel_slice (w : EuclideanSpace ℝ (Fin 24)) (s : ℝ) (hs : 1 ≤ s) :
    Integrable (fun x : EuclideanSpace ℝ (Fin 24) ↦ kernel w (x, s))
      (volume : Measure (EuclideanSpace ℝ (Fin 24))) :=
  by
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hmajor :
    Integrable
      (fun x : EuclideanSpace ℝ (Fin 24) ↦
        (‖ψS' ((Complex.I : ℂ) * (s : ℂ))‖ * ‖(s ^ (-12 : ℤ) : ℂ)‖) * Real.exp (-π * (‖x‖ ^ 2) / s))
      (volume : Measure (EuclideanSpace ℝ (Fin 24))) :=
    by
    simpa [mul_assoc] using
      (integrable_gaussian_rexp (s := s) hs0).const_mul
        (‖ψS' ((Complex.I : ℂ) * (s : ℂ))‖ * ‖(s ^ (-12 : ℤ) : ℂ)‖)
  have hmeas :
    AEStronglyMeasurable (fun x : EuclideanSpace ℝ (Fin 24) ↦ kernel w (x, s))
      (volume : Measure (EuclideanSpace ℝ (Fin 24))) :=
    by
    have hs_mem : s ∈ Ici (1 : ℝ) := by simpa [Set.mem_Ici] using hs
    have hpair_cont : Continuous fun x : EuclideanSpace ℝ (Fin 24) => (x, s) :=
      continuous_id.prodMk continuous_const
    have hpair_on :
      ContinuousOn (fun x : EuclideanSpace ℝ (Fin 24) => (x, s))
        (univ : Set (EuclideanSpace ℝ (Fin 24))) :=
      hpair_cont.continuousOn
    have hmaps :
      MapsTo (fun x : EuclideanSpace ℝ (Fin 24) => (x, s)) (univ : Set (EuclideanSpace ℝ (Fin 24)))
        (univ ×ˢ Ici (1 : ℝ)) :=
      by intro x hx; exact ⟨Set.mem_univ _, hs_mem⟩
    have hphase :
      Continuous fun x : EuclideanSpace ℝ (Fin 24) => Complex.exp (↑(-2 * (π * ⟪x, w⟫)) * I) :=
      by
      have hinner : Continuous fun x : EuclideanSpace ℝ (Fin 24) => (⟪x, w⟫ : ℝ) := by
        simpa using (continuous_id.inner continuous_const)
      have hreal :
        Continuous fun x : EuclideanSpace ℝ (Fin 24) => ((-2 : ℝ) * ((π : ℝ) * (⟪x, w⟫ : ℝ))) :=
        continuous_const.mul (continuous_const.mul hinner)
      have hofReal :
        Continuous fun x : EuclideanSpace ℝ (Fin 24) =>
          (↑(((-2 : ℝ) * ((π : ℝ) * (⟪x, w⟫ : ℝ)))) : ℂ) :=
        Complex.continuous_ofReal.comp hreal
      have harg :
        Continuous fun x : EuclideanSpace ℝ (Fin 24) =>
          (↑(((-2 : ℝ) * ((π : ℝ) * (⟪x, w⟫ : ℝ)))) : ℂ) * I :=
        hofReal.mul continuous_const
      simpa [mul_assoc, mul_left_comm, mul_comm] using (Complex.continuous_exp.comp harg)
    have hg_on :
      ContinuousOn (fun x : EuclideanSpace ℝ (Fin 24) => J5Change.g (‖x‖ ^ 2) s)
        (univ : Set (EuclideanSpace ℝ (Fin 24))) :=
      by simpa using (continuousOn_J₅_g.comp hpair_on hmaps)
    have hg : Continuous fun x : EuclideanSpace ℝ (Fin 24) => J5Change.g (‖x‖ ^ 2) s := by
      simpa [continuousOn_univ] using hg_on
    have hcont : Continuous fun x : EuclideanSpace ℝ (Fin 24) => kernel w (x, s) := by
      simpa [kernel] using hphase.mul hg
    exact hcont.aestronglyMeasurable
  refine Integrable.mono' hmajor hmeas ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  exact le_of_eq (kernel_norm_eq (w := w) (x := x) (s := s))


-- @@ L93-201 expanded
/-- Integrability of `PermJ5.kernel w` on `ℝ²⁴ × Ici 1`, with the product measure used in Fubini. -/
public lemma integrable_kernel (w : EuclideanSpace ℝ (Fin 24)) :
    Integrable (kernel w) ((volume : Measure (EuclideanSpace ℝ (Fin 24))).prod μIciOne) :=
  by
  haveI : MeasureTheory.SFinite μIciOne := by
    dsimp [μIciOne]
    infer_instance
  have hmeas :
    AEStronglyMeasurable (kernel w) ((volume : Measure (EuclideanSpace ℝ (Fin 24))).prod μIciOne) :=
    aestronglyMeasurable_kernel (w := w)
  refine
    (MeasureTheory.integrable_prod_iff' (μ := (volume : Measure (EuclideanSpace ℝ (Fin 24)))) (ν :=
          μIciOne) hmeas).2
      ?_
  refine ⟨?_, ?_⟩
  · refine (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall ?_
    intro s hs
    exact integrable_kernel_slice (w := w) (s := s) hs
  · -- Integrability in `s` follows from exponential decay of `ψS` on the imaginary axis.
    
    rcases PsiExpBounds.exists_bound_norm_ψS_resToImagAxis_exp_Ici_one with ⟨C, hC⟩
    have hmajor : Integrable (fun s : ℝ ↦ C * Real.exp (-π * s)) μIciOne :=
      by
      have hIci : IntegrableOn (fun s : ℝ ↦ Real.exp (-(π : ℝ) * s)) (Ici (1 : ℝ)) volume := by
        simpa [pow_zero, one_mul] using
          (SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici (n := 0) (b := (π : ℝ))
            Real.pi_pos)
      have hIci' : IntegrableOn (fun s : ℝ ↦ C * Real.exp (-(π : ℝ) * s)) (Ici (1 : ℝ)) volume := by
        simpa [IntegrableOn, mul_assoc] using hIci.const_mul C
      simpa [μIciOne, IntegrableOn, mul_assoc, mul_left_comm, mul_comm] using hIci'
    have hmeas' :
      AEStronglyMeasurable (fun s : ℝ ↦ ∫ x : EuclideanSpace ℝ (Fin 24), ‖kernel w (x, s)‖)
        μIciOne :=
      by
      simpa using
        (SpherePacking.ForMathlib.aestronglyMeasurable_integral_norm_prod_right' (μ := μIciOne)
          (ν := (volume : Measure (EuclideanSpace ℝ (Fin 24)))) (f := kernel w) hmeas)
    refine Integrable.mono' hmajor hmeas' ?_
    refine (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall ?_
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
    have hs_ne0 : s ≠ 0 := hs0.ne'
    have hgauss : (∫ x : EuclideanSpace ℝ (Fin 24), Real.exp (-π * (‖x‖ ^ 2) / s)) = s ^ 12 :=
      integral_gaussian_rexp (s := s) hs0
    have hnorm :
      (fun x : EuclideanSpace ℝ (Fin 24) ↦ ‖kernel w (x, s)‖) = fun x : EuclideanSpace ℝ (Fin 24) ↦
        (‖ψS' ((Complex.I : ℂ) * (s : ℂ))‖ * ‖(s ^ (-12 : ℤ) : ℂ)‖) *
          Real.exp (-π * (‖x‖ ^ 2) / s) :=
      by
      funext x
      exact kernel_norm_eq (w := w) (x := x) (s := s)
    have hval : ∫ x : EuclideanSpace ℝ (Fin 24), ‖kernel w (x, s)‖ ≤ ‖ψS.resToImagAxis s‖ :=
      by
      have hs_zpow_pos : 0 < s ^ (-12 : ℤ) := zpow_pos hs0 _
      have habs : ‖(s ^ (-12 : ℤ) : ℂ)‖ = s ^ (-12 : ℤ) :=
        by
        change ‖(s : ℂ) ^ (-12 : ℤ)‖ = s ^ (-12 : ℤ)
        have hzpow : (s : ℂ) ^ (-12 : ℤ) = (↑(s ^ (-12 : ℤ)) : ℂ) := by
          exact (Complex.ofReal_zpow s (-12 : ℤ)).symm
        rw [hzpow]
        calc
          ‖(↑(s ^ (-12 : ℤ)) : ℂ)‖ = |s ^ (-12 : ℤ)| := by
            exact
              (RCLike.norm_ofReal (s ^ (-12 : ℤ)) : ‖((s ^ (-12 : ℤ) : ℝ) : ℂ)‖ = |s ^ (-12 : ℤ)|)
          _ = s ^ (-12 : ℤ) := by exact abs_of_pos hs_zpow_pos
      have hs_pow : s ^ 12 ≠ 0 := pow_ne_zero 12 hs_ne0
      have hz : (s ^ (-12 : ℤ)) = (s ^ 12)⁻¹ := by simpa using (zpow_negSucc s 11)
      have hscal : (‖(s ^ (-12 : ℤ) : ℂ)‖) * (s ^ 12) = (1 : ℝ) :=
        by
        rw [habs]
        rw [hz]
        exact inv_mul_cancel₀ hs_pow
      have hψS' : ‖ψS' ((Complex.I : ℂ) * (s : ℂ))‖ = ‖ψS.resToImagAxis s‖ :=
        by
        have h : ψS' ((Complex.I : ℂ) * (s : ℂ)) = ψS.resToImagAxis s := by
          simp [ψS', Function.resToImagAxis, ResToImagAxis, hs0, mul_comm]
        simpa using congrArg norm h
      have hEq : (∫ x : EuclideanSpace ℝ (Fin 24), ‖kernel w (x, s)‖) = ‖ψS.resToImagAxis s‖ :=
        by
        have hEq0 :
          (∫ x : EuclideanSpace ℝ (Fin 24), ‖kernel w (x, s)‖) =
            ∫ x : EuclideanSpace ℝ (Fin 24),
              (‖ψS' ((Complex.I : ℂ) * (s : ℂ))‖ * ‖(s ^ (-12 : ℤ) : ℂ)‖) *
                Real.exp (-π * (‖x‖ ^ 2) / s) :=
          congrArg (fun f : EuclideanSpace ℝ (Fin 24) → ℝ => ∫ x : EuclideanSpace ℝ (Fin 24), f x)
            hnorm
        have hEq1 :
          (∫ x : EuclideanSpace ℝ (Fin 24),
              (‖ψS' ((Complex.I : ℂ) * (s : ℂ))‖ * ‖(s ^ (-12 : ℤ) : ℂ)‖) *
                Real.exp (-π * (‖x‖ ^ 2) / s)) =
            (‖ψS' ((Complex.I : ℂ) * (s : ℂ))‖ * ‖(s ^ (-12 : ℤ) : ℂ)‖) *
              (∫ x : EuclideanSpace ℝ (Fin 24), Real.exp (-π * (‖x‖ ^ 2) / s)) :=
          (MeasureTheory.integral_const_mul (μ := (volume : Measure (EuclideanSpace ℝ (Fin 24))))
            (‖ψS' ((Complex.I : ℂ) * (s : ℂ))‖ * ‖(s ^ (-12 : ℤ) : ℂ)‖)
            (fun x : EuclideanSpace ℝ (Fin 24) ↦ Real.exp (-π * (‖x‖ ^ 2) / s)))
        calc
          (∫ x : EuclideanSpace ℝ (Fin 24), ‖kernel w (x, s)‖) =
              ∫ x : EuclideanSpace ℝ (Fin 24),
                (‖ψS' ((Complex.I : ℂ) * (s : ℂ))‖ * ‖(s ^ (-12 : ℤ) : ℂ)‖) *
                  Real.exp (-π * (‖x‖ ^ 2) / s) :=
            hEq0
          _ =
              (‖ψS' ((Complex.I : ℂ) * (s : ℂ))‖ * ‖(s ^ (-12 : ℤ) : ℂ)‖) *
                (∫ x : EuclideanSpace ℝ (Fin 24), Real.exp (-π * (‖x‖ ^ 2) / s)) :=
            hEq1
          _ = (‖ψS' ((Complex.I : ℂ) * (s : ℂ))‖ * ‖(s ^ (-12 : ℤ) : ℂ)‖) * (s ^ 12) := by
            rw [hgauss]
          _ = ‖ψS' ((Complex.I : ℂ) * (s : ℂ))‖ :=
            by
            rw [mul_assoc]
            rw [hscal]
            simp
          _ = ‖ψS.resToImagAxis s‖ := by simp [hψS']
      exact le_of_eq hEq
    have hbound : ‖(∫ x : EuclideanSpace ℝ (Fin 24), ‖kernel w (x, s)‖)‖ ≤ C * Real.exp (-π * s) :=
      by
      have hn0 : 0 ≤ ∫ x : EuclideanSpace ℝ (Fin 24), ‖kernel w (x, s)‖ :=
        MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)
      have habs :
        ‖∫ x : EuclideanSpace ℝ (Fin 24), ‖kernel w (x, s)‖‖ =
          ∫ x : EuclideanSpace ℝ (Fin 24), ‖kernel w (x, s)‖ :=
        by simp [Real.norm_eq_abs, abs_of_nonneg hn0]
      have : ∫ x : EuclideanSpace ℝ (Fin 24), ‖kernel w (x, s)‖ ≤ C * Real.exp (-π * s) :=
        hval.trans (hC s hs)
      simpa [habs] using this
    simpa using hbound


-- @@ L203-203 verbatim
end PermJ5



-- @@ L206-206 verbatim
end

-- @@ L207-207 verbatim
end SpherePacking.Dim24.BFourier
