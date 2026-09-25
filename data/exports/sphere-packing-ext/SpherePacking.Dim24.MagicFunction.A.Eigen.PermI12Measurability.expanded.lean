/-
Measurability/continuity helpers on `Ioc (0,1]`.
-/
module
public import SpherePacking.Dim24.MagicFunction.A.Eigen.PermI12FourierKernels
public import SpherePacking.Dim24.ModularForms.Psi.ImagAxis
public import SpherePacking.Integration.Measure
import SpherePacking.Contour.Segments
import Mathlib.Tactic.Ring.RingNF
import SpherePacking.Dim24.MagicFunction.A.DefsAux.VarphiExpBounds



-- @@ L13-25 verbatim
/-!
# Measurability on `Ioc (0, 1]` for the `I₁/I₂` kernels

This file provides measurability and continuity lemmas on the interval `t ∈ Ioc (0, 1]`
used in the Fourier permutation argument for `I₁` and `I₂`.

The main point is to control the `varphi'` factors appearing in `permI1Kernel` and `permI2Kernel`
near the endpoint `t → 0`, by rewriting them in terms of the restriction `t ↦ varphi(it)`.

## Main statements
* `permI1Kernel_measurable`
* `permI2Kernel_measurable`
-/


-- @@ L27-27 verbatim
open Complex Real


-- @@ L29-29 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L31-31 verbatim
namespace SpherePacking.Dim24.AFourier

-- @@ L32-32 verbatim
open MeasureTheory Set Complex Real Filter

-- @@ L33-33 verbatim
open SpherePacking.ForMathlib

-- @@ L34-34 verbatim
open SpherePacking.Integration

-- @@ L35-35 verbatim
open SpherePacking.Contour

-- @@ L36-36 verbatim
open scoped Interval Topology RealInnerProductSpace UpperHalfPlane Manifold


-- @@ L38-38 verbatim
noncomputable section


-- @@ L40-40 verbatim
open MagicFunction.Parametrisations

-- @@ L41-46 verbatim
open scoped Interval


/-
Endpoint bounds and integrability near `t → 0`.
-/


-- @@ L48-53 verbatim
/--
A closed-form identity for `(-1) / (z₁line t + 1)`, used to rewrite `varphi'` on `Ioc (0, 1]`.
-/
public lemma neg_one_div_z₁line_add_one_eq (t : ℝ) :
    (-1 : ℂ) / (z₁line t + 1) = (Complex.I : ℂ) * ((1 / t : ℝ) : ℂ) := by
  simp [div_eq_mul_inv, mul_comm]


-- @@ L55-60 verbatim
/-- On `t ∈ Ioc (0, 1]`, rewrite `varphi' (-1 / (z₁line t + 1))` as `varphi(i / t)`. -/
public lemma varphi'_neg_one_div_z₁line_add_one_eq (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    varphi' (-1 / (z₁line t + 1)) = varphi.resToImagAxis (1 / t) := by
  rw [show (-1 : ℂ) / (z₁line t + 1) = (it t⁻¹ (inv_pos.2 ht.1) : ℂ) by
    simpa [it] using (neg_one_div_z₁line_add_one_eq (t := t))]
  simpa [Function.resToImagAxis] using (resToImagAxis_eq_it varphi t⁻¹ (inv_pos.2 ht.1)).symm


-- @@ L62-64 verbatim
lemma continuousOn_varphi_resToImagAxis_Ioi :
    ContinuousOn (fun t : ℝ => varphi.resToImagAxis t) (Ioi (0 : ℝ)) :=
  Function.continuousOn_resToImagAxis_Ioi_of (F := varphi) VarphiExpBounds.continuous_varphi


-- @@ L66-86 verbatim
lemma continuousOn_varphi'_neg_one_div_z₁line_add_one :
    ContinuousOn (fun t : ℝ => varphi' (-1 / (z₁line t + 1))) (Ioc (0 : ℝ) 1) := by
  have hEq :
      EqOn (fun t : ℝ => varphi' (-1 / (z₁line t + 1))) (fun t : ℝ => varphi.resToImagAxis (1 / t))
        (Ioc (0 : ℝ) 1) := by
    intro t ht
    simpa using (varphi'_neg_one_div_z₁line_add_one_eq (t := t) ht)
  have hcontRes : ContinuousOn (fun t : ℝ => varphi.resToImagAxis t) (Ioi (0 : ℝ)) :=
    continuousOn_varphi_resToImagAxis_Ioi
  have hcontInv : ContinuousOn (fun t : ℝ => (1 / t : ℝ)) (Ioc (0 : ℝ) 1) := by
    have hcont_inv :
        ContinuousOn (fun t : ℝ => (t : ℝ)⁻¹) (Ioc (0 : ℝ) 1) :=
      (continuousOn_inv₀ : ContinuousOn (fun t : ℝ => (t : ℝ)⁻¹) ({0}ᶜ)).mono (by
        intro t ht
        simp [ne_of_gt ht.1])
    simpa [one_div] using hcont_inv
  have hcomp : ContinuousOn (fun t : ℝ => varphi.resToImagAxis (1 / t)) (Ioc (0 : ℝ) 1) :=
    hcontRes.comp hcontInv (by
      intro t ht
      exact one_div_pos.2 ht.1)
  exact hcomp.congr hEq


-- @@ L88-103 verbatim
/-- The Mobius transform `(-1) / (z₂line t + 1)` stays in the upper half-plane. -/
public lemma neg_one_div_z₂line_add_one_im_pos (t : ℝ) : 0 < ((-1 : ℂ) / (z₂line t + 1)).im := by
  -- normalize the denominator `z₂line t + 1 = t + I`
  rw [z₂line_add_one (t := t)]
  -- `Im((-1)/(t+i)) = 1/(t^2+1)`.
  have hnormSq : Complex.normSq ((t : ℂ) + Complex.I) = t ^ (2 : ℕ) + 1 := by
    simp [Complex.normSq, pow_two]
  have hIm :
      ((-1 : ℂ) / ((t : ℂ) + Complex.I)).im = 1 / (t ^ (2 : ℕ) + 1) := by
    simp [hnormSq, div_eq_mul_inv, pow_two]
  have hden_pos : 0 < (t ^ (2 : ℕ) + 1 : ℝ) := by
    have : 0 ≤ t ^ (2 : ℕ) := pow_two_nonneg t
    linarith
  -- conclude
  have hpos : (0 : ℝ) < 1 / (t ^ (2 : ℕ) + 1) := one_div_pos.2 hden_pos
  simpa [hIm] using hpos


-- @@ L105-138 verbatim
/-- Continuity of `t ↦ varphi' (-1 / (z₂line t + 1))` on `Ioc (0, 1]`. -/
public lemma continuousOn_varphi'_neg_one_div_z₂line_add_one :
    ContinuousOn (fun t : ℝ => varphi' (-1 / (z₂line t + 1))) (Ioc (0 : ℝ) 1) := by
  -- Work on the subtype `Ioc (0,1]`.
  rw [continuousOn_iff_continuous_restrict]
  let s : Set ℝ := Ioc (0 : ℝ) 1
  let Z : s → ℍ := fun t =>
    ⟨(-1 : ℂ) / (z₂line (t : ℝ) + 1), by
      have ht0 : 0 < (t : ℝ) := t.property.1
      exact neg_one_div_z₂line_add_one_im_pos (t := (t : ℝ))⟩
  have hZ : Continuous Z := by
    have hbase : Continuous fun t : s => (-1 : ℂ) / (z₂line (t : ℝ) + 1) := by
      have hcont_z₂line : Continuous z₂line := by
        simpa using SpherePacking.Contour.continuous_z₂line
      have hz : Continuous fun t : s => z₂line (t : ℝ) :=
        hcont_z₂line.comp continuous_subtype_val
      have hz1 : Continuous fun t : s => z₂line (t : ℝ) + 1 := hz.add continuous_const
      have hne : ∀ t : s, z₂line (t : ℝ) + 1 ≠ 0 := by
        intro t
        -- `z₂line t + 1 = t + I`, never zero.
        have him : (z₂line (t : ℝ) + 1).im = (1 : ℝ) := by
          simp
        intro h0
        have him0 : (z₂line (t : ℝ) + 1).im = 0 := by
          simpa using congrArg Complex.im h0
        have : (1 : ℝ) = 0 := him.symm.trans him0
        exact one_ne_zero this
      exact (continuous_const.div hz1 hne)
    exact Continuous.upperHalfPlaneMk hbase fun x => neg_one_div_z₂line_add_one_im_pos ↑x
  have hvarphi : Continuous fun t : s => varphi (Z t) :=
    VarphiExpBounds.continuous_varphi.comp hZ
  refine hvarphi.congr ?_
  intro t
  simpa [Z, s] using (SpherePacking.Dim24.varphi'_coe_upperHalfPlane (z := Z t)).symm


-- @@ L140-209 expanded
/-- Measurability of the kernel `permI1Kernel w` with respect to `volume.prod μIoc01`. -/
public lemma permI1Kernel_measurable (w : EuclideanSpace ℝ (Fin 24)) :
    AEStronglyMeasurable (permI1Kernel w)
      ((volume : Measure (EuclideanSpace ℝ (Fin 24))).prod μIoc01) :=
  by
  -- Continuity on the set `univ ×ˢ Ioc (0,1]`.
  
  have hphase :
    ContinuousOn (fun p : EuclideanSpace ℝ (Fin 24) × ℝ ↦ cexp (↑(-2 * (π * ⟪p.1, w⟫)) * I))
      (univ ×ˢ Ioc (0 : ℝ) 1) :=
    by
    have hinner : Continuous fun p : EuclideanSpace ℝ (Fin 24) × ℝ => (⟪p.1, w⟫ : ℝ) := by
      simpa using (continuous_fst.inner continuous_const)
    have hreal :
      Continuous fun p : EuclideanSpace ℝ (Fin 24) × ℝ => ((-2 : ℝ) * ((π : ℝ) * (⟪p.1, w⟫ : ℝ))) :=
      continuous_const.mul (continuous_const.mul hinner)
    have harg :
      Continuous fun p : EuclideanSpace ℝ (Fin 24) × ℝ =>
        (↑(((-2 : ℝ) * ((π : ℝ) * (⟪p.1, w⟫ : ℝ)))) : ℂ) * I :=
      (Complex.continuous_ofReal.comp hreal).mul continuous_const
    exact (Complex.continuous_exp.comp harg).continuousOn
  have hz₁ :
    ContinuousOn (fun p : EuclideanSpace ℝ (Fin 24) × ℝ => z₁line p.2) (univ ×ˢ Ioc (0 : ℝ) 1) :=
    by
    have hcont_z₁line : Continuous z₁line := by simpa using SpherePacking.Contour.continuous_z₁line
    exact (hcont_z₁line.comp continuous_snd).continuousOn
  have hvarphi :
    ContinuousOn (fun p : EuclideanSpace ℝ (Fin 24) × ℝ => varphi' (-1 / (z₁line p.2 + 1)))
      (univ ×ˢ Ioc (0 : ℝ) 1) :=
    by
    -- depends only on `p.2`
    
    refine continuousOn_varphi'_neg_one_div_z₁line_add_one.comp ?_ ?_
    · exact continuousOn_snd
    · intro p hp
      exact hp.2
  have hpow :
    ContinuousOn (fun p : EuclideanSpace ℝ (Fin 24) × ℝ => (z₁line p.2 + 1) ^ (10 : ℕ))
      (univ ×ˢ Ioc (0 : ℝ) 1) :=
    ((hz₁.add continuousOn_const).pow 10)
  have hnormSq :
    ContinuousOn (fun p : EuclideanSpace ℝ (Fin 24) × ℝ => ((‖p.1‖ ^ 2 : ℝ) : ℂ))
      (univ ×ˢ Ioc (0 : ℝ) 1) :=
    by
    have : Continuous fun p : EuclideanSpace ℝ (Fin 24) × ℝ => (‖p.1‖ ^ 2 : ℝ) := by fun_prop
    exact (Complex.continuous_ofReal.comp this).continuousOn
  have hexp :
    ContinuousOn
      (fun p : EuclideanSpace ℝ (Fin 24) × ℝ =>
        cexp ((π : ℂ) * I * ((‖p.1‖ ^ 2 : ℝ) : ℂ) * (z₁line p.2 : ℂ)))
      (univ ×ˢ Ioc (0 : ℝ) 1) :=
    by fun_prop
  have hΦ :
    ContinuousOn (fun p : EuclideanSpace ℝ (Fin 24) × ℝ => (I : ℂ) * Φ₁' (‖p.1‖ ^ 2) (z₁line p.2))
      (univ ×ˢ Ioc (0 : ℝ) 1) :=
    by
    -- unfold `Φ₁'` and assemble continuous factors
    
    have hcore :
      ContinuousOn
        (fun p : EuclideanSpace ℝ (Fin 24) × ℝ =>
          varphi' (-1 / (z₁line p.2 + 1)) * (z₁line p.2 + 1) ^ (10 : ℕ) *
            cexp ((π : ℂ) * I * ((‖p.1‖ ^ 2 : ℝ) : ℂ) * (z₁line p.2 : ℂ)))
        (univ ×ˢ Ioc (0 : ℝ) 1) :=
      (hvarphi.mul hpow).mul hexp
    simpa [Φ₁', mul_assoc] using (continuousOn_const.mul hcore)
  have hkernel : ContinuousOn (permI1Kernel w) (univ ×ˢ Ioc (0 : ℝ) 1) := by
    -- normalize the definition of `permI1Kernel`
    
    refine (hphase.mul hΦ).congr ?_
    intro p _hp
    simp [permI1Kernel]
  have hmeas :
    AEStronglyMeasurable (permI1Kernel w)
      (((volume : Measure (EuclideanSpace ℝ (Fin 24))).prod (volume : Measure ℝ)).restrict
        (univ ×ˢ Ioc (0 : ℝ) 1)) :=
    by
    have hs : MeasurableSet (Set.univ : Set (EuclideanSpace ℝ (Fin 24))) := MeasurableSet.univ
    have ht : MeasurableSet (Ioc (0 : ℝ) 1) := measurableSet_Ioc
    exact ContinuousOn.aestronglyMeasurable hkernel (hs.prod ht)
  have hμ :
    ((volume : Measure (EuclideanSpace ℝ (Fin 24))).prod μIoc01) =
      (((volume : Measure (EuclideanSpace ℝ (Fin 24))).prod (volume : Measure ℝ)).restrict
        (univ ×ˢ Ioc (0 : ℝ) 1)) :=
    by
    simpa using
      (SpherePacking.Integration.prod_muIoc01_eq_restrict (μ :=
        (volume : Measure (EuclideanSpace ℝ (Fin 24)))))
  simpa [hμ] using hmeas


-- @@ L211-277 expanded
/-- Measurability of the kernel `permI2Kernel w` with respect to `volume.prod μIoc01`. -/
public lemma permI2Kernel_measurable (w : EuclideanSpace ℝ (Fin 24)) :
    AEStronglyMeasurable (permI2Kernel w)
      ((volume : Measure (EuclideanSpace ℝ (Fin 24))).prod μIoc01) :=
  by
  have hphase :
    ContinuousOn (fun p : EuclideanSpace ℝ (Fin 24) × ℝ ↦ cexp (↑(-2 * (π * ⟪p.1, w⟫)) * I))
      (univ ×ˢ Ioc (0 : ℝ) 1) :=
    by
    have hinner : Continuous fun p : EuclideanSpace ℝ (Fin 24) × ℝ => (⟪p.1, w⟫ : ℝ) := by
      simpa using (continuous_fst.inner continuous_const)
    have hreal :
      Continuous fun p : EuclideanSpace ℝ (Fin 24) × ℝ => ((-2 : ℝ) * ((π : ℝ) * (⟪p.1, w⟫ : ℝ))) :=
      continuous_const.mul (continuous_const.mul hinner)
    have harg :
      Continuous fun p : EuclideanSpace ℝ (Fin 24) × ℝ =>
        (↑(((-2 : ℝ) * ((π : ℝ) * (⟪p.1, w⟫ : ℝ)))) : ℂ) * I :=
      (Complex.continuous_ofReal.comp hreal).mul continuous_const
    exact (Complex.continuous_exp.comp harg).continuousOn
  have hz₂ :
    ContinuousOn (fun p : EuclideanSpace ℝ (Fin 24) × ℝ => z₂line p.2) (univ ×ˢ Ioc (0 : ℝ) 1) :=
    by
    have hcont_z₂line : Continuous z₂line := by simpa using SpherePacking.Contour.continuous_z₂line
    exact (hcont_z₂line.comp continuous_snd).continuousOn
  have hvarphi :
    ContinuousOn (fun p : EuclideanSpace ℝ (Fin 24) × ℝ => varphi' (-1 / (z₂line p.2 + 1)))
      (univ ×ˢ Ioc (0 : ℝ) 1) :=
    by
    refine continuousOn_varphi'_neg_one_div_z₂line_add_one.comp ?_ ?_
    · exact continuousOn_snd
    · intro p hp
      exact hp.2
  have hpow :
    ContinuousOn (fun p : EuclideanSpace ℝ (Fin 24) × ℝ => (z₂line p.2 + 1) ^ (10 : ℕ))
      (univ ×ˢ Ioc (0 : ℝ) 1) :=
    ((hz₂.add continuousOn_const).pow 10)
  have hnormSq :
    ContinuousOn (fun p : EuclideanSpace ℝ (Fin 24) × ℝ => ((‖p.1‖ ^ 2 : ℝ) : ℂ))
      (univ ×ˢ Ioc (0 : ℝ) 1) :=
    by
    have : Continuous fun p : EuclideanSpace ℝ (Fin 24) × ℝ => (‖p.1‖ ^ 2 : ℝ) := by fun_prop
    exact (Complex.continuous_ofReal.comp this).continuousOn
  have hexp :
    ContinuousOn
      (fun p : EuclideanSpace ℝ (Fin 24) × ℝ =>
        cexp ((π : ℂ) * I * ((‖p.1‖ ^ 2 : ℝ) : ℂ) * (z₂line p.2 : ℂ)))
      (univ ×ˢ Ioc (0 : ℝ) 1) :=
    by fun_prop
  have hΦ :
    ContinuousOn (fun p : EuclideanSpace ℝ (Fin 24) × ℝ => Φ₁' (‖p.1‖ ^ 2) (z₂line p.2))
      (univ ×ˢ Ioc (0 : ℝ) 1) :=
    by
    have hcore :
      ContinuousOn
        (fun p : EuclideanSpace ℝ (Fin 24) × ℝ =>
          varphi' (-1 / (z₂line p.2 + 1)) * (z₂line p.2 + 1) ^ (10 : ℕ) *
            cexp ((π : ℂ) * I * ((‖p.1‖ ^ 2 : ℝ) : ℂ) * (z₂line p.2 : ℂ)))
        (univ ×ˢ Ioc (0 : ℝ) 1) :=
      (hvarphi.mul hpow).mul hexp
    simpa [Φ₁', mul_assoc] using hcore
  have hkernel : ContinuousOn (permI2Kernel w) (univ ×ˢ Ioc (0 : ℝ) 1) :=
    by
    refine (hphase.mul hΦ).congr ?_
    intro p _hp
    simp [permI2Kernel]
  have hmeas :
    AEStronglyMeasurable (permI2Kernel w)
      (((volume : Measure (EuclideanSpace ℝ (Fin 24))).prod (volume : Measure ℝ)).restrict
        (univ ×ˢ Ioc (0 : ℝ) 1)) :=
    by
    have hs : MeasurableSet (Set.univ : Set (EuclideanSpace ℝ (Fin 24))) := MeasurableSet.univ
    have ht : MeasurableSet (Ioc (0 : ℝ) 1) := measurableSet_Ioc
    exact ContinuousOn.aestronglyMeasurable hkernel (hs.prod ht)
  have hμ :
    ((volume : Measure (EuclideanSpace ℝ (Fin 24))).prod μIoc01) =
      (((volume : Measure (EuclideanSpace ℝ (Fin 24))).prod (volume : Measure ℝ)).restrict
        (univ ×ˢ Ioc (0 : ℝ) 1)) :=
    by
    simpa using
      (SpherePacking.Integration.prod_muIoc01_eq_restrict (μ :=
        (volume : Measure (EuclideanSpace ℝ (Fin 24)))))
  simpa [hμ] using hmeas


-- @@ L280-280 verbatim
end


-- @@ L282-282 verbatim
end SpherePacking.Dim24.AFourier
