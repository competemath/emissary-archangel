module
public import SpherePacking.Dim24.MagicFunction.B.Eigen.Prelude
import SpherePacking.ForMathlib.GaussianFourierCommon
import SpherePacking.ForMathlib.GaussianRexpIntegral
public import SpherePacking.Integration.Measure
public import SpherePacking.Contour.Segments
import SpherePacking.Contour.PermJ12CurveIntegral
import SpherePacking.Contour.GaussianIntegral
import SpherePacking.ForMathlib.UpperHalfPlane
import SpherePacking.Contour.GaussianIntegral



-- @@ L13-28 verbatim
/-!
# Curve-integral representations for `J₁', ..., J₄'`

We rewrite the one-variable pieces `RealIntegrals.J₁'`, ..., `RealIntegrals.J₄'` of `bProfile` as
curve integrals along the standard segments in the upper half-plane. We also define the kernel
`permJ1Kernel` used to express the Fourier transform of `J₁` via Fubini.

## Main definitions
* `permJ1Kernel`

## Main statements
* `J₁'_eq_curveIntegral_segment`, `J₂'_eq_curveIntegral_segment`,
  `J₃'_eq_curveIntegral_segment`, `J₄'_eq_curveIntegral_segment`
* `ψT'_z₁line_eq`
* `phase_mul_J₁'_eq_integral_permJ1Kernel`
-/

-- @@ L29-29 verbatim
open scoped FourierTransform


-- @@ L31-31 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L33-33 verbatim
namespace SpherePacking.Dim24.BFourier

-- @@ L34-34 verbatim
open MeasureTheory Set Filter

-- @@ L35-35 verbatim
open scoped Interval RealInnerProductSpace UpperHalfPlane


-- @@ L37-37 verbatim
noncomputable section



-- @@ L40-40 verbatim
section PermJ12


-- @@ L42-42 verbatim
open SpherePacking.ForMathlib

-- @@ L43-43 verbatim
open SpherePacking.Integration

-- @@ L44-44 verbatim
open SpherePacking.Contour



-- @@ L47-47 verbatim
open MagicFunction.Parametrisations

-- @@ L48-48 verbatim
open MagicFunction


-- @@ L50-56 verbatim
/-- Curve-integral representation of `J₁'` along the segment from `-1` to `-1 + i`. -/
public lemma J₁'_eq_curveIntegral_segment (r : ℝ) :
    RealIntegrals.J₁' r =
      (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I),
        scalarOneForm (Ψ₁' r) z) := by
  simpa [RealIntegrals.J₁', Ψ₁', scalarOneForm_apply, mul_assoc, mul_left_comm, mul_comm] using
    (SpherePacking.Contour.curveIntegral_segment_z₁ (f := Ψ₁' r)).symm


-- @@ L58-64 verbatim
/-- Curve-integral representation of `J₂'` along the segment from `-1 + i` to `i`. -/
public lemma J₂'_eq_curveIntegral_segment (r : ℝ) :
    RealIntegrals.J₂' r =
      (∫ᶜ z in Path.segment ((-1 : ℂ) + Complex.I) Complex.I,
        scalarOneForm (Ψ₁' r) z) := by
  simpa [RealIntegrals.J₂', Ψ₁', scalarOneForm_apply, mul_assoc, mul_left_comm, mul_comm] using
    (SpherePacking.Contour.curveIntegral_segment_z₂ (f := Ψ₁' r)).symm


-- @@ L66-72 verbatim
/-- Curve-integral representation of `J₃'` along the segment from `1` to `1 + i`. -/
public lemma J₃'_eq_curveIntegral_segment (r : ℝ) :
    RealIntegrals.J₃' r =
      (∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I),
        scalarOneForm (Ψ₁' r) z) := by
  simpa [RealIntegrals.J₃', Ψ₁', scalarOneForm_apply, mul_assoc, mul_left_comm, mul_comm] using
    (SpherePacking.Contour.curveIntegral_segment_z₃ (f := Ψ₁' r)).symm


-- @@ L74-80 verbatim
/-- Curve-integral representation of `J₄'` along the segment from `1 + i` to `i`. -/
public lemma J₄'_eq_curveIntegral_segment (r : ℝ) :
    RealIntegrals.J₄' r =
      (∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I,
        scalarOneForm (Ψ₁' r) z) := by
  simpa [RealIntegrals.J₄', Ψ₁', scalarOneForm_apply, mul_assoc, mul_left_comm, mul_comm] using
    (SpherePacking.Contour.curveIntegral_segment_z₄ (f := Ψ₁' r)).symm


-- @@ L82-89 verbatim
/-- Expression of `J₁' + J₂'` as a sum of curve integrals along the left two segments. -/
public lemma J₁'_add_J₂'_eq_curveIntegral_segments (r : ℝ) :
    RealIntegrals.J₁' r + RealIntegrals.J₂' r =
      (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I),
          scalarOneForm (Ψ₁' r) z) +
        ∫ᶜ z in Path.segment ((-1 : ℂ) + Complex.I) Complex.I,
          scalarOneForm (Ψ₁' r) z := by
  simp [J₁'_eq_curveIntegral_segment (r := r), J₂'_eq_curveIntegral_segment (r := r)]


-- @@ L91-98 verbatim
/-- Expression of `J₃' + J₄'` as a sum of curve integrals along the right two segments. -/
public lemma J₃'_add_J₄'_eq_curveIntegral_segments (r : ℝ) :
    RealIntegrals.J₃' r + RealIntegrals.J₄' r =
      (∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I),
          scalarOneForm (Ψ₁' r) z) +
        ∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I,
          scalarOneForm (Ψ₁' r) z := by
  simp [J₃'_eq_curveIntegral_segment (r := r), J₄'_eq_curveIntegral_segment (r := r)]


-- @@ L100-100 verbatim
/-! #### Modular rewrites along the `z₁'` segment -/


-- @@ L102-102 verbatim
open UpperHalfPlane Complex ModularGroup MatrixGroups ModularForm SlashAction Matrix

-- @@ L103-103 verbatim
open scoped Real ModularForm MatrixGroups


-- @@ L105-114 verbatim
lemma slashST' (z : ℍ) (F : ℍ → ℂ) :
    ((F) ∣[-10] (ModularGroup.S * ModularGroup.T)) z = F ((ModularGroup.S * ModularGroup.T) • z) *
      (z + 1 : ℂ) ^ (10 : ℕ) := by
  rw [ModularForm.SL_slash_apply, ModularGroup.S_mul_T, UpperHalfPlane.denom]
  simp only [Int.reduceNeg, Fin.isValue, SpecialLinearGroup.coe_GL_coe_matrix,
    SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Int.coe_castRingHom, map_apply,
    of_apply, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one, Int.cast_one, ofReal_one,
    one_mul]
  -- `(-(-10)) = 10` and convert `zpow` to a natural power.
  simp [zpow_ofNat]


-- @@ L116-167 verbatim
/-- Modular rewrite of `ψT'` along the parametrized line segment `z₁line`. -/
public lemma ψT'_z₁line_eq (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    ψT' (z₁line t) = ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ (10 : ℕ) := by
  have htIcc : t ∈ Icc (0 : ℝ) 1 := mem_Icc_of_Ioc ht
  have ht0 : 0 < t := ht.1
  have hz1 : z₁' t = z₁line t := z₁'_eq_z₁line t htIcc
  have hz_im : 0 < (z₁' t).im := by
    exact im_z₁'_pos ht
  let z : ℍ := ⟨z₁' t, hz_im⟩
  have hrel := congrArg (fun f : ℍ → ℂ => f z) (SpherePacking.Dim24.PsiSlash.ψS_slash_ST)
  have hψT : ψT z = ψS ((ModularGroup.S * ModularGroup.T) • z) * (z + 1 : ℂ) ^ (10 : ℕ) := by
    have h1 : (ψS ∣[-10] (ModularGroup.S * ModularGroup.T)) z = ψT z := by
      simpa using hrel
    calc
      ψT z = (ψS ∣[-10] (ModularGroup.S * ModularGroup.T)) z := by simpa using h1.symm
      _ = ψS ((ModularGroup.S * ModularGroup.T) • z) * (z + 1 : ℂ) ^ (10 : ℕ) := by
            simpa using (slashST' (z := z) (F := ψS))
  have hzplus : (z + 1 : ℂ) = (Complex.I : ℂ) * (t : ℂ) := by
    simp [z, hz1, z₁line, SpherePacking.Contour.z₁line, add_assoc]
  have htne : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht0)
  have hsmul :
      (ModularGroup.S * ModularGroup.T) • z =
        (⟨(Complex.I : ℂ) * (1 / t), by simp [ht0]⟩ : ℍ) := by
    ext1
    have hcoe : (↑((ModularGroup.S * ModularGroup.T) • z) : ℂ) = (Complex.I : ℂ) * (1 / t) := by
      calc
        (↑((ModularGroup.S * ModularGroup.T) • z) : ℂ) =
            (-1 : ℂ) / ((z : ℂ) + 1) := coe_ST_smul (z := z)
        _ = (-1 : ℂ) / ((Complex.I : ℂ) * (t : ℂ)) := by simp [hzplus]
        _ = (Complex.I : ℂ) * (1 / t) := by
              field_simp [htne, Complex.I_ne_zero]
              simp
    exact hcoe
  have hzline_im : 0 < (z₁line t).im := by
    simpa [z₁line] using (SpherePacking.Contour.z₁line_im_pos_Ioc (t := t) ht)
  have hψT' : ψT' (z₁line t) = ψT z := by
    have hzline_im' : 0 < ((-1 : ℂ) + Complex.I * (t : ℂ)).im := by
      simpa [z₁line] using hzline_im
    have hz : (⟨(-1 : ℂ) + Complex.I * (t : ℂ), hzline_im'⟩ : ℍ) = z := by
      ext1
      simpa [z, z₁line] using hz1.symm
    simp [ψT', z₁line, ht0, hz]
  have hψS' : ψS ((ModularGroup.S * ModularGroup.T) • z) = ψS.resToImagAxis (1 / t) := by
    simpa [Function.resToImagAxis, ResToImagAxis, ht0] using congrArg ψS hsmul
  have hψT'' :
      ψT z = ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ (10 : ℕ) := by
    have hψT1 := hψT
    rw [hψS'] at hψT1
    simpa [hzplus] using hψT1
  calc
    ψT' (z₁line t) = ψT z := hψT'
    _ = ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ (10 : ℕ) := hψT''


-- @@ L169-169 verbatim
/-! ##### Fourier transform of `J₁` and `J₂` (as curve integrals) -/


-- @@ L171-183 verbatim
/-- Rewrite `J₁'` as a set integral over `t ∈ Ioc (0,1)` using the parametrization `z₁line`. -/
public lemma J₁'_eq_integral_z₁line (r : ℝ) :
    RealIntegrals.J₁' r =
      ∫ t in Ioc (0 : ℝ) 1,
        (Complex.I : ℂ) * ψT' (z₁line t) *
          Complex.exp ((π : ℂ) * Complex.I * (r : ℂ) * (z₁line t)) := by
  rw [RealIntegrals.J₁']
  rw [intervalIntegral.integral_of_le (μ := (volume : Measure ℝ)) zero_le_one]
  refine MeasureTheory.integral_congr_ae ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall ?_
  intro t ht
  have htIcc : t ∈ Icc (0 : ℝ) 1 := mem_Icc_of_Ioc ht
  simp [z₁'_eq_z₁line (t := t) htIcc, mul_assoc, mul_left_comm, mul_comm]


-- @@ L185-196 verbatim
/-- Rewrite `J₂'` as a set integral over `t ∈ Ioc (0,1)` using the parametrization `z₂line`. -/
public lemma J₂'_eq_integral_z₂line (r : ℝ) :
    RealIntegrals.J₂' r =
      ∫ t in Ioc (0 : ℝ) 1,
        ψT' (z₂line t) * Complex.exp ((π : ℂ) * Complex.I * (r : ℂ) * (z₂line t)) := by
  rw [RealIntegrals.J₂']
  rw [intervalIntegral.integral_of_le (μ := (volume : Measure ℝ)) zero_le_one]
  refine MeasureTheory.integral_congr_ae ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 <| .of_forall ?_
  intro t ht
  have htIcc : t ∈ Icc (0 : ℝ) 1 := mem_Icc_of_Ioc ht
  simp [z₂'_eq_z₂line (t := t) htIcc, mul_assoc, mul_left_comm, mul_comm]


-- @@ L198-203 expanded
/-- Auxiliary kernel for the Fubini argument computing the Fourier transform of `J₁`. -/
@[expose]
public def permJ1Kernel (w : EuclideanSpace ℝ (Fin 24)) : EuclideanSpace ℝ (Fin 24) × ℝ → ℂ :=
  fun p =>
  Complex.exp (↑(-2 * π * ⟪p.1, w⟫) * Complex.I) *
    ((Complex.I : ℂ) * ψT' (z₁line p.2) *
      Complex.exp ((π : ℂ) * Complex.I * ((‖p.1‖ ^ 2 : ℝ) : ℂ) * (z₁line p.2)))


-- @@ L205-237 expanded
/-- Pull the Fourier phase inside the `t`-integral and express `J₁'` via `permJ1Kernel`. -/
public lemma phase_mul_J₁'_eq_integral_permJ1Kernel (w x : EuclideanSpace ℝ (Fin 24)) :
    Complex.exp (↑(-2 * Real.pi * ⟪x, w⟫) * Complex.I) * RealIntegrals.J₁' (‖x‖ ^ (2 : ℕ)) =
      ∫ t : ℝ, permJ1Kernel w (x, t) ∂SpherePacking.Integration.μIoc01 :=
  by
  have hJ₁μ :
    RealIntegrals.J₁' (‖x‖ ^ (2 : ℕ)) =
      ∫ t : ℝ,
        (Complex.I : ℂ) * ψT' (z₁line t) *
          Complex.exp
            ((π : ℂ) * Complex.I * ((‖x‖ ^ (2 : ℕ) : ℝ) : ℂ) *
              (z₁line t)) ∂SpherePacking.Integration.μIoc01 :=
    by
    -- Use the set-integral representation and unfold `μIoc01`.
    simpa [SpherePacking.Integration.μIoc01] using
      (J₁'_eq_integral_z₁line (r := (‖x‖ ^ (2 : ℕ))))
        -- Pull the phase factor inside the integral and match the kernel definition.
        
  calc
    Complex.exp (↑(-2 * Real.pi * ⟪x, w⟫) * Complex.I) * RealIntegrals.J₁' (‖x‖ ^ (2 : ℕ)) =
        Complex.exp (↑(-2 * Real.pi * ⟪x, w⟫) * Complex.I) *
          ∫ t : ℝ,
            (Complex.I : ℂ) * ψT' (z₁line t) *
              Complex.exp
                ((π : ℂ) * Complex.I * ((‖x‖ ^ (2 : ℕ) : ℝ) : ℂ) *
                  (z₁line t)) ∂SpherePacking.Integration.μIoc01 :=
      by simp [hJ₁μ, mul_assoc]
    _ =
        ∫ t : ℝ,
          Complex.exp (↑(-2 * Real.pi * ⟪x, w⟫) * Complex.I) *
            ((Complex.I : ℂ) * ψT' (z₁line t) *
              Complex.exp
                ((π : ℂ) * Complex.I * ((‖x‖ ^ (2 : ℕ) : ℝ) : ℂ) *
                  (z₁line t))) ∂SpherePacking.Integration.μIoc01 :=
      (Eq.symm
        (integral_const_mul (cexp (↑(-2 * π * ⟪x, w⟫) * Complex.I)) fun a =>
          Complex.I * ψT' (z₁line a) * cexp (↑π * Complex.I * ↑(‖x‖ ^ 2) * z₁line a)))
    _ = ∫ t : ℝ, permJ1Kernel w (x, t) ∂SpherePacking.Integration.μIoc01 := by
      simp [permJ1Kernel, mul_assoc]


-- @@ L239-269 expanded
/-- Pointwise norm identity for `permJ1Kernel`, separating the `ψT'` factor and Gaussian decay. -/
public lemma norm_permJ1Kernel (w x : EuclideanSpace ℝ (Fin 24)) (t : ℝ) :
    ‖permJ1Kernel w (x, t)‖ = ‖ψT' (z₁line t)‖ * rexp (-(π * t * (‖x‖ ^ 2))) :=
  by
  have hz_im : (z₁line t).im = t := by simp [z₁line]
  have hphase : ‖Complex.exp (↑(-2 * π * ⟪x, w⟫) * Complex.I)‖ = (1 : ℝ) := by
    simpa using (Complex.norm_exp_ofReal_mul_I (-2 * π * ⟪x, w⟫))
  have hgauss :
    ‖Complex.exp ((π : ℂ) * Complex.I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₁line t))‖ =
      rexp (-(π * t * (‖x‖ ^ 2))) :=
    by
    have hgauss0 :
      ‖Complex.exp ((π : ℂ) * Complex.I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₁line t))‖ =
        rexp (-π * (‖x‖ ^ 2) * (z₁line t).im) :=
      by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (SpherePacking.ForMathlib.norm_cexp_pi_mul_I_mul_sq (V := EuclideanSpace ℝ (Fin 24)) (z :=
          z₁line t) (x := x))
    rw [hgauss0, hz_im]
    ring_nf
  calc
    ‖permJ1Kernel w (x, t)‖ =
        ‖Complex.exp (↑(-2 * π * ⟪x, w⟫) * Complex.I)‖ *
          ‖(Complex.I : ℂ) * ψT' (z₁line t) *
              Complex.exp ((π : ℂ) * Complex.I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₁line t))‖ :=
      by simp [permJ1Kernel, mul_assoc]
    _ =
        ‖Complex.exp (↑(-2 * π * ⟪x, w⟫) * Complex.I)‖ *
          (‖ψT' (z₁line t)‖ *
            ‖Complex.exp ((π : ℂ) * Complex.I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₁line t))‖) :=
      by simp [mul_assoc]
    _ = ‖ψT' (z₁line t)‖ * rexp (-(π * t * (‖x‖ ^ 2))) :=
      by
      rw [hphase, hgauss]
      simp [mul_assoc]


-- @@ L271-275 expanded
/-- Gaussian integral on `ℝ²⁴`: `∫ exp (-π * t * ‖x‖^2) = (1/t)^12` for `t > 0`. -/
public lemma integral_rexp_neg_pi_mul_sq_norm (t : ℝ) (ht : 0 < t) :
    (∫ x : EuclideanSpace ℝ (Fin 24), rexp (-(π * t * (‖x‖ ^ 2)))) = (1 / t) ^ (12 : ℕ) := by
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (SpherePacking.Contour.integral_rexp_neg_pi_mul_sq_norm_even (k := 12) (t := t) ht)


-- @@ L277-295 expanded
/-- Integrate `‖permJ1Kernel w (x,t)‖` in the `x`-variable for `t ∈ Ioc (0,1)`. -/
public lemma integral_norm_permJ1Kernel (w : EuclideanSpace ℝ (Fin 24)) (t : ℝ)
    (ht : t ∈ Ioc (0 : ℝ) 1) :
    (∫ x : EuclideanSpace ℝ (Fin 24), ‖permJ1Kernel w (x, t)‖) =
      ‖ψT' (z₁line t)‖ * (1 / t) ^ (12 : ℕ) :=
  by
  have ht0 : 0 < t := ht.1
  have hfun :
    (fun x : EuclideanSpace ℝ (Fin 24) => ‖permJ1Kernel w (x, t)‖) =
      fun x : EuclideanSpace ℝ (Fin 24) => ‖ψT' (z₁line t)‖ * rexp (-(π * (t * (‖x‖ ^ 2)))) :=
    by
    funext x
    simpa [mul_assoc] using (norm_permJ1Kernel (w := w) (x := x) (t := t))
  have hgauss' :
    (∫ x : EuclideanSpace ℝ (Fin 24), rexp (-(π * (t * (‖x‖ ^ 2))))) = (1 / t) ^ (12 : ℕ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using (integral_rexp_neg_pi_mul_sq_norm (t := t) ht0)
  rw [hfun]
  calc
    (∫ x : EuclideanSpace ℝ (Fin 24), ‖ψT' (z₁line t)‖ * rexp (-(π * (t * (‖x‖ ^ 2))))) =
        ‖ψT' (z₁line t)‖ * (∫ x : EuclideanSpace ℝ (Fin 24), rexp (-(π * (t * (‖x‖ ^ 2))))) :=
      by exact integral_const_mul ‖ψT' (z₁line t)‖ fun a => rexp (-(π * (t * ‖a‖ ^ 2)))
    _ = ‖ψT' (z₁line t)‖ * (1 / t) ^ (12 : ℕ) := by simp [hgauss']


-- @@ L297-348 expanded
/-- For `t ∈ Ioc (0,1)`, the function `x ↦ permJ1Kernel w (x,t)` is integrable. -/
public lemma integrable_permJ1Kernel_slice (w : EuclideanSpace ℝ (Fin 24)) (t : ℝ)
    (ht : t ∈ Ioc (0 : ℝ) 1) :
    Integrable (fun x : EuclideanSpace ℝ (Fin 24) ↦ permJ1Kernel w (x, t))
      (volume : Measure (EuclideanSpace ℝ (Fin 24))) :=
  by
  have hz : 0 < (z₁line t).im := by
    simpa [z₁line] using (SpherePacking.Contour.z₁line_im_pos_Ioc (t := t) ht)
  have hgauss :
    Integrable
      (fun x : EuclideanSpace ℝ (Fin 24) ↦
        Complex.exp ((π : ℂ) * Complex.I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₁line t)))
      (volume : Measure (EuclideanSpace ℝ (Fin 24))) :=
    by
    simpa [mul_assoc] using
      (SpherePacking.ForMathlib.integrable_gaussian_cexp_pi_mul_I_mul (V :=
        EuclideanSpace ℝ (Fin 24)) (z := z₁line t) hz)
  have hgauss' :
    Integrable
      (fun x : EuclideanSpace ℝ (Fin 24) ↦
        ((Complex.I : ℂ) * ψT' (z₁line t)) *
          Complex.exp ((π : ℂ) * Complex.I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₁line t)))
      (volume : Measure (EuclideanSpace ℝ (Fin 24))) :=
    by simpa [mul_assoc] using hgauss.const_mul ((Complex.I : ℂ) * ψT' (z₁line t))
  have hmeas_phase :
    AEStronglyMeasurable
      (fun x : EuclideanSpace ℝ (Fin 24) ↦ Complex.exp (↑(-2 * π * ⟪x, w⟫) * Complex.I))
      (volume : Measure (EuclideanSpace ℝ (Fin 24))) :=
    by
    have hinner : Continuous fun x : EuclideanSpace ℝ (Fin 24) => (⟪x, w⟫ : ℝ) := by
      simpa using (continuous_id.inner continuous_const)
    have hreal : Continuous fun x : EuclideanSpace ℝ (Fin 24) => (-2 * π) * (⟪x, w⟫ : ℝ) :=
      continuous_const.mul hinner
    have hofReal :
      Continuous fun x : EuclideanSpace ℝ (Fin 24) => (↑(((-2 * π) * (⟪x, w⟫ : ℝ))) : ℂ) :=
      Complex.continuous_ofReal.comp hreal
    have harg :
      Continuous fun x : EuclideanSpace ℝ (Fin 24) =>
        (↑(((-2 * π) * (⟪x, w⟫ : ℝ))) : ℂ) * Complex.I :=
      hofReal.mul continuous_const
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (Complex.continuous_exp.comp harg) |>.aestronglyMeasurable
  have hbound :
    (∀ᵐ x : EuclideanSpace ℝ (Fin 24) ∂(volume : Measure (EuclideanSpace ℝ (Fin 24))),
      ‖Complex.exp (↑(-2 * π * ⟪x, w⟫) * Complex.I)‖ ≤ (1 : ℝ)) :=
    by
    refine Filter.Eventually.of_forall ?_
    intro x
    have hn : ‖Complex.exp (↑(-2 * π * ⟪x, w⟫) * Complex.I)‖ = (1 : ℝ) := by
      simpa using (Complex.norm_exp_ofReal_mul_I (-2 * π * ⟪x, w⟫))
    simpa [hn] using (le_of_eq hn)
  have h :=
    Integrable.bdd_mul (hg := hgauss') (f := fun x : EuclideanSpace ℝ (Fin 24) ↦
      Complex.exp (↑(-2 * π * ⟪x, w⟫) * Complex.I)) (g := fun x : EuclideanSpace ℝ (Fin 24) ↦
      ((Complex.I : ℂ) * ψT' (z₁line t)) *
        Complex.exp ((π : ℂ) * Complex.I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₁line t)))
      (c := (1 : ℝ)) hmeas_phase hbound
  simpa [permJ1Kernel, mul_assoc] using h


-- @@ L350-382 expanded
/-- Evaluate the `x`-integral of `permJ1Kernel` in terms of `Ψ₁_fourier`. -/
public lemma integral_permJ1Kernel_x (w : EuclideanSpace ℝ (Fin 24)) (t : ℝ)
    (ht : t ∈ Ioc (0 : ℝ) 1) :
    (∫ x : EuclideanSpace ℝ (Fin 24), permJ1Kernel w (x, t)) =
      (Complex.I : ℂ) * Ψ₁_fourier (‖w‖ ^ 2) (z₁line t) :=
  by
  have ht0 : 0 < t := ht.1
  have hz : 0 < (z₁line t).im := by
    simpa [z₁line] using (SpherePacking.Contour.z₁line_im_pos_Ioc (t := t) ht)
  let c : ℂ := (Complex.I : ℂ) * ψT' (z₁line t)
  have hfactor :
    (fun x : EuclideanSpace ℝ (Fin 24) => permJ1Kernel w (x, t)) =
      fun x : EuclideanSpace ℝ (Fin 24) =>
      c *
        (Complex.exp (↑(-2 * (π * ⟪x, w⟫)) * Complex.I) *
          Complex.exp ((π : ℂ) * Complex.I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₁line t))) :=
    by
    funext x
    dsimp [permJ1Kernel, c]
    simp [mul_assoc, mul_left_comm, mul_comm]
  calc
    (∫ x : EuclideanSpace ℝ (Fin 24), permJ1Kernel w (x, t)) =
        ∫ x : EuclideanSpace ℝ (Fin 24),
          c *
            (Complex.exp (↑(-2 * (π * ⟪x, w⟫)) * Complex.I) *
              Complex.exp ((π : ℂ) * Complex.I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₁line t))) :=
      by
      simpa using
        congrArg (fun F : EuclideanSpace ℝ (Fin 24) → ℂ => ∫ x : EuclideanSpace ℝ (Fin 24), F x)
          hfactor
    _ =
        c *
          ((((Complex.I : ℂ) / (z₁line t)) ^ (12 : ℕ)) *
            Complex.exp ((π : ℂ) * Complex.I * (‖w‖ ^ 2 : ℝ) * (-1 / (z₁line t)))) :=
      by
      -- `I` in the shared lemma is `Complex.I`.
      simpa using
        (SpherePacking.Contour.integral_const_mul_phase_gaussian_pi_mul_I_mul_even (k := 12) (w :=
          w) (z := z₁line t) hz (c := c))
    _ = (Complex.I : ℂ) * Ψ₁_fourier (‖w‖ ^ 2) (z₁line t) := by simp [c, Ψ₁_fourier, mul_assoc]


-- @@ L385-385 verbatim
end PermJ12



-- @@ L388-388 verbatim
end

-- @@ L389-389 verbatim
end SpherePacking.Dim24.BFourier
