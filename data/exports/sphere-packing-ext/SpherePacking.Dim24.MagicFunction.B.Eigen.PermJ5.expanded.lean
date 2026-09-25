module
public import SpherePacking.Dim24.MagicFunction.B.Defs.Eigenfunction
import SpherePacking.ForMathlib.GaussianFourierCommon
import SpherePacking.Dim24.MagicFunction.A.Eigen.GaussianFourier
import SpherePacking.Dim24.MagicFunction.B.Eigen.PermJ12ContourIdentity
import SpherePacking.Dim24.MagicFunction.B.Eigen.PermJ5Integrability



-- @@ L9-19 verbatim
/-!
# The `J₅` permutation and the `-1` eigenvalue of `b`

This file completes the Fourier permutation argument for the dim-24 magic function `b`. The main
step is the `J₅/J₆` identity, proved via the `t ↦ 1/t` change of variables and an integrability
argument for Fubini. We then assemble this with the `J₁`--`J₄` contour deformation identities to
obtain the `-1` eigenvalue.

## Main statements
* `eig_b`
-/


-- @@ L21-21 verbatim
open scoped FourierTransform Real

-- @@ L22-22 verbatim
open Complex


-- @@ L24-24 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

-- @@ L25-25 expanded
local notation "FT" => FourierTransform.fourierCLE ℂ (SchwartzMap (EuclideanSpace ℝ (Fin 24)) ℂ)


-- @@ L27-27 verbatim
namespace SpherePacking.Dim24.BFourier

-- @@ L28-28 verbatim
open MeasureTheory Set Filter

-- @@ L29-29 verbatim
open scoped RealInnerProductSpace


-- @@ L31-31 verbatim
noncomputable section


-- @@ L33-60 verbatim
lemma J₆'_eq (r : ℝ) :
    RealIntegrals.J₆' r =
      (-2 : ℂ) *
        ∫ s in Ici (1 : ℝ),
          (Complex.I : ℂ) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * r * s) := by
  simp only [RealIntegrals.J₆', mul_assoc]
  congr 1
  refine MeasureTheory.integral_congr_ae ?_
  refine (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall ?_
  intro s hs
  have hz : MagicFunction.Parametrisations.z₆' s = (Complex.I : ℂ) * (s : ℂ) := by
    -- `z₆'` is `I*s` on `Ici 1`.
    simpa using (MagicFunction.Parametrisations.z₆'_eq_of_mem (t := s) hs)
  -- Reduce the lambda-application form and rewrite `z₆' s`.
  simp only [neg_mul, mul_eq_mul_left_iff, I_ne_zero, or_false]
  rw [hz]
  -- Simplify the exponential using `I * I = -1`.
  have hexp :
      cexp (↑π * ((Complex.I : ℂ) * ((r : ℂ) * ((Complex.I : ℂ) * (s : ℂ))))) =
        cexp (-(↑π * (r : ℂ) * (s : ℂ))) := by
    have harg :
        (↑π : ℂ) * ((Complex.I : ℂ) * ((r : ℂ) * ((Complex.I : ℂ) * (s : ℂ)))) =
          (-(↑π * (r : ℂ) * (s : ℂ))) := by
      ring_nf
      simp
    simp [harg]
  rw [hexp]
  simp [mul_assoc]


-- @@ L62-235 expanded
theorem perm_J₅ :
    (FourierTransform.fourierCLE ℂ (SchwartzMap (EuclideanSpace ℝ (Fin 24)) ℂ)) J₅ = -J₆ :=
  by
  ext w
  simp only [FourierTransform.fourierCLE_apply, SchwartzMap.neg_apply]
    -- Rewrite the RHS via the explicit radial profile (avoid unfolding the Schwartz construction).
    
  rw [J₆_apply]
  change 𝓕 (J₅ : EuclideanSpace ℝ (Fin 24) → ℂ) w = -RealIntegrals.J₆' (‖w‖ ^ 2)
  rw [Real.fourier_eq' (J₅ : EuclideanSpace ℝ (Fin 24) → ℂ) w]
  simp only [smul_eq_mul, J₅_apply]
    -- Rewrite `J₅'` using the `t ↦ 1/t` substitution.
    
  have hJ5' (x : EuclideanSpace ℝ (Fin 24)) :
    RealIntegrals.J₅' (‖x‖ ^ 2) = (-2 : ℂ) * ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s := by
    simpa using (J5Change.Complete_Change_of_Variables (r := (‖x‖ ^ 2)))
  simp only [hJ5', mul_assoc]
    -- Move the phase factor inside the `s`-integral so we can use Fubini.
    
  let μs : Measure ℝ := (volume : Measure ℝ).restrict (Ici (1 : ℝ))
  have hmul :
    (fun x : EuclideanSpace ℝ (Fin 24) ↦
        cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s) =
      fun x : EuclideanSpace ℝ (Fin 24) ↦
      ∫ s in Ici (1 : ℝ), cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * J5Change.g (‖x‖ ^ 2) s :=
    by
    ext x
    exact
      Eq.symm
        (integral_const_mul (cexp (↑(-2 * (π * ⟪x, w⟫)) * I)) (J5Change.g (‖x‖ ^ 2)))
          -- Apply Fubini to swap the order of integration.
          
  let f : EuclideanSpace ℝ (Fin 24) → ℝ → ℂ := fun x s ↦ PermJ5.kernel w (x, s)
  have hint :
    Integrable (Function.uncurry f) ((volume : Measure (EuclideanSpace ℝ (Fin 24))).prod μs) :=
    by
    have hint' :
      Integrable (PermJ5.kernel w) ((volume : Measure (EuclideanSpace ℝ (Fin 24))).prod μs) := by
      simpa [μs, SpherePacking.Integration.μIciOne] using (PermJ5.integrable_kernel (w := w))
    simpa [f, Function.uncurry] using hint'
  have hswap :=
    MeasureTheory.integral_integral_swap (μ := (volume : Measure (EuclideanSpace ℝ (Fin 24)))) (ν :=
      μs) (f := f) hint
  have hinner (s : ℝ) (hs : s ∈ Ici (1 : ℝ)) :
    (∫ x : EuclideanSpace ℝ (Fin 24), f x s) =
      (-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s) :=
    by
    have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
    have hs_ne0 : s ≠ 0 := ne_of_gt hs0
    have hcancel : ((s ^ (-12 : ℤ)) : ℂ) * (s ^ 12 : ℂ) = 1 :=
      AFourier.zpow_neg_twelve_mul_pow_twelve (s := s) hs_ne0
    have hfactor :
      (fun x : EuclideanSpace ℝ (Fin 24) ↦ f x s) = fun x : EuclideanSpace ℝ (Fin 24) ↦
        ((-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * ((s ^ (-12 : ℤ)) : ℂ)) *
          (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * cexp (-π * (‖x‖ ^ 2) / s)) :=
      by
      funext x
      dsimp [f, PermJ5.kernel, J5Change.g]
      simp
      ac_rfl
    calc
      (∫ x : EuclideanSpace ℝ (Fin 24), f x s) =
          ∫ x : EuclideanSpace ℝ (Fin 24),
            ((-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * ((s ^ (-12 : ℤ)) : ℂ)) *
              (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * cexp (-π * (‖x‖ ^ 2) / s)) :=
        congrArg (fun F : EuclideanSpace ℝ (Fin 24) → ℂ => ∫ x, F x) hfactor
      _ =
          ((-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * ((s ^ (-12 : ℤ)) : ℂ)) *
            ∫ x : EuclideanSpace ℝ (Fin 24),
              cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * cexp (-π * (‖x‖ ^ 2) / s) :=
        by
        exact
          integral_const_mul (-I * ψS' (I * ↑s) * ↑s ^ (-12)) fun a =>
            cexp (↑(-2 * (π * ⟪a, w⟫)) * I) * cexp (-↑π * ↑‖a‖ ^ 2 / ↑s)
      _ =
          ((-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * ((s ^ (-12 : ℤ)) : ℂ)) *
            ((s ^ 12 : ℂ) * cexp (-π * (‖w‖ ^ 2) * s)) :=
        by
        rw [SpherePacking.ForMathlib.integral_phase_gaussian_even (k := 12) (w := w) (s := s) hs0]
      _ = (-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s) := by
        calc
          ((-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * ((s ^ (-12 : ℤ)) : ℂ)) *
                ((s ^ 12 : ℂ) * cexp (-π * (‖w‖ ^ 2) * s)) =
              (-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * ((((s ^ (-12 : ℤ)) : ℂ) * (s ^ 12 : ℂ))) *
                cexp (-π * (‖w‖ ^ 2) * s) :=
            by ac_rfl
          _ = (-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s) :=
            by
            rw [hcancel]
            simp [mul_assoc]
  have htoIter :
    (∫ x : EuclideanSpace ℝ (Fin 24),
        cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s) =
      ∫ x : EuclideanSpace ℝ (Fin 24), ∫ s in Ici (1 : ℝ), f x s :=
    by
    simpa [f, PermJ5.kernel] using congrArg (fun F : EuclideanSpace ℝ (Fin 24) → ℂ => ∫ x, F x) hmul
  have hswap' :
    (∫ x : EuclideanSpace ℝ (Fin 24), ∫ s in Ici (1 : ℝ), f x s) =
      ∫ s in Ici (1 : ℝ), ∫ x : EuclideanSpace ℝ (Fin 24), f x s :=
    by simpa [μs] using hswap
  have hAE :
    (fun s : ℝ ↦ ∫ x : EuclideanSpace ℝ (Fin 24), f x s) =ᵐ[μs] fun s : ℝ ↦
      (-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s) :=
    by
    refine (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall ?_
    intro s hs
    simpa [f] using hinner s hs
  have hintEq :
    (∫ s in Ici (1 : ℝ), ∫ x : EuclideanSpace ℝ (Fin 24), f x s) =
      ∫ s in Ici (1 : ℝ), (-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s) :=
    by
    simpa [μs] using
      (MeasureTheory.integral_congr_ae hAE)
        -- Finish: match `-J₆`.
        
  have hmain :
    (∫ x : EuclideanSpace ℝ (Fin 24),
        cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * ((-2 : ℂ) * ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s)) =
      (-2 : ℂ) *
        ∫ s in Ici (1 : ℝ), (-I) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s) :=
    by
    have hpull :
      (∫ x : EuclideanSpace ℝ (Fin 24),
          cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
            ((-2 : ℂ) * ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s)) =
        (-2 : ℂ) *
          (∫ x : EuclideanSpace ℝ (Fin 24),
            cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s) :=
      by
      have hfun :
        (fun x : EuclideanSpace ℝ (Fin 24) ↦
            cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              ((-2 : ℂ) * ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s)) =
          fun x : EuclideanSpace ℝ (Fin 24) ↦
          (-2 : ℂ) *
            (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s) :=
        by
        funext x
        ac_rfl
      calc
        (∫ x : EuclideanSpace ℝ (Fin 24),
              cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
                ((-2 : ℂ) * ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s)) =
            ∫ x : EuclideanSpace ℝ (Fin 24),
              (-2 : ℂ) *
                (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s) :=
          congrArg (fun F : EuclideanSpace ℝ (Fin 24) → ℂ => ∫ x, F x) hfun
        _ =
            (-2 : ℂ) *
              ∫ x : EuclideanSpace ℝ (Fin 24),
                cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * ∫ s in Ici (1 : ℝ), J5Change.g (‖x‖ ^ 2) s :=
          integral_const_mul (-2) fun a =>
            cexp (↑(-2 * (π * ⟪a, w⟫)) * I) * ∫ (s : ℝ) in Ici 1, J5Change.g (‖a‖ ^ 2) s
    lia
      -- Compare the computed `s`-integral with the explicit representation of `J₆'`.
      
  rw [hmain]
  rw [J₆'_eq (r := ‖w‖ ^ 2)]
  have hneg :
    (fun s : ℝ ↦ (-I : ℂ) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s)) =
      fun s : ℝ ↦
      -((Complex.I : ℂ) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s)) :=
    by
    funext s
    ring
  have hInt :
    (∫ s in Ici (1 : ℝ), (-I : ℂ) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s)) =
      ∫ s in Ici (1 : ℝ),
        -((Complex.I : ℂ) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s)) :=
    by exact congrArg (fun F : ℝ → ℂ => ∫ s in Ici (1 : ℝ), F s) hneg
  rw [hInt]
  have hnegint :
    (∫ s in Ici (1 : ℝ),
        -((Complex.I : ℂ) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s))) =
      -(∫ s in Ici (1 : ℝ),
          (Complex.I : ℂ) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s)) :=
    by
    exact
      (MeasureTheory.integral_neg (μ := (volume : Measure ℝ).restrict (Ici (1 : ℝ))) (f :=
        fun s : ℝ ↦ (Complex.I : ℂ) * ψS' ((Complex.I : ℂ) * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s)))
  rw [hnegint]
  simp [mul_assoc]


-- @@ L237-245 expanded
theorem perm_J₆ :
    (FourierTransform.fourierCLE ℂ (SchwartzMap (EuclideanSpace ℝ (Fin 24)) ℂ)) J₆ = -J₅ :=
  by
  have heven : (fun x : EuclideanSpace ℝ (Fin 24) ↦ J₆ (-x)) = fun x ↦ J₆ x :=
    by
    funext x
    simp [J₆, mkRadial]
  have hsymm :
    (FourierTransform.fourierCLE ℂ (SchwartzMap (EuclideanSpace ℝ (Fin 24)) ℂ)).symm J₆ =
      (FourierTransform.fourierCLE ℂ (SchwartzMap (EuclideanSpace ℝ (Fin 24)) ℂ)) J₆ :=
    AFourier.fourierTransformCLE_symm_eq_of_even (f := J₆) heven
  have h :=
    (congrArg (FourierTransform.fourierCLE ℂ (SchwartzMap (EuclideanSpace ℝ (Fin 24)) ℂ)).symm
        perm_J₅).symm
  simp only [map_neg, ContinuousLinearEquiv.symm_apply_apply, ← hsymm] at h ⊢
  rw [← h, neg_neg]


-- @@ L247-247 verbatim
end

-- @@ L248-248 verbatim
end BFourier


-- @@ L250-263 expanded
/-- The Fourier transform of the dim-24 magic function `b` is `-b`. -/
public theorem eig_b :
    (FourierTransform.fourierCLE ℂ (SchwartzMap (EuclideanSpace ℝ (Fin 24)) ℂ)) b = -b := by
  /- Proof sketch (paper Lemma 3.1):
    Apply the radial Fourier transform to the defining contour expression for `b`.
    Use the transformation laws of `ψI,ψS,ψT` under `S` together with the relation
    `ψT | S = -ψT` to obtain the eigenvalue `-1`. -/
  
  rw [BFourier.b_eq_sum_integrals]
  have hrw :
    BFourier.J₁ + BFourier.J₂ + BFourier.J₃ + BFourier.J₄ + BFourier.J₅ + BFourier.J₆ =
      (BFourier.J₁ + BFourier.J₂) + (BFourier.J₃ + BFourier.J₄) + BFourier.J₅ + BFourier.J₆ :=
    by ac_rfl
  rw [hrw, map_add, map_add, map_add, BFourier.perm_J₁_J₂, BFourier.perm_J₃_J₄, BFourier.perm_J₅,
    BFourier.perm_J₆]
  abel


-- @@ L265-265 verbatim
end SpherePacking.Dim24
