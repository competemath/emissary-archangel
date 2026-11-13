import Mathlib
import Submission.MorseEvents


-- @@ L4-17 verbatim
/-!
# A constructive two-dimensional local Morse lemma

This file isolates the analytic input needed to manufacture the exact
`StandardMorseEventAt.time_model` field.  The construction is split into three
independently reusable layers:

1. an exact second-order Hadamard formula with integral remainder;
2. algebraic square completion for a smoothly varying `2 × 2` quadratic form;
3. a local inverse obtained from the inverse function theorem.

The final API packages a local parametrization on which the scalar function is
literally one of `morseQuadratic minimum/saddle/maximum`.
-/


-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
open Set Filter Function Metric

-- @@ L22-22 verbatim
open scoped Topology ContDiff RealInnerProductSpace Interval


-- @@ L24-24 verbatim
namespace Submission


-- @@ L26-26 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)


-- @@ L28-28 verbatim
/-! ## Coordinates and radial Hadamard factorization -/


-- @@ L30-31 verbatim
/-- Translate a scalar function so that the point under study becomes the origin. -/
def recenter (f : E₂ → ℝ) (p x : E₂) : ℝ := f (p + x)


-- @@ L33-34 verbatim
@[simp] lemma recenter_zero (f : E₂ → ℝ) (p : E₂) : recenter f p 0 = f p := by
  simp [recenter]


-- @@ L36-38 verbatim
lemma contDiff_recenter {f : E₂ → ℝ} {k : ℕ∞ω} (hf : ContDiff ℝ k f) (p : E₂) :
    ContDiff ℝ k (recenter f p) := by
  exact hf.comp (contDiff_const.add contDiff_id)


-- @@ L40-53 verbatim
lemma fderiv_recenter_zero {f : E₂ → ℝ} {p : E₂}
    (hf : DifferentiableAt ℝ f p) :
    fderiv ℝ (recenter f p) 0 = fderiv ℝ f p := by
  have hc : HasFDerivAt (fun _ : E₂ => p) (0 : E₂ →L[ℝ] E₂) 0 :=
    hasFDerivAt_const (x := (0 : E₂)) p
  have hi : HasFDerivAt (fun x : E₂ => x) (ContinuousLinearMap.id ℝ E₂) 0 :=
    hasFDerivAt_id (x := (0 : E₂))
  have hshift := hc.add hi
  have hfp : HasFDerivAt f (fderiv ℝ f p) (p + 0) := by simpa using hf.hasFDerivAt
  have h := hfp.comp 0 hshift
  change fderiv ℝ (fun x : E₂ => f (p + x)) 0 = fderiv ℝ f p
  convert h.fderiv using 1 <;> try rfl
  ext v
  simp


-- @@ L55-58 verbatim
/-- Exact second-order radial remainder in Taylor--Hadamard form. -/
def radialHadamardRemainder (f : E₂ → ℝ) (x : E₂) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    (1 - t) • iteratedFDeriv ℝ 2 f (t • x) (fun _ => x)


-- @@ L60-74 verbatim
/-- Hadamard's second-order factorization at a critical point.  This is an exact
identity, not a little-`o` Taylor estimate. -/
theorem map_eq_add_radialHadamardRemainder {f : E₂ → ℝ}
    (hf : ContDiff ℝ (1 + 1) f) (hcrit : fderiv ℝ f 0 = 0) (x : E₂) :
    f x = f 0 + radialHadamardRemainder f x := by
  have hTaylor := map_add_eq_sum_add_integral_iteratedFDeriv
    (f := f) (x := (0 : E₂)) (y := x) (n := 1) (fun _ _ => by
      exact hf.contDiffAt)
  have hsum :
      ∑ k ∈ Finset.range (1 + 1), (Nat.factorial k : ℝ)⁻¹ •
        (iteratedFDeriv ℝ k f 0 (fun _ => x)) = f 0 := by
    norm_num [Finset.sum_range_succ, iteratedFDeriv_zero_apply,
      iteratedFDeriv_one_apply, hcrit]
  rw [hsum] at hTaylor
  simpa [radialHadamardRemainder, pow_one] using hTaylor


-- @@ L76-85 verbatim
/-- Centered form of the exact Hadamard identity at an arbitrary critical point. -/
theorem map_add_eq_add_radialHadamardRemainder {f : E₂ → ℝ} {p : E₂}
    (hf : ContDiff ℝ (1 + 1) f) (hcrit : fderiv ℝ f p = 0) (x : E₂) :
    f (p + x) = f p + radialHadamardRemainder (recenter f p) x := by
  have hrec : ContDiff ℝ (1 + 1) (recenter f p) := contDiff_recenter hf p
  have hdiff : Differentiable ℝ f := ContDiff.differentiable hf (by simp)
  have hc : fderiv ℝ (recenter f p) 0 = 0 := by
    rw [fderiv_recenter_zero hdiff.differentiableAt]
    exact hcrit
  simpa [recenter] using map_eq_add_radialHadamardRemainder hrec hc x


-- @@ L87-87 verbatim
/-! ## Smooth quadratic Hadamard data -/


-- @@ L89-102 verbatim
/-- A coordinate-wise second-order Hadamard factorization

`f(x,y) = f(0) + a(x,y)x² + 2b(x,y)xy + c(x,y)y²`.

Only smoothness near the origin is needed by the local inverse theorem. -/
structure HadamardQuadraticData (f : E₂ → ℝ) where
  a : E₂ → ℝ
  b : E₂ → ℝ
  c : E₂ → ℝ
  smooth_a : ContDiffAt ℝ ∞ a 0
  smooth_b : ContDiffAt ℝ ∞ b 0
  smooth_c : ContDiffAt ℝ ∞ c 0
  exact : ∀ x, f x = f 0 +
    (a x * (x 0) ^ 2 + 2 * b x * (x 0) * (x 1) + c x * (x 1) ^ 2)


-- @@ L104-104 verbatim
namespace HadamardQuadraticData


-- @@ L106-106 verbatim
variable {f : E₂ → ℝ} (H : HadamardQuadraticData f)


-- @@ L108-109 verbatim
/-- Determinant of the symmetric coefficient matrix. -/
def det (x : E₂) : ℝ := H.a x * H.c x - H.b x ^ 2


-- @@ L111-112 verbatim
lemma smooth_det : ContDiffAt ℝ ∞ H.det 0 :=
  (H.smooth_a.mul H.smooth_c).sub (H.smooth_b.pow 2)


-- @@ L114-116 verbatim
/-- Nondegeneracy of the coefficient Hessian.  The actual Hessian is twice this
matrix, so this is equivalent to the usual nonzero determinant condition. -/
def IsNondegenerate : Prop := H.det 0 ≠ 0


-- @@ L118-132 verbatim
/-- A nondegenerate two-dimensional quadratic form always admits a nonzero pivot
after at most the fixed basis change `e₀ ↦ e₀ + e₁`. -/
theorem exists_nonzero_pivot_candidate (hnd : H.IsNondegenerate) :
    H.a 0 ≠ 0 ∨ H.c 0 ≠ 0 ∨ H.a 0 + 2 * H.b 0 + H.c 0 ≠ 0 := by
  by_cases ha : H.a 0 = 0
  · by_cases hc : H.c 0 = 0
    · right; right
      intro hp
      apply hnd
      rw [det, ha, hc]
      have hb : H.b 0 = 0 := by linarith
      rw [hb]
      norm_num
    · exact Or.inr (Or.inl hc)
  · exact Or.inl ha


-- @@ L134-142 verbatim
/-- Literal two-by-two square completion, valid whenever the first pivot is
nonzero. -/
theorem completeSquare {x : E₂} (ha : H.a x ≠ 0) :
    H.a x * (x 0) ^ 2 + 2 * H.b x * (x 0) * (x 1) + H.c x * (x 1) ^ 2 =
      H.a x * (x 0 + H.b x / H.a x * x 1) ^ 2 +
        H.det x / H.a x * (x 1) ^ 2 := by
  rw [det]
  field_simp
  ring


-- @@ L144-144 verbatim
/-! ### The three normalized coordinate maps -/


-- @@ L146-146 verbatim
def e₀ : E₂ := EuclideanSpace.single 0 1


-- @@ L148-148 verbatim
def e₁ : E₂ := EuclideanSpace.single 1 1


-- @@ L150-150 verbatim
@[simp] lemma e₀_apply_zero : (e₀ : E₂) 0 = 1 := by simp [e₀]

-- @@ L151-151 verbatim
@[simp] lemma e₀_apply_one : (e₀ : E₂) 1 = 0 := by simp [e₀]

-- @@ L152-152 verbatim
@[simp] lemma e₁_apply_zero : (e₁ : E₂) 0 = 0 := by simp [e₁]

-- @@ L153-153 verbatim
@[simp] lemma e₁_apply_one : (e₁ : E₂) 1 = 1 := by simp [e₁]


-- @@ L155-157 verbatim
lemma basis_decomposition (x : E₂) : x = x 0 • e₀ + x 1 • e₁ := by
  ext i
  fin_cases i <;> simp


-- @@ L159-179 verbatim
/-- Coordinate expansion of a continuous bilinear form.  No symmetry is used:
the two mixed entries are retained separately. -/
theorem bilinear_expand_coordinates (M : E₂ [×2]→L[ℝ] ℝ) (x : E₂) :
    M (fun _ => x) =
      x 0 ^ 2 * M ![e₀, e₀] + x 0 * x 1 * M ![e₀, e₁] +
      x 1 * x 0 * M ![e₁, e₀] + x 1 ^ 2 * M ![e₁, e₁] := by
  conv_lhs => rw [basis_decomposition x]
  have hv (z : E₂) : (fun _ : Fin 2 => z) = Fin.cons z (Fin.cons z Fin.elim0) := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  change M.curryLeft (x 0 • e₀ + x 1 • e₁)
    (Fin.cons (x 0 • e₀ + x 1 • e₁) Fin.elim0) = _
  have hcons (u v : E₂) : Fin.cons u (Fin.cons v Fin.elim0) = ![u, v] := by
    funext i
    fin_cases i <;> rfl
  simp only [map_add, map_smul, ContinuousMultilinearMap.cons_add,
    ContinuousMultilinearMap.cons_smul, ContinuousMultilinearMap.curryLeft_apply,
    add_apply, smul_apply, smul_eq_mul]
  simp_rw [hcons]
  ring


-- @@ L181-184 verbatim
/-- First diagonal coefficient obtained by integrating the Hessian along the
radial segment from `0` to `x`. -/
def integratedHadamardA (f : E₂ → ℝ) (x : E₂) : ℝ :=
  ∫ t in (0 : ℝ)..1, (1 - t) * iteratedFDeriv ℝ 2 f (t • x) ![e₀, e₀]


-- @@ L186-190 verbatim
/-- Symmetrized mixed coefficient obtained from the radial Hessian. -/
def integratedHadamardB (f : E₂ → ℝ) (x : E₂) : ℝ :=
  ∫ t in (0 : ℝ)..1, (1 - t) *
    ((iteratedFDeriv ℝ 2 f (t • x) ![e₀, e₁] +
      iteratedFDeriv ℝ 2 f (t • x) ![e₁, e₀]) / 2)


-- @@ L192-194 verbatim
/-- Second diagonal coefficient obtained from the radial Hessian. -/
def integratedHadamardC (f : E₂ → ℝ) (x : E₂) : ℝ :=
  ∫ t in (0 : ℝ)..1, (1 - t) * iteratedFDeriv ℝ 2 f (t • x) ![e₁, e₁]


-- @@ L196-248 verbatim
/-- Exact coordinate form of radial second-order Hadamard factorization. -/
theorem exact_integratedHadamard {f : E₂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hcrit : fderiv ℝ f 0 = 0) (x : E₂) :
    f x = f 0 +
      (integratedHadamardA f x * (x 0) ^ 2 +
        2 * integratedHadamardB f x * (x 0) * (x 1) +
        integratedHadamardC f x * (x 1) ^ 2) := by
  have htwo : (2 : ℕ∞ω) ≤ ∞ := by
    change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr (le_of_lt (ENat.coe_lt_top 2))
  rw [map_eq_add_radialHadamardRemainder
    (hf.of_le (by simpa only [one_add_one_eq_two] using htwo)) hcrit]
  congr 1
  have hM : Continuous (fun t : ℝ => iteratedFDeriv ℝ 2 f (t • x)) :=
    (hf.continuous_iteratedFDeriv htwo).comp
      (continuous_id.smul continuous_const)
  have h00 : Continuous (fun t : ℝ => iteratedFDeriv ℝ 2 f (t • x) ![e₀, e₀]) :=
    hM.eval continuous_const
  have h01 : Continuous (fun t : ℝ => iteratedFDeriv ℝ 2 f (t • x) ![e₀, e₁]) :=
    hM.eval continuous_const
  have h10 : Continuous (fun t : ℝ => iteratedFDeriv ℝ 2 f (t • x) ![e₁, e₀]) :=
    hM.eval continuous_const
  have h11 : Continuous (fun t : ℝ => iteratedFDeriv ℝ 2 f (t • x) ![e₁, e₁]) :=
    hM.eval continuous_const
  let A : ℝ → ℝ := fun t => (1 - t) * iteratedFDeriv ℝ 2 f (t • x) ![e₀, e₀]
  let B : ℝ → ℝ := fun t => (1 - t) *
    ((iteratedFDeriv ℝ 2 f (t • x) ![e₀, e₁] +
      iteratedFDeriv ℝ 2 f (t • x) ![e₁, e₀]) / 2)
  let C : ℝ → ℝ := fun t => (1 - t) * iteratedFDeriv ℝ 2 f (t • x) ![e₁, e₁]
  have hA : Continuous A := (continuous_const.sub continuous_id).mul h00
  have hB : Continuous B := (continuous_const.sub continuous_id).mul
    ((h01.add h10).div_const 2)
  have hC : Continuous C := (continuous_const.sub continuous_id).mul h11
  have hAi : IntervalIntegrable (fun t => x 0 ^ 2 * A t) MeasureTheory.volume 0 1 :=
    (hA.const_mul _).intervalIntegrable 0 1
  have hBi : IntervalIntegrable (fun t => (2 * x 0 * x 1) * B t)
      MeasureTheory.volume 0 1 :=
    (hB.const_mul _).intervalIntegrable 0 1
  have hCi : IntervalIntegrable (fun t => x 1 ^ 2 * C t) MeasureTheory.volume 0 1 :=
    (hC.const_mul _).intervalIntegrable 0 1
  have hexpand : ∀ t : ℝ,
      (1 - t) • iteratedFDeriv ℝ 2 f (t • x) (fun _ => x) =
        x 0 ^ 2 * A t + (2 * x 0 * x 1) * B t + x 1 ^ 2 * C t := by
    intro t
    rw [bilinear_expand_coordinates]
    simp only [smul_eq_mul, A, B, C]
    ring
  simp_rw [radialHadamardRemainder, hexpand]
  rw [intervalIntegral.integral_add (hAi.add hBi) hCi,
    intervalIntegral.integral_add hAi hBi]
  simp only [intervalIntegral.integral_const_mul, integratedHadamardA,
    integratedHadamardB, integratedHadamardC, A, B, C]
  ring


-- @@ L250-265 verbatim
/-- Package the explicit radial-integral coefficients as quadratic Hadamard
data.  The three hypotheses isolate precisely the parameter-integral
smoothness obligation; the exact factorization itself is proved above. -/
def integratedHadamardData {f : E₂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hcrit : fderiv ℝ f 0 = 0)
    (hA : ContDiffAt ℝ ∞ (integratedHadamardA f) 0)
    (hB : ContDiffAt ℝ ∞ (integratedHadamardB f) 0)
    (hC : ContDiffAt ℝ ∞ (integratedHadamardC f) 0) :
    HadamardQuadraticData f where
  a := integratedHadamardA f
  b := integratedHadamardB f
  c := integratedHadamardC f
  smooth_a := hA
  smooth_b := hB
  smooth_c := hC
  exact := exact_integratedHadamard hf hcrit


-- @@ L267-272 verbatim
/-- Determinant of the radial-integral coefficient matrix at the critical
point.  It differs from the determinant of the usual Hessian only by the
nonzero normalization coming from the second-order Taylor convention. -/
def integratedHadamardDet (f : E₂ → ℝ) : ℝ :=
  integratedHadamardA f 0 * integratedHadamardC f 0 -
    integratedHadamardB f 0 ^ 2


-- @@ L274-276 verbatim
/-- A triangular varying coordinate change. -/
def squareCoord (α β γ : E₂ → ℝ) (x : E₂) : E₂ :=
  ((α x * (x 0 + β x * x 1)) • e₀ : E₂) + ((γ x * x 1) • e₁ : E₂)


-- @@ L278-280 verbatim
@[simp] lemma squareCoord_apply_zero (α β γ : E₂ → ℝ) (x : E₂) :
    squareCoord α β γ x 0 = α x * (x 0 + β x * x 1) := by
  simp [squareCoord]


-- @@ L282-284 verbatim
@[simp] lemma squareCoord_apply_one (α β γ : E₂ → ℝ) (x : E₂) :
    squareCoord α β γ x 1 = γ x * x 1 := by
  simp [squareCoord]


-- @@ L286-288 verbatim
@[simp] lemma squareCoord_zero (α β γ : E₂ → ℝ) :
    squareCoord α β γ 0 = 0 := by
  simp [squareCoord]


-- @@ L290-290 verbatim
def proj₀ : E₂ →L[ℝ] ℝ := EuclideanSpace.proj 0


-- @@ L292-292 verbatim
def proj₁ : E₂ →L[ℝ] ℝ := EuclideanSpace.proj 1


-- @@ L294-295 verbatim
/-- Swap the two coordinates. -/
def swapCLM : E₂ →L[ℝ] E₂ := proj₁.smulRight e₀ + proj₀.smulRight e₁


-- @@ L297-298 verbatim
@[simp] lemma swapCLM_apply_zero (v : E₂) : swapCLM v 0 = v 1 := by
  simp [swapCLM, proj₀, proj₁]


-- @@ L300-301 verbatim
@[simp] lemma swapCLM_apply_one (v : E₂) : swapCLM v 1 = v 0 := by
  simp [swapCLM, proj₀, proj₁]


-- @@ L303-305 verbatim
@[simp] lemma swapCLM_swap (v : E₂) : swapCLM (swapCLM v) = v := by
  ext i
  fin_cases i <;> simp


-- @@ L307-315 verbatim
lemma swapCLM_bijective : Function.Bijective swapCLM := by
  constructor
  · intro x y h
    calc
      x = swapCLM (swapCLM x) := (swapCLM_swap x).symm
      _ = swapCLM (swapCLM y) := congrArg swapCLM h
      _ = y := swapCLM_swap y
  · intro y
    exact ⟨swapCLM y, swapCLM_swap y⟩


-- @@ L317-320 verbatim
def swapEquiv : E₂ ≃L[ℝ] E₂ :=
  ContinuousLinearEquiv.ofBijective swapCLM
    (LinearMap.ker_eq_bot'.mpr fun m hm => swapCLM_bijective.1 (by simpa using hm))
    (LinearMap.range_eq_top.mpr swapCLM_bijective.2)


-- @@ L322-322 verbatim
@[simp] lemma swapEquiv_coe : (swapEquiv : E₂ →L[ℝ] E₂) = swapCLM := rfl


-- @@ L324-326 verbatim
@[simp] lemma swapEquiv_apply_zero (v : E₂) : swapEquiv v 0 = v 1 := by
  change swapCLM v 0 = v 1
  simp


-- @@ L328-330 verbatim
@[simp] lemma swapEquiv_apply_one (v : E₂) : swapEquiv v 1 = v 0 := by
  change swapCLM v 1 = v 0
  simp


-- @@ L332-335 verbatim
lemma norm_swapCLM (v : E₂) : ‖swapCLM v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp [Fin.sum_univ_two, add_comm]


-- @@ L337-341 verbatim
/-- Fixed determinant-one shear sending the first basis vector to `e₀ + e₁`.
It supplies a nonzero pivot in the sole case where both diagonal coefficients
vanish. -/
def sumShearCLM : E₂ →L[ℝ] E₂ :=
  proj₀.smulRight e₀ + (proj₀ + proj₁).smulRight e₁


-- @@ L343-344 verbatim
def sumShearInvCLM : E₂ →L[ℝ] E₂ :=
  proj₀.smulRight e₀ + (proj₁ - proj₀).smulRight e₁


-- @@ L346-347 verbatim
@[simp] lemma sumShearCLM_apply_zero (v : E₂) : sumShearCLM v 0 = v 0 := by
  simp [sumShearCLM, proj₀, proj₁]


-- @@ L349-350 verbatim
@[simp] lemma sumShearCLM_apply_one (v : E₂) : sumShearCLM v 1 = v 0 + v 1 := by
  simp [sumShearCLM, proj₀, proj₁]


-- @@ L352-353 verbatim
@[simp] lemma sumShearInvCLM_apply_zero (v : E₂) : sumShearInvCLM v 0 = v 0 := by
  simp [sumShearInvCLM, proj₀, proj₁]


-- @@ L355-356 verbatim
@[simp] lemma sumShearInvCLM_apply_one (v : E₂) : sumShearInvCLM v 1 = v 1 - v 0 := by
  simp [sumShearInvCLM, proj₀, proj₁]


-- @@ L358-361 verbatim
@[simp] lemma sumShearInvCLM_shear (v : E₂) :
    sumShearInvCLM (sumShearCLM v) = v := by
  ext i
  fin_cases i <;> simp


-- @@ L363-366 verbatim
@[simp] lemma sumShearCLM_inv (v : E₂) :
    sumShearCLM (sumShearInvCLM v) = v := by
  ext i
  fin_cases i <;> simp


-- @@ L368-376 verbatim
lemma sumShearCLM_bijective : Function.Bijective sumShearCLM := by
  constructor
  · intro x y h
    calc
      x = sumShearInvCLM (sumShearCLM x) := (sumShearInvCLM_shear x).symm
      _ = sumShearInvCLM (sumShearCLM y) := congrArg sumShearInvCLM h
      _ = y := sumShearInvCLM_shear y
  · intro y
    exact ⟨sumShearInvCLM y, sumShearCLM_inv y⟩


-- @@ L378-381 verbatim
def sumShearEquiv : E₂ ≃L[ℝ] E₂ :=
  ContinuousLinearEquiv.ofBijective sumShearCLM
    (LinearMap.ker_eq_bot'.mpr fun m hm => sumShearCLM_bijective.1 (by simpa using hm))
    (LinearMap.range_eq_top.mpr sumShearCLM_bijective.2)


-- @@ L383-383 verbatim
@[simp] lemma sumShearEquiv_coe : (sumShearEquiv : E₂ →L[ℝ] E₂) = sumShearCLM := rfl


-- @@ L385-387 verbatim
@[simp] lemma sumShearEquiv_apply_zero (v : E₂) : sumShearEquiv v 0 = v 0 := by
  change sumShearCLM v 0 = v 0
  simp


-- @@ L389-391 verbatim
@[simp] lemma sumShearEquiv_apply_one (v : E₂) : sumShearEquiv v 1 = v 0 + v 1 := by
  change sumShearCLM v 1 = v 0 + v 1
  simp


-- @@ L393-411 verbatim
/-- Quadratic Hadamard data after swapping the source coordinates. -/
def swapData : HadamardQuadraticData (fun x => f (swapEquiv x)) where
  a := fun x => H.c (swapEquiv x)
  b := fun x => H.b (swapEquiv x)
  c := fun x => H.a (swapEquiv x)
  smooth_a := by
    have hc : ContDiffAt ℝ ∞ H.c (swapEquiv 0) := by simpa using H.smooth_c
    exact hc.comp (0 : E₂) swapEquiv.contDiff.contDiffAt
  smooth_b := by
    have hb : ContDiffAt ℝ ∞ H.b (swapEquiv 0) := by simpa using H.smooth_b
    exact hb.comp (0 : E₂) swapEquiv.contDiff.contDiffAt
  smooth_c := by
    have ha : ContDiffAt ℝ ∞ H.a (swapEquiv 0) := by simpa using H.smooth_a
    exact ha.comp (0 : E₂) swapEquiv.contDiff.contDiffAt
  exact := by
    intro x
    rw [H.exact]
    simp only [map_zero, swapEquiv_apply_zero, swapEquiv_apply_one]
    ring


-- @@ L413-414 verbatim
@[simp] lemma swapData_a_zero : H.swapData.a 0 = H.c 0 := by
  simp [swapData]


-- @@ L416-418 verbatim
@[simp] lemma swapData_det (x : E₂) : H.swapData.det x = H.det (swapEquiv x) := by
  simp [swapData, det]
  ring


-- @@ L420-446 verbatim
/-- Quadratic Hadamard data after the fixed sum shear. -/
def sumShearData : HadamardQuadraticData (fun x => f (sumShearEquiv x)) where
  a := fun x => H.a (sumShearEquiv x) + 2 * H.b (sumShearEquiv x) +
    H.c (sumShearEquiv x)
  b := fun x => H.b (sumShearEquiv x) + H.c (sumShearEquiv x)
  c := fun x => H.c (sumShearEquiv x)
  smooth_a := by
    have ha0 : ContDiffAt ℝ ∞ H.a (sumShearEquiv 0) := by simpa using H.smooth_a
    have hb0 : ContDiffAt ℝ ∞ H.b (sumShearEquiv 0) := by simpa using H.smooth_b
    have hc0 : ContDiffAt ℝ ∞ H.c (sumShearEquiv 0) := by simpa using H.smooth_c
    have ha := ha0.comp (0 : E₂) sumShearEquiv.contDiff.contDiffAt
    have hb := hb0.comp (0 : E₂) sumShearEquiv.contDiff.contDiffAt
    have hc := hc0.comp (0 : E₂) sumShearEquiv.contDiff.contDiffAt
    exact (ha.add (contDiffAt_const.mul hb)).add hc
  smooth_b := by
    have hb0 : ContDiffAt ℝ ∞ H.b (sumShearEquiv 0) := by simpa using H.smooth_b
    have hc0 : ContDiffAt ℝ ∞ H.c (sumShearEquiv 0) := by simpa using H.smooth_c
    exact (hb0.comp (0 : E₂) sumShearEquiv.contDiff.contDiffAt).add
      (hc0.comp (0 : E₂) sumShearEquiv.contDiff.contDiffAt)
  smooth_c := by
    have hc : ContDiffAt ℝ ∞ H.c (sumShearEquiv 0) := by simpa using H.smooth_c
    exact hc.comp (0 : E₂) sumShearEquiv.contDiff.contDiffAt
  exact := by
    intro x
    rw [H.exact]
    simp only [map_zero, sumShearEquiv_apply_zero, sumShearEquiv_apply_one]
    ring


-- @@ L448-450 verbatim
@[simp] lemma sumShearData_a_zero :
    H.sumShearData.a 0 = H.a 0 + 2 * H.b 0 + H.c 0 := by
  simp [sumShearData]


-- @@ L452-455 verbatim
@[simp] lemma sumShearData_det (x : E₂) :
    H.sumShearData.det x = H.det (sumShearEquiv x) := by
  simp [sumShearData, det]
  ring


-- @@ L457-459 verbatim
/-- Triangular linearization of `squareCoord` at the origin. -/
def triangularDeriv (α β γ : ℝ) : E₂ →L[ℝ] E₂ :=
  (α • (proj₀ + β • proj₁)).smulRight e₀ + (γ • proj₁).smulRight e₁


-- @@ L461-464 verbatim
@[simp] lemma triangularDeriv_apply_zero (α β γ : ℝ) (v : E₂) :
    triangularDeriv α β γ v 0 = α * (v 0 + β * v 1) := by
  simp [triangularDeriv, proj₀, proj₁]
  ring


-- @@ L466-468 verbatim
@[simp] lemma triangularDeriv_apply_one (α β γ : ℝ) (v : E₂) :
    triangularDeriv α β γ v 1 = γ * v 1 := by
  simp [triangularDeriv, proj₀, proj₁]


-- @@ L470-501 verbatim
/-- The triangular derivative is bijective exactly when both diagonal entries are
nonzero. -/
theorem triangularDeriv_bijective {α β γ : ℝ} (hα : α ≠ 0) (hγ : γ ≠ 0) :
    Function.Bijective (triangularDeriv α β γ) := by
  constructor
  · intro x y hxy
    apply (WithLp.equiv 2 _).injective
    funext i
    fin_cases i
    · have h0 := congrArg (fun v : E₂ => v 0) hxy
      have h1 := congrArg (fun v : E₂ => v 1) hxy
      simp only [triangularDeriv_apply_zero, triangularDeriv_apply_one] at h0 h1
      have hy1 : x 1 = y 1 := by
        exact mul_left_cancel₀ hγ h1
      rw [hy1] at h0
      have heq := mul_left_cancel₀ hα h0
      exact add_right_cancel heq
    · have h1 := congrArg (fun v : E₂ => v 1) hxy
      simp only [triangularDeriv_apply_one] at h1
      exact mul_left_cancel₀ hγ h1
  · intro y
    let x₁ : ℝ := y 1 / γ
    let x₀ : ℝ := y 0 / α - β * x₁
    let x : E₂ := WithLp.toLp 2 ![x₀, x₁]
    refine ⟨x, ?_⟩
    apply (WithLp.equiv 2 _).injective
    funext i
    fin_cases i
    · simp [x, x₀, x₁, div_eq_mul_inv]
      field_simp
    · simp [x, x₁, div_eq_mul_inv]
      field_simp


-- @@ L503-509 verbatim
/-- The continuous linear equivalence underlying the inverse-function step. -/
def triangularEquiv (α β γ : ℝ) (hα : α ≠ 0) (hγ : γ ≠ 0) :
    E₂ ≃L[ℝ] E₂ :=
  ContinuousLinearEquiv.ofBijective (triangularDeriv α β γ)
    (LinearMap.ker_eq_bot'.mpr fun m hm =>
      (triangularDeriv_bijective (β := β) hα hγ).1 (by simpa using hm))
    (LinearMap.range_eq_top.mpr (triangularDeriv_bijective (β := β) hα hγ).2)


-- @@ L511-513 verbatim
@[simp] lemma triangularEquiv_coe (α β γ : ℝ) (hα : α ≠ 0) (hγ : γ ≠ 0) :
    (triangularEquiv α β γ hα hγ : E₂ →L[ℝ] E₂) =
      triangularDeriv α β γ := rfl


-- @@ L515-528 verbatim
/-- Differential calculation behind the square-completion chart. -/
theorem hasFDerivAt_squareCoord_zero {α β γ : E₂ → ℝ}
    (hα : DifferentiableAt ℝ α 0) (hβ : DifferentiableAt ℝ β 0)
    (hγ : DifferentiableAt ℝ γ 0) :
    HasFDerivAt (squareCoord α β γ) (triangularDeriv (α 0) (β 0) (γ 0)) 0 := by
  have h₀ : HasFDerivAt (fun x : E₂ => x 0) proj₀ 0 := proj₀.hasFDerivAt
  have h₁ : HasFDerivAt (fun x : E₂ => x 1) proj₁ 0 := proj₁.hasFDerivAt
  have hfirst := (hα.hasFDerivAt.mul (h₀.add (hβ.hasFDerivAt.mul h₁))).smul_const e₀
  have hsecond := (hγ.hasFDerivAt.mul h₁).smul_const e₁
  convert hfirst.add hsecond using 1 <;> try rfl
  ext v i
  fin_cases i
  · simp [triangularDeriv, proj₀, proj₁]
  · simp [triangularDeriv, proj₀, proj₁]


-- @@ L530-532 verbatim
def minimumCoord (x : E₂) : E₂ :=
  squareCoord (fun x => Real.sqrt (H.a x)) (fun x => H.b x / H.a x)
    (fun x => Real.sqrt (H.det x / H.a x)) x


-- @@ L534-536 verbatim
def saddleCoord (x : E₂) : E₂ :=
  squareCoord (fun x => Real.sqrt (H.a x)) (fun x => H.b x / H.a x)
    (fun x => Real.sqrt (-(H.det x / H.a x))) x


-- @@ L538-540 verbatim
def maximumCoord (x : E₂) : E₂ :=
  squareCoord (fun x => Real.sqrt (-H.a x)) (fun x => H.b x / H.a x)
    (fun x => Real.sqrt (-(H.det x / H.a x))) x


-- @@ L542-547 verbatim
/-- Saddle chart for a negative first pivot.  Square completion first produces
`(-u₀² + u₁²)`; the final coordinate swap puts this in the convention
`u₀² - u₁²` used by `morseQuadratic .saddle`. -/
def saddleNegativeCoord (x : E₂) : E₂ :=
  swapCLM <| squareCoord (fun x => Real.sqrt (-H.a x)) (fun x => H.b x / H.a x)
    (fun x => Real.sqrt (H.det x / H.a x)) x


-- @@ L549-550 verbatim
lemma contDiffAt_coord_zero : ContDiffAt ℝ ∞ (fun x : E₂ => x 0) 0 :=
  (EuclideanSpace.proj 0 : E₂ →L[ℝ] ℝ).contDiff.contDiffAt


-- @@ L552-553 verbatim
lemma contDiffAt_coord_one : ContDiffAt ℝ ∞ (fun x : E₂ => x 1) 0 :=
  (EuclideanSpace.proj 1 : E₂ →L[ℝ] ℝ).contDiff.contDiffAt


-- @@ L555-566 verbatim
lemma minimumCoord_contDiffAt (ha : 0 < H.a 0) (hd : 0 < H.det 0) :
    ContDiffAt ℝ ∞ H.minimumCoord 0 := by
  have hba : ContDiffAt ℝ ∞ (fun x => H.b x / H.a x) 0 :=
    H.smooth_b.div H.smooth_a ha.ne'
  have hda : ContDiffAt ℝ ∞ (fun x => H.det x / H.a x) 0 :=
    H.smooth_det.div H.smooth_a ha.ne'
  have hdiv : 0 < H.det 0 / H.a 0 := div_pos hd ha
  unfold minimumCoord squareCoord
  exact (((H.smooth_a.sqrt ha.ne').mul
      (contDiffAt_coord_zero.add (hba.mul contDiffAt_coord_one))).smul
        contDiffAt_const).add
    (((hda.sqrt hdiv.ne').mul contDiffAt_coord_one).smul contDiffAt_const)


-- @@ L568-581 verbatim
lemma saddleCoord_contDiffAt (ha : 0 < H.a 0) (hd : H.det 0 < 0) :
    ContDiffAt ℝ ∞ H.saddleCoord 0 := by
  have hba : ContDiffAt ℝ ∞ (fun x => H.b x / H.a x) 0 :=
    H.smooth_b.div H.smooth_a ha.ne'
  have hda : ContDiffAt ℝ ∞ (fun x => -(H.det x / H.a x)) 0 :=
    (H.smooth_det.div H.smooth_a ha.ne').neg
  have hdiv : 0 < -(H.det 0 / H.a 0) := by
    have := div_neg_of_neg_of_pos hd ha
    linarith
  unfold saddleCoord squareCoord
  exact (((H.smooth_a.sqrt ha.ne').mul
      (contDiffAt_coord_zero.add (hba.mul contDiffAt_coord_one))).smul
        contDiffAt_const).add
    (((hda.sqrt hdiv.ne').mul contDiffAt_coord_one).smul contDiffAt_const)


-- @@ L583-597 verbatim
lemma maximumCoord_contDiffAt (ha : H.a 0 < 0) (hd : 0 < H.det 0) :
    ContDiffAt ℝ ∞ H.maximumCoord 0 := by
  have hba : ContDiffAt ℝ ∞ (fun x => H.b x / H.a x) 0 :=
    H.smooth_b.div H.smooth_a ha.ne
  have hna : ContDiffAt ℝ ∞ (fun x => -H.a x) 0 := H.smooth_a.neg
  have hda : ContDiffAt ℝ ∞ (fun x => -(H.det x / H.a x)) 0 :=
    (H.smooth_det.div H.smooth_a ha.ne).neg
  have hdiv : 0 < -(H.det 0 / H.a 0) := by
    have := div_neg_of_pos_of_neg hd ha
    linarith
  unfold maximumCoord squareCoord
  exact (((hna.sqrt (by linarith : -H.a 0 ≠ 0)).mul
      (contDiffAt_coord_zero.add (hba.mul contDiffAt_coord_one))).smul
        contDiffAt_const).add
    (((hda.sqrt hdiv.ne').mul contDiffAt_coord_one).smul contDiffAt_const)


-- @@ L599-616 verbatim
lemma saddleNegativeCoord_contDiffAt (ha : H.a 0 < 0) (hd : H.det 0 < 0) :
    ContDiffAt ℝ ∞ H.saddleNegativeCoord 0 := by
  have hba : ContDiffAt ℝ ∞ (fun x => H.b x / H.a x) 0 :=
    H.smooth_b.div H.smooth_a ha.ne
  have hna : ContDiffAt ℝ ∞ (fun x => -H.a x) 0 := H.smooth_a.neg
  have hda : ContDiffAt ℝ ∞ (fun x => H.det x / H.a x) 0 :=
    H.smooth_det.div H.smooth_a ha.ne
  have hdiv : 0 < H.det 0 / H.a 0 := div_pos_of_neg_of_neg hd ha
  have hsquare : ContDiffAt ℝ ∞
      (squareCoord (fun x => Real.sqrt (-H.a x)) (fun x => H.b x / H.a x)
        (fun x => Real.sqrt (H.det x / H.a x))) 0 := by
    unfold squareCoord
    exact (((hna.sqrt (by linarith : -H.a 0 ≠ 0)).mul
        (contDiffAt_coord_zero.add (hba.mul contDiffAt_coord_one))).smul
          contDiffAt_const).add
      (((hda.sqrt hdiv.ne').mul contDiffAt_coord_one).smul contDiffAt_const)
  unfold saddleNegativeCoord
  exact swapCLM.contDiff.contDiffAt.comp (0 : E₂) hsquare


-- @@ L618-627 verbatim
theorem minimumCoord_hasFDerivAt (ha : 0 < H.a 0) (hd : 0 < H.det 0) :
    HasFDerivAt H.minimumCoord
      (triangularDeriv (Real.sqrt (H.a 0)) (H.b 0 / H.a 0)
        (Real.sqrt (H.det 0 / H.a 0))) 0 := by
  unfold minimumCoord
  apply hasFDerivAt_squareCoord_zero
  · exact (H.smooth_a.sqrt ha.ne').differentiableAt (by simp)
  · exact (H.smooth_b.div H.smooth_a ha.ne').differentiableAt (by simp)
  · have hdiv : 0 < H.det 0 / H.a 0 := div_pos hd ha
    exact ((H.smooth_det.div H.smooth_a ha.ne').sqrt hdiv.ne').differentiableAt (by simp)


-- @@ L629-641 verbatim
theorem saddleCoord_hasFDerivAt (ha : 0 < H.a 0) (hd : H.det 0 < 0) :
    HasFDerivAt H.saddleCoord
      (triangularDeriv (Real.sqrt (H.a 0)) (H.b 0 / H.a 0)
        (Real.sqrt (-(H.det 0 / H.a 0)))) 0 := by
  unfold saddleCoord
  apply hasFDerivAt_squareCoord_zero
  · exact (H.smooth_a.sqrt ha.ne').differentiableAt (by simp)
  · exact (H.smooth_b.div H.smooth_a ha.ne').differentiableAt (by simp)
  · have hdiv : 0 < -(H.det 0 / H.a 0) := by
      have := div_neg_of_neg_of_pos hd ha
      linarith
    exact (((H.smooth_det.div H.smooth_a ha.ne').neg).sqrt hdiv.ne').differentiableAt
      (by simp)


-- @@ L643-655 verbatim
theorem maximumCoord_hasFDerivAt (ha : H.a 0 < 0) (hd : 0 < H.det 0) :
    HasFDerivAt H.maximumCoord
      (triangularDeriv (Real.sqrt (-H.a 0)) (H.b 0 / H.a 0)
        (Real.sqrt (-(H.det 0 / H.a 0)))) 0 := by
  unfold maximumCoord
  apply hasFDerivAt_squareCoord_zero
  · exact (H.smooth_a.neg.sqrt (by linarith : -H.a 0 ≠ 0)).differentiableAt (by simp)
  · exact (H.smooth_b.div H.smooth_a ha.ne).differentiableAt (by simp)
  · have hdiv : 0 < -(H.det 0 / H.a 0) := by
      have := div_neg_of_pos_of_neg hd ha
      linarith
    exact (((H.smooth_det.div H.smooth_a ha.ne).neg).sqrt hdiv.ne').differentiableAt
      (by simp)


-- @@ L657-667 verbatim
theorem saddleNegativeCoord_hasFDerivAt (ha : H.a 0 < 0) (hd : H.det 0 < 0) :
    HasFDerivAt H.saddleNegativeCoord
      (swapCLM.comp <| triangularDeriv (Real.sqrt (-H.a 0)) (H.b 0 / H.a 0)
        (Real.sqrt (H.det 0 / H.a 0))) 0 := by
  unfold saddleNegativeCoord
  apply swapCLM.hasFDerivAt.comp (0 : E₂)
  apply hasFDerivAt_squareCoord_zero
  · exact (H.smooth_a.neg.sqrt (by linarith : -H.a 0 ≠ 0)).differentiableAt (by simp)
  · exact (H.smooth_b.div H.smooth_a ha.ne).differentiableAt (by simp)
  · have hdiv : 0 < H.det 0 / H.a 0 := div_pos_of_neg_of_neg hd ha
    exact ((H.smooth_det.div H.smooth_a ha.ne).sqrt hdiv.ne').differentiableAt (by simp)


-- @@ L669-675 verbatim
theorem exact_minimum {x : E₂} (ha : 0 < H.a x) (hd : 0 < H.det x) :
    f x = f 0 + morseQuadratic .minimum (H.minimumCoord x 0, H.minimumCoord x 1) := by
  rw [H.exact, morseQuadratic, minimumCoord, squareCoord_apply_zero,
    squareCoord_apply_one, H.completeSquare ha.ne']
  rw [mul_pow, Real.sq_sqrt ha.le]
  have hdiv : 0 ≤ H.det x / H.a x := div_nonneg hd.le ha.le
  rw [mul_pow, Real.sq_sqrt hdiv]


-- @@ L677-686 verbatim
theorem exact_saddle {x : E₂} (ha : 0 < H.a x) (hd : H.det x < 0) :
    f x = f 0 + morseQuadratic .saddle (H.saddleCoord x 0, H.saddleCoord x 1) := by
  rw [H.exact, morseQuadratic, saddleCoord, squareCoord_apply_zero,
    squareCoord_apply_one, H.completeSquare ha.ne']
  rw [mul_pow, Real.sq_sqrt ha.le]
  have hdiv : 0 ≤ -(H.det x / H.a x) := by
    have : H.det x / H.a x < 0 := div_neg_of_neg_of_pos hd ha
    linarith
  rw [mul_pow, Real.sq_sqrt hdiv]
  ring


-- @@ L688-698 verbatim
theorem exact_maximum {x : E₂} (ha : H.a x < 0) (hd : 0 < H.det x) :
    f x = f 0 + morseQuadratic .maximum (H.maximumCoord x 0, H.maximumCoord x 1) := by
  rw [H.exact, morseQuadratic, maximumCoord, squareCoord_apply_zero,
    squareCoord_apply_one, H.completeSquare ha.ne]
  have hna : 0 ≤ -H.a x := by linarith
  rw [mul_pow, Real.sq_sqrt hna]
  have hdiv : 0 ≤ -(H.det x / H.a x) := by
    have : H.det x / H.a x < 0 := div_neg_of_pos_of_neg hd ha
    linarith
  rw [mul_pow, Real.sq_sqrt hdiv]
  ring


-- @@ L700-711 verbatim
theorem exact_saddleNegative {x : E₂} (ha : H.a x < 0) (hd : H.det x < 0) :
    f x = f 0 + morseQuadratic .saddle
      (H.saddleNegativeCoord x 0, H.saddleNegativeCoord x 1) := by
  rw [H.exact, morseQuadratic, saddleNegativeCoord, swapCLM_apply_zero,
    swapCLM_apply_one, squareCoord_apply_zero, squareCoord_apply_one,
    H.completeSquare ha.ne]
  simp only
  have hna : 0 ≤ -H.a x := by linarith
  have hdiv : 0 ≤ H.det x / H.a x := (div_pos_of_neg_of_neg hd ha).le
  simp_rw [mul_pow]
  rw [Real.sq_sqrt hna, Real.sq_sqrt hdiv]
  ring


-- @@ L713-721 verbatim
lemma eventually_exact_minimum (ha : 0 < H.a 0) (hd : 0 < H.det 0) :
    ∀ᶠ x in nhds 0,
      f x = f 0 + morseQuadratic .minimum (H.minimumCoord x 0, H.minimumCoord x 1) := by
  have haev : ∀ᶠ x in nhds 0, 0 < H.a x :=
    H.smooth_a.continuousAt.eventually (Ioi_mem_nhds ha)
  have hdev : ∀ᶠ x in nhds 0, 0 < H.det x :=
    H.smooth_det.continuousAt.eventually (Ioi_mem_nhds hd)
  filter_upwards [haev, hdev] with x hax hdx
  exact H.exact_minimum hax hdx


-- @@ L723-731 verbatim
lemma eventually_exact_saddle (ha : 0 < H.a 0) (hd : H.det 0 < 0) :
    ∀ᶠ x in nhds 0,
      f x = f 0 + morseQuadratic .saddle (H.saddleCoord x 0, H.saddleCoord x 1) := by
  have haev : ∀ᶠ x in nhds 0, 0 < H.a x :=
    H.smooth_a.continuousAt.eventually (Ioi_mem_nhds ha)
  have hdev : ∀ᶠ x in nhds 0, H.det x < 0 :=
    H.smooth_det.continuousAt.eventually (Iio_mem_nhds hd)
  filter_upwards [haev, hdev] with x hax hdx
  exact H.exact_saddle hax hdx


-- @@ L733-741 verbatim
lemma eventually_exact_maximum (ha : H.a 0 < 0) (hd : 0 < H.det 0) :
    ∀ᶠ x in nhds 0,
      f x = f 0 + morseQuadratic .maximum (H.maximumCoord x 0, H.maximumCoord x 1) := by
  have haev : ∀ᶠ x in nhds 0, H.a x < 0 :=
    H.smooth_a.continuousAt.eventually (Iio_mem_nhds ha)
  have hdev : ∀ᶠ x in nhds 0, 0 < H.det x :=
    H.smooth_det.continuousAt.eventually (Ioi_mem_nhds hd)
  filter_upwards [haev, hdev] with x hax hdx
  exact H.exact_maximum hax hdx


-- @@ L743-752 verbatim
lemma eventually_exact_saddleNegative (ha : H.a 0 < 0) (hd : H.det 0 < 0) :
    ∀ᶠ x in nhds 0,
      f x = f 0 + morseQuadratic .saddle
        (H.saddleNegativeCoord x 0, H.saddleNegativeCoord x 1) := by
  have haev : ∀ᶠ x in nhds 0, H.a x < 0 :=
    H.smooth_a.continuousAt.eventually (Iio_mem_nhds ha)
  have hdev : ∀ᶠ x in nhds 0, H.det x < 0 :=
    H.smooth_det.continuousAt.eventually (Iio_mem_nhds hd)
  filter_upwards [haev, hdev] with x hax hdx
  exact H.exact_saddleNegative hax hdx


-- @@ L754-754 verbatim
end HadamardQuadraticData


-- @@ L756-756 verbatim
/-! ## Local inverse and exact Morse normal form -/


-- @@ L758-769 verbatim
/-- The precise input to the inverse-function step.  The preceding square-completion
lemmas construct `coord`; the remaining derivative field says its triangular
linearization is invertible. -/
structure LocalMorseCoordinateInput (f : E₂ → ℝ) where
  index : MorseIndexTwo
  coord : E₂ → E₂
  coord_zero : coord 0 = 0
  coord_smooth : ContDiffAt ℝ ∞ coord 0
  coordDeriv : E₂ ≃L[ℝ] E₂
  coord_hasFDerivAt : HasFDerivAt coord (coordDeriv : E₂ →L[ℝ] E₂) 0
  model_eventually : ∀ᶠ x in nhds 0,
    f x = f 0 + morseQuadratic index (coord x 0, coord x 1)


-- @@ L771-771 verbatim
namespace HadamardQuadraticData


-- @@ L773-773 verbatim
variable {f : E₂ → ℝ} (H : HadamardQuadraticData f)


-- @@ L775-786 verbatim
/-- Minimum square completion promoted to inverse-function input. -/
def minimumInput (ha : 0 < H.a 0) (hd : 0 < H.det 0)
    (D : E₂ ≃L[ℝ] E₂)
    (hD : HasFDerivAt H.minimumCoord (D : E₂ →L[ℝ] E₂) 0) :
    LocalMorseCoordinateInput f where
  index := .minimum
  coord := H.minimumCoord
  coord_zero := by simp [minimumCoord]
  coord_smooth := H.minimumCoord_contDiffAt ha hd
  coordDeriv := D
  coord_hasFDerivAt := hD
  model_eventually := H.eventually_exact_minimum ha hd


-- @@ L788-799 verbatim
/-- Saddle square completion promoted to inverse-function input. -/
def saddleInput (ha : 0 < H.a 0) (hd : H.det 0 < 0)
    (D : E₂ ≃L[ℝ] E₂)
    (hD : HasFDerivAt H.saddleCoord (D : E₂ →L[ℝ] E₂) 0) :
    LocalMorseCoordinateInput f where
  index := .saddle
  coord := H.saddleCoord
  coord_zero := by simp [saddleCoord]
  coord_smooth := H.saddleCoord_contDiffAt ha hd
  coordDeriv := D
  coord_hasFDerivAt := hD
  model_eventually := H.eventually_exact_saddle ha hd


-- @@ L801-812 verbatim
/-- Maximum square completion promoted to inverse-function input. -/
def maximumInput (ha : H.a 0 < 0) (hd : 0 < H.det 0)
    (D : E₂ ≃L[ℝ] E₂)
    (hD : HasFDerivAt H.maximumCoord (D : E₂ →L[ℝ] E₂) 0) :
    LocalMorseCoordinateInput f where
  index := .maximum
  coord := H.maximumCoord
  coord_zero := by simp [maximumCoord]
  coord_smooth := H.maximumCoord_contDiffAt ha hd
  coordDeriv := D
  coord_hasFDerivAt := hD
  model_eventually := H.eventually_exact_maximum ha hd


-- @@ L814-825 verbatim
/-- Negative-pivot saddle square completion promoted to inverse-function input. -/
def saddleNegativeInput (ha : H.a 0 < 0) (hd : H.det 0 < 0)
    (D : E₂ ≃L[ℝ] E₂)
    (hD : HasFDerivAt H.saddleNegativeCoord (D : E₂ →L[ℝ] E₂) 0) :
    LocalMorseCoordinateInput f where
  index := .saddle
  coord := H.saddleNegativeCoord
  coord_zero := by simp [saddleNegativeCoord]
  coord_smooth := H.saddleNegativeCoord_contDiffAt ha hd
  coordDeriv := D
  coord_hasFDerivAt := hD
  model_eventually := H.eventually_exact_saddleNegative ha hd


-- @@ L827-837 verbatim
/-- Fully automatic minimum input: square roots give nonzero diagonal entries, so
the triangular differential is promoted to a continuous linear equivalence. -/
def minimumInputAuto (ha : 0 < H.a 0) (hd : 0 < H.det 0) :
    LocalMorseCoordinateInput f := by
  let α := Real.sqrt (H.a 0)
  let β := H.b 0 / H.a 0
  let γ := Real.sqrt (H.det 0 / H.a 0)
  have hα : α ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  have hγ : γ ≠ 0 := (Real.sqrt_pos.mpr (div_pos hd ha)).ne'
  exact H.minimumInput ha hd (triangularEquiv α β γ hα hγ) (by
    simpa [α, β, γ] using H.minimumCoord_hasFDerivAt ha hd)


-- @@ L839-850 verbatim
def saddleInputAuto (ha : 0 < H.a 0) (hd : H.det 0 < 0) :
    LocalMorseCoordinateInput f := by
  let α := Real.sqrt (H.a 0)
  let β := H.b 0 / H.a 0
  let γ := Real.sqrt (-(H.det 0 / H.a 0))
  have hdiv : 0 < -(H.det 0 / H.a 0) := by
    have := div_neg_of_neg_of_pos hd ha
    linarith
  have hα : α ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  have hγ : γ ≠ 0 := (Real.sqrt_pos.mpr hdiv).ne'
  exact H.saddleInput ha hd (triangularEquiv α β γ hα hγ) (by
    simpa [α, β, γ] using H.saddleCoord_hasFDerivAt ha hd)


-- @@ L852-863 verbatim
def maximumInputAuto (ha : H.a 0 < 0) (hd : 0 < H.det 0) :
    LocalMorseCoordinateInput f := by
  let α := Real.sqrt (-H.a 0)
  let β := H.b 0 / H.a 0
  let γ := Real.sqrt (-(H.det 0 / H.a 0))
  have hdiv : 0 < -(H.det 0 / H.a 0) := by
    have := div_neg_of_pos_of_neg hd ha
    linarith
  have hα : α ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  have hγ : γ ≠ 0 := (Real.sqrt_pos.mpr hdiv).ne'
  exact H.maximumInput ha hd (triangularEquiv α β γ hα hγ) (by
    simpa [α, β, γ] using H.maximumCoord_hasFDerivAt ha hd)


-- @@ L865-881 verbatim
/-- Fully automatic saddle input when the first square-completion pivot is
negative.  The final continuous-linear equivalence incorporates coordinate
swap, so the inverse-function theorem sees the exact derivative. -/
def saddleNegativeInputAuto (ha : H.a 0 < 0) (hd : H.det 0 < 0) :
    LocalMorseCoordinateInput f := by
  let α := Real.sqrt (-H.a 0)
  let β := H.b 0 / H.a 0
  let γ := Real.sqrt (H.det 0 / H.a 0)
  have hdiv : 0 < H.det 0 / H.a 0 := div_pos_of_neg_of_neg hd ha
  have hα : α ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  have hγ : γ ≠ 0 := (Real.sqrt_pos.mpr hdiv).ne'
  let D : E₂ ≃L[ℝ] E₂ := (triangularEquiv α β γ hα hγ).trans swapEquiv
  refine H.saddleNegativeInput ha hd D ?_
  change HasFDerivAt H.saddleNegativeCoord
    (swapCLM.comp <| triangularDeriv (Real.sqrt (-H.a 0)) (H.b 0 / H.a 0)
      (Real.sqrt (H.det 0 / H.a 0))) 0
  exact H.saddleNegativeCoord_hasFDerivAt ha hd


-- @@ L883-885 verbatim
@[simp] lemma minimumInputAuto_index (ha : 0 < H.a 0) (hd : 0 < H.det 0) :
    (H.minimumInputAuto ha hd).index = .minimum := by
  rfl


-- @@ L887-889 verbatim
@[simp] lemma saddleInputAuto_index (ha : 0 < H.a 0) (hd : H.det 0 < 0) :
    (H.saddleInputAuto ha hd).index = .saddle := by
  rfl


-- @@ L891-893 verbatim
@[simp] lemma maximumInputAuto_index (ha : H.a 0 < 0) (hd : 0 < H.det 0) :
    (H.maximumInputAuto ha hd).index = .maximum := by
  rfl


-- @@ L895-897 verbatim
@[simp] lemma saddleNegativeInputAuto_index (ha : H.a 0 < 0) (hd : H.det 0 < 0) :
    (H.saddleNegativeInputAuto ha hd).index = .saddle := by
  rfl


-- @@ L899-899 verbatim
end HadamardQuadraticData


-- @@ L901-901 verbatim
namespace LocalMorseCoordinateInput


-- @@ L903-903 verbatim
variable {f : E₂ → ℝ} (I : LocalMorseCoordinateInput f)


-- @@ L905-908 verbatim
/-- Strict derivative used by the inverse function theorem. -/
theorem strictDeriv : HasStrictFDerivAt I.coord
    (I.coordDeriv : E₂ →L[ℝ] E₂) 0 :=
  I.coord_smooth.hasStrictFDerivAt' I.coord_hasFDerivAt (by simp)


-- @@ L910-912 verbatim
/-- The inverse-function-theorem parametrization. -/
def param : E₂ → E₂ :=
  I.strictDeriv.localInverse I.coord I.coordDeriv 0


-- @@ L914-916 verbatim
lemma param_zero : I.param 0 = 0 := by
  have h := I.strictDeriv.localInverse_apply_image
  simpa [param, I.coord_zero] using h


-- @@ L918-920 verbatim
lemma param_contDiffAt : ContDiffAt ℝ ∞ I.param 0 := by
  have h := I.coord_smooth.to_localInverse I.coord_hasFDerivAt (by simp)
  simpa [param, strictDeriv, ContDiffAt.localInverse, I.coord_zero] using h


-- @@ L922-924 verbatim
lemma param_tendsto : Tendsto I.param (nhds 0) (nhds 0) := by
  have h := I.strictDeriv.localInverse_tendsto
  simpa [param, I.coord_zero] using h


-- @@ L926-928 verbatim
lemma eventually_coord_param : ∀ᶠ u in nhds 0, I.coord (I.param u) = u := by
  have h := I.strictDeriv.eventually_right_inverse
  simpa [param, I.coord_zero] using h


-- @@ L930-938 verbatim
/-- Pulling back by the local inverse makes the Morse model literally exact. -/
theorem eventually_exact_param : ∀ᶠ u in nhds 0,
    f (I.param u) = f 0 + morseQuadratic I.index (u 0, u 1) := by
  have hmodel : ∀ᶠ u in nhds 0,
      f (I.param u) = f 0 +
        morseQuadratic I.index (I.coord (I.param u) 0, I.coord (I.param u) 1) :=
    I.param_tendsto.eventually I.model_eventually
  filter_upwards [hmodel, I.eventually_coord_param] with u hu hcoord
  simpa [hcoord] using hu


-- @@ L940-951 verbatim
/-- Radius form consumed by `StandardMorseEventAt.time_model`. -/
theorem exists_radius_exact_param : ∃ r > 0, ∀ u : E₂, ‖u‖ < r →
    f (I.param u) = f 0 + morseQuadratic I.index (u 0, u 1) := by
  have hmem : {u : E₂ | f (I.param u) =
      f 0 + morseQuadratic I.index (u 0, u 1)} ∈ nhds 0 :=
    I.eventually_exact_param
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hmem
  refine ⟨r, hr, ?_⟩
  intro u hu
  apply hball
  rw [mem_ball, dist_zero_right]
  exact hu


-- @@ L953-953 verbatim
end LocalMorseCoordinateInput


-- @@ L955-955 verbatim
/-! ## A compact output package -/


-- @@ L957-968 verbatim
/-- Scalar local Morse normal form, in the exact shape needed for the time-model
field of a standard event chart.  Smoothness is stated locally, as supplied by the
inverse function theorem; an ambient cutoff extension can later globalize `param`. -/
structure LocalMorseNormalForm (f : E₂ → ℝ) where
  index : MorseIndexTwo
  radius : ℝ
  radius_pos : 0 < radius
  param : E₂ → E₂
  param_zero : param 0 = 0
  param_contDiffAt : ContDiffAt ℝ ∞ param 0
  exact : ∀ u, ‖u‖ < radius →
    f (param u) = f 0 + morseQuadratic index (u 0, u 1)


-- @@ L970-970 verbatim
namespace LocalMorseNormalForm


-- @@ L972-972 verbatim
variable {f : E₂ → ℝ} (M : LocalMorseNormalForm f)


-- @@ L974-976 verbatim
/-- Compose the local inverse coordinates with a pre-existing surface chart. -/
def liftParam {A : Type*} (surface : E₂ → A) (u : E₂) : A :=
  surface (M.param u)


-- @@ L978-980 verbatim
@[simp] lemma liftParam_zero {A : Type*} (surface : E₂ → A) :
    M.liftParam surface 0 = surface 0 := by
  simp [liftParam, M.param_zero]


-- @@ L982-990 verbatim
/-- This is the direct bridge to `StandardMorseEventAt.time_model`: once `surface`
parametrizes the cobordism and `τ` is its time coordinate, the composed ambient
parametrization has the literal standard quadratic time function. -/
theorem liftParam_time_model {A : Type*} (surface : E₂ → A) (τ : A → ℝ)
    (hscalar : ∀ x, f x = τ (surface x)) (u : E₂) (hu : ‖u‖ < M.radius) :
    τ (M.liftParam surface u) =
      τ (surface 0) + morseQuadratic M.index (u 0, u 1) := by
  rw [← hscalar, liftParam, ← hscalar]
  exact M.exact u hu


-- @@ L992-998 verbatim
lemma liftParam_contDiffAt {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {surface : E₂ → A} (hsurface : ContDiffAt ℝ ∞ surface 0) :
    ContDiffAt ℝ ∞ (M.liftParam surface) 0 := by
  change ContDiffAt ℝ ∞ (fun u : E₂ => surface (M.param u)) 0
  have hs : ContDiffAt ℝ ∞ surface (M.param 0) := by
    simpa [M.param_zero] using hsurface
  exact hs.comp (0 : E₂) M.param_contDiffAt


-- @@ L1000-1012 verbatim
/-- Transport a normal form for `f ∘ L` back to one for `f`.  This is the
coordinate-invariance step used below to select a nonzero quadratic pivot. -/
def pushLinear (L : E₂ ≃L[ℝ] E₂)
    (M : LocalMorseNormalForm (fun x => f (L x))) : LocalMorseNormalForm f where
  index := M.index
  radius := M.radius
  radius_pos := M.radius_pos
  param := fun u => L (M.param u)
  param_zero := by simp [M.param_zero]
  param_contDiffAt := L.contDiff.contDiffAt.comp (0 : E₂) M.param_contDiffAt
  exact := by
    intro u hu
    simpa using M.exact u hu


-- @@ L1014-1016 verbatim
@[simp] lemma pushLinear_index (L : E₂ ≃L[ℝ] E₂)
    (M : LocalMorseNormalForm (fun x => f (L x))) :
    (pushLinear L M).index = M.index := rfl


-- @@ L1018-1018 verbatim
end LocalMorseNormalForm


-- @@ L1020-1032 verbatim
/-- The completed-square coordinate data produces an actual local Morse normal
form by the inverse function theorem. -/
theorem LocalMorseCoordinateInput.exists_normalForm {f : E₂ → ℝ}
    (I : LocalMorseCoordinateInput f) : Nonempty (LocalMorseNormalForm f) := by
  obtain ⟨r, hr, hexact⟩ := I.exists_radius_exact_param
  exact ⟨{
    index := I.index
    radius := r
    radius_pos := hr
    param := I.param
    param_zero := I.param_zero
    param_contDiffAt := I.param_contDiffAt
    exact := hexact }⟩


-- @@ L1034-1045 verbatim
theorem LocalMorseCoordinateInput.exists_normalForm_with_index {f : E₂ → ℝ}
    (I : LocalMorseCoordinateInput f) :
    ∃ M : LocalMorseNormalForm f, M.index = I.index := by
  obtain ⟨r, hr, hexact⟩ := I.exists_radius_exact_param
  refine ⟨{
    index := I.index
    radius := r
    radius_pos := hr
    param := I.param
    param_zero := I.param_zero
    param_contDiffAt := I.param_contDiffAt
    exact := hexact }, rfl⟩


-- @@ L1047-1047 verbatim
namespace HadamardQuadraticData


-- @@ L1049-1049 verbatim
variable {f : E₂ → ℝ} (H : HadamardQuadraticData f)


-- @@ L1051-1055 verbatim
/-- Constructive two-dimensional Morse lemma, positive-definite pivot case. -/
theorem exists_minimum_normalForm (ha : 0 < H.a 0) (hd : 0 < H.det 0) :
    ∃ M : LocalMorseNormalForm f, M.index = .minimum := by
  obtain ⟨M, hM⟩ := (H.minimumInputAuto ha hd).exists_normalForm_with_index
  exact ⟨M, hM.trans (H.minimumInputAuto_index ha hd)⟩


-- @@ L1057-1061 verbatim
/-- Constructive two-dimensional Morse lemma, indefinite case. -/
theorem exists_saddle_normalForm (ha : 0 < H.a 0) (hd : H.det 0 < 0) :
    ∃ M : LocalMorseNormalForm f, M.index = .saddle := by
  obtain ⟨M, hM⟩ := (H.saddleInputAuto ha hd).exists_normalForm_with_index
  exact ⟨M, hM.trans (H.saddleInputAuto_index ha hd)⟩


-- @@ L1063-1069 verbatim
/-- Constructive two-dimensional Morse lemma for an indefinite Hessian with a
negative first pivot.  Coordinate swap converts the completed square to the
same saddle convention as the positive-pivot theorem. -/
theorem exists_saddle_negative_normalForm (ha : H.a 0 < 0) (hd : H.det 0 < 0) :
    ∃ M : LocalMorseNormalForm f, M.index = .saddle := by
  obtain ⟨M, hM⟩ := (H.saddleNegativeInputAuto ha hd).exists_normalForm_with_index
  exact ⟨M, hM.trans (H.saddleNegativeInputAuto_index ha hd)⟩


-- @@ L1071-1075 verbatim
/-- Constructive two-dimensional Morse lemma, negative-definite pivot case. -/
theorem exists_maximum_normalForm (ha : H.a 0 < 0) (hd : 0 < H.det 0) :
    ∃ M : LocalMorseNormalForm f, M.index = .maximum := by
  obtain ⟨M, hM⟩ := (H.maximumInputAuto ha hd).exists_normalForm_with_index
  exact ⟨M, hM.trans (H.maximumInputAuto_index ha hd)⟩


-- @@ L1077-1090 verbatim
/-- A nonzero first pivot and nonzero determinant suffice for some exact local
Morse normal form; signs select the corresponding constructive chart. -/
theorem exists_normalForm_of_firstPivot (ha : H.a 0 ≠ 0) (hd : H.det 0 ≠ 0) :
    Nonempty (LocalMorseNormalForm f) := by
  rcases lt_or_gt_of_ne ha with ha | ha <;>
    rcases lt_or_gt_of_ne hd with hd | hd
  · obtain ⟨M, _⟩ := H.exists_saddle_negative_normalForm ha hd
    exact ⟨M⟩
  · obtain ⟨M, _⟩ := H.exists_maximum_normalForm ha hd
    exact ⟨M⟩
  · obtain ⟨M, _⟩ := H.exists_saddle_normalForm ha hd
    exact ⟨M⟩
  · obtain ⟨M, _⟩ := H.exists_minimum_normalForm ha hd
    exact ⟨M⟩


-- @@ L1092-1099 verbatim
/-- In the negative-determinant case the constructed normal form has Morse
index one, independently of the sign of the selected pivot. -/
theorem exists_saddle_normalForm_of_firstPivot (ha : H.a 0 ≠ 0)
    (hd : H.det 0 < 0) :
    ∃ M : LocalMorseNormalForm f, M.index = .saddle := by
  rcases lt_or_gt_of_ne ha with ha | ha
  · exact H.exists_saddle_negative_normalForm ha hd
  · exact H.exists_saddle_normalForm ha hd


-- @@ L1101-1118 verbatim
/-- Full constructive two-dimensional local Morse lemma.  Nondegeneracy alone
is enough: coordinate swap handles a nonzero second diagonal coefficient, and
the fixed sum shear handles the remaining off-diagonal form. -/
theorem morseLemma2D_of_nondegenerate (hnd : H.IsNondegenerate) :
    Nonempty (LocalMorseNormalForm f) := by
  have hdet : H.det 0 ≠ 0 := hnd
  rcases H.exists_nonzero_pivot_candidate hnd with ha | hc | hs
  · exact H.exists_normalForm_of_firstPivot ha hdet
  · let K := H.swapData
    have hKa : K.a 0 ≠ 0 := by simpa [K] using hc
    have hKd : K.det 0 ≠ 0 := by simpa [K] using hdet
    obtain ⟨M⟩ := K.exists_normalForm_of_firstPivot hKa hKd
    exact ⟨LocalMorseNormalForm.pushLinear swapEquiv M⟩
  · let K := H.sumShearData
    have hKa : K.a 0 ≠ 0 := by simpa [K] using hs
    have hKd : K.det 0 ≠ 0 := by simpa [K] using hdet
    obtain ⟨M⟩ := K.exists_normalForm_of_firstPivot hKa hKd
    exact ⟨LocalMorseNormalForm.pushLinear sumShearEquiv M⟩


-- @@ L1120-1136 verbatim
/-- Full saddle specialization, retaining the exact index statement after
pivot selection and transport. -/
theorem morseLemma2D_saddle (hd : H.det 0 < 0) :
    ∃ M : LocalMorseNormalForm f, M.index = .saddle := by
  have hnd : H.IsNondegenerate := hd.ne
  rcases H.exists_nonzero_pivot_candidate hnd with ha | hc | hs
  · exact H.exists_saddle_normalForm_of_firstPivot ha hd
  · let K := H.swapData
    have hKa : K.a 0 ≠ 0 := by simpa [K] using hc
    have hKd : K.det 0 < 0 := by simpa [K] using hd
    obtain ⟨M, hM⟩ := K.exists_saddle_normalForm_of_firstPivot hKa hKd
    exact ⟨LocalMorseNormalForm.pushLinear swapEquiv M, by simpa using hM⟩
  · let K := H.sumShearData
    have hKa : K.a 0 ≠ 0 := by simpa [K] using hs
    have hKd : K.det 0 < 0 := by simpa [K] using hd
    obtain ⟨M, hM⟩ := K.exists_saddle_normalForm_of_firstPivot hKa hKd
    exact ⟨LocalMorseNormalForm.pushLinear sumShearEquiv M, by simpa using hM⟩


-- @@ L1138-1152 verbatim
/-- End-to-end local Morse lemma from the explicit integrated Hessian
coefficients.  This theorem exposes only the analytic smoothness of the three
parameter integrals and the standard nonzero determinant condition; all
square-completion and inverse-function steps are discharged internally. -/
theorem morseLemma2D_integrated {g : E₂ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hcrit : fderiv ℝ g 0 = 0)
    (hA : ContDiffAt ℝ ∞ (integratedHadamardA g) 0)
    (hB : ContDiffAt ℝ ∞ (integratedHadamardB g) 0)
    (hC : ContDiffAt ℝ ∞ (integratedHadamardC g) 0)
    (hdet : integratedHadamardDet g ≠ 0) :
    Nonempty (LocalMorseNormalForm g) := by
  let K := integratedHadamardData hg hcrit hA hB hC
  have hKdet : K.det 0 ≠ 0 := by
    simpa [K, integratedHadamardData, det, integratedHadamardDet] using hdet
  exact K.morseLemma2D_of_nondegenerate hKdet


-- @@ L1154-1154 verbatim
end HadamardQuadraticData


-- @@ L1156-1156 verbatim
end Submission
