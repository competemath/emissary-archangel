import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeFiniteResolventWords
import NLAlib.ForMathlib.Algebra.ResolventHom
import NLAlib.ForMathlib.MeasureTheory.ProductSelection
import NLAlib.Matrix.Norms.TraceSpectral
import Mathlib.Algebra.Algebra.Spectrum.Pi


-- @@ L7-15 verbatim
/-! # The actual original Gaussian endpoint of the finite-N interpolation

At q=1 the genuine finite-N random matrix is block diagonal with copies of
the original affine Gaussian matrix series. Selecting each copy's true
coordinates preserves the canonical product Gaussian law. Consequently its
actual expected normalized resolvent words equal those of the original
matrix, without a moment-matching assumption.
Source: arXiv:2108.06312v2, Section 5.1, equation (5.1).
-/


-- @@ L17-17 verbatim
noncomputable section

-- @@ L18-18 verbatim
set_option autoImplicit false

-- @@ L19-19 verbatim
set_option backward.isDefEq.respectTransparency false

-- @@ L20-20 verbatim
open MeasureTheory ProbabilityTheory

-- @@ L21-21 verbatim
open scoped Matrix Kronecker

-- @@ L22-22 verbatim
namespace NLAlib

-- @@ L23-24 verbatim
variable {ι n d : Type*} [Fintype ι] [Fintype n] [Fintype d]
  [DecidableEq ι] [DecidableEq n] [DecidableEq d]

-- @@ L25-25 verbatim
local notation "E" => GaussianFreeFiniteCoordinate ι n → ℝ

-- @@ L26-26 verbatim
local notation "D" => Matrix d d ℂ

-- @@ L27-27 verbatim
local notation "M" => Matrix (d × n) (d × n) ℂ


-- @@ L29-35 verbatim
private def blockDiagonalAlgHom : (n → D) →ₐ[ℂ] M :=
  { Matrix.blockDiagonalRingHom d n ℂ with
    commutes' := by
      intro c
      change Matrix.blockDiagonal (algebraMap ℂ (n → D) c) = algebraMap ℂ M c
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
      rw [Matrix.blockDiagonal_smul, Matrix.blockDiagonal_one] }


-- @@ L37-50 verbatim
private theorem blockDiagonal_resolvent (T : n → D) (ζ : ℂ)
    (hζ : ∀ a, ζ ∈ resolventSet ℂ (T a)) :
    resolvent (Matrix.blockDiagonal T) ζ =
      Matrix.blockDiagonal (fun a => resolvent (T a) ζ) := by
  have hu : ζ ∈ resolventSet ℂ T := by
    change IsUnit (algebraMap ℂ (n → D) ζ - T)
    exact Pi.isUnit_iff.mpr hζ
  have he : resolvent T ζ = fun a => resolvent (T a) ζ := by
    funext a
    exact (Pi.evalAlgHom ℂ (fun _ : n => D) a).map_resolvent hu
  have hm := (blockDiagonalAlgHom (n := n) (d := d)).map_resolvent hu
  change Matrix.blockDiagonal (resolvent T ζ) = resolvent (Matrix.blockDiagonal T) ζ at hm
  rw [he] at hm
  exact hm.symm


-- @@ L52-67 verbatim
omit [Fintype d] [DecidableEq ι] [DecidableEq d] in
/-- At q=1 the actual interpolant is literally block diagonal, with one
copy of the original affine series in each ensemble coordinate. -/
theorem gaussianFreeFiniteInterpolation_one_eq_blockDiagonal
    (A₀ : D) (A : ι → D) (x : E) :
    gaussianFreeFiniteInterpolation A₀ A 1 x =
      Matrix.blockDiagonal (fun a : n => A₀ + ∑ i, x (.inl (i, a)) • A i) := by
  rw [gaussianFreeFiniteInterpolation_eq_diagonal_add_gue]
  simp only [Real.sqrt_one, sub_self, Real.sqrt_zero, one_smul, zero_smul, add_zero]
  ext ab ce
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Matrix.diagonal_apply, Matrix.blockDiagonal_apply,
    Matrix.smul_apply, Complex.real_smul]
  by_cases h : ab.2 = ce.2
  · simp [h, mul_comm]
  · simp [h]


-- @@ L69-75 verbatim
omit [DecidableEq d] in
private theorem normalizedTrace_blockDiagonal (T : n → D) :
    normalizedTrace (Matrix.blockDiagonal T) =
      (Fintype.card n : ℂ)⁻¹ * ∑ a, normalizedTrace (T a) := by
  simp only [normalizedTrace, Matrix.trace_blockDiagonal, Fintype.card_prod,
    Nat.cast_mul, mul_inv_rev, ← Finset.mul_sum]
  ring


-- @@ L77-88 verbatim
private theorem blockDiagonal_resolvent_word (T : n → D)
    {m : ℕ} (ζ : Fin m → ℂ) (hζ : ∀ a j, ζ j ∈ resolventSet ℂ (T a)) :
    (List.ofFn (fun j => resolvent (Matrix.blockDiagonal T) (ζ j))).prod =
      Matrix.blockDiagonal (fun a => (List.ofFn (fun j => resolvent (T a) (ζ j))).prod) := by
  induction m with
  | zero =>
    simp only [List.ofFn_zero, List.prod_nil]
    exact Matrix.blockDiagonal_one.symm
  | succ m ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    rw [blockDiagonal_resolvent T (ζ 0) (fun a => hζ a 0),
      ih (fun j => ζ j.succ) (fun a j => hζ a j.succ), ← Matrix.blockDiagonal_mul]


-- @@ L90-111 verbatim
omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
private theorem continuous_original_resolvent_word
    (A₀ : D) (hA₀ : A₀.IsHermitian) (A : ι → D) (hA : ∀ i, (A i).IsHermitian)
    {m : ℕ} (ζ : Fin m → ℂ) (hζ : ∀ j, (ζ j).im ≠ 0) :
    Continuous (fun x : ι → ℝ =>
      (List.ofFn (fun j => resolvent (A₀ + ∑ i, x i • A i) (ζ j))).prod) := by
  induction m with
  | zero => simpa using (continuous_const : Continuous (fun _ : ι → ℝ => (1 : D)))
  | succ m ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    apply Continuous.mul _ (ih (Fin.tail ζ) (fun j => hζ j.succ))
    apply continuous_iff_continuousAt.mpr
    intro x
    have hcont : ContinuousAt (fun y : ι → ℝ => A₀ + ∑ i, y i • A i) x := by
      apply Continuous.continuousAt
      apply continuous_const.add
      exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
    exact (hasFDerivAt_resolvent_of_isHermitian (ζ 0) _
      (hA₀.add (isHermitian_sum_smul_real A hA x)) (hζ 0)).continuousAt.comp
      (f := fun y : ι → ℝ => A₀ + ∑ i, y i • A i)
      hcont


-- @@ L113-124 verbatim
open scoped Matrix.Norms.L2Operator in
private theorem norm_original_resolvent_word_le (T : D) (hT : T.IsHermitian)
    {m : ℕ} (ζ : Fin m → ℂ) (hζ : ∀ j, (ζ j).im ≠ 0) :
    ‖(List.ofFn (fun j => resolvent T (ζ j))).prod‖ ≤ ∏ j, |(ζ j).im|⁻¹ := by
  induction m with
  | zero => simpa only [List.ofFn_zero, List.prod_nil, Fin.prod_univ_zero,
      ← specNorm_eq_norm] using (specNorm_one_le (n := d) (𝕜 := ℂ))
  | succ m ih =>
    simp only [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul
      (by simpa only [← specNorm_eq_norm] using hT.specNorm_resolvent_le (hζ 0))
      (ih (Fin.tail ζ) (fun j => hζ j.succ)) (norm_nonneg _) (by positivity))


-- @@ L126-177 verbatim
omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
/-- The actual q=1 finite-N expected normalized nonreal resolvent word equals
the original affine Gaussian matrix series's expectation, for every word
length, arbitrary Hermitian mean, and positive ensemble size. Empty matrix
and coordinate dimensions are included. No distributional or moment
comparison premise is supplied.
Source: arXiv:2108.06312v2, Section 5.1.
atlas: gaussian-free-spectrum-two-sided (partial). -/
theorem integral_normalizedTrace_gaussianFreeFiniteResolventWord_one
    [Nonempty n] (A₀ : D) (hA₀ : A₀.IsHermitian)
    (A : ι → D) (hA : ∀ i, (A i).IsHermitian)
    {m : ℕ} (ζ : Fin m → ℂ) (hζ : ∀ j, (ζ j).im ≠ 0) :
    (∫ x : E, normalizedTrace (gaussianFreeFiniteResolventWord A₀ A 1 ζ x)
      ∂gaussianVector (GaussianFreeFiniteCoordinate ι n)) =
      ∫ x : ι → ℝ, normalizedTrace
        ((List.ofFn (fun j => resolvent (A₀ + ∑ i, x i • A i) (ζ j))).prod)
        ∂gaussianVector ι := by
  let μ := gaussianVector (GaussianFreeFiniteCoordinate ι n)
  let F : (ι → ℝ) → ℂ := fun x => normalizedTrace
    ((List.ofFn (fun j => resolvent (A₀ + ∑ i, x i • A i) (ζ j))).prod)
  let L : D →L[ℂ] ℂ := (normalizedTraceLinearMap : D →ₗ[ℂ] ℂ).toContinuousLinearMap
  have hFc : Continuous F := L.continuous.comp
    (continuous_original_resolvent_word A₀ hA₀ A hA ζ hζ)
  have hFi : Integrable F (gaussianVector ι) :=
    Integrable.of_bound hFc.aestronglyMeasurable (∏ j, |(ζ j).im|⁻¹)
      (Filter.Eventually.of_forall fun x =>
        (norm_normalizedTrace_le_specNorm _).trans (by
          simpa only [specNorm_eq_norm] using norm_original_resolvent_word_le _
            (hA₀.add (isHermitian_sum_smul_real A hA x)) ζ hζ))
  have hsel (a : n) : HasLaw (fun x : E => fun i => x (.inl (i, a)))
      (gaussianVector ι) μ :=
    hasLaw_pi_select (fun _ : GaussianFreeFiniteCoordinate ι n => gaussianReal 0 1)
      (fun i : ι => Sum.inl (i, a)) (by intro i j h; exact Prod.mk.inj (Sum.inl.inj h) |>.1)
  have hInt (a : n) : (∫ x : E, F (fun i => x (.inl (i, a))) ∂μ) =
      ∫ x : ι → ℝ, F x ∂gaussianVector ι :=
    (hsel a).integral_comp hFc.aestronglyMeasurable
  have hI (a : n) : Integrable (fun x : E => F (fun i => x (.inl (i, a)))) μ :=
    (hsel a).measurePreserving (by fun_prop) |>.integrable_comp_of_integrable hFi
  have he (x : E) : normalizedTrace (gaussianFreeFiniteResolventWord A₀ A 1 ζ x) =
      (Fintype.card n : ℂ)⁻¹ * ∑ a : n, F (fun i => x (.inl (i, a))) := by
    unfold gaussianFreeFiniteResolventWord
    rw [gaussianFreeFiniteInterpolation_one_eq_blockDiagonal,
      blockDiagonal_resolvent_word, normalizedTrace_blockDiagonal]
    intro a j
    change IsUnit (algebraMap ℂ D (ζ j) - (A₀ + ∑ i, x (.inl (i, a)) • A i))
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (hA₀.add (isHermitian_sum_smul_real A hA _)).isUnit_smul_one_sub_of_im_ne_zero (hζ j)
  simp_rw [he]
  rw [integral_const_mul, integral_finsetSum _ (fun a _ => hI a)]
  simp only [hInt, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]


-- @@ L179-179 verbatim
end NLAlib
