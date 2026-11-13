import Submission.MorseGenericity2D
import Submission.MorseIntegralSmooth


-- @@ L4-12 verbatim
/-!
# From a nondegenerate chart gradient to the constructive Morse lemma

`MorseGenericity2D` expresses nondegeneracy invariantly as invertibility of the
derivative of the Euclidean gradient.  `MorseIntegralSmooth` constructs an exact
Morse normal form from the determinant of the radial Hadamard coefficients.
This file identifies those two notions and removes the last scalar normal-form
choice from the finite atlas pipeline.
-/


-- @@ L14-14 verbatim
noncomputable section


-- @@ L16-16 verbatim
open Set Function Metric

-- @@ L17-17 verbatim
open scoped RealInnerProductSpace ContDiff Topology Interval


-- @@ L19-19 verbatim
namespace Submission


-- @@ L21-21 verbatim
local notation "E₂" => EuclideanSpace ℝ (Fin 2)


-- @@ L23-31 verbatim
/-- Coordinate formula for the Euclidean gradient. -/
theorem chartGradient_apply (f : E₂ → ℝ) (x : E₂) (i : Fin 2) :
    chartGradient f x i =
      fderiv ℝ f x (EuclideanSpace.single i 1) := by
  let A : E₂ →L[ℝ] ℝ := fderiv ℝ f x
  have h := ContinuousLinearMap.adjoint_inner_left A
    (EuclideanSpace.single i 1) (1 : ℝ)
  simpa [chartGradient, scalarAdjointCLM, A,
    EuclideanSpace.inner_single_right] using h


-- @@ L33-51 verbatim
/-- Vanishing Euclidean gradient is the same as vanishing scalar differential. -/
theorem fderiv_eq_zero_of_chartGradient_eq_zero {f : E₂ → ℝ} {p : E₂}
    (hgrad : chartGradient f p = 0) : fderiv ℝ f p = 0 := by
  let A : E₂ →L[ℝ] ℝ := fderiv ℝ f p
  have hA1 : ContinuousLinearMap.adjoint A 1 = 0 := by
    simpa [chartGradient, scalarAdjointCLM, A] using hgrad
  have hAadj : ContinuousLinearMap.adjoint A = 0 := by
    apply ContinuousLinearMap.ext
    intro r
    calc
      ContinuousLinearMap.adjoint A r = r • ContinuousLinearMap.adjoint A 1 := by
        rw [← map_smul]
        simp
      _ = 0 := by rw [hA1, smul_zero]
  apply ContinuousLinearMap.ext
  intro v
  have hinner := ContinuousLinearMap.adjoint_inner_left A v (1 : ℝ)
  rw [hAadj] at hinner
  simpa [A] using hinner.symm


-- @@ L53-59 verbatim
/-- A critical point becomes a critical origin after recentering. -/
theorem fderiv_recenter_eq_zero_of_chartGradient_eq_zero
    {f : E₂ → ℝ} (hf : ContDiff ℝ ∞ f) {p : E₂}
    (hgrad : chartGradient f p = 0) :
    fderiv ℝ (recenter f p) 0 = 0 := by
  rw [fderiv_recenter_zero (hf.differentiable (by simp) p)]
  exact fderiv_eq_zero_of_chartGradient_eq_zero hgrad


-- @@ L61-99 verbatim
/-- The derivative of the gradient is the Hessian, coordinate by coordinate. -/
theorem fderiv_chartGradient_apply {f : E₂ → ℝ}
    (hf : ContDiff ℝ ∞ f) (x v : E₂) (i : Fin 2) :
    fderiv ℝ (chartGradient f) x v i =
      iteratedFDeriv ℝ 2 f x ![v, EuclideanSpace.single i 1] := by
  let ei : E₂ := EuclideanSpace.single i 1
  let proj : E₂ →L[ℝ] ℝ := EuclideanSpace.proj i
  have hleft : fderiv ℝ (fun y => chartGradient f y i) x v =
      fderiv ℝ (chartGradient f) x v i := by
    have hg : HasFDerivAt (chartGradient f)
        (fderiv ℝ (chartGradient f) x) x :=
      ((contDiff_chartGradient hf).differentiable (by simp) x).hasFDerivAt
    have hp := proj.hasFDerivAt.comp x hg
    have happ := congrArg (fun A : E₂ →L[ℝ] ℝ => A v) hp.fderiv
    change fderiv ℝ (proj ∘ chartGradient f) x v = _ at happ
    change fderiv ℝ (proj ∘ chartGradient f) x v = _
    simpa [proj] using happ
  have hright : fderiv ℝ (fun y => fderiv ℝ f y ei) x v =
      fderiv ℝ (fderiv ℝ f) x v ei := by
    have hcSmooth : ContDiff ℝ ∞ (fderiv ℝ f) :=
      hf.fderiv_right (by simp)
    have hc : DifferentiableAt ℝ (fderiv ℝ f) x :=
      hcSmooth.differentiable infty_ne_zero x
    have hu : DifferentiableAt ℝ (fun _ : E₂ => ei) x :=
      differentiableAt_const ei
    have happ := congrArg (fun A : E₂ →L[ℝ] ℝ => A v)
      (fderiv_clm_apply hc hu)
    simpa [ei] using happ
  calc
    fderiv ℝ (chartGradient f) x v i =
        fderiv ℝ (fun y => chartGradient f y i) x v := hleft.symm
    _ = fderiv ℝ (fun y => fderiv ℝ f y ei) x v := by
      congr 2
      funext y
      exact chartGradient_apply f y i
    _ = fderiv ℝ (fderiv ℝ f) x v ei := hright
    _ = iteratedFDeriv ℝ 2 f x ![v, ei] := by
      simp [iteratedFDeriv_two_apply]
    _ = iteratedFDeriv ℝ 2 f x ![v, EuclideanSpace.single i 1] := rfl


-- @@ L101-110 verbatim
/-- The differential of a recentered function at an arbitrary point. -/
theorem fderiv_recenter_apply {f : E₂ → ℝ} (hf : Differentiable ℝ f)
    (p x : E₂) :
    fderiv ℝ (recenter f p) x = fderiv ℝ f (p + x) := by
  have h : HasFDerivAt (fun y : E₂ => f (p + y))
      (fderiv ℝ f (p + x)) x := by
    have hcomp := (hf (p + x)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).const_add p)
    simpa [Function.comp_def] using hcomp
  exact h.fderiv


-- @@ L112-116 verbatim
/-- Recentering translates the Euclidean gradient. -/
theorem chartGradient_recenter {f : E₂ → ℝ} (hf : Differentiable ℝ f)
    (p x : E₂) :
    chartGradient (recenter f p) x = chartGradient f (p + x) := by
  rw [chartGradient, chartGradient, fderiv_recenter_apply hf]


-- @@ L118-134 verbatim
/-- Recentering translates the derivative of the Euclidean gradient. -/
theorem fderiv_chartGradient_recenter {f : E₂ → ℝ}
    (hf : ContDiff ℝ ∞ f) (p x : E₂) :
    fderiv ℝ (chartGradient (recenter f p)) x =
      fderiv ℝ (chartGradient f) (p + x) := by
  have hfun : chartGradient (recenter f p) =
      fun y : E₂ => chartGradient f (p + y) := by
    funext y
    exact chartGradient_recenter (hf.differentiable (by simp)) p y
  rw [hfun]
  have h : HasFDerivAt (fun y : E₂ => chartGradient f (p + y))
      (fderiv ℝ (chartGradient f) (p + x)) x := by
    have hd : DifferentiableAt ℝ (chartGradient f) (p + x) :=
      (contDiff_chartGradient hf).differentiable (by simp) _
    have hcomp := hd.hasFDerivAt.comp x ((hasFDerivAt_id x).const_add p)
    simpa [Function.comp_def] using hcomp
  exact h.fderiv


-- @@ L136-136 verbatim
namespace HadamardQuadraticData


-- @@ L138-146 verbatim
private lemma integral_one_sub_zero_one :
    (∫ t : ℝ in (0 : ℝ)..1, 1 - t) = (1 / 2 : ℝ) := by
  change (∫ t : ℝ in (0 : ℝ)..1, (fun _ : ℝ => 1) t - id t) = (1 / 2 : ℝ)
  rw [intervalIntegral.integral_sub
    (continuous_const.intervalIntegrable 0 1)
    (continuous_id.intervalIntegrable 0 1), integral_one]
  simp only [id_eq]
  rw [integral_id]
  norm_num


-- @@ L148-153 verbatim
/-- At the origin the first radial Hadamard coefficient is half the corresponding
Hessian entry. -/
lemma integratedHadamardA_zero (f : E₂ → ℝ) :
    integratedHadamardA f 0 =
      (1 / 2 : ℝ) * iteratedFDeriv ℝ 2 f 0 ![e₀, e₀] := by
  simp [integratedHadamardA, integral_one_sub_zero_one]


-- @@ L155-163 verbatim
/-- At the origin the mixed radial coefficient is one quarter of the sum of the
two mixed Hessian entries. -/
lemma integratedHadamardB_zero (f : E₂ → ℝ) :
    integratedHadamardB f 0 =
      (1 / 4 : ℝ) *
        (iteratedFDeriv ℝ 2 f 0 ![e₀, e₁] +
          iteratedFDeriv ℝ 2 f 0 ![e₁, e₀]) := by
  simp [integratedHadamardB, integral_one_sub_zero_one]
  ring


-- @@ L165-170 verbatim
/-- At the origin the second radial Hadamard coefficient is half the
corresponding Hessian entry. -/
lemma integratedHadamardC_zero (f : E₂ → ℝ) :
    integratedHadamardC f 0 =
      (1 / 2 : ℝ) * iteratedFDeriv ℝ 2 f 0 ![e₁, e₁] := by
  simp [integratedHadamardC, integral_one_sub_zero_one]


-- @@ L172-198 verbatim
/-- First coordinate of the derivative of the gradient, written in the radial
Hadamard coefficients. -/
lemma fderiv_chartGradient_apply_zero {f : E₂ → ℝ}
    (hf : ContDiff ℝ ∞ f) (v : E₂) :
    fderiv ℝ (chartGradient f) 0 v 0 =
      2 * integratedHadamardA f 0 * v 0 +
        2 * integratedHadamardB f 0 * v 1 := by
  rw [fderiv_chartGradient_apply hf]
  have htwo : (2 : ℕ∞ω) ≤ ∞ := by
    change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr (le_of_lt (ENat.coe_lt_top 2))
  have hsym : iteratedFDeriv ℝ 2 f 0 ![e₀, e₁] =
      iteratedFDeriv ℝ 2 f 0 ![e₁, e₀] :=
    (hf.contDiffAt.isSymmSndFDerivAt
      (by simpa using htwo)).iteratedFDeriv_cons
  let H := iteratedFDeriv ℝ 2 f 0
  have hexpand : H ![v, e₀] =
      v 0 * H ![e₀, e₀] + v 1 * H ![e₁, e₀] := by
    change H.curryLeft v (Fin.cons e₀ Fin.elim0) =
      v 0 * H.curryLeft e₀ (Fin.cons e₀ Fin.elim0) +
        v 1 * H.curryLeft e₁ (Fin.cons e₀ Fin.elim0)
    rw [basis_decomposition v, map_add, map_smul, map_smul]
    simp [smul_eq_mul]
  change H ![v, e₀] = _
  rw [hexpand]
  rw [integratedHadamardA_zero, integratedHadamardB_zero, hsym]
  ring


-- @@ L200-226 verbatim
/-- Second coordinate of the derivative of the gradient, in the same
coefficients. -/
lemma fderiv_chartGradient_apply_one {f : E₂ → ℝ}
    (hf : ContDiff ℝ ∞ f) (v : E₂) :
    fderiv ℝ (chartGradient f) 0 v 1 =
      2 * integratedHadamardB f 0 * v 0 +
        2 * integratedHadamardC f 0 * v 1 := by
  rw [fderiv_chartGradient_apply hf]
  have htwo : (2 : ℕ∞ω) ≤ ∞ := by
    change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr (le_of_lt (ENat.coe_lt_top 2))
  have hsym : iteratedFDeriv ℝ 2 f 0 ![e₀, e₁] =
      iteratedFDeriv ℝ 2 f 0 ![e₁, e₀] :=
    (hf.contDiffAt.isSymmSndFDerivAt
      (by simpa using htwo)).iteratedFDeriv_cons
  let H := iteratedFDeriv ℝ 2 f 0
  have hexpand : H ![v, e₁] =
      v 0 * H ![e₀, e₁] + v 1 * H ![e₁, e₁] := by
    change H.curryLeft v (Fin.cons e₁ Fin.elim0) =
      v 0 * H.curryLeft e₀ (Fin.cons e₁ Fin.elim0) +
        v 1 * H.curryLeft e₁ (Fin.cons e₁ Fin.elim0)
    rw [basis_decomposition v, map_add, map_smul, map_smul]
    simp [smul_eq_mul]
  change H ![v, e₁] = _
  rw [hexpand]
  rw [integratedHadamardB_zero, integratedHadamardC_zero, hsym]
  ring


-- @@ L228-238 verbatim
/-- The derivative of the gradient at the origin, fully expanded in the
integrated Hadamard coefficients. -/
lemma fderiv_chartGradient_zero_expand {f : E₂ → ℝ}
    (hf : ContDiff ℝ ∞ f) (v : E₂) :
    fderiv ℝ (chartGradient f) 0 v =
      (2 * integratedHadamardA f 0 * v 0 +
          2 * integratedHadamardB f 0 * v 1) • e₀ +
        (2 * integratedHadamardB f 0 * v 0 +
          2 * integratedHadamardC f 0 * v 1) • e₁ := by
  conv_lhs => rw [basis_decomposition (fderiv ℝ (chartGradient f) 0 v)]
  rw [fderiv_chartGradient_apply_zero hf, fderiv_chartGradient_apply_one hf]


-- @@ L240-281 verbatim
/-- **Nondegeneracy bridge, scalar form.**  If the derivative of the Euclidean
gradient is injective at the origin, the determinant of the integrated
Hadamard coefficient matrix is nonzero.  The kernel vector of a singular
symmetric `2 × 2` matrix is produced explicitly in each pivot case. -/
theorem integratedHadamardDet_ne_zero_of_injective {f : E₂ → ℝ}
    (hf : ContDiff ℝ ∞ f)
    (hinj : Injective (fderiv ℝ (chartGradient f) 0)) :
    integratedHadamardDet f ≠ 0 := by
  intro hdet
  have hdet' : integratedHadamardA f 0 * integratedHadamardC f 0 -
      integratedHadamardB f 0 ^ 2 = 0 := hdet
  by_cases hA : integratedHadamardA f 0 = 0
  · -- Degenerate first pivot: the whole first row vanishes and `e₀` is in the
    -- kernel.
    have hb2 : integratedHadamardB f 0 ^ 2 = 0 := by
      linear_combination integratedHadamardC f 0 * hA - hdet'
    have hb0 : integratedHadamardB f 0 = 0 := sq_eq_zero_iff.mp hb2
    have hker : fderiv ℝ (chartGradient f) 0 e₀ = 0 := by
      rw [fderiv_chartGradient_zero_expand hf]
      simp [hA, hb0]
    have he : (e₀ : E₂) = 0 := hinj (hker.trans (map_zero _).symm)
    have h := congrArg (fun w : E₂ => w 0) he
    simp at h
  · -- Nonzero first pivot: `(b, -a)` is an explicit nonzero kernel vector.
    set w : E₂ := integratedHadamardB f 0 • e₀ +
        (-integratedHadamardA f 0) • e₁ with hw
    have hw0 : w 0 = integratedHadamardB f 0 := by simp [hw]
    have hw1 : w 1 = -integratedHadamardA f 0 := by simp [hw]
    have hker : fderiv ℝ (chartGradient f) 0 w = 0 := by
      rw [fderiv_chartGradient_zero_expand hf, hw0, hw1]
      have h1 : 2 * integratedHadamardA f 0 * integratedHadamardB f 0 +
          2 * integratedHadamardB f 0 * -integratedHadamardA f 0 = 0 := by
        ring
      have h2 : 2 * integratedHadamardB f 0 * integratedHadamardB f 0 +
          2 * integratedHadamardC f 0 * -integratedHadamardA f 0 = 0 := by
        linear_combination (-2 : ℝ) * hdet'
      rw [h1, h2]
      simp
    have hwz : w = 0 := hinj (hker.trans (map_zero _).symm)
    rw [hwz] at hw1
    simp at hw1
    exact hA hw1


-- @@ L283-283 verbatim
end HadamardQuadraticData


-- @@ L285-294 verbatim
/-- Nondegeneracy of a critical point is preserved by recentering it to the
origin. -/
theorem nondegenerateCriticalAt_recenter {f : E₂ → ℝ}
    (hf : ContDiff ℝ ∞ f) {p : E₂} (hnd : NondegenerateCriticalAt f p) :
    NondegenerateCriticalAt (recenter f p) 0 := by
  constructor
  · rw [chartGradient_recenter (hf.differentiable (by simp)) p 0, add_zero]
    exact hnd.1
  · rw [fderiv_chartGradient_recenter hf p 0, add_zero]
    exact hnd.2


-- @@ L296-304 verbatim
/-- **Determinant bridge at a recentered critical point.**  Invariant
nondegeneracy of a critical point makes the integrated Hadamard determinant of
the recentered function nonzero. -/
theorem integratedHadamardDet_recenter_ne_zero {f : E₂ → ℝ}
    (hf : ContDiff ℝ ∞ f) {p : E₂} (hnd : NondegenerateCriticalAt f p) :
    HadamardQuadraticData.integratedHadamardDet (recenter f p) ≠ 0 :=
  HadamardQuadraticData.integratedHadamardDet_ne_zero_of_injective
    (contDiff_recenter hf p)
    (nondegenerateCriticalAt_recenter hf hnd).2.injective


-- @@ L306-314 verbatim
/-- The constructive Morse lemma at a nondegenerate critical origin: invariant
nondegeneracy alone produces an exact local Morse normal form. -/
theorem nonempty_localMorseNormalForm_of_nondegenerate_origin {f : E₂ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hnd : NondegenerateCriticalAt f 0) :
    Nonempty (LocalMorseNormalForm f) :=
  HadamardQuadraticData.morseLemma2D_integrated_of_contDiff hf
    (fderiv_eq_zero_of_chartGradient_eq_zero hnd.1)
    (HadamardQuadraticData.integratedHadamardDet_ne_zero_of_injective hf
      hnd.2.injective)


-- @@ L316-325 verbatim
/-- **Nondegeneracy-to-normal-form bridge.**  Every nondegenerate critical
point of a smooth chart function admits an exact local Morse normal form after
recentering; this is the statement shape consumed by the finite atlas
pipeline (`InstalledMorseEventGeometry` takes a
`LocalMorseNormalForm (recenter f base)`). -/
theorem nonempty_localMorseNormalForm_recenter {f : E₂ → ℝ}
    (hf : ContDiff ℝ ∞ f) {p : E₂} (hnd : NondegenerateCriticalAt f p) :
    Nonempty (LocalMorseNormalForm (recenter f p)) :=
  nonempty_localMorseNormalForm_of_nondegenerate_origin
    (contDiff_recenter hf p) (nondegenerateCriticalAt_recenter hf hnd)


-- @@ L327-327 verbatim
end Submission
