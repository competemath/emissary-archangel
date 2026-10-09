import OAI.Analysis.LiebThirring.MatrixOrder


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u6 u7 u8 u9 u10 u11


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open MeasureTheory

-- @@ L9-9 verbatim
open scoped ENNReal Matrix.Norms.L2Operator

-- @@ L10-10 verbatim
open Matrix



-- @@ L13-13 verbatim
open Matrix Unitary MeasureTheory Set

-- @@ L14-14 verbatim
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

-- @@ L15-15 verbatim
namespace SharpLiebThirring.MatrixProof

-- @@ L16-16 verbatim
variable {n : Type u6} [Fintype n] [DecidableEq n]


-- @@ L18-35 verbatim
/-- Finite spectral synthesis as a real continuous linear map. -/
def spectralCLM {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (n → ℝ) →L[ℝ] Matrix n n ℂ :=
  ({ toFun := fun x ↦ conjStarAlgAut ℂ (Matrix n n ℂ) hA.eigenvectorUnitary
        (diagonal (fun i ↦ (x i : ℂ)))
     map_add' := by
       intro x y
       simp only [Pi.add_apply, Complex.ofReal_add, conjStarAlgAut_apply]
       rw [show diagonal (fun i ↦ (x i : ℂ) + (y i : ℂ)) =
         diagonal (fun i ↦ (x i : ℂ)) + diagonal (fun i ↦ (y i : ℂ)) from
         (diagonal_add _ _).symm]
       simp only [mul_add, add_mul]
     map_smul' := by
       intro r x
       simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
       rw [show diagonal (fun i ↦ (r : ℂ) * (x i : ℂ)) =
         r • diagonal (fun i ↦ (x i : ℂ)) by ext i j; simp [diagonal_apply]]
       simp [conjStarAlgAut_apply] } : (n → ℝ) →ₗ[ℝ] Matrix n n ℂ).toContinuousLinearMap


-- @@ L37-39 verbatim
@[simp] lemma spectralCLM_apply {A : Matrix n n ℂ} (hA : A.IsHermitian) (x : n → ℝ) :
    spectralCLM hA x = conjStarAlgAut ℂ (Matrix n n ℂ) hA.eigenvectorUnitary
      (diagonal (fun i ↦ (x i : ℂ))) := rfl


-- @@ L41-45 verbatim
lemma integrable_hermitian_cfc {X : Type u7} [MeasurableSpace X] {μ : Measure X}
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : X → ℝ → ℝ)
    (hf : ∀ i, Integrable (fun x ↦ f x (hA.eigenvalues i)) μ) :
    Integrable (fun x ↦ hA.cfc (f x)) μ :=
  (spectralCLM hA).integrable_comp (integrable_pi_iff.2 hf)


-- @@ L47-59 verbatim
lemma integral_hermitian_cfc {X : Type u8} [MeasurableSpace X] {μ : Measure X}
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : X → ℝ → ℝ)
    (hf : ∀ i, Integrable (fun x ↦ f x (hA.eigenvalues i)) μ) :
    ∫ x, hA.cfc (f x) ∂μ = hA.cfc (fun t ↦ ∫ x, f x t ∂μ) := by
  have hi := integrable_pi_iff.2 hf
  calc
    _ = ∫ x, spectralCLM hA (fun i ↦ f x (hA.eigenvalues i)) ∂μ := rfl
    _ = spectralCLM hA (∫ x, fun i ↦ f x (hA.eigenvalues i) ∂μ) :=
      (spectralCLM hA).integral_comp_comm hi
    _ = _ := by
      apply congrArg (spectralCLM hA)
      ext i
      exact ((ContinuousLinearMap.proj i : (n → ℝ) →L[ℝ] ℝ).integral_comp_comm hi).symm


-- @@ L61-71 verbatim
lemma cfc_shifted_inverse {A : Matrix n n ℂ} (hA : A.PosSemidef) {a : ℝ} (ha : 0 < a) :
    hA.isHermitian.cfc (fun y ↦ (y + a)⁻¹) = (A + a • 1)⁻¹ := by
  have hn : ∀ x ∈ spectrum ℝ A, x + a ≠ 0 := by
    intro x hx
    have hx₀ : 0 ≤ x := spectrum_nonneg_of_nonneg hA.nonneg hx
    linarith
  erw [← hA.isHermitian.cfc_eq,
    cfc_inv (fun y : ℝ ↦ y + a) A hn (by fun_prop) hA.isHermitian,
    cfc_add A id (fun _ ↦ a) (by fun_prop) (by fun_prop),
    cfc_const a A hA.isHermitian, cfc_id ℝ A hA.isHermitian,
    Matrix.nonsing_inv_eq_ringInverse, Algebra.algebraMap_eq_smul_one]


-- @@ L73-73 verbatim
open ScalarProof


-- @@ L75-82 verbatim
lemma shifted_inverse_norm_le {A : Matrix n n ℂ} (hA : A.PosSemidef) {a : ℝ} (ha : 0 < a) :
    ‖(A + a • 1)⁻¹‖ ≤ a⁻¹ := by
  rw [← cfc_shifted_inverse hA ha, ← hA.isHermitian.cfc_eq]
  apply norm_cfc_le (inv_nonneg.2 ha.le)
  intro x hx
  have hx₀ : 0 ≤ x := spectrum_nonneg_of_nonneg hA.nonneg hx
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 (by linarith : 0 < x + a))]
  exact inv_anti₀ ha (by linarith)


-- @@ L84-85 verbatim
def resolventMatrix (β δ : ℝ) (A : Matrix n n ℂ) (v : ℝ) : Matrix n n ℂ :=
  v ^ β • ((δ + v)⁻¹ • 1 - (A + (δ + v) • 1)⁻¹)


-- @@ L87-107 verbatim
lemma cfc_resolventDifference {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (β : ℝ) {δ v : ℝ} (hδ : 0 < δ) (hv : 0 ≤ v) :
    hA.isHermitian.cfc (fun y ↦ resolventDifference β δ y v) =
      resolventMatrix β δ A v := by
  have ha : 0 < δ + v := by linarith
  have hn : ∀ x ∈ spectrum ℝ A, x + (δ + v) ≠ 0 := by
    intro x hx
    have hx₀ : 0 ≤ x := spectrum_nonneg_of_nonneg hA.nonneg hx
    linarith
  have hc : ContinuousOn (fun x : ℝ ↦ (x + (δ + v))⁻¹) (spectrum ℝ A) :=
    (continuousOn_id.add continuousOn_const).inv₀ hn
  unfold resolventDifference resolventMatrix
  simp only [add_assoc]
  erw [← hA.isHermitian.cfc_eq,
    cfc_const_mul (v ^ β) (fun y ↦ (δ + v)⁻¹ - (y + (δ + v))⁻¹) A
      (continuousOn_const.sub hc),
    cfc_sub (fun _ ↦ (δ + v)⁻¹) (fun y ↦ (y + (δ + v))⁻¹) A
      continuousOn_const hc,
    cfc_const (δ + v)⁻¹ A hA.isHermitian,
    hA.isHermitian.cfc_eq, cfc_shifted_inverse hA ha,
    Algebra.algebraMap_eq_smul_one]


-- @@ L109-119 verbatim
lemma integrable_resolventMatrix {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {β δ : ℝ} (hβ₀ : -1 < β) (hβ₁ : β < 1) (hδ : 0 < δ) :
    IntegrableOn (resolventMatrix β δ A) (Ioi 0) := by
  have hi := integrable_hermitian_cfc hA.isHermitian
    (fun v y ↦ resolventDifference β δ y v) (μ := volume.restrict (Ioi (0 : ℝ)))
    (fun i ↦ resolvent_difference_integrable hβ₀ hβ₁ hδ (by
      have := hA.eigenvalues_nonneg i
      linarith))
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact cfc_resolventDifference hA β hδ (le_of_lt hv)


-- @@ L121-147 verbatim
/-- Matrix-valued resolvent representation, not only a scalar or commuting case. -/
lemma primitive_cfc_resolvent_representation {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {σ δ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hδ : 0 < δ) :
    hA.isHermitian.cfc (regularizedPrimitive σ δ) =
      resolventNormalization (σ - 1 / 2) •
        ∫ v in Ioi (0 : ℝ), resolventMatrix (σ - 1 / 2) δ A v := by
  have hβ₀ : -1 < σ - 1 / 2 := by linarith
  have hβ₁ : σ - 1 / 2 < 1 := by linarith
  have hi (i : n) : IntegrableOn
      (fun v ↦ resolventDifference (σ - 1 / 2) δ (hA.isHermitian.eigenvalues i) v) (Ioi 0) :=
    resolvent_difference_integrable hβ₀ hβ₁ hδ (by
      have := hA.eigenvalues_nonneg i
      linarith)
  have he : (∫ v in Ioi (0 : ℝ), resolventMatrix (σ - 1 / 2) δ A v) =
      hA.isHermitian.cfc (fun y ↦ ∫ v in Ioi (0 : ℝ), resolventDifference (σ - 1 / 2) δ y v) := by
    rw [← integral_hermitian_cfc hA.isHermitian
      (fun v y ↦ resolventDifference (σ - 1 / 2) δ y v) hi]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact (cfc_resolventDifference hA _ hδ (le_of_lt hv)).symm
  rw [he]
  change spectralCLM hA.isHermitian (fun i ↦ regularizedPrimitive σ δ (hA.isHermitian.eigenvalues i)) =
    _ • spectralCLM hA.isHermitian _
  rw [← map_smul]
  apply congrArg (spectralCLM hA.isHermitian)
  ext i
  exact primitive_resolvent_representation hσ₀ hσ₁ hδ (hA.eigenvalues_nonneg i)


-- @@ L149-149 verbatim
end SharpLiebThirring.MatrixProof



-- @@ L152-152 verbatim
namespace SharpLiebThirring.MatrixProof

-- @@ L153-153 verbatim
open ScalarProof Matrix MeasureTheory Set

-- @@ L154-154 verbatim
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology

-- @@ L155-155 verbatim
variable {n : Type u9} [Fintype n] [DecidableEq n]


-- @@ L157-158 verbatim
def resolventTangentKernel (β δ : ℝ) (Y Z : Matrix n n ℂ) (v : ℝ) : Matrix n n ℂ :=
  v ^ β • ((Y + (δ + v) • 1)⁻¹ * Z * (Y + (δ + v) • 1)⁻¹)


-- @@ L160-176 verbatim
lemma continuousOn_shifted_inverse {Y : Matrix n n ℂ} (hY : Y.PosSemidef)
    {δ : ℝ} (hδ : 0 < δ) :
    ContinuousOn (fun v : ℝ ↦ (Y + (δ + v) • 1)⁻¹) (Ioi 0) := by
  have hc : ContinuousOn (fun v : ℝ ↦ fun i ↦ (hY.isHermitian.eigenvalues i + (δ + v))⁻¹)
      (Ioi 0) := by
    apply continuousOn_pi.2
    intro i
    apply (continuousOn_const.add (continuousOn_const.add continuousOn_id)).inv₀
    intro v hv
    change hY.isHermitian.eigenvalues i + (δ + v) ≠ 0
    have hv' : 0 < v := hv
    have := hY.eigenvalues_nonneg i
    linarith
  apply ((spectralCLM hY.isHermitian).continuous.comp_continuousOn hc).congr
  intro v hv
  change (Y + (δ + v) • 1)⁻¹ = hY.isHermitian.cfc (fun y ↦ (y + (δ + v))⁻¹)
  exact (cfc_shifted_inverse hY (by have hv' : 0 < v := hv; linarith)).symm


-- @@ L178-198 verbatim
lemma integrable_resolventTangentKernel {Y : Matrix n n ℂ} (hY : Y.PosSemidef)
    (Z : Matrix n n ℂ) {β δ : ℝ} (hβ₀ : -1 < β) (hβ₁ : β < 1) (hδ : 0 < δ) :
    IntegrableOn (resolventTangentKernel β δ Y Z) (Ioi 0) := by
  have hc := continuousOn_shifted_inverse hY hδ
  have ht : ContinuousOn (resolventTangentKernel β δ Y Z) (Ioi 0) :=
    (continuousOn_id.rpow_const (fun _ hv ↦ Or.inl (ne_of_gt hv))).smul
      ((hc.mul continuousOn_const).mul hc)
  apply ((resolvent_kernel_integrable hβ₀ hβ₁ hδ).const_mul ‖Z‖).mono'
    (ht.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv' : 0 < v := hv
  have hb := shifted_inverse_norm_le hY (show 0 < δ + v by linarith)
  have hn : 0 ≤ v ^ β := Real.rpow_nonneg hv'.le _
  unfold resolventTangentKernel
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hn]
  calc
    _ ≤ v ^ β * ((‖(Y + (δ + v) • 1)⁻¹‖ * ‖Z‖) * ‖(Y + (δ + v) • 1)⁻¹‖) := by
      gcongr
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ v ^ β * (((δ + v)⁻¹ * ‖Z‖) * (δ + v)⁻¹) := by gcongr
    _ = ‖Z‖ * (v ^ β / (δ + v) ^ 2) := by rw [div_eq_mul_inv, ← inv_pow]; ring


-- @@ L200-203 verbatim
omit [Fintype n] in
lemma shifted_posDef {Y : Matrix n n ℂ} (hY : Y.PosSemidef) {a : ℝ} (ha : 0 < a) :
    (Y + a • 1).PosDef :=
  PosDef.posSemidef_add hY ((PosDef.one : (1 : Matrix n n ℂ).PosDef).smul ha)


-- @@ L205-215 verbatim
lemma resolventMatrix_le {X Y : Matrix n n ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    {β δ v : ℝ} (hδ : 0 < δ) (hv : 0 < v) :
    resolventMatrix β δ X v ≤ resolventMatrix β δ Y v + resolventTangentKernel β δ Y (X - Y) v := by
  have ha : 0 < δ + v := by linarith
  have ht := resolvent_tangent (shifted_posDef hY ha) (shifted_posDef hX ha)
  have he : (X + (δ + v) • 1) - (Y + (δ + v) • 1) = X - Y := by abel
  rw [he] at ht
  have hh := add_le_add_left ht ((δ + v)⁻¹ • (1 : Matrix n n ℂ))
  have hsm := smul_le_smul_of_nonneg_left hh (Real.rpow_nonneg hv.le β)
  convert! hsm using 1 <;> simp only [resolventMatrix, resolventTangentKernel, sub_eq_add_neg,
    smul_add, add_assoc] <;> abel


-- @@ L217-237 verbatim
/-- Operator tangent inequality for every pair of positive Hermitian matrices,
with a fully convergent resolvent integral. -/
lemma primitive_cfc_tangent {X Y : Matrix n n ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    {σ δ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hδ : 0 < δ) :
    hX.isHermitian.cfc (regularizedPrimitive σ δ) ≤
      hY.isHermitian.cfc (regularizedPrimitive σ δ) +
        resolventNormalization (σ - 1 / 2) •
          ∫ v in Ioi (0 : ℝ), resolventTangentKernel (σ - 1 / 2) δ Y (X - Y) v := by
  have hβ₀ : -1 < σ - 1 / 2 := by linarith
  have hβ₁ : σ - 1 / 2 < 1 := by linarith
  have hiX := integrable_resolventMatrix hX hβ₀ hβ₁ hδ
  have hiY := integrable_resolventMatrix hY hβ₀ hβ₁ hδ
  have hiT := integrable_resolventTangentKernel hY (X - Y) hβ₀ hβ₁ hδ
  have hle := integral_mono_ae hiX (hiY.add hiT) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact resolventMatrix_le hX hY hδ hv)
  simp only [Pi.add_apply] at hle
  rw [integral_add hiY hiT] at hle
  rw [primitive_cfc_resolvent_representation hX hσ₀ hσ₁ hδ,
    primitive_cfc_resolvent_representation hY hσ₀ hσ₁ hδ, ← smul_add]
  exact smul_le_smul_of_nonneg_left hle (resolvent_normalization_pos hβ₀ hβ₁).le


-- @@ L239-239 verbatim
end SharpLiebThirring.MatrixProof



-- @@ L242-242 verbatim
namespace SharpLiebThirring.ScalarProof

-- @@ L243-243 verbatim
open MeasureTheory Set


-- @@ L245-246 verbatim
def dividedPrimitive (σ δ x y : ℝ) : ℝ :=
  ∫ τ in Icc (0 : ℝ) 1, (τ * x + (1 - τ) * y + δ) ^ (σ - 3 / 2)


-- @@ L248-250 verbatim
lemma convex_combo_nonneg {x y τ : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hτ : τ ∈ Icc (0 : ℝ) 1) : 0 ≤ τ * x + (1 - τ) * y :=
  add_nonneg (mul_nonneg hτ.1 hx) (mul_nonneg (sub_nonneg.2 hτ.2) hy)


-- @@ L252-258 verbatim
lemma continuousOn_divided_integrand (σ : ℝ) {δ x y : ℝ} (hδ : 0 < δ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ContinuousOn (fun τ : ℝ ↦ (τ * x + (1 - τ) * y + δ) ^ (σ - 3 / 2)) (Icc 0 1) := by
  apply ContinuousOn.rpow_const (by fun_prop)
  intro τ hτ
  left
  exact ne_of_gt (add_pos_of_nonneg_of_pos (convex_combo_nonneg hx hy hτ) hδ)


-- @@ L260-263 verbatim
lemma dividedPrimitive_self (σ δ x : ℝ) :
    dividedPrimitive σ δ x x = (x + δ) ^ (σ - 3 / 2) := by
  simp only [dividedPrimitive, show ∀ τ : ℝ, τ * x + (1 - τ) * x = x by intro τ; ring]
  simp


-- @@ L265-283 verbatim
lemma dividedPrimitive_mul_sub (σ : ℝ) {δ x y : ℝ} (hδ : 0 < δ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x - y) * dividedPrimitive σ δ x y =
      regularizedPrimitive σ δ x - regularizedPrimitive σ δ y := by
  have hd (τ : ℝ) (hτ : τ ∈ uIcc (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ ↦ regularizedPrimitive σ δ (t * x + (1 - t) * y))
        ((x - y) * (τ * x + (1 - τ) * y + δ) ^ (σ - 3 / 2)) τ := by
    have hc : HasDerivAt (fun t : ℝ ↦ t * x + (1 - t) * y) (x - y) τ := by
      convert! ((hasDerivAt_id τ).mul_const x).add
        (((hasDerivAt_const τ (1 : ℝ)).sub (hasDerivAt_id τ)).mul_const y) using 1; ring
    have hp := (primitive_hasDerivAt σ hδ (τ * x + (1 - τ) * y)).comp τ hc
    rw [max_eq_left (convex_combo_nonneg hx hy (by simpa using hτ))] at hp
    convert! hp using 1; ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuousOn_divided_integrand σ hδ hx hy).const_mul (x - y)).intervalIntegrable_of_Icc zero_le_one)
  simp only [one_mul, sub_self, zero_mul, add_zero, sub_zero, zero_add] at he
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc] at he
  exact he


-- @@ L285-304 verbatim
lemma mixed_resolvent_integrable {β δ x y : ℝ} (hβ₀ : -1 < β) (hβ₁ : β < 1)
    (hδ : 0 < δ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    IntegrableOn (fun v : ℝ ↦ v ^ β / ((x + δ + v) * (y + δ + v))) (Ioi 0) := by
  have hc : ContinuousOn (fun v : ℝ ↦ v ^ β / ((x + δ + v) * (y + δ + v))) (Ioi 0) := by
    apply ContinuousOn.div
    · exact continuousOn_id.rpow_const (fun _ hv ↦ Or.inl (ne_of_gt hv))
    · fun_prop
    · intro v hv
      have hv' : 0 < v := hv
      exact mul_ne_zero (by linarith) (by linarith)
  apply (resolvent_kernel_integrable hβ₀ hβ₁ hδ).mono'
    (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv' : 0 < v := hv
  have h1 : 0 < x + δ + v := by linarith
  have h2 : 0 < y + δ + v := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.rpow_nonneg hv'.le _) (mul_pos h1 h2).le)]
  apply div_le_div_of_nonneg_left (Real.rpow_nonneg hv'.le _) (sq_pos_of_pos (add_pos hδ hv'))
  nlinarith [mul_nonneg hx hy, mul_nonneg hx (add_pos hδ hv').le,
    mul_nonneg hy (add_pos hδ hv').le]


-- @@ L306-338 verbatim
/-- The divided-difference coefficient, including coincident eigenvalues. -/
lemma mixed_resolvent_eq_divided {σ δ x y : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hδ : 0 < δ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    resolventNormalization (σ - 1 / 2) *
      (∫ v in Ioi (0 : ℝ), v ^ (σ - 1 / 2) / ((x + δ + v) * (y + δ + v))) =
        dividedPrimitive σ δ x y := by
  have hβ₀ : -1 < σ - 1 / 2 := by linarith
  have hβ₁ : σ - 1 / 2 < 1 := by linarith
  by_cases hxy : x = y
  · subst y
    simp only [dividedPrimitive_self, ← pow_two]
    rw [resolvent_kernel_integral_scale _ (show 0 < x + δ by linarith)]
    unfold resolventNormalization
    have hn := (resolvent_kernel_integral_pos hβ₀ hβ₁ zero_lt_one).ne'
    rw [mul_left_comm, inv_mul_cancel₀ hn, mul_one]
    congr 1
    ring
  · apply mul_left_cancel₀ (sub_ne_zero.mpr hxy)
    rw [dividedPrimitive_mul_sub _ hδ hx hy,
      primitive_resolvent_representation hσ₀ hσ₁ hδ hx,
      primitive_resolvent_representation hσ₀ hσ₁ hδ hy, ← mul_sub,
      ← integral_sub (resolvent_difference_integrable hβ₀ hβ₁ hδ (by linarith))
        (resolvent_difference_integrable hβ₀ hβ₁ hδ (by linarith))]
    rw [mul_left_comm, ← integral_const_mul]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    have hv' : 0 < v := hv
    unfold resolventDifference
    have ha : x + δ + v ≠ 0 := by linarith
    have hb : y + δ + v ≠ 0 := by linarith
    field_simp
    ring


-- @@ L340-340 verbatim
end SharpLiebThirring.ScalarProof


-- @@ L342-342 verbatim
noncomputable section

-- @@ L343-343 verbatim
open Matrix Unitary MeasureTheory Set

-- @@ L344-344 verbatim
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra

-- @@ L345-345 verbatim
namespace SharpLiebThirring.MatrixProof

-- @@ L346-346 verbatim
variable {n : Type u10} [Fintype n] [DecidableEq n]


-- @@ L348-355 verbatim
def diagonalStarAlgHom : (n → ℂ) →⋆ₐ[ℝ] Matrix n n ℂ :=
  { diagonalAlgHom ℝ with
    map_star' := by
      intro x
      ext i j
      by_cases hij : i = j
      · subst j; simp [star_apply]
      · simp [star_apply, hij, Ne.symm hij] }


-- @@ L357-370 verbatim
lemma cfc_diagonal_real (f : ℝ → ℝ) (x : n → ℝ) (hf : Continuous f) :
    cfc f (diagonal (fun i ↦ (x i : ℂ))) = diagonal (fun i ↦ (f (x i) : ℂ)) := by
  have : ContinuousFunctionalCalculus ℝ (n → ℂ) IsSelfAdjoint :=
    (IsSelfAdjoint.instIsometricContinuousFunctionalCalculus (A := n → ℂ)).toContinuousFunctionalCalculus
  have hself : IsSelfAdjoint (fun i ↦ (x i : ℂ)) := by ext i; simp
  change cfc f (diagonalStarAlgHom (fun i ↦ (x i : ℂ))) = _
  erw [← (diagonalStarAlgHom (n := n)).map_cfc f (fun i ↦ (x i : ℂ)) hf.continuousOn
    (by change Continuous (diagonal : (n → ℂ) → Matrix n n ℂ); fun_prop) hself
    (isHermitian_diagonal_iff.2 fun i ↦ by simp [IsSelfAdjoint])]
  rw [cfc_map_pi (S := ℝ) f _ hf.continuousOn hself (fun i ↦ by simp [IsSelfAdjoint])]
  change diagonal (fun i ↦ cfc f (x i : ℂ)) = diagonal (fun i ↦ (f (x i) : ℂ))
  apply congrArg diagonal
  funext i
  exact cfc_algebraMap (R := ℝ) (A := ℂ) (x i) f


-- @@ L372-379 verbatim
lemma inverse_diagonal_real (x : n → ℝ) (hx : ∀ i, x i ≠ 0) :
    (diagonal (fun i ↦ (x i : ℂ)))⁻¹ = diagonal (fun i ↦ ((x i)⁻¹ : ℂ)) := by
  apply Matrix.inv_eq_right_inv
  ext i j
  simp only [diagonal_mul_diagonal]
  by_cases hij : i = j
  · subst j; simp [hx]
  · simp [hij]


-- @@ L381-388 verbatim
omit [Fintype n] in
lemma shifted_diagonal_real (x : n → ℝ) (a : ℝ) :
    diagonal (fun i ↦ (x i : ℂ)) + a • (1 : Matrix n n ℂ) =
      diagonal (fun i ↦ ((x i + a : ℝ) : ℂ)) := by
  ext i j
  by_cases hij : i = j
  · subst j; simp
  · simp [hij]


-- @@ L390-390 verbatim
end SharpLiebThirring.MatrixProof



-- @@ L393-393 verbatim
namespace SharpLiebThirring.MatrixProof

-- @@ L394-394 verbatim
open ScalarProof Matrix MeasureTheory Set

-- @@ L395-395 verbatim
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

-- @@ L396-396 verbatim
variable {n : Type u11} [Fintype n] [DecidableEq n]


-- @@ L398-401 verbatim
omit [Fintype n] in
lemma diagonal_real_posSemidef (x : n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (diagonal (fun i ↦ (x i : ℂ))).PosSemidef :=
  posSemidef_diagonal_iff.2 (fun i ↦ by exact_mod_cast hx i)


-- @@ L403-412 verbatim
lemma resolventTangentKernel_diagonal {δ : ℝ} (hδ : 0 < δ) (β : ℝ)
    (x : n → ℝ) (hx : ∀ i, 0 ≤ x i) (Z : Matrix n n ℂ) {v : ℝ} (hv : 0 < v) (i j : n) :
    resolventTangentKernel β δ (diagonal (fun i ↦ (x i : ℂ))) Z v i j =
      ((v ^ β / ((x i + δ + v) * (x j + δ + v)) : ℝ) : ℂ) * Z i j := by
  unfold resolventTangentKernel
  rw [shifted_diagonal_real, inverse_diagonal_real _ (fun i ↦ by have := hx i; linarith)]
  simp only [Matrix.smul_apply, Complex.real_smul, mul_diagonal, diagonal_mul]
  simp only [div_eq_mul_inv, _root_.mul_inv_rev]
  push_cast
  ring


-- @@ L414-441 verbatim
lemma integral_resolventTangent_diagonal {σ δ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hδ : 0 < δ) (x : n → ℝ) (hx : ∀ i, 0 ≤ x i) (Z : Matrix n n ℂ) :
    resolventNormalization (σ - 1 / 2) •
      ∫ v in Ioi (0 : ℝ), resolventTangentKernel (σ - 1 / 2) δ
        (diagonal (fun i ↦ (x i : ℂ))) Z v =
      fun i j ↦ (dividedPrimitive σ δ (x i) (x j) : ℂ) * Z i j := by
  have hi := integrable_resolventTangentKernel (diagonal_real_posSemidef x hx) Z
    (show -1 < σ - 1 / 2 by linarith) (show σ - 1 / 2 < 1 by linarith) hδ
  ext i j
  have he := (entryCLM i j).integral_comp_comm hi
  simp only [entryCLM_apply] at he
  simp only [Matrix.smul_apply]
  rw [← he]
  have he' : (∫ v in Ioi (0 : ℝ), resolventTangentKernel (σ - 1 / 2) δ
      (diagonal (fun i ↦ (x i : ℂ))) Z v i j) =
      (∫ v in Ioi (0 : ℝ), ((v ^ (σ - 1 / 2) / ((x i + δ + v) *
        (x j + δ + v)) : ℝ) : ℂ)) * Z i j := by
    rw [← integral_mul_const]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    exact resolventTangentKernel_diagonal hδ _ x hx Z hv i j
  rw [he']
  erw [integral_ofReal]
  rw [Complex.real_smul, ← mul_assoc]
  change (resolventNormalization (σ - 1 / 2) : ℂ) *
    ((∫ v in Ioi (0 : ℝ), v ^ (σ - 1 / 2) / ((x i + δ + v) * (x j + δ + v)) : ℝ) : ℂ) *
      Z i j = _
  rw [← Complex.ofReal_mul, mixed_resolvent_eq_divided hσ₀ hσ₁ hδ (hx i) (hx j)]


-- @@ L443-443 verbatim
end SharpLiebThirring.MatrixProof



-- @@ L446-446 verbatim
namespace SharpLiebThirring.ScalarProof

-- @@ L447-447 verbatim
open MeasureTheory Set


-- @@ L449-450 verbatim
def quadraticDividedIntegrand (σ δ d x y s τ : ℝ) : ℝ :=
  (max (τ * ((s - x) ^ 2 + d) + (1 - τ) * ((s - y) ^ 2 + d)) 0 + δ) ^ (σ - 3 / 2)


-- @@ L452-454 verbatim
lemma quadratic_combo (d x y s τ : ℝ) :
    τ * ((s - x) ^ 2 + d) + (1 - τ) * ((s - y) ^ 2 + d) =
      (s - (τ * x + (1 - τ) * y)) ^ 2 + (d + τ * (1 - τ) * (x - y) ^ 2) := by ring


-- @@ L456-461 verbatim
lemma quadraticDivided_integrable_left {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (d x y τ : ℝ) : Integrable (fun s ↦ quadraticDividedIntegrand σ δ d x y s τ) := by
  have hi := shifted_derivative_integrable hσ hδ (d + τ * (1 - τ) * (x - y) ^ 2)
  have hp := (measurePreserving_sub_right (volume : Measure ℝ) (τ * x + (1 - τ) * y)).integrable_comp
    hi.aestronglyMeasurable |>.2 hi
  simpa only [Function.comp_def, quadraticDividedIntegrand, quadratic_combo] using hp


-- @@ L463-482 verbatim
lemma integral_quadraticDivided_left {σ δ d τ : ℝ} (hδ : 0 < δ) (hd : 0 ≤ d)
    (hτ : τ ∈ Icc (0 : ℝ) 1) (x y : ℝ) :
    (∫ s : ℝ, quadraticDividedIntegrand σ δ d x y s τ) =
      (d + δ + τ * (1 - τ) * (x - y) ^ 2) ^ (σ - 1) *
        ∫ s : ℝ, (1 + s ^ 2) ^ (σ - 3 / 2) := by
  have hz : 0 ≤ d + τ * (1 - τ) * (x - y) ^ 2 := by
    exact add_nonneg hd (mul_nonneg (mul_nonneg hτ.1 (sub_nonneg.2 hτ.2)) (sq_nonneg _))
  have ha : 0 < d + δ + τ * (1 - τ) * (x - y) ^ 2 := by linarith
  have he (s : ℝ) : quadraticDividedIntegrand σ δ d x y s τ =
      ((s - (τ * x + (1 - τ) * y)) ^ 2 + (d + δ + τ * (1 - τ) * (x - y) ^ 2)) ^
        (σ - 3 / 2) := by
    unfold quadraticDividedIntegrand
    rw [quadratic_combo, max_eq_left (add_nonneg (sq_nonneg _) hz)]
    congr 1
    ring
  simp_rw [he]
  rw [integral_sub_right_eq_self (fun s : ℝ ↦ (s ^ 2 + (d + δ + τ * (1 - τ) * (x - y) ^ 2)) ^
    (σ - 3 / 2)), quadratic_integral_scale _ ha]
  congr 2
  ring


-- @@ L484-509 verbatim
lemma quadraticDivided_integrable_prod {σ δ d : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (hd : 0 ≤ d) (x y : ℝ) :
    Integrable (fun p : ℝ × ℝ ↦ quadraticDividedIntegrand σ δ d x y p.1 p.2)
      (volume.prod (volume.restrict (Icc (0 : ℝ) 1))) := by
  have hc : Continuous (fun p : ℝ × ℝ ↦ quadraticDividedIntegrand σ δ d x y p.1 p.2) :=
    (derivative_continuous σ hδ).comp (by fun_prop)
  apply (integrable_prod_iff' hc.aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall (quadraticDivided_integrable_left hσ hδ d x y)
  · have hv : ContinuousOn (fun τ : ℝ ↦
        (d + δ + τ * (1 - τ) * (x - y) ^ 2) ^ (σ - 1) *
          ∫ s : ℝ, (1 + s ^ 2) ^ (σ - 3 / 2)) (Icc 0 1) := by
      apply ContinuousOn.mul _ continuousOn_const
      apply ContinuousOn.rpow_const (by fun_prop)
      intro τ hτ
      left
      have hz : 0 ≤ τ * (1 - τ) * (x - y) ^ 2 :=
        mul_nonneg (mul_nonneg hτ.1 (sub_nonneg.2 hτ.2)) (sq_nonneg _)
      linarith
    apply hv.integrableOn_Icc.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
    rw [← integral_quadraticDivided_left hδ hd hτ x y]
    apply integral_congr_ae
    filter_upwards [] with s
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ quadraticDividedIntegrand σ δ d x y s τ by
      unfold quadraticDividedIntegrand; positivity)]


-- @@ L511-523 verbatim
/-- Absolute convergence of the integrated tangent coefficients. -/
lemma integrable_divided_quadratic {σ δ d : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (hd : 0 ≤ d) (x y : ℝ) :
    Integrable (fun s ↦ dividedPrimitive σ δ ((s - x) ^ 2 + d) ((s - y) ^ 2 + d)) := by
  have hi := (quadraticDivided_integrable_prod hσ hδ hd x y).integral_prod_left
  apply hi.congr
  filter_upwards [] with s
  unfold dividedPrimitive
  apply setIntegral_congr_fun measurableSet_Icc
  intro τ hτ
  unfold quadraticDividedIntegrand
  rw [max_eq_left (convex_combo_nonneg (add_nonneg (sq_nonneg _) hd)
    (add_nonneg (sq_nonneg _) hd) hτ)]


-- @@ L525-567 verbatim
/-- The integrated tangent kernel. -/
lemma integral_divided_quadratic {σ δ d : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (hd : 0 ≤ d) (x y : ℝ) :
    fieldNormalization σ *
      (∫ s : ℝ, dividedPrimitive σ δ ((s - x) ^ 2 + d) ((s - y) ^ 2 + d)) =
      σ * (d + δ) ^ (σ - 1) *
        ∫ τ in Icc (0 : ℝ) 1,
          (1 + τ * (1 - τ) / (d + δ) * (x - y) ^ 2) ^ (σ - 1) := by
  have ha : 0 < d + δ := by linarith
  have hn := (normalization_integral_pos hσ).ne'
  have he (s : ℝ) : dividedPrimitive σ δ ((s - x) ^ 2 + d) ((s - y) ^ 2 + d) =
      ∫ τ in Icc (0 : ℝ) 1, quadraticDividedIntegrand σ δ d x y s τ := by
    unfold dividedPrimitive
    apply setIntegral_congr_fun measurableSet_Icc
    intro τ hτ
    unfold quadraticDividedIntegrand
    rw [max_eq_left (convex_combo_nonneg (add_nonneg (sq_nonneg _) hd)
      (add_nonneg (sq_nonneg _) hd) hτ)]
  simp_rw [he]
  rw [integral_integral_swap (quadraticDivided_integrable_prod hσ hδ hd x y)]
  have he' : (∫ τ in Icc (0 : ℝ) 1, ∫ s : ℝ, quadraticDividedIntegrand σ δ d x y s τ) =
      ((d + δ) ^ (σ - 1) * ∫ s : ℝ, (1 + s ^ 2) ^ (σ - 3 / 2)) *
        ∫ τ in Icc (0 : ℝ) 1,
          (1 + τ * (1 - τ) / (d + δ) * (x - y) ^ 2) ^ (σ - 1) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Icc
    intro τ hτ
    dsimp only
    rw [integral_quadraticDivided_left (σ := σ) hδ hd hτ x y]
    have hp : 0 ≤ 1 + τ * (1 - τ) / (d + δ) * (x - y) ^ 2 := by
      have := mul_nonneg (div_nonneg (mul_nonneg hτ.1 (sub_nonneg.2 hτ.2)) ha.le) (sq_nonneg (x - y))
      linarith
    rw [show d + δ + τ * (1 - τ) * (x - y) ^ 2 =
      (d + δ) * (1 + τ * (1 - τ) / (d + δ) * (x - y) ^ 2) by field_simp,
      Real.mul_rpow ha.le hp]
    ring
  rw [he']
  unfold fieldNormalization
  calc
    _ = (σ / (∫ s : ℝ, (1 + s ^ 2) ^ (σ - 3 / 2)) *
        (∫ s : ℝ, (1 + s ^ 2) ^ (σ - 3 / 2))) * ((d + δ) ^ (σ - 1) *
        ∫ τ in Icc (0 : ℝ) 1, (1 + τ * (1 - τ) / (d + δ) * (x - y) ^ 2) ^ (σ - 1)) := by ring
    _ = _ := by rw [div_mul_cancel₀ _ hn]; ring


-- @@ L569-569 verbatim
end SharpLiebThirring.ScalarProof


-- @@ L571-571 verbatim
end

-- @@ L572-572 verbatim
end


-- @@ L574-574 verbatim
end OAI
