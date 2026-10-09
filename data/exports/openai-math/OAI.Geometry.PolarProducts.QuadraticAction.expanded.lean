import OAI.Geometry.PolarProducts.FourierPaths


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u112


-- @@ L7-7 verbatim
section NonsqueezingInline


-- @@ L9-9 verbatim
namespace DiagonalQuadratic

-- @@ L10-10 verbatim
noncomputable section

-- @@ L11-11 verbatim
open Finset

-- @@ L12-12 verbatim
open scoped ComplexConjugate ContDiff

-- @@ L13-13 verbatim
variable {α : Type u112} [Fintype α]

 
-- @@ L15-16 verbatim
def diag (w : α → ℝ) (a : EuclideanSpace ℂ α) : EuclideanSpace ℂ α :=
  (EuclideanSpace.equiv α ℂ).symm (fun p => w p • a p)


-- @@ L18-20 verbatim
omit [Fintype α] in
@[simp] theorem diag_apply (w : α → ℝ) (a : EuclideanSpace ℂ α) (p : α) :
    diag w a p = w p • a p := rfl

 
-- @@ L22-26 verbatim
def diagCLM (w : α → ℝ) : EuclideanSpace ℂ α →L[ℝ] EuclideanSpace ℂ α :=
  LinearMap.toContinuousLinearMap {
    toFun := diag w
    map_add' := by intros; ext; simp [smul_add]
    map_smul' := by intros; ext; simp; ring }


-- @@ L28-28 verbatim
@[simp] theorem diagCLM_apply (w : α → ℝ) (a : EuclideanSpace ℂ α) : diagCLM w a = diag w a := rfl

 
-- @@ L30-32 verbatim
theorem real_inner_eq_sum (a b : EuclideanSpace ℂ α) :
    inner (𝕜 := ℝ) a b = ∑ p, inner (𝕜 := ℝ) (a p) (b p) := by
  exact PiLp.inner_apply a b

 
-- @@ L34-37 verbatim
theorem inner_diag (w : α → ℝ) (a b : EuclideanSpace ℂ α) :
    inner (𝕜 := ℝ) (diag w a) b = ∑ p, w p * inner (𝕜 := ℝ) (a p) (b p) := by
  rw [real_inner_eq_sum]
  simp only [diag_apply, real_inner_smul_left]

 
-- @@ L39-42 verbatim
theorem self_adjoint (w : α → ℝ) (a b : EuclideanSpace ℂ α) :
    inner (𝕜 := ℝ) (diag w a) b = inner (𝕜 := ℝ) a (diag w b) := by
  rw [inner_diag, real_inner_eq_sum]
  simp only [diag_apply, real_inner_smul_right]

 
-- @@ L44-44 verbatim
def energy (w : α → ℝ) (a : EuclideanSpace ℂ α) : ℝ := ∑ p, w p * ‖a p‖^2

 
-- @@ L46-49 verbatim
theorem energy_eq_inner (w : α → ℝ) (a : EuclideanSpace ℂ α) :
    energy w a = inner (𝕜 := ℝ) (diag w a) a := by
  rw [inner_diag]
  simp only [energy, real_inner_self_eq_norm_sq]

 
-- @@ L51-53 verbatim
theorem contDiff_energy (w : α → ℝ) : ContDiff ℝ ∞ (energy w) := by
  simp_rw [funext (energy_eq_inner w)]
  exact (diagCLM w).contDiff.inner ℝ contDiff_id

 
-- @@ L55-68 verbatim
theorem hasGradientAt_energy (w : α → ℝ) (a : EuclideanSpace ℂ α) :
    HasGradientAt (energy w) ((2 : ℝ) • diag w a) a := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := (diagCLM w).hasFDerivAt.inner ℝ (hasFDerivAt_id a)
  simp only [diagCLM_apply] at h
  change HasFDerivAt (fun x => inner (𝕜 := ℝ) (diag w x) x) _ a at h
  simp_rw [← energy_eq_inner] at h
  apply h.congr_fderiv
  ext b
  change inner (𝕜 := ℝ) (diag w a) b + inner (𝕜 := ℝ) (diag w b) a =
    inner (𝕜 := ℝ) ((2 : ℝ) • diag w a) b
  rw [real_inner_smul_left, self_adjoint w b a]
  rw [real_inner_comm b (diag w a)]
  ring

 
-- @@ L70-71 verbatim
theorem gradient_energy (w : α → ℝ) (a : EuclideanSpace ℂ α) :
    gradient (energy w) a = (2 : ℝ) • diag w a := (hasGradientAt_energy w a).gradient

 
-- @@ L73-76 verbatim
theorem norm_diag_sq (w : α → ℝ) (a : EuclideanSpace ℂ α) :
    ‖diag w a‖^2 = ∑ p, (w p)^2*‖a p‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq, diag_apply, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs]

 
-- @@ L78-88 verbatim
theorem norm_diag_lower (w : α → ℝ) {d : ℝ} (hd : 0 ≤ d) (hw : ∀ p, d ≤ |w p|)
    (a : EuclideanSpace ℂ α) : d*‖a‖ ≤ ‖diag w a‖ := by
  have h : (d*‖a‖)^2 ≤ ‖diag w a‖^2 := by
    rw [mul_pow, norm_diag_sq, EuclideanSpace.norm_sq_eq, mul_sum]
    apply sum_le_sum
    intro p _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    calc
      d^2 ≤ |w p|^2 := pow_le_pow_left₀ hd (hw p) 2
      _ = _ := sq_abs _
  nlinarith [norm_nonneg (diag w a), mul_nonneg hd (norm_nonneg a)]

 
-- @@ L90-100 verbatim
theorem norm_diag_upper (w : α → ℝ) {d : ℝ} (hd : 0 ≤ d) (hw : ∀ p, |w p| ≤ d)
    (a : EuclideanSpace ℂ α) : ‖diag w a‖ ≤ d*‖a‖ := by
  have h : ‖diag w a‖^2 ≤ (d*‖a‖)^2 := by
    rw [mul_pow, norm_diag_sq, EuclideanSpace.norm_sq_eq, mul_sum]
    apply sum_le_sum
    intro p _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    calc
      (w p)^2 = |w p|^2 := (sq_abs _).symm
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) (hw p) 2
  nlinarith [norm_nonneg (diag w a), mul_nonneg hd (norm_nonneg a)]

 
-- @@ L102-108 verbatim
theorem energy_smul (w : α → ℝ) (r : ℝ) (a : EuclideanSpace ℂ α) :
    energy w (r • a) = r^2*energy w a := by
  simp only [energy, PiLp.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    mul_sum]
  apply sum_congr rfl
  intro p _
  ring

 
-- @@ L110-112 verbatim
theorem energy_mul (w : α → ℝ) (r : ℝ) (a : EuclideanSpace ℂ α) :
    energy (fun p => r*w p) a = r*energy w a := by
  simp only [energy, mul_sum, mul_assoc]

 
-- @@ L114-117 verbatim
theorem energy_lower (w : α → ℝ) (d : ℝ) (hw : ∀ p, d ≤ w p)
    (a : EuclideanSpace ℂ α) : d*‖a‖^2 ≤ energy w a := by
  simp only [EuclideanSpace.norm_sq_eq, mul_sum, energy]
  exact sum_le_sum (fun p _ => mul_le_mul_of_nonneg_right (hw p) (sq_nonneg _))

 
-- @@ L119-121 verbatim
theorem energy_nonpos (w : α → ℝ) (hw : ∀ p, w p ≤ 0)
    (a : EuclideanSpace ℂ α) : energy w a ≤ 0 :=
  sum_nonpos (fun p _ => mul_nonpos_of_nonpos_of_nonneg (hw p) (sq_nonneg _))

 
-- @@ L123-131 verbatim
theorem energy_single [DecidableEq α] (w : α → ℝ) (p : α) (z : ℂ) :
    energy w (PiLp.single 2 p z) = w p * ‖z‖^2 := by
  classical
  unfold energy
  rw [sum_eq_single p]
  · simp
  · intro q _ hq
    simp [hq]
  · simp


-- @@ L133-133 verbatim
end

-- @@ L134-134 verbatim
end DiagonalQuadratic


-- @@ L136-136 verbatim
namespace FourierPolynomial

-- @@ L137-137 verbatim
noncomputable section

-- @@ L138-138 verbatim
open MeasureTheory AddCircle Finset

-- @@ L139-139 verbatim
open scoped ComplexConjugate ContDiff

-- @@ L140-140 verbatim
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

-- @@ L141-141 verbatim
variable {ι κ : Type} [Fintype ι] [Fintype κ]

-- @@ L142-142 verbatim
open DiagonalQuadratic

 
-- @@ L144-145 verbatim
def action (k : ι → ℤ) (H : Vector κ → ℝ) (a : Coeff ι κ) : ℝ :=
   energy (fun p => Real.pi*(k p.1 : ℝ)) a - potential k H a

 
-- @@ L147-149 verbatim
theorem contDiff_action (k : ι → ℤ) {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (action k H) :=
  (contDiff_energy _).sub (contDiff_potential k hH)

 
-- @@ L151-161 verbatim
theorem hasGradientAt_action (k : ι → ℤ) {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H)
    (a : Coeff ι κ) :
    HasGradientAt (action k H)
      ((2 : ℝ) • diag (fun p => Real.pi*(k p.1 : ℝ)) a - project k (gradLoop k hH a)) a := by
  have h := (hasGradientAt_energy (fun p : ι × κ => Real.pi*(k p.1 : ℝ)) a).hasFDerivAt.sub
    (hasGradientAt_potential k hH a).hasFDerivAt
  rw [hasGradientAt_iff_hasFDerivAt]
  change HasFDerivAt (action k H) _ a at h
  apply h.congr_fderiv
  ext b
  simp only [map_sub]

 
-- @@ L163-166 verbatim
theorem gradient_action (k : ι → ℤ) {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H)
    (a : Coeff ι κ) : gradient (action k H) a =
      (2 : ℝ) • diag (fun p => Real.pi*(k p.1 : ℝ)) a - project k (gradLoop k hH a) :=
  (hasGradientAt_action k hH a).gradient

 
-- @@ L168-169 verbatim
theorem potential_nonneg (k : ι → ℤ) {H : Vector κ → ℝ} (hH : ∀ z, 0 ≤ H z)
    (a : Coeff ι κ) : 0 ≤ potential k H a := integral_nonneg (fun _ => hH _)

 
-- @@ L171-181 verbatim
theorem integral_energy (k : ι → ℤ) (hk : Function.Injective k) (d : κ → ℝ)
    (a : Coeff ι κ) :
    (∫ t : Time, energy d (loop k a t) ∂μ) = energy (fun p => d p.2) a := by
  classical
  simp only [energy]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul, integral_loop_coord_sq k hk, mul_sum]
    rw [Fintype.sum_prod_type, sum_comm]
  · intro j _
    exact integrable_continuous (continuous_const.mul
      ((((PiLp.continuous_apply 2 _ j).comp (loop k a).continuous).norm.pow 2)))

 
-- @@ L183-193 verbatim
theorem potential_lower (k : ι → ℤ) (hk : Function.Injective k) {H : Vector κ → ℝ}
    (hH : Continuous H) (d : κ → ℝ) (C : ℝ) (hlo : ∀ z, energy d z-C ≤ H z)
    (a : Coeff ι κ) : energy (fun p => d p.2) a-C ≤ potential k H a := by
  have hi : Integrable (fun t : Time => energy d (loop k a t)) μ :=
    integrable_continuous ((contDiff_energy d).continuous.comp (loop k a).continuous)
  calc
    _ = ∫ t : Time, energy d (loop k a t)-C ∂μ := by
      rw [integral_sub hi (integrable_const _), integral_energy k hk]
      simp
    _ ≤ _ := integral_mono (hi.sub (integrable_const _))
      (integrable_continuous (hH.comp (loop k a).continuous)) (fun t => hlo _)

 
-- @@ L195-207 verbatim
theorem potential_upper_fourth (k : ι → ℕ) (hk : Function.Injective k)
    (hk0 : ∀ i, 0 < k i) {H : Vector κ → ℝ} (hH : Continuous H)
    {C : ℝ} (hC : 0 ≤ C) (hup : ∀ z, H z ≤ C*‖z‖^4) (a : Coeff ι κ) :
    potential (fun i => (k i : ℤ)) H a ≤
      C*(Fintype.card κ : ℝ)*(∑ p : ι × κ, (k p.1 : ℝ)*‖a p‖^2)^2 := by
  calc
    _ ≤ ∫ t : Time, C*‖loop (fun i => (k i : ℤ)) a t‖^4 ∂μ :=
      integral_mono (integrable_continuous (hH.comp (loop _ a).continuous))
        (integrable_continuous (continuous_const.mul ((loop _ a).continuous.norm.pow 4)))
        (fun t => hup _)
    _ = C*(∫ t : Time, ‖loop (fun i => (k i : ℤ)) a t‖^4 ∂μ) := integral_const_mul _ _
    _ ≤ _ := by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (integral_loop_norm_fourth_le k hk hk0 a) hC


-- @@ L209-209 verbatim
end

-- @@ L210-210 verbatim
end FourierPolynomial


-- @@ L212-212 verbatim
namespace FourierPolynomial

-- @@ L213-213 verbatim
noncomputable section

-- @@ L214-214 verbatim
open MeasureTheory AddCircle Finset

-- @@ L215-215 verbatim
open scoped ComplexConjugate ContDiff

-- @@ L216-216 verbatim
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

-- @@ L217-217 verbatim
variable {ι κ : Type} [Fintype ι] [Fintype κ]

-- @@ L218-218 verbatim
open DiagonalQuadratic


-- @@ L220-230 verbatim
omit [Fintype ι] in
 theorem project_add (k : ι → ℤ) (f g : C(Time, Vector κ)) :
    project k (f+g) = project k f + project k g := by
  ext p
  change fourierCoeff ((fun t => f t p.2)+(fun t => g t p.2)) (k p.1) = _
  have hf : Integrable (fun t : Time => f t p.2) μ :=
    integrable_continuous ((PiLp.continuous_apply 2 _ p.2).comp f.continuous)
  have hg : Integrable (fun t : Time => g t p.2) μ :=
    integrable_continuous ((PiLp.continuous_apply 2 _ p.2).comp g.continuous)
  rw [fourierCoeff.add hf hg]
  rfl


-- @@ L232-242 verbatim
omit [Fintype ι] in
 theorem project_sub (k : ι → ℤ) (f g : C(Time, Vector κ)) :
    project k (f-g) = project k f - project k g := by
  ext p
  simp only [project_apply, ContinuousMap.sub_apply, PiLp.sub_apply, fourierCoeff,
    smul_sub]
  rw [integral_sub]
  · exact integrable_continuous ((fourier (-k p.1)).continuous.smul
      ((PiLp.continuous_apply 2 _ p.2).comp f.continuous))
  · exact integrable_continuous ((fourier (-k p.1)).continuous.smul
      ((PiLp.continuous_apply 2 _ p.2).comp g.continuous))

 
-- @@ L244-248 verbatim
theorem loop_diag (k : ι → ℤ) (d : κ → ℝ) (a : Coeff ι κ) (t : Time) :
    loop k (diag (fun p => d p.2) a) t = diag d (loop k a t) := by
  ext j
  simp only [loop_coord, eval, diag_apply, RCLike.real_smul_eq_coe_mul, mul_assoc,
    ← mul_sum]

 
-- @@ L250-251 verbatim
theorem loop_smul (k : ι → ℤ) (r : ℝ) (a : Coeff ι κ) :
    loop k (r • a) = r • loop k a := (loopCLM k).map_smul r a

 
-- @@ L253-253 verbatim
theorem loop_zero (k : ι → ℤ) : loop k (0 : Coeff ι κ) = 0 := (loopCLM k).map_zero


-- @@ L255-255 verbatim
end

-- @@ L256-256 verbatim
end FourierPolynomial


-- @@ L258-258 verbatim
namespace FourierPolynomial

-- @@ L259-259 verbatim
noncomputable section

-- @@ L260-260 verbatim
open MeasureTheory AddCircle Finset

-- @@ L261-261 verbatim
open scoped ComplexConjugate ContDiff

-- @@ L262-262 verbatim
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

-- @@ L263-263 verbatim
variable {ι κ : Type} [Fintype ι] [Fintype κ]

-- @@ L264-264 verbatim
open DiagonalQuadratic

 
-- @@ L266-268 verbatim
def remainderLoop (k : ι → ℤ) {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H)
    (d : κ → ℝ) (a : Coeff ι κ) : C(Time, Vector κ) :=
  gradLoop k hH a - loop k ((2 : ℝ) • diag (fun p => d p.2) a)

 
-- @@ L270-274 verbatim
theorem remainderLoop_apply (k : ι → ℤ) {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H)
    (d : κ → ℝ) (a : Coeff ι κ) (t : Time) :
    remainderLoop k hH d a t = gradient H (loop k a t)-(2 : ℝ) • diag d (loop k a t) := by
  simp only [remainderLoop, ContinuousMap.sub_apply, gradLoop, ContinuousMap.coe_mk,
    loop_smul, ContinuousMap.smul_apply, loop_diag]

 
-- @@ L276-286 verbatim
theorem gradient_action_remainder (k : ι → ℤ) (hk : Function.Injective k)
    {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (d : κ → ℝ) (a : Coeff ι κ) :
    gradient (action k H) a =
      (2 : ℝ) • diag (fun p => Real.pi*(k p.1 : ℝ)-d p.2) a-project k (remainderLoop k hH d a) := by
  rw [gradient_action k hH, remainderLoop, project_sub, project_loop k hk]
  have he : diag (fun p : ι × κ => Real.pi*(k p.1 : ℝ)-d p.2) a =
      diag (fun p : ι × κ => Real.pi*(k p.1 : ℝ)) a-diag (fun p : ι × κ => d p.2) a := by
    ext p
    simp only [diag_apply, PiLp.sub_apply, sub_smul]
  rw [he, smul_sub]
  abel

 
-- @@ L288-303 verbatim
theorem norm_gradient_lower (k : ι → ℤ) (hk : Function.Injective k)
    {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (d : κ → ℝ) {γ B : ℝ}
    (hγ : 0 ≤ γ) (hB : 0 ≤ B) (hgap : ∀ i j, γ ≤ |Real.pi*(k i : ℝ)-d j|)
    (hrem : ∀ z, ‖gradient H z-(2 : ℝ) • diag d z‖ ≤ B) (a : Coeff ι κ) :
    2*γ*‖a‖ ≤ ‖gradient (action k H) a‖+B := by
  have hb : ‖project k (remainderLoop k hH d a)‖ ≤ B :=
    project_bounded k hk _ hB (fun t => by rw [remainderLoop_apply]; exact hrem _)
  have hd := norm_diag_lower (fun p : ι × κ => Real.pi*(k p.1 : ℝ)-d p.2) hγ
    (fun p => hgap p.1 p.2) a
  have ht := norm_sub_le (gradient (action k H) a) (-project k (remainderLoop k hH d a))
  rw [sub_neg_eq_add, norm_neg] at ht
  have he : gradient (action k H) a + project k (remainderLoop k hH d a) =
      (2 : ℝ) • diag (fun p => Real.pi*(k p.1 : ℝ)-d p.2) a := by
    rw [gradient_action_remainder k hk hH]; abel
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at ht
  nlinarith

 
-- @@ L305-313 verbatim
theorem gradient_coercive (k : ι → ℤ) (hk : Function.Injective k)
    {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (d : κ → ℝ) {γ B : ℝ}
    (hγ : 0 < γ) (hB : 0 ≤ B) (hgap : ∀ i j, γ ≤ |Real.pi*(k i : ℝ)-d j|)
    (hrem : ∀ z, ‖gradient H z-(2 : ℝ) • diag d z‖ ≤ B) :
    ∃ C : ℝ, ∀ a : Coeff ι κ, C ≤ ‖a‖ → 1 ≤ ‖gradient (action k H) a‖ := by
  refine ⟨(B+1)/(2*γ), fun a ha => ?_⟩
  have h := norm_gradient_lower k hk hH d hγ.le hB hgap hrem a
  have hm := (div_le_iff₀ (mul_pos (by norm_num) hγ)).mp ha
  nlinarith

 
-- @@ L315-323 verbatim
theorem critical_norm_bound (k : ι → ℤ) (hk : Function.Injective k)
    {H : Vector κ → ℝ} (hH : ContDiff ℝ ∞ H) (d : κ → ℝ) {γ B : ℝ}
    (hγ : 0 < γ) (hB : 0 ≤ B) (hgap : ∀ i j, γ ≤ |Real.pi*(k i : ℝ)-d j|)
    (hrem : ∀ z, ‖gradient H z-(2 : ℝ) • diag d z‖ ≤ B) (a : Coeff ι κ)
    (ha : gradient (action k H) a = 0) : ‖a‖ ≤ B/(2*γ) := by
  have h := norm_gradient_lower k hk hH d hγ.le hB hgap hrem a
  rw [ha, norm_zero, zero_add] at h
  rw [le_div_iff₀ (mul_pos (by norm_num) hγ)]
  nlinarith


-- @@ L325-325 verbatim
end

-- @@ L326-326 verbatim
end FourierPolynomial


-- @@ L328-328 verbatim
end NonsqueezingInline


-- @@ L330-330 verbatim
end OAI
