import OAI.Geometry.PolarProducts.MoserFlow


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u27 u28 u29


-- @@ L7-7 verbatim
section LowerBoundInline

-- @@ L8-8 verbatim
open Set Filter Function

-- @@ L9-9 verbatim
open scoped Topology ContDiff NNReal

-- @@ L10-10 verbatim
open Set Filter Metric

-- @@ L11-11 verbatim
open scoped Topology ContDiff

-- @@ L12-12 verbatim
open Set Filter Function MeasureTheory Metric

-- @@ L13-13 verbatim
open scoped Topology ContDiff NNReal

-- @@ L14-14 verbatim
open Set Filter Function

-- @@ L15-15 verbatim
open scoped Topology ContDiff

-- @@ L16-16 verbatim
open Set Filter Function

-- @@ L17-17 verbatim
open scoped Topology ContDiff NNReal

-- @@ L18-18 verbatim
open Set Filter

-- @@ L19-19 verbatim
open scoped Topology ContDiff

-- @@ L20-20 verbatim
open Set Filter Function

-- @@ L21-21 verbatim
open scoped Topology ContDiff


-- @@ L23-23 verbatim
namespace ComplexPotential


-- @@ L25-25 verbatim
open TensorCalculus Set Filter

-- @@ L26-26 verbatim
open scoped Topology ContDiff


-- @@ L28-28 verbatim
variable {E : Type u27} [NormedAddCommGroup E] [NormedSpace ℝ E]


-- @@ L30-30 verbatim
noncomputable section


-- @@ L32-32 verbatim
local instance oneTensorGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance

-- @@ L33-33 verbatim
local instance oneTensorSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance

-- @@ L34-34 verbatim
local instance twoTensorGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

-- @@ L35-35 verbatim
local instance twoTensorSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance


-- @@ L37-38 verbatim
def dcOp (J : E →L[ℝ] E) : (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ :=
  (-1 / 4 : ℝ) • (ContinuousLinearMap.compL ℝ E E ℝ).flip J


-- @@ L40-41 verbatim
def dc (J : E →L[ℝ] E) (φ : E → ℝ) (x : E) : E →L[ℝ] ℝ :=
  dcOp J (fderiv ℝ φ x)


-- @@ L43-43 verbatim
def ddc (J : E →L[ℝ] E) (φ : E → ℝ) : E → TwoTensor E := exteriorD (dc J φ)


-- @@ L45-49 verbatim
@[simp] theorem dcOp_apply (J : E →L[ℝ] E) (L : E →L[ℝ] ℝ) (a : E) :
    dcOp J L a = -(L (J a)) / 4 := by
  simp only [dcOp, smul_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  ring


-- @@ L51-52 verbatim
@[simp] theorem dc_apply (J : E →L[ℝ] E) (φ : E → ℝ) (x a : E) :
    dc J φ x a = -(fderiv ℝ φ x (J a)) / 4 := dcOp_apply J _ a


-- @@ L54-57 verbatim
theorem contDiffAt_dc (J : E →L[ℝ] E) {φ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) : ContDiffAt ℝ ∞ (dc J φ) x := by
  change ContDiffAt ℝ ∞ (dcOp J ∘ fderiv ℝ φ) x
  exact (dcOp J).contDiff.contDiffAt.comp x (hφ.fderiv_right (m := ∞) (by simp))


-- @@ L59-62 verbatim
theorem contDiff_dc (J : E →L[ℝ] E) {φ : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (dc J φ) := by
  rw [contDiff_iff_contDiffAt]
  exact fun x => contDiffAt_dc J (hφ.contDiffAt (x := x))


-- @@ L64-69 verbatim
theorem fderiv_dc (J : E →L[ℝ] E) {φ : E → ℝ} {x : E}
    (hφ : DifferentiableAt ℝ (fderiv ℝ φ) x) (a b : E) :
    fderiv ℝ (dc J φ) x a b = -(fderiv ℝ (fderiv ℝ φ) x a (J b)) / 4 := by
  change fderiv ℝ (dcOp J ∘ fderiv ℝ φ) x a b = _
  rw [fderiv_comp x (dcOp J).differentiableAt hφ]
  simp


-- @@ L71-76 verbatim
theorem ddc_apply (J : E →L[ℝ] E) {φ : E → ℝ} {x : E}
    (hφ : DifferentiableAt ℝ (fderiv ℝ φ) x) (a b : E) :
    ddc J φ x a b =
      (fderiv ℝ (fderiv ℝ φ) x b (J a) - fderiv ℝ (fderiv ℝ φ) x a (J b)) / 4 := by
  simp only [ddc, exteriorD_apply, fderiv_dc J hφ]
  ring


-- @@ L78-79 verbatim
theorem ddc_skew (J : E →L[ℝ] E) (φ : E → ℝ) (x a b : E) :
    ddc J φ x a b = -ddc J φ x b a := exteriorD_skew _ _ _ _


-- @@ L81-85 verbatim
theorem contDiffAt_ddc (J : E →L[ℝ] E) {φ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) : ContDiffAt ℝ ∞ (ddc J φ) x := by
  change ContDiffAt ℝ ∞ (alt ∘ fderiv ℝ (dc J φ)) x
  exact (alt (E := E)).contDiff.contDiffAt.comp x
    ((contDiffAt_dc J hφ).fderiv_right (m := ∞) (by simp))


-- @@ L87-89 verbatim
theorem contDiff_ddc (J : E →L[ℝ] E) {φ : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (ddc J φ) :=
  contDiff_exteriorD (contDiff_dc J hφ)


-- @@ L91-94 verbatim
theorem ddc_closed (J : E →L[ℝ] E) {φ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) (a b c : E) :
    fderiv ℝ (ddc J φ) x a b c + fderiv ℝ (ddc J φ) x b c a +
      fderiv ℝ (ddc J φ) x c a b = 0 := exteriorD_closed (contDiffAt_dc J hφ) a b c


-- @@ L96-102 verbatim
theorem ddc_complex_line (J : E →L[ℝ] E) (hJ : ∀ a, J (J a) = -a)
    {φ : E → ℝ} {x : E} (hφ : DifferentiableAt ℝ (fderiv ℝ φ) x) (a : E) :
    ddc J φ x a (J a) =
      (fderiv ℝ (fderiv ℝ φ) x a a + fderiv ℝ (fderiv ℝ φ) x (J a) (J a)) / 4 := by
  rw [ddc_apply J hφ, hJ]
  simp only [map_neg]
  ring


-- @@ L104-105 verbatim
def IsPSHAt (J : E →L[ℝ] E) (φ : E → ℝ) (x : E) : Prop :=
  ContDiffAt ℝ ∞ φ x ∧ ∀ a, 0 ≤ ddc J φ x a (J a)


-- @@ L107-109 verbatim
theorem dc_congr (J : E →L[ℝ] E) {φ ψ : E → ℝ} {x : E}
    (h : φ =ᶠ[𝓝 x] ψ) : dc J φ x = dc J ψ x := by
  rw [dc, dc, h.fderiv_eq]


-- @@ L111-114 verbatim
theorem ddc_congr (J : E →L[ℝ] E) {φ ψ : E → ℝ} {x : E}
    (h : φ =ᶠ[𝓝 x] ψ) : ddc J φ x = ddc J ψ x := by
  have he : dc J φ =ᶠ[𝓝 x] dc J ψ := h.eventuallyEq_nhds.mono (fun y hy => dc_congr J hy)
  simpa only [ddc, exteriorD] using congrArg alt he.fderiv_eq


-- @@ L116-119 verbatim
theorem dc_add (J : E →L[ℝ] E) {φ ψ : E → ℝ} {x : E}
    (hφ : DifferentiableAt ℝ φ x) (hψ : DifferentiableAt ℝ ψ x) :
    dc J (fun y => φ y + ψ y) x = dc J φ x + dc J ψ x := by
  simp only [dc, fderiv_fun_add hφ hψ, map_add]


-- @@ L121-132 verbatim
theorem ddc_add (J : E →L[ℝ] E) {φ ψ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) (hψ : ContDiffAt ℝ ∞ ψ x) :
    ddc J (fun y => φ y + ψ y) x = ddc J φ x + ddc J ψ x := by
  have h1 : (1 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have he : dc J (fun y => φ y + ψ y) =ᶠ[𝓝 x] fun y => dc J φ y + dc J ψ y := by
    filter_upwards [(hφ.of_le h1).eventually (by simp),
      (hψ.of_le h1).eventually (by simp)] with y hy hz
    exact dc_add J (hy.differentiableAt (by simp)) (hz.differentiableAt (by simp))
  unfold ddc exteriorD
  rw [he.fderiv_eq, fderiv_fun_add
    ((contDiffAt_dc J hφ).differentiableAt (by simp))
    ((contDiffAt_dc J hψ).differentiableAt (by simp)), map_add]


-- @@ L134-134 verbatim
end

-- @@ L135-135 verbatim
end ComplexPotential


-- @@ L137-137 verbatim
namespace ComplexPotential


-- @@ L139-139 verbatim
open TensorCalculus

-- @@ L140-140 verbatim
open scoped ContDiff Topology


-- @@ L142-142 verbatim
variable {E : Type u28} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


-- @@ L144-144 verbatim
noncomputable section


-- @@ L146-146 verbatim
def standardTensor (J : E →L[ℝ] E) : TwoTensor E := (innerSL ℝ).comp J


-- @@ L148-149 verbatim
@[simp] theorem standardTensor_apply (J : E →L[ℝ] E) (a b : E) :
    standardTensor J a b = inner (𝕜 := ℝ) (J a) b := rfl


-- @@ L151-158 verbatim
theorem dc_norm_sq (J : E →L[ℝ] E)
    (hsk : ∀ a b, inner (𝕜 := ℝ) a (J b) = -inner (𝕜 := ℝ) (J a) b) (x : E) :
    dc J (fun x : E => ‖x‖^2) x = (1 / 2 : ℝ) • standardTensor J x := by
  ext a
  rw [dc_apply, fderiv_norm_sq_apply]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply, standardTensor_apply]
  rw [hsk]
  ring


-- @@ L160-178 verbatim
theorem ddc_norm_sq (J : E →L[ℝ] E)
    (hsk : ∀ a b, inner (𝕜 := ℝ) a (J b) = -inner (𝕜 := ℝ) (J a) b) (x : E) :
    ddc J (fun x : E => ‖x‖^2) x = standardTensor J := by
  have he : dc J (fun x : E => ‖x‖^2) = fun x => (1 / 2 : ℝ) • standardTensor J x :=
    funext (dc_norm_sq J hsk)
  apply ContinuousLinearMap.ext
  intro a
  apply ContinuousLinearMap.ext
  intro b
  rw [ddc, he, exteriorD_apply]
  have hd : fderiv ℝ (fun x => (1 / 2 : ℝ) • standardTensor J x) x =
      (1 / 2 : ℝ) • standardTensor J := by
    exact ((standardTensor J).hasFDerivAt.const_smul (1 / 2 : ℝ)).fderiv
  rw [hd]
  simp only [smul_apply, smul_eq_mul, standardTensor_apply]
  have hh : inner (𝕜 := ℝ) (J b) a = -inner (𝕜 := ℝ) (J a) b := by
    rw [real_inner_comm, hsk]
  rw [hh]
  ring


-- @@ L180-182 verbatim
theorem standardTensor_complex_line (J : E →L[ℝ] E) (hJ : ∀ a, ‖J a‖ = ‖a‖) (a : E) :
    standardTensor J a (J a) = ‖a‖^2 := by
  rw [standardTensor_apply, real_inner_self_eq_norm_sq, hJ]


-- @@ L184-204 verbatim
theorem isInvertible_of_positive_complex_line [FiniteDimensional ℝ E]
    (B : TwoTensor E) (J : E →L[ℝ] E) (hp : ∀ a : E, a ≠ 0 → 0 < B a (J a)) :
    B.IsInvertible := by
  have hi : Function.Injective B := by
    intro a b hab
    have hz : B (a - b) = 0 := by rw [map_sub, hab, sub_self]
    by_contra hn
    have hpos := hp (a - b) (sub_ne_zero.mpr hn)
    rw [hz, zero_apply] at hpos
    exact (lt_irrefl 0) hpos
  let e := (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv
  let L : E →L[ℝ] E := e.symm.toContinuousLinearMap.comp B
  have hL : Function.Injective L := e.symm.injective.comp hi
  have hsL : Function.Surjective L := LinearMap.surjective_of_injective hL
  have hs : Function.Surjective B := by
    intro v
    obtain ⟨x, hx⟩ := hsL (e.symm v)
    refine ⟨x, ?_⟩
    exact e.symm.injective hx
  exact ⟨ContinuousLinearEquiv.ofBijective B (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr hs), rfl⟩


-- @@ L206-214 verbatim
theorem isInvertible_ddc_norm_sq_add [FiniteDimensional ℝ E]
    (J : E →L[ℝ] E) (hsk : ∀ a b, inner (𝕜 := ℝ) a (J b) = -inner (𝕜 := ℝ) (J a) b)
    (hJ : ∀ a, ‖J a‖ = ‖a‖) {φ : E → ℝ} {x : E} (hφ : IsPSHAt J φ x) :
    (ddc J (fun y => ‖y‖^2 + φ y) x).IsInvertible := by
  apply isInvertible_of_positive_complex_line _ J
  intro a ha
  rw [ddc_add J (contDiff_norm_sq ℝ).contDiffAt hφ.1, add_apply, add_apply,
    ddc_norm_sq J hsk, standardTensor_complex_line J hJ]
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (norm_pos_iff.mpr ha)) (hφ.2 a)


-- @@ L216-216 verbatim
end

-- @@ L217-217 verbatim
end ComplexPotential


-- @@ L219-219 verbatim
namespace ComplexPotential


-- @@ L221-221 verbatim
open TensorCalculus Set Filter

-- @@ L222-222 verbatim
open scoped ContDiff Topology


-- @@ L224-224 verbatim
variable {E : Type u29} [NormedAddCommGroup E] [NormedSpace ℝ E]


-- @@ L226-226 verbatim
noncomputable section


-- @@ L228-228 verbatim
local instance linearOneGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance

-- @@ L229-229 verbatim
local instance linearOneSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance

-- @@ L230-230 verbatim
local instance linearTwoGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

-- @@ L231-231 verbatim
local instance linearTwoSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance


-- @@ L233-235 verbatim
@[simp] theorem dc_const (J : E →L[ℝ] E) (c : ℝ) (x : E) :
    dc J (fun _ => c) x = 0 := by
  simp [dc]


-- @@ L237-239 verbatim
@[simp] theorem ddc_const (J : E →L[ℝ] E) (c : ℝ) (x : E) :
    ddc J (fun _ => c) x = 0 := by
  simp [ddc, exteriorD, show dc J (fun _ : E => c) = fun _ => 0 by funext y; simp]


-- @@ L241-247 verbatim
theorem dc_const_smul (J : E →L[ℝ] E) (c : ℝ) {φ : E → ℝ} {x : E}
    (hφ : DifferentiableAt ℝ φ x) :
    dc J (fun y => c * φ y) x = c • dc J φ x := by
  ext a
  rw [dc_apply, fderiv_const_mul hφ]
  simp only [smul_apply, smul_eq_mul, dc_apply]
  ring


-- @@ L249-260 verbatim
theorem ddc_const_smul (J : E →L[ℝ] E) (c : ℝ) {φ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) :
    ddc J (fun y => c * φ y) x = c • ddc J φ x := by
  have h1 : (1 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have he : dc J (fun y => c * φ y) =ᶠ[𝓝 x] fun y => c • dc J φ y := by
    filter_upwards [(hφ.of_le h1).eventually (by simp)] with y hy
    exact dc_const_smul J c (hy.differentiableAt one_ne_zero)
  unfold ddc exteriorD
  rw [he.fderiv_eq]
  have hd : fderiv ℝ (fun y => c • dc J φ y) x = c • fderiv ℝ (dc J φ) x :=
    (((contDiffAt_dc J hφ).differentiableAt (by simp)).hasFDerivAt.const_smul c).fderiv
  rw [hd, map_smul]


-- @@ L262-265 verbatim
theorem ddc_neg (J : E →L[ℝ] E) {φ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) :
    ddc J (fun y => -φ y) x = -ddc J φ x := by
  simpa only [neg_one_mul, neg_one_smul] using ddc_const_smul J (-1) hφ


-- @@ L267-271 verbatim
theorem ddc_sub (J : E →L[ℝ] E) {φ ψ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) (hψ : ContDiffAt ℝ ∞ ψ x) :
    ddc J (fun y => φ y - ψ y) x = ddc J φ x - ddc J ψ x := by
  simp_rw [sub_eq_add_neg]
  rw [ddc_add J hφ hψ.neg, ddc_neg J hψ]


-- @@ L273-276 verbatim
theorem ddc_add_const (J : E →L[ℝ] E) {φ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) (c : ℝ) :
    ddc J (fun y => φ y + c) x = ddc J φ x := by
  rw [ddc_add J hφ contDiffAt_const, ddc_const, add_zero]


-- @@ L278-281 verbatim
theorem ddc_sub_const (J : E →L[ℝ] E) {φ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) (c : ℝ) :
    ddc J (fun y => φ y - c) x = ddc J φ x := by
  rw [ddc_sub J hφ contDiffAt_const, ddc_const, sub_zero]


-- @@ L283-288 verbatim
theorem IsPSHAt.add {J : E →L[ℝ] E} {φ ψ : E → ℝ} {x : E}
    (hφ : IsPSHAt J φ x) (hψ : IsPSHAt J ψ x) :
    IsPSHAt J (fun y => φ y + ψ y) x := by
  refine ⟨hφ.1.add hψ.1, fun a => ?_⟩
  rw [ddc_add J hφ.1 hψ.1, add_apply, add_apply]
  exact add_nonneg (hφ.2 a) (hψ.2 a)


-- @@ L290-295 verbatim
theorem IsPSHAt.const_smul {J : E →L[ℝ] E} {φ : E → ℝ} {x : E}
    (hφ : IsPSHAt J φ x) {c : ℝ} (hc : 0 ≤ c) :
    IsPSHAt J (fun y => c * φ y) x := by
  refine ⟨contDiffAt_const.mul hφ.1, fun a => ?_⟩
  rw [ddc_const_smul J c hφ.1]
  simpa only [smul_apply, smul_eq_mul] using mul_nonneg hc (hφ.2 a)


-- @@ L297-301 verbatim
theorem IsPSHAt.sub_const {J : E →L[ℝ] E} {φ : E → ℝ} {x : E}
    (hφ : IsPSHAt J φ x) (c : ℝ) : IsPSHAt J (fun y => φ y - c) x := by
  refine ⟨hφ.1.sub contDiffAt_const, fun a => ?_⟩
  rw [ddc_sub_const J hφ.1 c]
  exact hφ.2 a


-- @@ L303-303 verbatim
end

-- @@ L304-304 verbatim
end ComplexPotential


-- @@ L306-306 verbatim
end LowerBoundInline


-- @@ L308-308 verbatim
end OAI
